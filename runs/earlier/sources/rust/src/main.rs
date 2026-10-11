//! `rchk` checks the stored values behind an upper bound for the Beardwood–Halton–Hammersley
//! travelling salesman constant.
//!
//! The file `RECIPE.md` defines, by integer arithmetic alone, a number that is an upper bound
//! for the constant, together with the intermediate integers that lead to it. A values file
//! records these integers. This program computes all of them again from the parameters in a
//! spec file, compares them with the values file, and applies the test of Section 8 of the
//! recipe: the bound must not exceed the threshold that the spec file names.
//!
//! # Building
//!
//! ```text
//! cargo build --release
//! ```
//!
//! The crate has no dependencies. The tests are run with `cargo test --release`.
//!
//! # Running
//!
//! ```text
//! rchk SPEC [-j N]
//! ```
//!
//! `SPEC` is the spec file; it names the values file. `N` is the number of threads for the cell
//! sums of Section 7: a number that is at least 1 (1 if `-j` is absent). At most 1024 threads
//! are started, and never more than there are gap tuples. The output does not depend on `N`.
//!
//! # The steps of the check
//!
//! These are the steps of Section 10 of the recipe, in its order. The first that fails decides
//! the exit status.
//!
//! 1. The command line has the form above, and the spec file can be read, has the prescribed
//!    form and has its parameters in the ranges of Section 1; otherwise status 2.
//! 2. The values file can be read and has the prescribed form; otherwise status 2.
//! 3. The seven parameter lines of the values file give the same numbers as those of the spec
//!    file; otherwise status 1.
//! 4. The values file has as many masses, table lines, numbers in each table line and cell sums
//!    as the parameters require; otherwise status 2.
//! 5. Every number of the values file equals the recomputed one; otherwise status 1.
//! 6. The test of Section 8 holds; otherwise status 1.
//!
//! Nothing is recomputed before step 4 has passed. After that, an arithmetic bound that is
//! violated gives status 2 at whatever point this occurs, and so do tables that would need
//! more memory than the program is willing to take.
//!
//! # Output
//!
//! With status 0 the standard output receives exactly five lines:
//!
//! ```text
//! the stored values agree with the recomputed values
//! total <A_0>
//! bound <ceil(B·10^12)/10^12, with 12 decimals> (rounded up)
//! bound <= <θ_1>/<θ_2>
//! ACCEPTED
//! ```
//!
//! With status 1 its last line begins with `REJECTED:` and says what failed: the first number
//! that differs, or the threshold that the bound exceeds; in the second case the first three
//! of the lines above precede it. With status 2 it receives nothing. Messages about the
//! progress, the running times and the reason for status 2 go to the standard error stream.
//!
//! # Arithmetic
//!
//! All arithmetic is exact, in unsigned integers: 64 or 128 bits for the quantities of the
//! recipe, smaller types for keys, places and counts. There is no floating point.
//! No operation can wrap silently. Where a bound of Section 9 of the recipe is relied upon, it
//! is checked: either each operation separately (`arith`), or once for a whole loop, in which
//! case the comment at the check says why it covers the loop. In addition the release profile
//! keeps the overflow checks of the compiler switched on.

#![forbid(unsafe_code)]
#![warn(clippy::pedantic)]
// The names follow the recipe, where many quantities have one letter or differ in one.
#![allow(clippy::many_single_char_names, clippy::similar_names)]
// The comments use the notation of the recipe, such as W_c(i); these are not names of the code.
#![allow(clippy::doc_markdown)]

mod arith;
mod failure;
mod files;
mod keys;
mod paths;
mod sizes;
mod tables;
mod total;

use std::ffi::{OsStr, OsString};
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use crate::arith::{power, wide};
use crate::failure::{invalid, note, rejected, Outcome, Stop};
use crate::files::{parameter_name, Params, Spec, Values};
use crate::keys::Keys;
use crate::sizes::Sizes;
use crate::total::Verdict;

/// At most this many threads are started, however large the number after `-j` is.
const MAX_THREADS: usize = 1024;

fn main() -> ExitCode {
    let arguments: Vec<OsString> = std::env::args_os().skip(1).collect();
    // A panic would mean a mistake in this program, for instance an overflow that the checks
    // before it should have excluded. It must not look like a verdict on the stored values.
    let outcome = std::panic::catch_unwind(|| run(&arguments))
        .unwrap_or_else(|_| invalid("internal error; no verdict".to_string()));
    let status = conclusion(outcome).and_then(|(status, text)| {
        // Nothing has been written to the standard output before this point, so that with
        // status 2 it stays empty. A verdict that cannot be written is no verdict either.
        let mut output = std::io::stdout().lock();
        let written = output.write_all(text.as_bytes());
        match written.and_then(|()| output.flush()) {
            Ok(()) => Ok(status),
            Err(error) => Err(format!("the standard output cannot be written: {error}")),
        }
    });
    match status {
        Ok(status) => ExitCode::from(status),
        Err(reason) => {
            note(&format!("rchk: {reason}"));
            ExitCode::from(2)
        }
    }
}

/// The exit status 0 or 1 with the text for the standard output (Section 10, "Output"), or
/// the reason for exit status 2, which goes to the standard error stream.
fn conclusion(outcome: Outcome<Agreement>) -> Result<(u8, String), String> {
    match outcome {
        Ok(agreement) => Ok((u8::from(!agreement.verdict.accepted), agreement.text())),
        Err(Stop::Rejected(reason)) => Ok((1, format!("REJECTED: {reason}\n"))),
        Err(Stop::Invalid(reason)) => Err(reason),
    }
}

/// The number of threads for the field after `-j`: N is written in decimal digits and is at
/// least 1. Section 10 sets no upper limit, so every such N is taken; what exceeds
/// `MAX_THREADS` counts as `MAX_THREADS`.
fn thread_count(field: &OsStr) -> Option<usize> {
    let digits = field.to_str()?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let significant = digits.trim_start_matches('0');
    if significant.is_empty() {
        // N = 0.
        return None;
    }
    // A number too long for a machine word is above the limit as well.
    Some(
        significant
            .parse()
            .map_or(MAX_THREADS, |threads: usize| threads.min(MAX_THREADS)),
    )
}

/// Reads `SPEC` or `SPEC -j N` (Section 10).
fn command_line(arguments: &[OsString]) -> Outcome<(PathBuf, usize)> {
    let threads = match arguments {
        [_] => Some(1),
        [_, flag, number] if flag == "-j" => thread_count(number),
        _ => None,
    };
    match threads {
        Some(threads) => Ok((PathBuf::from(&arguments[0]), threads)),
        None => invalid("usage: rchk SPEC [-j N], with a number N of at least 1".to_string()),
    }
}

/// Stops with exit status 1 unless the values file has the recomputed number.
fn agree(expected: u128, found: u128, place: impl FnOnce() -> String) -> Outcome<()> {
    if expected == found {
        return Ok(());
    }
    rejected(format!(
        "{}: the values file has {found}, the recomputed number is {expected}",
        place()
    ))
}

/// Writes the numbers of a line as they stand in a file.
fn spaced(numbers: &[u128]) -> String {
    let numbers: Vec<String> = numbers.iter().map(u128::to_string).collect();
    numbers.join(" ")
}

/// Step 3 of Section 10: the parameter lines of the values file repeat those of the spec file.
/// They are compared as numbers and are not held to the ranges of Section 1, so that a
/// parameter out of range is a parameter that differs.
fn compare_parameters(params: &Params, values: &Values) -> Outcome<()> {
    for (position, expected) in params.lines().iter().enumerate() {
        let found = &values.params[position];
        if expected != found {
            return rejected(format!(
                "parameter line `{}`: the values file has `{}`, the spec file has `{}`",
                parameter_name(position),
                spaced(found),
                spaced(expected)
            ));
        }
    }
    Ok(())
}

/// Step 4 of Section 10: the values file has m masses, one table line of m + n numbers for
/// each key, and m^k cell sums.
fn compare_counts(params: &Params, keys: &Keys, values: &Values) -> Outcome<()> {
    let (cells, columns) = (params.cells(), params.cells() + params.n);
    let tuples = power(wide(cells), params.k, "m^k")?;
    let counts = [
        ("masses", wide(cells), values.masses.len()),
        ("table lines", wide(keys.len()), values.table.len()),
        ("cell sums", tuples, values.sums.len()),
    ];
    for (what, expected, found) in counts {
        if expected != wide(found) {
            return invalid(format!(
                "the values file has {found} {what} instead of {expected}"
            ));
        }
    }
    if let Some(line) = values.table.iter().position(|line| line.len() != columns) {
        return invalid(format!(
            "table line {} of the values file has {} numbers instead of {columns}",
            line + 1,
            values.table[line].len()
        ));
    }
    Ok(())
}

/// The first part of step 5: the masses, the tail term and the table (Sections 3 and 6), in
/// the order of the values file.
fn compare_tables(
    params: &Params,
    keys: &Keys,
    tables: &tables::Tables,
    values: &Values,
) -> Outcome<()> {
    for (c, (&expected, &found)) in tables.masses.iter().zip(&values.masses).enumerate() {
        agree(expected, found, || format!("masses, cell {c}"))?;
    }
    agree(tables.tail_term, values.tail_term, || {
        "tail_term".to_string()
    })?;
    let (cells, n) = (params.cells(), params.n);
    let rows = tables.table.chunks_exact(n);
    for (line, ((key, row), stored)) in keys.iter().zip(rows).zip(&values.table).enumerate() {
        let key: Vec<u128> = key[..cells]
            .iter()
            .map(|&count| u128::from(count))
            .collect();
        if key != stored[..cells] {
            return rejected(format!(
                "table line {}: the values file has the key `{}`, the key in this place is `{}`",
                line + 1,
                spaced(&stored[..cells]),
                spaced(&key)
            ));
        }
        for (d, (&expected, &found)) in row.iter().zip(&stored[cells..]).enumerate() {
            agree(u128::from(expected), found, || {
                format!("table, key `{}`, height difference {d}", spaced(&key))
            })?;
        }
    }
    Ok(())
}

/// The bound with 12 decimals, from ceil(B·10^12).
fn decimal(scaled: u128) -> String {
    let unit = 1_000_000_000_000;
    format!("{}.{:012}", scaled / unit, scaled % unit)
}

/// A duration in seconds, to the millisecond.
fn seconds(since: Instant) -> String {
    let elapsed = since.elapsed();
    format!("{}.{:03} s", elapsed.as_secs(), elapsed.subsec_millis())
}

/// The result of a check in which every stored value agrees: what is left is the outcome of
/// the test of Section 8.
struct Agreement {
    /// A_0.
    total: u128,
    /// θ_1 and θ_2.
    threshold: (u64, u64),
    verdict: Verdict,
}

impl Agreement {
    /// The lines for the standard output (Section 10, "Output").
    fn text(&self) -> String {
        let (theta_1, theta_2) = self.threshold;
        let end = if self.verdict.accepted {
            format!("bound <= {theta_1}/{theta_2}\nACCEPTED")
        } else {
            format!("REJECTED: the bound exceeds the threshold {theta_1}/{theta_2}")
        };
        format!(
            "the stored values agree with the recomputed values\n\
             total {}\n\
             bound {} (rounded up)\n\
             {end}\n",
            self.total,
            decimal(self.verdict.decimals)
        )
    }
}

/// Steps 1 and 2 of Section 10, which are the reading of the two files, and then the further
/// steps. Nothing is written to the standard output here.
fn run(arguments: &[OsString]) -> Outcome<Agreement> {
    let (spec_path, threads) = command_line(arguments)?;
    let spec = Spec::read(&spec_path)?;
    let values = Values::read(&spec.values_path(&spec_path))?;
    check(&spec, &values, threads)
}

/// Steps 3 to 6 of Section 10, for a spec file and a values file that have the prescribed
/// form. Nothing is recomputed before step 4 has passed. Step 5 follows the order of the values
/// file: the masses, the tail term and the table are compared when Sections 2–6 have been
/// carried out, the cell sums after Section 7, and the total last.
fn check(spec: &Spec, values: &Values, threads: usize) -> Outcome<Agreement> {
    let params = &spec.params;
    let Ok(gaps) = u8::try_from(params.k) else {
        return invalid("k is too large".to_string());
    };
    let keys = Keys::new(params.cells(), gaps);
    compare_parameters(params, values)?;
    compare_counts(params, &keys, values)?;

    let mut sizes = Sizes::default();
    let started = Instant::now();
    let tables = tables::build(params, &keys, &mut sizes)?;
    note(&format!(
        "rchk: Sections 2-6: table of {} keys after {}",
        keys.len(),
        seconds(started)
    ));
    compare_tables(params, &keys, &tables, values)?;
    note("rchk: parameters, masses, tail term and table agree");

    let started = Instant::now();
    let sums = paths::cell_sums(params, &keys, &tables.table, threads, &mut sizes)?;
    let tuples = power(wide(params.n), params.k + 1, "n^(k+1)")?;
    let picoseconds = started.elapsed().as_nanos() * 1000 / (wide(sums.len()) * tuples);
    note(&format!(
        "rchk: Section 7: {} cell sums of {tuples} height tuples each after {}, \
         with -j {threads}: {}.{:03} ns of wall time for a height tuple",
        sums.len(),
        seconds(started),
        picoseconds / 1000,
        picoseconds % 1000
    ));
    for (index, (&expected, &found)) in sums.iter().zip(&values.sums).enumerate() {
        agree(expected, found, || format!("sums, gap tuple {index}"))?;
    }

    let total = total::total(&tables.masses, &sums, params.k, &mut sizes)?;
    agree(total, values.total, || "total".to_string())?;
    let verdict = total::test(total, params, spec.threshold, &mut sizes)?;
    note("rchk: largest values, in binary digits:");
    for line in sizes.report() {
        note(&format!("rchk:   {line}"));
    }
    Ok(Agreement {
        total,
        threshold: spec.threshold,
        verdict,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The small example of the recipe: `data/specs/tiny.txt` and its values file.
    const SPEC: &str = include_str!("../../../data/specs/tiny.txt");
    const VALUES: &str = include_str!("../../../data/values/tiny.txt");

    /// The five lines that Section 10 shows for the small example.
    const ACCEPTED: &str = "the stored values agree with the recomputed values\n\
                            total 1907697663974\n\
                            bound 0.913931018519 (rounded up)\n\
                            bound <= 95/100\n\
                            ACCEPTED\n";

    /// The exit status and the standard output for the texts of a spec file and of a values
    /// file.
    fn end(spec: &str, values: &str) -> (u8, String) {
        let outcome = Spec::parse("spec", spec).and_then(|spec| {
            let values = Values::parse("values", values)?;
            check(&spec, &values, 2)
        });
        conclusion(outcome).unwrap_or_else(|_| (2, String::new()))
    }

    /// The exit status for the spec file of the small example and the given values file. With
    /// status 1 the output must be one line that begins with `REJECTED:`.
    fn status(values: &str) -> u8 {
        let (status, output) = end(SPEC, values);
        if status == 1 {
            assert!(output.starts_with("REJECTED: ") && output.ends_with('\n'));
            assert_eq!(output.lines().count(), 1);
        }
        status
    }

    fn arguments(words: &[&str]) -> Vec<OsString> {
        words.iter().map(OsString::from).collect()
    }

    #[test]
    fn the_command_line() {
        let read = |words: &[&str]| command_line(&arguments(words)).ok();
        assert_eq!(read(&["spec.txt"]), Some((PathBuf::from("spec.txt"), 1)));
        assert_eq!(
            read(&["spec.txt", "-j", "4"]),
            Some((PathBuf::from("spec.txt"), 4))
        );
        assert_eq!(
            read(&["spec.txt", "-j", "0012"]),
            Some((PathBuf::from("spec.txt"), 12))
        );
        assert_eq!(
            read(&["spec.txt", "-j", "1024"]),
            Some((PathBuf::from("spec.txt"), 1024))
        );
        assert_eq!(read(&[]), None);
        assert_eq!(read(&["-j", "4"]), None);
        assert_eq!(read(&["-j", "4", "spec.txt"]), None);
        assert_eq!(read(&["spec.txt", "-j"]), None);
        assert_eq!(read(&["spec.txt", "-j", "0"]), None);
        assert_eq!(read(&["spec.txt", "-j", "four"]), None);
        assert_eq!(read(&["spec.txt", "-j", "-4"]), None);
        assert_eq!(read(&["spec.txt", "-j", "+4"]), None);
        assert_eq!(read(&["spec.txt", "-j", ""]), None);
        assert_eq!(read(&["spec.txt", "-j", "000"]), None);
        assert_eq!(read(&["spec.txt", "-j", "4 "]), None);
        assert_eq!(read(&["spec.txt", "-j", "4.0"]), None);
        // Section 10 sets no upper limit for N; no more than 1024 threads are started.
        let most = Some((PathBuf::from("spec.txt"), 1024));
        assert_eq!(read(&["spec.txt", "-j", "1025"]), most);
        assert_eq!(read(&["spec.txt", "-j", "99999999999999999999999"]), most);
        let long = "9".repeat(5000);
        assert_eq!(read(&["spec.txt", "-j", &long]), most);
        assert_eq!(read(&["spec.txt", "-j4"]), None);
        assert_eq!(read(&["spec.txt", "-J", "4"]), None);
        assert_eq!(read(&["spec.txt", "-j", "2", "-j", "2"]), None);
        assert_eq!(read(&["spec.txt", "other.txt"]), None);
        assert_eq!(read(&["spec.txt", "-j", "2", "other.txt"]), None);
    }

    #[test]
    fn the_bound_is_written_with_twelve_decimals() {
        assert_eq!(decimal(0), "0.000000000000");
        assert_eq!(decimal(1), "0.000000000001");
        assert_eq!(decimal(873_216_540_001), "0.873216540001");
        assert_eq!(decimal(1_000_000_000_000), "1.000000000000");
        assert_eq!(decimal(12_000_000_000_042), "12.000000000042");
    }

    #[test]
    fn the_small_example_is_accepted() {
        assert_eq!(end(SPEC, VALUES), (0, ACCEPTED.to_string()));
        // Only the numbers of the files matter, not the way in which they are written.
        let rewritten = VALUES
            .replace(' ', "\t ")
            .replace('\n', " \r\n")
            .replace("\nk\t 3", "\nk 003")
            .replace("tail\t 12", "tail 0012")
            .replace("\n1543114881265", "\n01543114881265");
        assert!(rewritten.contains("\nk 003 \r\n") && rewritten.contains("\ntail 0012 \r\n"));
        assert!(rewritten.contains("\n01543114881265 \r\n"));
        assert_eq!(end(SPEC, &rewritten), (0, ACCEPTED.to_string()));
        let unfinished = VALUES.strip_suffix('\n').unwrap();
        assert_eq!(
            end(&SPEC.replace('\n', "\r\n"), unfinished),
            (0, ACCEPTED.to_string())
        );
    }

    #[test]
    fn the_threshold_is_compared_exactly() {
        // 3^4·F·3·2 = 2087354105856 is the denominator of the bound, so that the first of these
        // thresholds is the bound itself.
        let equal = SPEC.replace("95 100", "1907697663974 2087354105856");
        let (status, output) = end(&equal, VALUES);
        assert_eq!(status, 0);
        assert!(output.ends_with("\nbound <= 1907697663974/2087354105856\nACCEPTED\n"));
        let below = SPEC.replace("95 100", "1907697663973 2087354105856");
        let expected = "the stored values agree with the recomputed values\n\
                        total 1907697663974\n\
                        bound 0.913931018519 (rounded up)\n\
                        REJECTED: the bound exceeds the threshold 1907697663973/2087354105856\n";
        assert_eq!(end(&below, VALUES), (1, expected.to_string()));
        // A number that differs is found before the test is made.
        let other_total = VALUES.replace("total 1907697663974", "total 1907697663973");
        let (status, output) = end(&below, &other_total);
        assert_eq!(status, 1);
        assert!(output.starts_with("REJECTED: total: "));
    }

    #[test]
    fn a_spec_file_out_of_range_gives_status_2() {
        let nine = SPEC.replace("k 3", "k 9");
        assert_eq!(end(&nine, VALUES), (2, String::new()));
        assert_eq!(
            end(&nine, &VALUES.replace("k 3", "k 9")),
            (2, String::new())
        );
        let unordered = SPEC.replace("gaps 11 28", "gaps 28 11");
        assert_eq!(end(&unordered, VALUES), (2, String::new()));
    }

    #[test]
    fn parameter_lines_that_differ_give_status_1() {
        for (good, other) in [
            ("\nk 3\n", "\nk 9\n"),
            ("\nk 3\n", "\nk 2\n"),
            ("\nk 3\n", "\nk 340282366920938463463374607431768211455\n"),
            ("h 2 1", "h 4 2"),
            ("h 2 1", "h 0 0"),
            ("mesh 16", "mesh 17"),
            ("gaps 11 28", "gaps 11"),
            ("gaps 11 28", "gaps 11 28 30"),
            ("gaps 11 28", "gaps 28 11"),
            ("gaps 11 28", "gaps"),
            ("heights 3", "heights 0"),
            ("height_mesh 4", "height_mesh 1000"),
            ("tail 12", "tail 11"),
        ] {
            assert!(VALUES.contains(good));
            assert_eq!(status(&VALUES.replace(good, other)), 1, "{other}");
        }
    }

    #[test]
    fn wrong_counts_give_status_2() {
        let masses = "masses 139940470011903 92621490013121 48913016685633";
        let last_row = "3 0 0 4637203702 7205937300 12216866929\n";
        let last_sum = "3332858396868\n";
        for (good, other) in [
            ("48913016685633\n", "48913016685633 0\n"),
            (" 48913016685633\n", "\n"),
            (masses, "masses"),
            ("7205937300 12216866929", "7205937300 12216866929 0"),
            ("7205937300 12216866929", "7205937300"),
            ("3 0 0 4637203702 7205937300 12216866929", "3"),
            (last_row, ""),
            (last_sum, ""),
            ("sums 27\n", "sums 28\n0\n"),
            ("table 19\n", "table 20\n0 0 0 1 1 1\n"),
        ] {
            assert!(VALUES.contains(good));
            // Where a line is taken away, the number of lines announced goes down with it.
            let table = if good == last_row {
                "table 18"
            } else {
                "table 19"
            };
            let sums = if good == last_sum {
                "sums 26"
            } else {
                "sums 27"
            };
            let other = VALUES
                .replace(good, other)
                .replace("table 19", table)
                .replace("sums 27", sums);
            assert_eq!(status(&other), 2, "{good}");
        }
    }

    #[test]
    fn numbers_that_differ_give_status_1() {
        for (good, other) in [
            ("masses 139940470011903", "masses 139940470011904"),
            ("48913016685633\n", "48913016685632\n"),
            ("tail_term 26390", "tail_term 26391"),
            ("tail_term 26390", "tail_term 0"),
            ("0 0 1 12087143222", "0 0 1 12087143223"),
            ("14579812659 17701717119", "14579812659 17701717120"),
            ("3 0 0 4637203702", "9 1 0 4637203702"),
            ("3 0 0 4637203702", "0 0 3 4637203702"),
            ("\n1366776418032\n", "\n1366776418031\n"),
            ("3332858396868\ntotal", "3332858396869\ntotal"),
            ("total 1907697663974", "total 1907697663975"),
            ("total 1907697663974", "total 1907697663973"),
        ] {
            assert!(VALUES.contains(good));
            assert_eq!(status(&VALUES.replace(good, other)), 1, "{other}");
        }
        // Lines in another order have other numbers.
        let rows = "0 0 1 12087143222 13416178336 16756528437\n\
                    0 0 2 23758684847 24465629759 26461446133\n";
        let rows_swapped = "0 0 2 23758684847 24465629759 26461446133\n\
                            0 0 1 12087143222 13416178336 16756528437\n";
        assert!(VALUES.contains(rows));
        assert_eq!(status(&VALUES.replace(rows, rows_swapped)), 1);
        let sums = "1366776418032\n1543114881265\n";
        let sums_swapped = "1543114881265\n1366776418032\n";
        assert!(VALUES.contains(sums));
        assert_eq!(status(&VALUES.replace(sums, sums_swapped)), 1);
    }

    /// Each values file here is damaged in two ways; the earlier step of Section 10 decides.
    #[test]
    fn the_first_step_that_fails_decides() {
        let masses = "masses 139940470011903 92621490013121 48913016685633";
        let other_parameter = ("tail 12", "tail 11");
        let malformed = ("\n1366776418032\n", "\nx\n");
        let line_added = ("total 1907697663974\n", "total 1907697663974\ntotal 0\n");
        let one_mass_more = ("48913016685633\n", "48913016685633 0\n");
        let no_masses = (masses, "masses");
        let other_mass = ("masses 139940470011903", "masses 139940470011904");
        let other_total = ("total 1907697663974", "total 1");
        for (first, second, expected) in [
            (other_parameter, malformed, 2),
            (other_parameter, line_added, 2),
            (other_mass, malformed, 2),
            (other_parameter, one_mass_more, 1),
            (other_parameter, no_masses, 1),
            (other_parameter, other_total, 1),
            (other_mass, one_mass_more, 2),
            (other_total, one_mass_more, 2),
            (other_total, no_masses, 2),
        ] {
            assert!(VALUES.contains(first.0) && VALUES.contains(second.0));
            let damaged = VALUES.replace(first.0, first.1).replace(second.0, second.1);
            assert_eq!(status(&damaged), expected, "{} and {}", first.1, second.1);
        }
    }

    /// Parameters at the ends of their ranges go through all sections without an error.
    #[test]
    fn unusual_parameters() {
        for lines in [
            "k 2\nh 1 1\nmesh 2\ngaps\nheights 1\nheight_mesh 1\ntail 1\n",
            "k 8\nh 3 2\nmesh 3\ngaps 2\nheights 2\nheight_mesh 3\ntail 2\n",
            "k 2\nh 5 3\nmesh 8\ngaps 1 2 3 4 5 6 7\nheights 16\nheight_mesh 256\ntail 2\n",
            "k 3\nh 2 1\nmesh 1024\ngaps 1000\nheights 2\nheight_mesh 2\ntail 1\n",
        ] {
            let text = format!("{lines}threshold 1 1\nvalues values.txt\n");
            let spec = Spec::parse("spec", &text).unwrap();
            let params = &spec.params;
            let (k, cells) = (params.k, params.cells());
            let keys = Keys::new(cells, u8::try_from(k).unwrap());
            let mut sizes = Sizes::default();
            let tables = tables::build(params, &keys, &mut sizes).unwrap();
            assert_eq!(tables.table.len(), keys.len() * params.n);
            let sums = paths::cell_sums(params, &keys, &tables.table, 3, &mut sizes).unwrap();
            // Reversing a gap tuple reverses the block, which does not change the sum.
            let reversed = |index: usize| {
                (0..k)
                    .fold((0, index), |(r, i), _| (r * cells + i % cells, i / cells))
                    .0
            };
            assert!((0..sums.len()).all(|index| sums[index] == sums[reversed(index)]));
            let total = total::total(&tables.masses, &sums, k, &mut sizes).unwrap();
            let verdict = total::test(total, params, spec.threshold, &mut sizes).unwrap();
            // The bound is an upper bound for a constant that is larger than 0.7.
            assert!(verdict.decimals > 700_000_000_000, "{lines}");
        }
    }
}
