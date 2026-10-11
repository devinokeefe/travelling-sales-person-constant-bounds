//! The spec file and the values file (RECIPE.md, Section 10).
//!
//! Both are ASCII text. A line ends with a line feed, which a carriage return may precede; the
//! last line may lack its line feed. Apart from these line ends, only the tab and the bytes 32
//! to 126 may occur. Fields are separated by blanks (spaces or tabs); a number is a string of
//! decimal digits whose value is below 2^128. Nothing else is accepted: no empty lines, no
//! signs, no further lines.

use std::fs;
use std::ops::RangeInclusive;
use std::path::{Path, PathBuf};

use crate::arith::{gcd, wide};
use crate::failure::{invalid, Outcome, Stop};
use crate::keys::MAX_CELLS;
use crate::paths::{MAX_GAPS, MAX_HEIGHTS};

/// The fields of the first line of a values file.
const FIRST_LINE: [&str; 2] = ["tsp-block-values", "1"];

/// The parameter lines that a spec file and a values file share, each with the number of its
/// numbers (`None`: any number).
const PARAMETER_LINES: [(&str, Option<usize>); 7] = [
    ("k", Some(1)),
    ("h", Some(2)),
    ("mesh", Some(1)),
    ("gaps", None),
    ("heights", Some(1)),
    ("height_mesh", Some(1)),
    ("tail", Some(1)),
];

/// The parameters of Section 1, without the threshold.
pub struct Params {
    /// k, the number of gaps in a block.
    pub k: usize,
    /// h_1: the strip height is h = h_1/h_2.
    pub h1: u64,
    /// h_2.
    pub h2: u64,
    /// M, the horizontal mesh.
    pub mesh: u64,
    /// b_1 < … < b_{m−1}, the boundaries between the gap cells.
    pub boundaries: Vec<u64>,
    /// n, the number of height cells.
    pub n: usize,
    /// ν, the vertical mesh.
    pub nu: usize,
    /// T, the truncation of the last gap cell.
    pub tail: u64,
}

impl Params {
    /// m, the number of gap cells.
    pub fn cells(&self) -> usize {
        self.boundaries.len() + 1
    }

    /// The numbers of the seven parameter lines, as a values file has to repeat them.
    pub fn lines(&self) -> Vec<Vec<u128>> {
        vec![
            vec![wide(self.k)],
            vec![u128::from(self.h1), u128::from(self.h2)],
            vec![u128::from(self.mesh)],
            self.boundaries.iter().map(|&b| u128::from(b)).collect(),
            vec![wide(self.n)],
            vec![wide(self.nu)],
            vec![u128::from(self.tail)],
        ]
    }
}

/// The name of the parameter line with the given position in `Params::lines`.
pub fn parameter_name(position: usize) -> &'static str {
    PARAMETER_LINES[position].0
}

/// A spec file.
pub struct Spec {
    pub params: Params,
    /// θ_1 and θ_2: the threshold is θ_1/θ_2.
    pub threshold: (u64, u64),
    /// The path of the values file, as written: relative to the folder of the spec file.
    pub values: String,
}

/// A values file, as written. Whether it has the right numbers, and the right number of them,
/// is for the caller to decide: its parameter lines in particular are not held to any range.
pub struct Values {
    /// The numbers of the seven parameter lines, in the form of `Params::lines`.
    pub params: Vec<Vec<u128>>,
    pub masses: Vec<u128>,
    pub tail_term: u128,
    /// The lines of the table: a key followed by a row of Tab.
    pub table: Vec<Vec<u128>>,
    pub sums: Vec<u128>,
    pub total: u128,
}

/// Whether a byte is a blank: a space or a tab.
fn blank(byte: u8) -> bool {
    byte == b' ' || byte == b'\t'
}

/// Reads a file as a sequence of bytes; the name used in messages is returned with the
/// contents. Every byte becomes the character with its number, so that `Reader::fields`, which
/// decides what may occur in a line, sees a byte above 127 as what it is.
fn read(path: &Path) -> Outcome<(String, String)> {
    let name = path.display().to_string();
    let bytes = fs::read(path).map_err(|error| Stop::Invalid(format!("{name}: {error}")))?;
    Ok((name, bytes.into_iter().map(char::from).collect()))
}

/// The lines of a file, handed out one at a time.
struct Reader<'a> {
    file: &'a str,
    /// The lines without their line ends.
    lines: Vec<&'a str>,
    /// The number of lines handed out so far, which is the number of the last of them.
    taken: usize,
}

impl<'a> Reader<'a> {
    fn new(file: &'a str, text: &'a str) -> Self {
        let mut lines: Vec<&str> = text.split('\n').collect();
        // What follows the last line feed is a last line without its line end, unless nothing
        // follows it.
        let unfinished = lines.pop().filter(|rest| !rest.is_empty());
        // A carriage return belongs to a line end only where a line feed follows it.
        for line in &mut lines {
            *line = line.strip_suffix('\r').unwrap_or(line);
        }
        lines.extend(unfinished);
        Self {
            file,
            lines,
            taken: 0,
        }
    }

    fn fail<T>(&self, message: &str) -> Outcome<T> {
        invalid(format!("{}, line {}: {message}", self.file, self.taken))
    }

    /// The fields of the next line, of which there is at least one; `wanted` describes the line
    /// for the message if it is absent or empty.
    fn fields(&mut self, wanted: &str) -> Outcome<Vec<&'a str>> {
        let Some(&line) = self.lines.get(self.taken) else {
            return invalid(format!(
                "{}: the file ends after line {} where {wanted} should follow",
                self.file, self.taken
            ));
        };
        self.taken += 1;
        // Apart from the line ends, a file has only blanks and the bytes 33 to 126. This excludes
        // what is not ASCII, and a carriage return that no line feed follows.
        if !line
            .bytes()
            .all(|byte| blank(byte) || byte.is_ascii_graphic())
        {
            return self.fail("a byte that is neither a blank nor one of the bytes 33 to 126");
        }
        let fields: Vec<&str> = line
            .split(|character: char| u8::try_from(character).is_ok_and(blank))
            .filter(|field| !field.is_empty())
            .collect();
        if fields.is_empty() {
            return self.fail(&format!("an empty line where {wanted} should be"));
        }
        Ok(fields)
    }

    /// The value of a string of decimal digits. Leading zeros are allowed, so the bound 2^128
    /// is one for the value and not for the length of the string.
    fn number(&self, field: &str) -> Outcome<u128> {
        if !field.bytes().all(|byte| byte.is_ascii_digit()) {
            return self.fail(&format!("`{field}` is not a number"));
        }
        let mut value: u128 = 0;
        for byte in field.bytes() {
            let digit = u128::from(byte - b'0');
            match value.checked_mul(10).and_then(|v| v.checked_add(digit)) {
                Some(longer) => value = longer,
                None => return self.fail(&format!("the number {field} is not below 2^128")),
            }
        }
        Ok(value)
    }

    /// A line that consists of numbers only.
    fn numbers(&mut self, wanted: &str) -> Outcome<Vec<u128>> {
        let fields = self.fields(wanted)?;
        fields.iter().map(|field| self.number(field)).collect()
    }

    /// A line that consists of `name` and of `count` numbers (`None`: any number of them).
    fn named(&mut self, name: &str, count: Option<usize>) -> Outcome<Vec<u128>> {
        let fields = self.fields(&format!("the line `{name}`"))?;
        if fields[0] != name {
            return self.fail(&format!("the line should begin with `{name}`"));
        }
        if let Some(count) = count.filter(|&count| count != fields.len() - 1) {
            return self.fail(&format!("`{name}` should be followed by {count} number(s)"));
        }
        fields[1..].iter().map(|field| self.number(field)).collect()
    }

    /// A line that consists of `name` and one number.
    fn single(&mut self, name: &str) -> Outcome<u128> {
        Ok(self.named(name, Some(1))?[0])
    }

    /// The seven parameter lines.
    fn parameters(&mut self) -> Outcome<Vec<Vec<u128>>> {
        PARAMETER_LINES
            .iter()
            .map(|&(name, count)| self.named(name, count))
            .collect()
    }

    /// A line that consists of `name` and the number of lines of the section that it opens.
    /// The lines of the section must be there; what they contain is not looked at here.
    fn section(&mut self, name: &str) -> Outcome<usize> {
        let count = self.single(name)?;
        match usize::try_from(count) {
            Ok(count) if count <= self.lines.len() - self.taken => Ok(count),
            _ => self.fail(&format!("{count} lines are announced, but fewer follow")),
        }
    }

    /// The file must have no further lines.
    fn end(&mut self) -> Outcome<()> {
        if self.taken < self.lines.len() {
            self.taken += 1;
            return self.fail("the file should have ended before this line");
        }
        Ok(())
    }
}

/// Checks that `value` lies in `range` and converts it.
fn ranged<T: TryFrom<u128>>(
    file: &str,
    name: &str,
    value: u128,
    range: RangeInclusive<u128>,
) -> Outcome<T> {
    let converted = T::try_from(value).ok().filter(|_| range.contains(&value));
    converted.ok_or_else(|| {
        let (low, high) = (range.start(), range.end());
        Stop::Invalid(format!(
            "{file}: {name} = {value} is not between {low} and {high}"
        ))
    })
}

impl Spec {
    /// Reads and validates a spec file.
    pub fn read(path: &Path) -> Outcome<Self> {
        let (name, text) = read(path)?;
        Self::parse(&name, &text)
    }

    /// Parses the text of a spec file; `file` is its name in messages. The parameters must lie
    /// in the ranges that Section 1 allows.
    pub fn parse(file: &str, text: &str) -> Outcome<Self> {
        let mut reader = Reader::new(file, text);
        let lines = reader.parameters()?;
        let threshold = reader.named("threshold", Some(2))?;
        let ["values", path] = reader.fields("the line `values`")?[..] else {
            return reader.fail("the line should be `values` and one field, the path");
        };
        reader.end()?;

        let too_long = wide(MAX_CELLS);
        let boundaries: Vec<u64> = lines[3]
            .iter()
            .map(|&b| {
                ranged(
                    file,
                    "a boundary of the gap cells",
                    b,
                    1..=u128::from(u64::MAX),
                )
            })
            .collect::<Outcome<_>>()?;
        let _: usize = ranged(file, "m", wide(boundaries.len() + 1), 1..=too_long)?;
        if boundaries.windows(2).any(|pair| pair[0] >= pair[1]) {
            return invalid(format!(
                "{file}: the boundaries of the gap cells must increase"
            ));
        }
        let any = 1..=u128::from(u64::MAX);
        let params = Params {
            k: ranged(file, "k", lines[0][0], 2..=wide(MAX_GAPS))?,
            h1: ranged(file, "h_1", lines[1][0], any.clone())?,
            h2: ranged(file, "h_2", lines[1][1], any.clone())?,
            mesh: ranged(file, "mesh", lines[2][0], 2..=1024)?,
            boundaries,
            n: ranged(file, "heights", lines[4][0], 1..=wide(MAX_HEIGHTS))?,
            nu: ranged(file, "height_mesh", lines[5][0], 1..=256)?,
            tail: ranged(file, "tail", lines[6][0], 1..=40)?,
        };
        if gcd(params.h1, params.h2) != 1 {
            return invalid(format!("{file}: h is not in lowest terms"));
        }
        let threshold = (
            ranged(file, "θ_1", threshold[0], any.clone())?,
            ranged(file, "θ_2", threshold[1], any)?,
        );
        // This keeps the path relative on every system, with `/` alone between its parts.
        if path.starts_with('/') || path.contains(['\\', ':']) {
            return invalid(format!(
                "{file}: the path of the values file must not begin with `/` or contain `\\` or `:`"
            ));
        }
        Ok(Self {
            params,
            threshold,
            values: path.to_string(),
        })
    }

    /// The path of the values file for a spec file at `spec_path`: the relative path that the
    /// spec file gives, taken from the folder of the spec file.
    pub fn values_path(&self, spec_path: &Path) -> PathBuf {
        let folder = spec_path.parent().unwrap_or(Path::new(""));
        folder.join(&self.values)
    }
}

impl Values {
    /// Reads a values file.
    pub fn read(path: &Path) -> Outcome<Self> {
        let (name, text) = read(path)?;
        Self::parse(&name, &text)
    }

    /// Parses the text of a values file; `file` is its name in messages. This is step 2 of
    /// Section 10: the form of the whole file, before any of its numbers is compared.
    pub fn parse(file: &str, text: &str) -> Outcome<Self> {
        let mut reader = Reader::new(file, text);
        if reader.fields("the line `tsp-block-values 1`")? != FIRST_LINE {
            return reader.fail("the line should be `tsp-block-values 1`");
        }
        let params = reader.parameters()?;
        let masses = reader.named("masses", None)?;
        let tail_term = reader.single("tail_term")?;
        let mut table = Vec::new();
        for _ in 0..reader.section("table")? {
            table.push(reader.numbers("a line of the table")?);
        }
        let mut sums = Vec::new();
        for _ in 0..reader.section("sums")? {
            let [sum] = reader.numbers("a cell sum")?[..] else {
                return reader.fail("a cell sum is a single number");
            };
            sums.push(sum);
        }
        let total = reader.single("total")?;
        reader.end()?;
        Ok(Self {
            params,
            masses,
            tail_term,
            table,
            sums,
            total,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SPEC: &str = "k 7\nh 21 10\nmesh 128\ngaps 48 112 208\nheights 6\nheight_mesh 64\n\
                        tail 16\nthreshold 869 1000\nvalues ../values/k7.txt\n";

    const VALUES: &str = "tsp-block-values 1\nk 2\nh 2 1\nmesh 16\ngaps\nheights 2\n\
                          height_mesh 4\ntail 12\nmasses 5\ntail_term 6\ntable 2\n1 7 8\n\
                          2 9 10\nsums 1\n11\ntotal 12\n";

    fn spec_error(text: &str) -> bool {
        matches!(Spec::parse("spec", text), Err(Stop::Invalid(_)))
    }

    fn values_error(text: &str) -> bool {
        matches!(Values::parse("values", text), Err(Stop::Invalid(_)))
    }

    #[test]
    fn a_spec_file_is_read() {
        let spec = Spec::parse("spec", SPEC).unwrap();
        assert_eq!(spec.params.k, 7);
        assert_eq!((spec.params.h1, spec.params.h2), (21, 10));
        assert_eq!(spec.params.mesh, 128);
        assert_eq!(spec.params.boundaries, [48, 112, 208]);
        assert_eq!(spec.params.cells(), 4);
        assert_eq!(spec.params.n, 6);
        assert_eq!(spec.params.nu, 64);
        assert_eq!(spec.params.tail, 16);
        assert_eq!(spec.threshold, (869, 1000));
        assert_eq!(spec.values, "../values/k7.txt");
        let path = spec.values_path(Path::new("data/specs/k7.txt"));
        let parts: Vec<_> = path.components().collect();
        assert_eq!(parts.len(), 5);
        assert_eq!(parts[2], std::path::Component::ParentDir);
        let beside = spec.values_path(Path::new("k7.txt"));
        assert_eq!(beside.components().count(), 3);
    }

    #[test]
    fn line_ends_and_blanks_are_tolerated() {
        let windows = SPEC.replace('\n', "\r\n");
        assert_eq!(Spec::parse("spec", &windows).unwrap().params.k, 7);
        let mixed = SPEC.replacen('\n', "\r\n", 3);
        assert_eq!(Spec::parse("spec", &mixed).unwrap().params.mesh, 128);
        let spaced = SPEC.replace("gaps 48 112", " gaps\t48   112 ");
        assert_eq!(
            Spec::parse("spec", &spaced)
                .unwrap()
                .params
                .boundaries
                .len(),
            3
        );
        let padded = SPEC
            .replace("values ", "\t values \t ")
            .replace('\n', " \t\n");
        assert_eq!(
            Spec::parse("spec", &padded).unwrap().values,
            "../values/k7.txt"
        );
        let unfinished = SPEC.strip_suffix('\n').unwrap();
        assert_eq!(
            Spec::parse("spec", unfinished).unwrap().values,
            "../values/k7.txt"
        );
        let one_cell = SPEC.replace("gaps 48 112 208", "gaps");
        assert_eq!(Spec::parse("spec", &one_cell).unwrap().params.cells(), 1);
    }

    #[test]
    fn leading_zeros_do_not_count() {
        let zeros = "0".repeat(60);
        let long = SPEC
            .replace("mesh 128", &format!("mesh {zeros}128"))
            .replace("k 7", "k 07")
            .replace("gaps 48", "gaps 0048");
        let spec = Spec::parse("spec", &long).unwrap();
        assert_eq!((spec.params.k, spec.params.mesh), (7, 128));
        assert_eq!(spec.params.boundaries[0], 48);
        let values = VALUES.replace("total 12", &format!("total {zeros}{}", u128::MAX));
        assert_eq!(Values::parse("values", &values).unwrap().total, u128::MAX);
        assert!(values_error(
            &VALUES.replace("total 12", &format!("total {zeros}{}0", u128::MAX))
        ));
        // 2^128 itself is not below 2^128.
        let limit = "340282366920938463463374607431768211456";
        assert!(values_error(
            &VALUES.replace("total 12", &format!("total {limit}"))
        ));
    }

    #[test]
    fn malformed_spec_files_are_refused() {
        assert!(spec_error(""));
        assert!(spec_error(&SPEC.replace("mesh 128\n", "")));
        assert!(spec_error(&SPEC.replace("mesh", "Mesh")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh 128 1")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh 12x")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh +128")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh -128")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh 128\n")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh 128\n \t")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh\u{b}128")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh\u{a0}128")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh 1２8")));
        assert!(spec_error(
            &SPEC.replace("h 21 10\nmesh 128", "mesh 128\nh 21 10")
        ));
        assert!(spec_error(&format!("\n{SPEC}")));
        assert!(spec_error(&format!("{SPEC}\n")));
        assert!(spec_error(&format!("{SPEC}\r\n")));
        assert!(spec_error(&format!("{SPEC}k 7\n")));
        assert!(spec_error(&format!("\u{feff}{SPEC}")));
        assert!(spec_error(
            &SPEC.replace("h 21 10", &format!("h {} 10", "9".repeat(40)))
        ));
    }

    #[test]
    fn a_carriage_return_needs_a_line_feed() {
        let unfinished = SPEC.strip_suffix('\n').unwrap();
        assert!(spec_error(&format!("{unfinished}\r")));
        assert!(spec_error(&SPEC.replace('\n', "\r")));
        assert!(spec_error(&SPEC.replace("mesh 128\n", "mesh 128\r\r\n")));
        assert!(spec_error(&SPEC.replace("mesh 128", "mesh\r128")));
        assert!(spec_error(&SPEC.replace("mesh 128\n", "mesh 128\n\r\n")));
        assert!(values_error(&VALUES.replace("total 12\n", "total 12\r")));
        assert!(values_error(&VALUES.replace("\n11\n", "\n11\r\r\n")));
    }

    #[test]
    fn the_line_of_the_values_file_names_one_relative_path() {
        let with = |line: &str| SPEC.replace("values ../values/k7.txt", line);
        assert_eq!(
            Spec::parse("spec", &with("values k7.txt")).unwrap().values,
            "k7.txt"
        );
        assert!(spec_error(&with("values")));
        assert!(spec_error(&with("values a b.txt")));
        assert!(spec_error(&with("values a.txt 1")));
        assert!(spec_error(&with("Values a.txt")));
        assert!(spec_error(&with("file a.txt")));
        assert!(spec_error(&with("values /a.txt")));
        assert!(spec_error(&with("values /")));
        assert!(spec_error(&with("values ..\\values\\k7.txt")));
        assert!(spec_error(&with("values a\\")));
        assert!(spec_error(&with("values C:/values/k7.txt")));
        assert!(spec_error(&with("values C:k7.txt")));
        assert!(spec_error(&with("values a/b:c.txt")));
        assert!(spec_error(&with("values a\u{7}b.txt")));
        assert!(spec_error(&with("values é.txt")));
        for path in ["./k7.txt", "a/../k7.txt", "a//b", "..", "~/k7.txt", "a/"] {
            let spec = Spec::parse("spec", &with(&format!("values {path}"))).unwrap();
            assert_eq!(spec.values, path);
        }
    }

    #[test]
    fn parameters_out_of_range_are_refused() {
        for (good, bad) in [
            ("k 7", "k 1"),
            ("k 7", "k 10"),
            ("h 21 10", "h 0 10"),
            ("h 21 10", "h 21 0"),
            ("h 21 10", "h 42 20"),
            ("h 21 10", "h 21 18446744073709551616"),
            ("mesh 128", "mesh 1"),
            ("mesh 128", "mesh 1025"),
            ("gaps 48 112 208", "gaps 0 112 208"),
            ("gaps 48 112 208", "gaps 48 48 208"),
            ("gaps 48 112 208", "gaps 48 208 112"),
            ("gaps 48 112 208", "gaps 48 112 18446744073709551616"),
            ("gaps 48 112 208", "gaps 1 2 3 4 5 6 7 8"),
            ("heights 6", "heights 0"),
            ("heights 6", "heights 17"),
            ("height_mesh 64", "height_mesh 0"),
            ("height_mesh 64", "height_mesh 257"),
            ("tail 16", "tail 0"),
            ("tail 16", "tail 41"),
            ("threshold 869 1000", "threshold 0 1000"),
            ("threshold 869 1000", "threshold 869 0"),
            ("threshold 869 1000", "threshold 18446744073709551616 1000"),
        ] {
            assert!(SPEC.contains(good));
            assert!(spec_error(&SPEC.replace(good, bad)), "{bad}");
        }
        let widest = SPEC.replace("gaps 48 112 208", "gaps 1 2 3 4 5 6 7");
        assert_eq!(Spec::parse("spec", &widest).unwrap().params.cells(), 8);
        // The threshold need not be in lowest terms, and its parts may be as large as h allows.
        let largest = "18446744073709551615";
        let extreme = SPEC
            .replace("h 21 10", &format!("h {largest} 2"))
            .replace("threshold 869 1000", &format!("threshold {largest} 30"));
        let spec = Spec::parse("spec", &extreme).unwrap();
        assert_eq!((spec.params.h1, spec.threshold), (u64::MAX, (u64::MAX, 30)));
    }

    #[test]
    fn a_values_file_is_read() {
        let values = Values::parse("values", VALUES).unwrap();
        let empty: Vec<u128> = Vec::new();
        assert_eq!(
            values.params,
            [
                vec![2],
                vec![2, 1],
                vec![16],
                empty,
                vec![2],
                vec![4],
                vec![12]
            ]
        );
        assert_eq!(values.masses, [5]);
        assert_eq!(values.tail_term, 6);
        assert_eq!(values.table, [[1, 7, 8], [2, 9, 10]]);
        assert_eq!(values.sums, [11]);
        assert_eq!(values.total, 12);
        let windows = VALUES.replace('\n', "\r\n");
        assert_eq!(Values::parse("values", &windows).unwrap().total, 12);
        let spaced = VALUES.replace(' ', " \t ").replace('\n', "  \n");
        assert_eq!(
            Values::parse("values", &spaced).unwrap().table[1],
            [2, 9, 10]
        );
    }

    /// The form of a values file says nothing about ranges or counts: these belong to the later
    /// steps, where they lead to other exit statuses.
    #[test]
    fn the_form_of_a_values_file_leaves_ranges_and_counts_open() {
        let odd = VALUES
            .replace("k 2", "k 9")
            .replace("h 2 1", "h 0 0")
            .replace("gaps", "gaps 5 5 1")
            .replace("masses 5", "masses 5 5 5")
            .replace("1 7 8", "1 7 8 8 8")
            .replace("2 9 10", "2");
        let values = Values::parse("values", &odd).unwrap();
        assert_eq!(values.params[0], [9]);
        assert_eq!(values.params[1], [0, 0]);
        assert_eq!(values.params[3], [5, 5, 1]);
        assert_eq!(values.masses.len(), 3);
        assert_eq!(values.table, [vec![1, 7, 8, 8, 8], vec![2]]);
        let bare = VALUES
            .replace("masses 5", "masses")
            .replace("table 2\n1 7 8\n2 9 10\n", "table 0\n")
            .replace("sums 1\n11\n", "sums 0\n");
        let values = Values::parse("values", &bare).unwrap();
        assert!(values.masses.is_empty() && values.table.is_empty() && values.sums.is_empty());
    }

    #[test]
    fn malformed_values_files_are_refused() {
        assert!(values_error(""));
        assert!(values_error(&VALUES.replace("values 1", "values 2")));
        assert!(values_error(&VALUES.replace("values 1", "values 01")));
        assert!(values_error(&VALUES.replace("values 1", "values")));
        assert!(values_error(&VALUES.replace("values 1", "values 1 1")));
        assert!(values_error(&VALUES.replace("tsp-block", "tsp-blok")));
        assert!(values_error(
            &VALUES.replace("tsp-block-values", "tsp-block-numbers")
        ));
        assert!(values_error(&VALUES.replace("tsp-block-values 1\n", "")));
        assert!(values_error(&VALUES.replace("h 2 1", "h 2")));
        assert!(values_error(
            &VALUES.replace("h 2 1\nmesh 16", "mesh 16\nh 2 1")
        ));
        assert!(values_error(&VALUES.replace("tail_term 6\n", "")));
        assert!(values_error(
            &VALUES.replace("tail_term 6", "tail_term 6 6")
        ));
        assert!(values_error(&VALUES.replace("table 2", "table 1")));
        assert!(values_error(&VALUES.replace("table 2", "table 3")));
        assert!(values_error(&VALUES.replace("table 2", "table 2 2")));
        assert!(values_error(&VALUES.replace("sums 1", "sums 0")));
        assert!(values_error(&VALUES.replace("sums 1", "sums 2")));
        assert!(values_error(
            &VALUES.replace("sums 1", "sums 99999999999999999999")
        ));
        assert!(values_error(&VALUES.replace("\n11\n", "\n11 11\n")));
        assert!(values_error(&VALUES.replace("\n11\n", "\n1l\n")));
        assert!(values_error(&VALUES.replace("\n11\n", "\n11\n\n")));
        assert!(values_error(&VALUES.replace("2 9 10", "2 9 1O")));
        assert!(values_error(&VALUES.replace("2 9 10", "2 9 -10")));
        assert!(values_error(&VALUES.replace("2 9 10", "")));
        assert!(values_error(&VALUES.replace("total 12", "total 0x12")));
        assert!(values_error(&VALUES.replace("total 12", "total 1.2")));
        assert!(values_error(&VALUES.replace("total 12", "total 1２")));
        assert!(values_error(&VALUES.replace("total 12\n", "")));
        assert!(values_error(&format!("{VALUES}13\n")));
        assert!(values_error(&format!("{VALUES}total 12\n")));
        assert!(values_error(&format!("{VALUES}\n")));
        assert!(values_error(&format!("{VALUES} \n")));
        // Every prefix lacks a line or a number, unless only the last number is cut short or
        // only the last line end is missing.
        for cut in 0..VALUES.len() - 2 {
            assert!(values_error(&VALUES[..cut]), "{cut}");
        }
        let shortened = &VALUES[..VALUES.len() - 2];
        assert_eq!(Values::parse("values", shortened).unwrap().total, 1);
        let unfinished = &VALUES[..VALUES.len() - 1];
        assert_eq!(Values::parse("values", unfinished).unwrap().total, 12);
    }
}
