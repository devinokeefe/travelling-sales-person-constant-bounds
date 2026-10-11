#!/usr/bin/env python3
"""Writes the test inputs for the checkers to data/tests/.

Each test input is a spec file NAME.txt with its values file NAME_values.txt, made from
data/specs/tiny.txt and data/values/tiny.txt by one change, or by two where the order of the steps of
Section 10 of RECIPE.md is tested; the two for the strip bound are made from data/specs/bhh.txt, whose
strip height is not an integer.  Most of them are faulty and must be refused; a few differ from the
original only in ways that the formats allow.  EXPECTED.txt lists the exit status that every checker
must return for each: 0 accepted, 1 rejected, 2 malformed.

usage:  make_tests.py          (from any folder)
"""

import os
import shutil

from check_bound import F, read_spec

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")
OUT = os.path.join(DATA, "tests")


def main():
    with open(os.path.join(DATA, "specs", "tiny.txt"), encoding="ascii") as handle:
        spec = handle.read().splitlines()
    with open(os.path.join(DATA, "values", "tiny.txt"), encoding="ascii") as handle:
        values = handle.read().splitlines()
    par = read_spec(os.path.join(DATA, "specs", "tiny.txt"))
    table = values.index(next(line for line in values if line.startswith("table ")))
    sums = values.index(next(line for line in values if line.startswith("sums ")))
    total = int(values[-1].split()[1])

    def named(lines):
        """Where the lines that begin with a name stand."""
        return {line.split(" ")[0]: index for index, line in enumerate(lines)}

    in_spec = named(spec)
    at = named(values[:table])  # the lines before the table
    # the bound is total * hd / denominator
    denominator = par["n"] ** (par["k"] + 1) * F * par["k"] * par["hn"]

    def changed(lines, index, function):
        return [function(line) if i == index else line for i, line in enumerate(lines)]

    def last_number(delta):
        def function(line):
            fields = line.split()
            return " ".join([*fields[:-1], str(int(fields[-1]) + delta)])

        return function

    def swapped(lines, i, j):
        lines = list(lines)
        lines[i], lines[j] = lines[j], lines[i]
        return lines

    def threshold(numerator, denominator):  # integers, or strings of digits
        return changed(spec, in_spec["threshold"], lambda _: f"threshold {numerator} {denominator}")

    def without(lines, index):
        return lines[:index] + lines[index + 1 :]

    def text(lines, end="\n"):
        return end.join(lines) + end

    keys = int(values[table].split()[1])
    with open(os.path.join(DATA, "specs", "bhh.txt"), encoding="ascii") as handle:
        strip_spec = handle.read().splitlines()
    with open(os.path.join(DATA, "values", "bhh.txt"), encoding="ascii") as handle:
        strip_values = handle.read().splitlines()
    strip = read_spec(os.path.join(DATA, "specs", "bhh.txt"))
    strip_numerator = int(strip_values[-1].split()[1]) * strip["hd"]
    strip_denominator = strip["n"] ** (strip["k"] + 1) * F * strip["k"] * strip["hn"]

    def strip_threshold(numerator):
        line = named(strip_spec)["threshold"]
        return changed(strip_spec, line, lambda _: f"threshold {numerator} {strip_denominator}")

    inputs = [
        # name, spec lines, values lines (or the text of the values file), expected status
        ("good", spec, values, 0),
        ("carriage_returns", spec, text(values, "\r\n"), 0),
        ("no_last_line_end", spec, text(values)[:-1], 0),
        ("tabs_and_blanks", spec, text([line.replace(" ", " \t ") + "  " for line in values]), 0),
        ("leading_zeros", spec, changed(values, sums + 2, lambda line: "00" + line), 0),
        ("threshold_equal", threshold(total * par["hd"], denominator), values, 0),
        ("threshold_below", threshold(total * par["hd"] - 1, denominator), values, 1),
        ("strip_threshold_equal", strip_threshold(strip_numerator), strip_values, 0),
        ("strip_threshold_below", strip_threshold(strip_numerator - 1), strip_values, 1),
        ("table_minus", spec, changed(values, table + 5, last_number(-1)), 1),
        ("table_plus", spec, changed(values, table + 11, last_number(1)), 1),
        ("table_rows_swapped", spec, swapped(values, table + 2, table + 3), 1),
        ("sum_minus", spec, changed(values, sums + 9, last_number(-1)), 1),
        ("sum_plus", spec, changed(values, sums + 27, last_number(1)), 1),
        ("sums_swapped", spec, swapped(values, sums + 1, sums + 2), 1),
        ("total_minus", spec, changed(values, len(values) - 1, last_number(-1)), 1),
        ("total_plus", spec, changed(values, len(values) - 1, last_number(1)), 1),
        ("mass_plus", spec, changed(values, at["masses"], last_number(1)), 1),
        ("tail_term_minus", spec, changed(values, at["tail_term"], last_number(-1)), 1),
        ("other_parameter", spec, changed(values, at["tail"], last_number(-1)), 1),
        ("parameter_out_of_range", spec, changed(values, at["k"], lambda _: "k 10"), 1),
        ("key_changed", spec, changed(values, table + 4, lambda line: "9" + line[1:]), 1),
        ("empty_line", spec, [*values[:sums], "", *values[sums:]], 2),
        ("number_too_long", spec, changed(values, sums + 6, lambda line: line + "0" * 30), 2),
        ("one_mass_more", spec, changed(values, at["masses"], lambda line: line + " 1"), 2),
        ("table_line_longer", spec, changed(values, table + 3, lambda line: line + " 1"), 2),
        (
            "table_shorter",
            spec,
            changed(without(values, table + keys), table, lambda _: f"table {keys - 1}"),
            2,
        ),
        ("sums_shorter", spec, changed(without(values, sums + 27), sums, lambda _: "sums 26"), 2),
        ("sums_count_changed", spec, changed(values, sums, lambda _: "sums 26"), 2),
        (  # the wrong number of sums is found (step 4) before the changed sum (step 5)
            "sums_shorter_and_changed",
            spec,
            changed(changed(without(values, sums + 27), sums, lambda _: "sums 26"), sums + 3, last_number(1)),
            2,
        ),
        ("table_count_huge", spec, changed(values, table, lambda _: f"table {2**128 - 1}"), 2),
        ("sums_count_huge", spec, changed(values, sums, lambda _: f"sums {2**128 - 1}"), 2),
        (
            "parameter_and_malformed",
            spec,
            changed(changed(values, at["tail"], last_number(-1)), sums + 4, lambda _: "x"),
            2,
        ),
        ("truncated", spec, values[: sums + 14], 2),
        ("line_missing", spec, values[: sums + 3] + values[sums + 4 :], 2),
        ("line_added", spec, [*values, "total 0"], 2),
        ("not_a_number", spec, changed(values, table + 7, lambda line: line.replace(" ", " x", 1)), 2),
        ("negative_number", spec, changed(values, sums + 4, lambda line: "-" + line), 2),
        ("wrong_first_line", spec, changed(values, 0, lambda _: "tsp-block-values 2"), 2),
        ("spec_lines_swapped", swapped(spec, in_spec["mesh"], in_spec["gaps"]), values, 2),
        ("spec_gaps_not_increasing", changed(spec, in_spec["gaps"], lambda _: "gaps 28 11"), values, 2),
        ("spec_zero_threshold", threshold(0, 1), values, 2),
        # the rules for text (Section 10 of RECIPE.md)
        ("many_leading_zeros", spec, changed(values, sums + 2, lambda line: "0" * 5000 + line), 0),
        ("threshold_leading_zeros", threshold("095", "0100"), values, 0),
        (
            "stray_carriage_return",
            spec,
            text(changed(values, at["tail_term"], lambda line: line.replace(" ", "\r"))),
            2,
        ),
        ("carriage_return_at_end", spec, text(values, "\r\n")[:-1], 2),
        ("form_feed", spec, text(changed(values, at["masses"], lambda line: line.replace(" ", "\f", 1))), 2),
        (
            "vertical_tab",
            spec,
            text(changed(values, at["masses"], lambda line: line.replace(" ", "\v", 1))),
            2,
        ),
        ("nul_byte", spec, text(values)[:-1] + "\0\n", 2),
        ("non_ascii_blank", spec, text(values).encode("ascii").replace(b"tail_term ", b"tail_term\xa0"), 2),
        ("non_ascii_digit", spec, text(values).encode("ascii").replace(b"sums 2", b"sums \xd9\xa2"), 2),
        ("blank_line", spec, [*values[:sums], "  ", *values[sums:]], 2),
        ("empty_values_file", spec, "", 2),
        ("first_line_zero", spec, changed(values, 0, lambda _: "tsp-block-values 01"), 2),
        ("name_in_capitals", spec, changed(values, at["k"], lambda line: line.upper()), 2),
        # the order of the steps and the form of a spec file
        (
            "parameter_and_count",
            spec,
            changed(changed(values, at["tail"], last_number(-1)), at["masses"], lambda line: line + " 1"),
            1,
        ),
        ("gaps_count_differs", spec, changed(values, at["gaps"], lambda line: line.rsplit(" ", 1)[0]), 1),
        (
            "spec_values_absolute",
            changed(spec, in_spec["values"], lambda _: "values /spec_values_absolute_values.txt"),
            values,
            2,
        ),
        (
            "spec_values_backslash",
            changed(spec, in_spec["values"], lambda _: "values .\\spec_values_backslash_values.txt"),
            values,
            2,
        ),
        (
            "spec_values_drive",
            changed(spec, in_spec["values"], lambda _: "values C:spec_values_drive_values.txt"),
            values,
            2,
        ),
        ("spec_h_not_lowest_terms", changed(spec, in_spec["h"], lambda _: "h 4 2"), values, 2),
        ("spec_k_too_large", changed(spec, in_spec["k"], lambda _: "k 10"), values, 2),
    ]
    unchanged = text(values).encode("ascii")
    if any(data == unchanged for _, _, data, _ in inputs if isinstance(data, bytes)):
        raise SystemExit("make_tests: a replacement of bytes found nothing to replace")
    shutil.rmtree(OUT, ignore_errors=True)
    os.makedirs(OUT)
    expected = []
    for name, given_lines, values_lines, status in inputs:
        spec_lines = given_lines
        # Three inputs name their values file in a way that is not allowed; that line is kept.
        if not name.startswith("spec_values_"):
            spec_lines = [
                f"values {name}_values.txt" if line.startswith("values ") else line for line in given_lines
            ]
        for file, lines in ((f"{name}.txt", spec_lines), (f"{name}_values.txt", values_lines)):
            data = lines if isinstance(lines, (str, bytes)) else text(lines)
            with open(os.path.join(OUT, file), "wb") as handle:
                handle.write(data if isinstance(data, bytes) else data.encode("ascii"))
        expected.append(f"{name} {status}")
    with open(os.path.join(OUT, "EXPECTED.txt"), "w", encoding="ascii", newline="\n") as handle:
        handle.write("\n".join(expected) + "\n")
    print(f"wrote {len(inputs)} test inputs to data/tests/")


if __name__ == "__main__":
    main()
