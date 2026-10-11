#!/usr/bin/env python3
r"""Writes the numbers of the paper and of the README from the records in runs/.

The numbers in the paper that come from a computation of this repository are LaTeX macros defined in
paper/tex/numbers.tex or entries of the tables paper/tex/*_table.tex; some are written out in the text,
and of those the sentences listed in `stated` are checked word for word.  This script derives these
files, and the two parts of README.md between markers (the table of results after "<!-- results:begin -->"
and the paragraph on running times after "<!-- times:begin -->"), from the records.  It also checks the
records against each other (the checkers must have printed the same lines for every spec file, on every
platform and in every run, and the printed bound must be the total of the record converted with exact
integer arithmetic) and against the sentences of the paper, of README.md, of checkers/README.md, of
checkers/TESTS.md, of controls/README.md and of paper/README.md that state what the records show.  If the
folder lean/ is present, it checks the record of the Lean build against the Lean sources and the records
of the checkers, and only then defines the macro \LeanMaxK, which the passages on Lean in the paper use.
It does not check that a record is the output of the run that it names, nor paper/main.pdf against its
sources.

Much of this script repeats the wording of the paper and of the README files: whoever changes a sentence
there that states a number or a comparison must change the function here that checks it.

The results are those of the spec files data/specs/k5.txt, k6.txt, ... that are present; the last of
them is the main theorem.

usage:  paper_numbers.py           write the targets
        paper_numbers.py --check   exit with status 1 if a target differs from what the records give
"""

import hashlib
import json
import math
import os
import re
import sys
import textwrap
from fractions import Fraction

REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
sys.path.insert(0, os.path.join(REPO, "checkers"))
from check_bound import D, F, all_keys, cdiv, read_spec  # noqa: E402

CHECKERS = ("python", "c", "rust")
LABELS = {"python": "Python", "c": "C", "rust": "Rust"}
WORDS = {5: "Five", 6: "Six", 7: "Seven", 8: "Eight", 9: "Nine"}
NUMERALS = {3: "three", 4: "four", 5: "five", 8: "eight", 9: "nine", 10: "ten"}
ONCE = {("python", "k9")}  # the pairs with one run, as the paper says; every other pair has at least two
# the records in runs/earlier: the programs of which an earlier version, from before the routines for
# the identities of Section 7 of RECIPE.md were added, was run on each spec file
EARLIER = {"k5": CHECKERS, "k6": CHECKERS, "k7": CHECKERS, "k8": ("c",)}
DONG_CAO_CELLS = 12**5 * 20**6  # the grid of Dong and Cao for k = 5, as Section 1.3 states it
# their bound as a fraction (the last display of their Section 4.2), as Section 6.1 uses it
DONG_CAO_BOUND = (70149051060530822644063354, 5 * 10**12 * DONG_CAO_CELLS)
PLAIN_DRAWN = 10  # gap tuples drawn at random for the record of controls/plain_sums.c
FULL_BRACKET = 7  # the bracket of the rule was summed over all cells up to this k
TOUR_STRIPS = ((2000, "Short"), (8000, "Long"))
BEGIN, END = "<!-- results:begin -->", "<!-- results:end -->"
TIMES_BEGIN, TIMES_END = "<!-- times:begin -->", "<!-- times:end -->"


def path(*parts):
    return os.path.join(REPO, *parts)


class Record(str):
    """The text of a file.  Its attribute `name` is the file, for the messages of failures."""


def read(*parts):
    with open(path(*parts), encoding="utf-8", newline="") as handle:
        text = Record(handle.read())
    text.name = "/".join(parts)
    return text


def fail(message):
    raise SystemExit(f"paper_numbers: {message}")


def find(pattern, text, what):
    """The first match of the pattern in the text of a record, which must have one."""
    match = re.search(pattern, text, re.MULTILINE)
    if not match:
        fail(f"no {what} in {getattr(text, 'name', 'the record')}")
    return match


def grouped(number):
    """An integer with LaTeX thousands separators; numbers below 10,000 are set without them."""
    if number < 10000:
        return str(number)
    return f"{number:,}".replace(",", "{,}")


def decimal(numerator, denominator, digits, up):
    """numerator / denominator with the given number of decimals, rounded up or down."""
    scaled = cdiv(numerator * 10**digits, denominator) if up else numerator * 10**digits // denominator
    return f"{scaled // 10**digits}.{scaled % 10**digits:0{digits}d}"


def power_of_ten(value, digits=1):
    """A positive real number as LaTeX, a \\cdot 10^{b}."""
    exponent = math.floor(math.log10(value))
    mantissa = f"{value / 10**exponent:.{digits}f}"
    if float(mantissa) >= 10:
        exponent += 1
        mantissa = f"{value / 10**exponent:.{digits}f}"
    if float(mantissa) == 1:
        return f"10^{{{exponent}}}"
    return f"{mantissa}\\cdot10^{{{exponent}}}"


def height(par):
    if par["hd"] == 1:
        return str(par["hn"])
    return f"{par['hn']}/{par['hd']}"


def in_tenths(count):
    """count / 10 in lowest terms, written like the strip heights."""
    divisor = math.gcd(count, 10)
    return height({"hn": count // divisor, "hd": 10 // divisor})


def tabular(columns, head, rows):
    lines = [
        f"\\begin{{tabular}}{{@{{}}{columns}@{{}}}}",
        "\\toprule",
        " & ".join(head) + " \\\\",
        "\\midrule",
    ]
    lines += [" & ".join(row) + " \\\\" for row in rows]
    return "\n".join([*lines, "\\bottomrule", "\\end{tabular}"]) + "\n"


# ----------------------------------------------------------------------------------- checker records
def result_names():
    """The spec files of the results: k5, k6, ... as far as they are present."""
    names = []
    for k in WORDS:
        if not os.path.exists(path("data", "specs", f"k{k}.txt")):
            break
        names.append(f"k{k}")
    if len(names) < 3:
        fail("fewer than three of the spec files k5.txt, k6.txt, ... are present")
    return names


def stored_total(name, par):
    """The total of the values file of a spec file, recomputed from the cell sums and the masses of that
    file (Section 8 of RECIPE.md); the file must end with this total."""
    k, m = par["k"], par["m"]
    lines = read("data", "values", f"{name}.txt").splitlines()
    masses = [
        int(field) for field in find(r"^masses((?: \d+)+)$", "\n".join(lines[:10]), "masses").group(1).split()
    ]
    start = lines.index(f"sums {m**k}") + 1
    level = [int(line) for line in lines[start : start + m**k]]
    if len(masses) != m or len(level) != m**k:
        fail(f"the values file of {name} has another number of masses or of cell sums")
    for j in range(k, 0, -1):  # A_{j-1} from A_j: the gap g_j is the highest digit of the index
        size = m ** (j - 1)
        level = [
            cdiv(sum(masses[c] * level[prefix + c * size] for c in range(m)), D) for prefix in range(size)
        ]
    if lines[start + m**k :] != [f"total {level[0]}"]:
        fail(f"the values file of {name} does not end with the total of its cell sums")
    return level[0]


def checker_record(name):
    """The total of a spec file from the records of the checkers, after checking them."""
    par = read_spec(path("data", "specs", f"{name}.txt"))
    texts = {}
    for checker in CHECKERS:
        if not os.path.exists(path("runs", f"{checker}_{name}.txt")):
            fail(f"no record of the {LABELS[checker]} checker for {name}")
        texts[checker] = read("runs", f"{checker}_{name}.txt")
    if len(set(texts.values())) != 1:
        fail(f"the checkers printed different lines for {name}")
    text = next(iter(texts.values()))
    if text.splitlines()[-1] != "ACCEPTED":
        fail(f"the record of {name} does not end with ACCEPTED")
    total = int(find(r"^total (\d+)$", text, "total").group(1))
    k, n = par["k"], par["n"]
    numerator, denominator = total * par["hd"], n ** (k + 1) * F * k * par["hn"]
    if find(r"^bound (\S+) \(rounded up\)$", text, "bound").group(1) != decimal(
        numerator, denominator, 12, True
    ):
        fail(f"the printed bound of {name} does not match its total")
    if not numerator * par["theta_d"] < par["theta_n"] * denominator:
        fail(f"the bound of {name} is not below its threshold")
    lines = [
        "the stored values agree with the recomputed values",
        f"total {total}",
        f"bound {decimal(numerator, denominator, 12, True)} (rounded up)",
        f"bound <= {par['theta_n']}/{par['theta_d']}",
        "ACCEPTED",
    ]
    if text.splitlines() != lines:
        fail(f"the record of {name} is not the five lines that a checker prints for its spec file")
    if stored_total(name, par) != total:
        fail(f"the total in the records of {name} is not that of the values file")
    digest = hashlib.sha256(text.encode()).hexdigest()
    return {
        "par": par,
        "total": total,
        "fraction": (numerator, denominator),
        "value": numerator / denominator,
        "digest": digest,
        "text": text,
        "checkers": tuple(texts),
    }


def times():
    """runs/times.txt as a dictionary (checker, spec, platform) -> list of (threads, seconds, digest)."""
    table = {}
    for line in read("runs", "times.txt").splitlines():
        if line.startswith("#") or not line.strip():
            continue
        checker, name, platform, threads, elapsed, digest = line.split()
        table.setdefault((checker, name, platform), []).append((int(threads), float(elapsed), digest))
    return table


def check_repeats(records, table, names):
    """Every run of every checker printed the lines of the record, and the runs were repeated.

    The paper states that every run was made at least twice, with the exceptions in ONCE; README.md
    gives times of the C checker under Linux.
    """
    for (checker, name, platform), runs in table.items():
        if name in records and any(digest != records[name]["digest"] for _, _, digest in runs):
            fail(f"a run of {checker} on {name} ({platform}) printed other lines")
    for name in names:
        for checker in records[name]["checkers"]:
            count = sum(len(runs) for key, runs in table.items() if key[:2] == (checker, name))
            enough = count == 1 if (checker, name) in ONCE else count >= 2
            if not enough:
                fail(f"{count} runs of {checker} on {name}: not what the paper states")
        if ("c", name, "linux") not in table:
            fail(f"no run of the C checker on {name} under Linux")


def check_earlier(records):
    """The records of runs/earlier are those listed in EARLIER, and each equals the present record."""
    for name, checkers in EARLIER.items():
        for checker in CHECKERS:
            exists = os.path.exists(path("runs", "earlier", f"{checker}_{name}.txt"))
            if exists != (checker in checkers):
                fail(f"runs/earlier: the record of {checker} for {name} is not as the paper states")
            if exists and read("runs", "earlier", f"{checker}_{name}.txt") != records[name]["text"]:
                fail(f"the earlier version of {checker} printed other lines for {name}")


def earlier_sentence():
    """The sentence of Section 5.2 on the runs of the earlier versions (check_earlier tests it)."""
    by_all = [name for name, checkers in EARLIER.items() if checkers == CHECKERS]
    by_c = [name for name, checkers in EARLIER.items() if checkers == ("c",)]
    if by_all != ["k5", "k6", "k7"] or by_c != ["k8"] or len(EARLIER) != 4:
        fail("the sentence on the earlier versions is written for k5, k6, k7 (all programs) and k8 (C)")
    return (
        "For $k\\le7$ we computed every cell sum with these versions as well, and for $k=8$ with the "
        "earlier version of the C program. The results were the same."
    )


LEAN_STANDARD = {"propext", "Classical.choice", "Quot.sound"}  # the three axioms of every Lean proof
LEAN_EVALUATION = r"Results\.\w+\._native\.native_decide\.ax_\d+_\d+"  # one evaluation in compiled code
LEAN_PROJECT_FILES = (
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
)  # sources beside the *.lean files


def lean_shared(name, k, total, stated_axioms):
    """The checks on the evaluation of one k by the routine of lean/TSPShared: the theorem in
    lean/Results/K{k}S.lean, the list of its pieces, one record for each piece (and only one: the
    paper says that the evaluation was run once), the end of the driver's output, and the axioms of the
    theorem (one evaluation for each piece and one for the last steps of the recursion)."""
    tag = f"{name}s"
    needed = [("Results", f"K{k}S.lean"), ("runs", f"{tag}_pieces.txt"), ("runs", f"{tag}_done.txt")]
    for parts in needed:
        if not os.path.exists(path("lean", *parts)):
            fail(f"the Lean development has no file lean/{'/'.join(parts)} for {name}")
    statement = f"theorem {tag}_total : Spec.total {name} = {total} := by"
    if statement not in read("lean", "Results", f"K{k}S.lean"):
        fail(f"the Lean development states another total for {name} in lean/Results/K{k}S.lean")
    folder = path("lean", "Results", f"K{k}S")
    pieces = sorted(file[:-5] for file in os.listdir(folder) if file.endswith(".lean"))
    if not pieces or read("lean", "runs", f"{tag}_pieces.txt").split() != [f"K{k}S", *pieces]:
        fail(f"lean/runs/{tag}_pieces.txt does not list the pieces in lean/Results/K{k}S")
    record = read("lean", "runs", f"{tag}_done.txt")
    done = [line.split() for line in record.splitlines() if line.strip()]
    if any(len(fields) != 6 for fields in done) or sorted(fields[0] for fields in done) != pieces:
        fail(f"lean/runs/{tag}_done.txt does not record every piece of {name} exactly once")
    for piece, _, _, source, _, _ in done:
        with open(os.path.join(folder, piece + ".lean"), "rb") as handle:
            if hashlib.sha256(handle.read()).hexdigest() != source:
                fail(f"lean/runs/{tag}_done.txt records another source for the piece {piece} of {name}")
    outputs = sorted(
        file for file in os.listdir(path("lean", "runs")) if re.fullmatch(rf"{tag}_run\d*\.out", file)
    )
    if not outputs or not read("lean", "runs", outputs[-1]).rstrip().endswith("== all done"):
        fail(f"the driver's record for {name} (lean/runs/{tag}_run*.out) does not end with '== all done'")
    expected = sorted(
        [f"Results.{tag}_P_{'_'.join(piece[1:])}._native.native_decide.ax_1_1" for piece in pieces]
        + [f"Results.{tag}_total._native.native_decide.ax_1_1"]
    )
    for theorem in (f"Results.{tag}_total", f"Results.{tag}_accepts"):
        evaluations = sorted(a for a in stated_axioms.get(theorem, []) if a not in LEAN_STANDARD)
        if evaluations != expected:
            fail(f"lean/runs/axioms.txt does not list one evaluation for each piece behind {theorem}")


def lean_pieces(name):
    """The pieces of the evaluation of one k by the routine of lean/TSPShared, from
    lean/runs/{name}s_done.txt (which lean_shared compares with the sources): their number, the sum of
    their times in hours, and the numbers of threads as lean/README.md writes them.  Each piece must state
    the values A_j(g_1, t) of Section 8 of RECIPE.md for all first gaps g_1 at once."""
    record = read("lean", "runs", f"{name}s_done.txt")
    done = [line.split() for line in record.splitlines() if line.strip()]
    for fields in done:
        source = read("lean", "Results", f"{name.upper()}S", fields[0] + ".lean")
        if source.count(f"(List.range (m {name})).map (fun g1 => Spec.A {name} (g1 :: [") != 1:
            fail(f"the piece {fields[0]} of {name} in Lean does not state the values for all first gaps")
    hours = sum(float(fields[2]) for fields in done) / 3600
    threads = " or ".join(str(count) for count in sorted({int(fields[1]) for fields in done}))
    return len(done), f"{hours:.1f}", threads


def lean_record(records, names):
    """The largest k for which the total is a theorem of the Lean development in lean/, after checking
    the records of its builds (lean/runs/final_build3.out for the older routine, the files that
    `lean_shared` reads for the routine of lean/TSPShared, and lean/runs/axioms.txt, the output of
    `lake build Results.Axioms`); None if the folder lean/ is not there.  The theorems must state the
    totals and the parameters of the records of the checkers, every step of the build must have ended
    with status 0, and no theorem may rest on an axiom other than the three standard ones and the
    evaluations in compiled code."""
    if not os.path.exists(path("lean")):
        return None
    for name in ("final_build3.out", "axioms.txt"):
        if not os.path.exists(path("lean", "runs", name)):
            fail(f"the folder lean/ is there without the record lean/runs/{name}")
    log, axioms = read("lean", "runs", "final_build3.out"), read("lean", "runs", "axioms.txt")
    steps = dict(re.findall(r"^== (\S+(?: \S+)?) exit (\d+) end ", log, re.MULTILINE))
    if "== all done" not in log or any(status != "0" for status in steps.values()):
        fail("the record of the Lean build is not complete, or a step failed")
    with open(path("lean", "TSPBound", "Spec.lean"), "rb") as handle:
        digest = hashlib.sha256(handle.read()).hexdigest()
    digests = re.findall(r"^([0-9a-f]{64}) [ *]TSPBound/Spec\.lean$", log, re.MULTILINE)
    if len(digests) != 2 or set(digests) != {digest}:
        fail("lean/TSPBound/Spec.lean is not the file that the record of the Lean build names")
    # every source must be the file that was there when the build had ended (lean/runs/sources_at_end.txt)
    if not os.path.exists(path("lean", "runs", "sources_at_end.txt")):
        fail("the folder lean/ is there without the record lean/runs/sources_at_end.txt")
    at_end = read("lean", "runs", "sources_at_end.txt")
    recorded = {
        name: digest for digest, name in re.findall(r"^([0-9a-f]{64}) [ *](\S+)$", at_end, re.MULTILINE)
    }
    sources = {}
    for folder, folders, files in os.walk(path("lean")):
        folders[:] = [name for name in folders if name not in (".lake", "runs")]
        for name in files:
            if name.endswith(".lean") or name in LEAN_PROJECT_FILES:
                with open(os.path.join(folder, name), "rb") as handle:
                    relative = os.path.relpath(os.path.join(folder, name), path("lean")).replace(os.sep, "/")
                    sources[relative] = hashlib.sha256(handle.read()).hexdigest()
    if sources != recorded or recorded.get("TSPBound/Spec.lean") != digest:
        fail("the sources in lean/ are not the files that lean/runs/sources_at_end.txt lists")
    commands = re.findall(r"^\$ .*lake build.*$", at_end, re.MULTILINE)
    if len(commands) < 2 or any(not command.endswith("exit status 0)") for command in commands):
        fail("lean/runs/sources_at_end.txt does not record builds that ended with status 0")
    stated_axioms = {}
    for theorem, text in re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", axioms):
        listed = [axiom.strip() for axiom in text.split(",")]
        # lake prints the list of a theorem again when it replays the file that states it
        if stated_axioms.setdefault(theorem, listed) != listed:
            fail(f"lean/runs/axioms.txt gives two different lists of axioms for {theorem}")
    foreign = {
        axiom
        for listed in stated_axioms.values()
        for axiom in listed
        if axiom not in LEAN_STANDARD and not re.fullmatch(LEAN_EVALUATION, axiom)
    }
    if foreign or "sorry" in axioms:
        fail(f"the Lean theorems rest on other axioms than lean/README.md states: {sorted(foreign)}")
    parameters = read("lean", "Results", "Params.lean").replace("\r\n", "\n")
    largest = None
    for name in names:  # the parameter sets of all results
        par, k = records[name]["par"], records[name]["par"]["k"]
        definition = (
            f"def {name} : Params :=\n"
            f"  {{ k := {k}, h1 := {par['hn']}, h2 := {par['hd']}, M := {par['M']}, "
            f"b := [{par['b'][1]}, {par['b'][2]}, {par['b'][3]}], n := {par['n']}, nu := {par['nu']}, "
            f"T := {par['T']},\n    theta1 := {par['theta_n']}, theta2 := {par['theta_d']} }}\n"
        )
        if definition not in parameters:
            fail(f"lean/Results/Params.lean states other parameters for {name} than its spec file")
    for name in names:  # the older routine, which evaluated every k but the largest
        k = records[name]["par"]["k"]
        if not os.path.exists(path("lean", "Results", f"K{k}.lean")):
            break
        statement = f"theorem {name}_total : Spec.total {name} = {records[name]['total']} := by"
        if statement not in read("lean", "Results", f"K{k}.lean"):
            fail(f"the Lean development states another total for {name}")
        if steps.get(f"Results.K{k}") != "0" or steps.get("Results") != "0":
            fail(f"the record of the Lean build has no step for {name}")
        for theorem in (f"Results.{name}_total", f"Results.{name}_accepts"):
            evaluations = [a for a in stated_axioms.get(theorem, []) if a not in LEAN_STANDARD]
            if not evaluations:
                fail(f"lean/runs/axioms.txt does not list the evaluations behind {theorem}")
        largest = k
    if largest is None or largest != records[names[0]]["par"]["k"] + len(names) - 2:
        fail("lean/README.md says that the older routine evaluated every k but the largest")
    for name in names:  # the routine of lean/TSPShared, which evaluated every k
        lean_shared(name, records[name]["par"]["k"], records[name]["total"], stated_axioms)
    return records[names[-1]]["par"]["k"]


def splitmix64(seed, count):
    """The first numbers of the generator SplitMix64 for a seed, as controls/plain_sums.c draws them."""
    mask, state = (1 << 64) - 1, seed
    for _ in range(count):
        state = (state + 0x9E3779B97F4A7C15) & mask
        z = ((state ^ (state >> 30)) * 0xBF58476D1CE4E5B9) & mask
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & mask
        yield z ^ (z >> 31)


def plain_record(name, par):
    """The record of controls/plain_sums.c for the values file of a spec file, checked against the values
    file.  Returns the number of cell sums that the control computed, the number of cells of each gap
    tuple in which it also went through all orders, and the step between these cells."""
    k, m, n = par["k"], par["m"], par["n"]
    record = f"the record of the plain cell sums for {name}"
    lines = [line for line in read("runs", f"plain_{name}.txt").splitlines() if not line.startswith("#")]
    first = (
        f"plain cell sums for data/values/{name}.txt: k {k}, {m} gap cells, {n} height cells, "
        f"{PLAIN_DRAWN} gap tuples drawn from seed "
    )
    if len(lines) < 3 or not lines[0].startswith(first) or not lines[0][len(first) :].isdigit():
        fail(f"{record} is for another sample")
    drawn = {number % m**k for number in splitmix64(int(lines[0][len(first) :]), PLAIN_DRAWN)}
    values = read("data", "values", f"{name}.txt").splitlines()
    start = values.index(f"sums {m**k}") + 1
    stored = [int(line) for line in values[start : start + m**k]]
    indices, orders = [], set()
    for line in lines[1:-1]:
        match = re.fullmatch(r"index (\d+) gaps((?: \d+)+) sum (\d+) orders (\d+) equal", line)
        if not match:
            fail(f"{record} has a line that is not of the form expected")
        index, gaps = int(match.group(1)), [int(gap) for gap in match.group(2).split()]
        if index >= m**k or gaps != [index // m**i % m for i in range(k)]:
            fail(f"{record}: index {index} and its gaps do not match")
        if int(match.group(3)) != stored[index]:
            fail(f"{record}: the sum of index {index} is not the stored one")
        indices.append(index)
        orders.add(int(match.group(4)))
    ends = {0, m**k - 1}
    if {stored.index(min(stored)), stored.index(max(stored))} != ends:
        fail("controls/README.md says that the first and the last gap tuple have the extreme cell sums")
    sample = ends | drawn
    sample |= {sum((index // m**i % m) * m ** (k - 1 - i) for i in range(k)) for index in sample}
    if len(set(indices)) != len(indices) or set(indices) != sample or len(drawn) != PLAIN_DRAWN:
        fail(f"{record} does not hold the sample that controls/README.md describes")
    count, cells = len(indices), n ** (k + 1)
    if lines[-1] != f"{count} cell sums of {cells} cells each: {count} equal to the stored sums, 0 different":
        fail(f"{record} does not end as expected")
    if len(orders) != 1 or min(orders) < 1:
        fail(f"{record}: the number of cells evaluated from all orders differs between the gap tuples")
    source = read("controls", "plain_sums.c")
    step = int(find(r"^#define STEP (\d+)\b", source, "step of the plain control").group(1))
    if orders != {-(-cells // step)}:
        fail(f"{record}: not every {step}th height tuple was evaluated from all orders")
    return count, orders.pop(), step


def plain_sentences(par, count):
    """What README.md and controls/README.md say on the control of the cell sums for the largest k, as
    pairs (file, text).  (The paper does not report this control.)"""
    k, m, n = par["k"], par["m"], par["n"]
    drawn = NUMERALS[PLAIN_DRAWN]
    controls = ("controls", "README.md")
    return [
        (("README.md",), f"for k = {k} there are {m**k:,} sums over {n ** (k + 1):,} cells each"),
        (("README.md",), f"recomputed {count} of them"),
        (controls, f"recomputed {count} of the {m**k:,} cell sums for k = {k}"),
        (
            controls,
            f"the gap tuples (0, …, 0) and ({m - 1}, …, {m - 1}), which are the least and the greatest",
        ),
        (controls, f"of {drawn} gap tuples drawn at random, and of the reverses of these {drawn}"),
    ]


# ----------------------------------------------------------------------------------- control records
NUMBER = r"([0-9.]+(?:e[+-]?[0-9]+)?)"


def plus_minus(text, label):
    match = find(rf"^{label}\s+{NUMBER} \+/- {NUMBER}", text, label)
    return float(match.group(1)), float(match.group(2))


def with_error(value, error, digits=5):
    return f"{value:.{digits}f}\\pm{error:.{digits}f}"


def limits():
    """The simulated shortest-path values.  Returns, for each k, the smallest value with its strip height
    (in tenths) and its error; the number of blocks; and all values, as values[k][tenths].  The paper
    says that the same blocks were used at all heights: all runs must have one seed and one size."""
    best, values, runs, count, k, h = {}, {}, set(), 0, None, None
    for line in read("runs", "limits.txt").splitlines():
        match = re.match(r"k (\d+), h ([0-9.]+), blocks (\d+), seed (\d+),", line)
        if match:
            k, h, count = int(match.group(1)), float(match.group(2)), int(match.group(3))
            runs.add((count, match.group(4)))
        match = re.match(r"shortest path\s+([0-9.]+) \+/- ([0-9.]+)", line)
        if match:
            entry = (float(match.group(1)), round(10 * h), float(match.group(2)))
            best[k] = min(best.get(k, entry), entry)
            values.setdefault(k, {})[entry[1]] = entry[0]
    if len(runs) != 1:
        fail("the runs of runs/limits.txt differ in the seed or in the number of blocks")
    return best, count, values


def bracket_record(k, record):
    """The margins of the table entries over their upper brackets and, if the record has them, the two
    brackets of the rule summed over all cells with the table cost of the rule."""
    text = read("runs", f"bracket_k{k}.txt")
    if find(r"^(PASSED|FAILED)$", text, "verdict").group(1) != "PASSED":
        fail(f"the bracket for k = {k} failed")
    head = find(r"^brackets on a mesh (\d+) times finer, (\d+) keys,", text, "mesh")
    if (int(head.group(1)), int(head.group(2))) != (2, math.comb(record["par"]["m"] + k, k) - 1):
        fail(f"the bracket for k = {k} is not on a mesh twice as fine or does not cover the table")
    for name in ("entries with lower > upper", "entries with upper > table"):
        if find(rf"^{name} : (\d+)$", text, name).group(1) != "0":
            fail(f"the bracket for k = {k}: {name}")
    match = find(r"^\(table - upper\)/table\s+: min (\S+), max (\S+)$", text, "margins")
    margins = [float(match.group(1)), float(match.group(2))]
    if not 0 < margins[0] <= margins[1] < math.inf:
        fail(f"the margins of the bracket for k = {k} are not positive numbers")
    if "rule evaluated over all cells" not in text:
        if k <= FULL_BRACKET:
            fail(f"the bracket for k = {k} lacks the sums over all cells")
        return margins, None
    if find(r"^cell sums that differ from the values file : (\d+)$", text, "comparison").group(1) != "0":
        fail(f"the bracket for k = {k} found other cell sums")
    cost = float(find(r"^table cost of the rule\s+: (\S+)$", text, "table cost").group(1))
    low = float(find(r"^lower bracket of its true length\s+: (\S+)$", text, "lower bracket").group(1))
    high = float(find(r"^upper bracket of its true length\s+: (\S+)$", text, "upper bracket").group(1))
    if not low <= high <= cost <= record["value"] + 1e-10 or record["value"] - cost > 1e-9:
        fail(f"the record of the bracket for k = {k} is not in the order lower end, upper end, cost, bound")
    return margins, (cost, low, high)


def integral_record(k, par):
    """The margins of the table entries over the conditional expected lengths that
    controls/segment_integral.py finds by numerical integration, after checking what Section 5.3 and
    controls/README.md say about that control."""
    text = read("runs", f"segments_k{k}.txt")
    if find(r"^(PASSED|FAILED)$", text, "verdict").group(1) != "PASSED":
        fail(f"the integrals for k = {k} failed")
    m = par["m"]
    counts = find(r"^integrals for (\d+) keys and (\d+) differences of the height cells,", text, "counts")
    if (int(counts.group(1)), int(counts.group(2))) != (math.comb(m + k, k) - 1, par["n"]):
        fail(f"the integrals for k = {k} do not cover the table")
    short = find(r"^double integrals for the (\d+) keys with one gap or two gaps,", text, "double integrals")
    if int(short.group(1)) != m + m * (m + 1) // 2:
        fail(f"the double integrals for k = {k} do not cover the keys with one gap and two gaps")
    difference = find(r"^largest relative difference between them: (\S+)$", text, "difference").group(1)
    if not float(difference) < 1e-12:
        fail(f"the two evaluations of the integrals for k = {k} differ in the twelfth digit")
    mass = find(r"^total mass of a density, largest error\s*: (\S+)$", text, "error of the mass").group(1)
    if not float(mass) < 1e-12:
        fail(f"a density of the integrals for k = {k} does not have total mass 1")
    for name in ("entries below the integral", "integrals outside the bracket"):
        if find(rf"^{name}\s*: (\d+)$", text, name).group(1) != "0":
            fail(f"the integrals for k = {k}: {name}")
    match = find(r"^\(table - integral\)/table\s+: min (\S+), max (\S+)$", text, "margins of the integrals")
    margins = [float(match.group(1)), float(match.group(2))]
    if not 0 < margins[0] <= margins[1] < math.inf:
        fail(f"the margins of the integrals for k = {k} are not positive numbers")
    return margins, (mass, difference, int(short.group(1)))


def largest(printed):
    """The largest of some numbers that a record prints as 1.9e-15, as LaTeX."""
    mantissa, exponent = max(printed, key=float).split("e")
    return f"{mantissa}\\cdot10^{{{int(exponent)}}}"


def outwards(values):
    """The least and the greatest of some positive numbers as LaTeX, rounded outwards to two significant
    digits."""
    low, high = min(values), max(values)
    exponent = math.floor(math.log10(low))
    low = math.floor(low / 10 ** (exponent - 1)) * 10 ** (exponent - 1)
    exponent = math.floor(math.log10(high))
    high = math.ceil(high / 10 ** (exponent - 1)) * 10 ** (exponent - 1)
    return power_of_ten(low), power_of_ten(high)


def controls(records, names):
    """Macros and the table of the controls of Section 5.3, and what the sentences there state."""
    macros, rows, agreement, over_integrals, costs = {}, [], [], [], []
    second_costs, over_brackets, self_tests = [], [], []
    blocks, seeds = set(), set()
    for name in names:
        record = records[name]
        k, bound = record["par"]["k"], record["value"]
        word = WORDS[k]
        margins, full = bracket_record(k, record)
        over_brackets += margins
        margins, self_test = integral_record(k, record["par"])
        over_integrals += margins
        self_tests.append(self_test)
        text = read("runs", f"blocks_k{k}.txt")
        blocks.add(int(find(r"^blocks (\d+),", text, "number of blocks").group(1)))
        seeds.add(find(r"^blocks \d+, seed (\d+),", text, "seed").group(1))
        rule, best = plus_minus(text, "rule"), plus_minus(text, "shortest path")
        over_low, over_high = plus_minus(text, "table - lower"), plus_minus(text, "table - upper")
        cost = plus_minus(text, "table cost")
        # what Section 5.3 says about the sample of cells
        if max(over_low[1], over_high[1]) >= 1e-9:
            fail(f"the brackets from sampled cells for k = {k} have standard errors of 1e-9 or more")
        costs.append((k, cost[0], cost[1], bound))
        if full is not None:
            if abs(full[0] - full[1] - over_low[0]) >= 1e-9 or abs(full[0] - full[2] - over_high[0]) >= 1e-9:
                fail(f"the brackets from sampled cells and from all cells differ for k = {k}")
            low, high = full[1], full[2]
        else:
            low, high = bound - over_low[0] - 1e-9, bound - over_high[0] + 1e-9
        if not low <= high <= bound or bound - low >= 1e-5:
            fail(f"the bracket for k = {k} does not fit the bound")
        if bound - low >= rule[1]:
            fail(f"for k = {k} the bound lies a standard error or more above the bracket of the rule")
        if k > FULL_BRACKET:
            # the second sample of blocks, with another seed
            second = read("runs", f"blocks_k{k}_second.txt")
            drawn = [
                find(r"^blocks (\d+), seed (\d+),", sample, "seed").groups() for sample in (text, second)
            ]
            if drawn[0][0] != drawn[1][0] or drawn[0][1] == drawn[1][1]:
                fail(f"the second sample of blocks for k = {k} needs the same size and another seed")
            second_rule, second_cost = plus_minus(second, "rule"), plus_minus(second, "table cost")
            if not low - 2 * second_rule[1] <= second_rule[0] <= high + 2 * second_rule[1]:
                fail(f"the second simulated value of the rule for k = {k} is far from its bracket")
            second_costs.append((k, second_cost[0], second_cost[1], bound))
            macros[f"SimCostSecond{word}"] = with_error(*second_cost, 6)
        low, high = math.floor(low * 1e6) / 1e6, math.ceil(high * 1e6) / 1e6
        macros[f"Loss{word}"] = f"{bound - best[0]:.4f}"
        agreement.append(
            (k, (rule[0] - high) / rule[1], (rule[0] - low) / rule[1], (rule[0] - bound) / rule[1])
        )
        rows.append(
            [
                f"${k}$",
                f"${height(record['par'])}$",
                f"${decimal(*record['fraction'], 6, True)}$",
                f"$[{low:.6f},\\,{high:.6f}]$",
                f"${with_error(*rule, 6)}$",
                f"${with_error(*best, 6)}$",
            ]
        )
    if len(blocks) != 1:
        fail("the records of the simulated blocks differ in the number of blocks")
    if len(seeds) != 1:
        fail("the paper says that the samples of blocks for the different k were drawn with one seed")
    macros["SimBlocks"] = power_of_ten(blocks.pop(), 0)
    macros["IntegralMarginMin"], macros["IntegralMarginMax"] = outwards(over_integrals)
    # for controls/README.md
    macros["BracketMarginMin"], macros["BracketMarginMax"] = outwards(over_brackets)
    macros["IntegralMassError"] = largest([mass for mass, _, _ in self_tests])
    macros["IntegralDifference"] = largest([difference for _, difference, _ in self_tests])
    if len({count for _, _, count in self_tests}) != 1:
        fail("controls/README.md gives one number of keys with one gap or two gaps")
    macros["IntegralShortKeys"] = str(self_tests[0][2])
    macros["SimCostMain"] = with_error(costs[-1][1], costs[-1][2], 6)
    table = tabular(
        "ccllll",
        ["$k$", "$h$", "Bound", "Rule, bracket", "Rule, simulated", "Shortest path, simulated"],
        rows,
    )
    return macros, table, agreement, (costs, second_costs)


def tour(record):
    """The records of the simulated tour for the main result, tested; returns the macros.  The paper
    does not report this control; controls/README.md describes it."""
    par = record["par"]
    k, h, bound = par["k"], par["hn"] / par["hd"], record["value"]
    macros = {}
    for strips, word in TOUR_STRIPS:
        text = read("runs", f"tour_k{k}_{strips}.txt")
        match = find(r"^strips (\d+), side ([0-9.]+), points (\d+), blocks (\d+),", text, "tour")
        side = float(match.group(2))
        if int(match.group(1)) != strips or abs(side - strips * h) > 1e-9:
            fail("the tour record has another number of strips or another side")

        def line(label, text=text):
            return float(find(rf"^{label}\s+= (\S+)$", text, "line of the tour record").group(1))

        block = plus_minus(text, r"walks of the proof: length / \(k \* blocks\)\s+=")
        walks = line(r"walks of the proof: length / side\^2")
        realised = line(r"blocks \* k / side\^2")
        factor = line(r"1 \+ \(k \+ 1\) / \(2 h side\)")
        closed = line(r"closed tour through the points: length / side\^2")
        per_root = line(r"closed tour: length / sqrt\(points \* area\)")
        # the lines of the record that follow from its other lines, to the digits printed
        points, blocks = int(match.group(3)), int(match.group(4))
        derived = (
            (realised, blocks * k / side**2),
            (factor, 1 + (k + 1) / (2 * h * side)),
            (walks, block[0] * realised),
            (per_root, closed * side / math.sqrt(points)),
        )
        if any(abs(printed - computed) > 2e-6 for printed, computed in derived):
            fail(f"a line of the tour record with {strips} strips does not follow from its other lines")
        # k * blocks is the number of points plus, for each strip, k less a remainder modulo k
        if abs(realised - (points / side**2 + factor - 1)) > 1e-4 or abs(points - side**2) > 6 * side:
            fail(f"the tour record with {strips} strips has impossible numbers of points or blocks")
        # the last inequality in the proof of the block bound, divided by side^2, with the proved bound
        allowed = bound + (bound * k / h + 2 * k / h**2 + 4) / side
        if not closed < allowed:
            fail("the simulated tour is longer than the proof allows on average")
        if abs(block[0] - bound) > 3 * block[1]:
            fail("the walks of the simulated tour are too far from the bound")
        macros[f"TourStrips{word}"] = str(strips)
    return macros


def numbers():
    names = result_names()
    records = {name: checker_record(name) for name in (*names, "bhh")}
    table = times()
    check_repeats(records, table, names)
    check_earlier(records)
    lean = lean_record(records, names)
    macros = {} if lean is None else {"LeanMaxK": str(lean)}
    if lean is not None:
        pieces, hours, _ = lean_pieces(names[-1])
        macros["LeanMainPieces"], macros["LeanMainHours"] = str(pieces), hours
        macros["LeanMainValues"] = str(pieces * records[names[-1]]["par"]["m"])

    result_rows, readme = [], []
    for name in names:
        record = records[name]
        par = record["par"]
        k, word = par["k"], WORDS[par["k"]]
        cells = power_of_ten(par["m"] ** k * par["n"] ** (k + 1))
        macros[f"Total{word}"] = grouped(record["total"])
        macros[f"Bound{word}"] = decimal(*record["fraction"], 12, True)
        macros[f"Bound{word}Short"] = decimal(*record["fraction"], 6, True)
        macros[f"Bound{word}Up"] = decimal(par["theta_n"], par["theta_d"], 4, True)
        macros[f"Cells{word}"] = cells
        result_rows.append(
            [f"${k}$", f"${height(par)}$", f"${macros[f'Total{word}']}$", f"${macros[f'Bound{word}']}$"]
        )
        readme.append(
            f"| `data/specs/{name}.txt` | {k} | {height(par)} | {record['total']} "
            f"| {decimal(*record['fraction'], 12, True)} | {par['theta_n']}/{par['theta_d']} |"
        )
    results_table = tabular(
        "cclr", ["$k$", "$h$", "$\\mathsf{A}_0$", "$h_2\\mathsf{A}_0/(n^{k+1}Fkh_1)$"], result_rows
    )

    main = records[names[-1]]
    par = main["par"]
    k, m, n, word = par["k"], par["m"], par["n"], WORDS[par["k"]]
    macros["ResultCountWord"] = NUMERALS[len(names)]
    macros["MainK"] = str(k)
    macros["MainPoints"] = NUMERALS[k + 1]
    macros["MainH"] = height(par)
    macros["MainBound"] = macros[f"Bound{word}Up"]
    macros["MainBoundShort"] = macros[f"Bound{word}Short"]
    macros["MainTotal"] = macros[f"Total{word}"]
    macros["MainCells"] = macros[f"Cells{word}"]
    macros["MainCellsFormula"] = f"{m}^{{{k}}}\\cdot{n}^{{{k + 1}}}"
    close = abs(m**k * n ** (k + 1) / DONG_CAO_CELLS - 1) < 0.05
    macros["MainCellsRemark"] = (
        ", about as many as that grid, though a cell takes more work for larger $k$" if close else ""
    )
    macros["MainGapTuples"] = grouped(m**k)
    macros["MainTableEntries"] = grouped(len(all_keys(m, k)) * n)
    macros["MainProofFraction"] = (
        f"{par['hd']}\\,\\mathsf{{A}}_0/({n}^{{{k + 1}}}\\cdot2^{{32}}\\cdot{k}\\cdot{par['hn']})"
    )
    macros["ControlBHH"] = decimal(*records["bhh"]["fraction"], 6, False)
    strip, strip_text = records["bhh"]["par"], read("runs", "strip_integral.txt")
    at_height = find(rf"^h = {strip['hn']}/{strip['hd']}: (0\.\d+)$", strip_text, "integral").group(1)
    at_root = find(r"^h = sqrt\(3\): (0\.\d+)$", strip_text, "integral for the root of 3").group(1)
    least = find(r"^least at h = (\d\.\d{4}): (0\.\d+)$", strip_text, "least integral")
    integral = float(at_height)
    if not 0 < records["bhh"]["value"] - integral < 1e-5:
        fail("the strip bound does not lie above its integral by less than 1e-5")
    if not float(least.group(2)) <= integral < float(at_root):
        fail("runs/strip_integral.txt: the integral at the control's height is not below that at sqrt 3")
    macros["StripIntegral"], macros["StripIntegralRoot"] = at_height[:8], at_root[:8]
    macros["StripExcess"] = power_of_ten(records["bhh"]["value"] - integral, 0)
    macros["StripLeast"] = f"{float(least.group(1)):.3f}"
    if macros["StripLeast"] == f"{math.sqrt(3):.3f}":
        fail("controls/README.md says that the strip integral is not least at the root of 3")
    # the margin that the threshold of the main theorem leaves, to one digit, rounded down
    margin = Fraction(par["theta_n"], par["theta_d"]) - Fraction(*main["fraction"])
    exponent = math.floor(math.log10(margin))
    digit = int(margin / Fraction(10) ** exponent)
    if not 2 <= digit <= 9:
        fail("the margin of the main theorem is not written as a digit times a power of ten")
    macros["MainMargin"] = f"{digit}\\cdot10^{{{exponent}}}"

    control_macros, controls_table, agreement, costs = controls(records, names)
    macros.update(control_macros)
    macros["BracketFullK"] = str(FULL_BRACKET)
    macros["LossMain"] = macros[f"Loss{word}"]
    shortest = plus_minus(read("runs", f"blocks_k{k}.txt"), "shortest path")[0]
    macros["MainLimit"] = f"{shortest:.3f}"
    losses = [float(macros[f"Loss{WORDS[records[name]['par']['k']]}"]) for name in names]
    if losses != sorted(losses) or len(set(losses)) != len(losses):
        fail("the paper says that the loss against the shortest path grows with k")
    macros.update(tour(main))

    text = read("runs", "dongcao_setting.txt")
    samples = int(find(r"^blocks (\d+),", text, "number of blocks").group(1))
    macros["DongCaoSamples"] = power_of_ten(samples, 0)
    macros["DongCaoBound"] = with_error(*plus_minus(text, "mean of their cell bound"))
    macros["DongCaoRule"] = with_error(*plus_minus(text, "true value of their rule"))
    macros["DongCaoShortest"] = with_error(*plus_minus(text, "shortest path"))
    rule, best = plus_minus(text, "true value of their rule")[0], plus_minus(text, "shortest path")[0]
    loss = plus_minus(text, "rule less shortest path")
    if abs(rule - best - loss[0]) > 2e-6 or not 0 < loss[1] < loss[0] / 10:
        fail("the record of the setting of Dong and Cao: the loss of the rule is not as the paper says")
    macros["DongCaoGap"] = with_error(*loss, 6)
    published = plus_minus(text, "mean of their cell bound")
    exact = DONG_CAO_BOUND[0] / DONG_CAO_BOUND[1]
    if decimal(*DONG_CAO_BOUND, 4, True) != "0.8810":
        fail("the paper gives the bound of Dong and Cao as 0.8810, which is not their fraction rounded up")
    if abs(published[0] - exact) > 2 * published[1]:
        fail("controls/README.md says that our mean of the bound of Dong and Cao agrees with their bound")
    # the shortest-path value that Dong and Cao report, as the record of the control quotes it
    theirs = float(find(r"\(their sample mean: (0\.\d+)\)", text, "sample mean of Dong and Cao").group(1))
    ours = plus_minus(read("runs", "blocks_k5.txt"), "shortest path")
    if f"{theirs:.5f}" != "0.87426" or abs(theirs - ours[0]) > 2 * ours[1]:
        fail("Section 6.1 says that the 0.87426 of Dong and Cao agrees with the last column of Table 5.1")

    best, count, values = limits()
    macros["LimitSamples"] = power_of_ten(count, 0)
    macros["LimitError"] = f"{math.ceil(max(error for _, _, error in best.values()) * 1e5) / 1e5:.5f}"
    ks = sorted(best)
    if {len(values[size]) for size in ks} != {3, 4}:
        fail("controls/README.md says that three or four strip heights were tried for each k")
    # what Section 6.1 says about the heights next to the best one
    close, gaps = [], []
    for size in ks:
        value, tenths, _ = best[size]
        below, above = (values[size].get(t, math.inf) - value for t in (tenths - 1, tenths + 1))
        if below < 1e-4:
            close.append(size)
        elif math.inf in (below, above):
            fail(f"for k = {size} the record lacks a height next to the best one")
        else:
            gaps += [below, above]
    if close != [7, 9]:
        fail("Section 6.1 names other k for which two heights give almost the same value")
    # Section 6.1: for k = 6 to 9, the best strip height for the shortest path is 1/10 above that of the
    # result
    if [records[name]["par"]["k"] for name in names] != [5, 6, 7, 8, 9]:
        fail("Section 6.1 compares the strip heights for k = 6 to 9")
    for name in names:
        size, hn, hd = (records[name]["par"][key] for key in ("k", "hn", "hd"))
        if best[size][1] - Fraction(10 * hn, hd) != (1 if size >= 6 else 0):
            fail(f"Section 6.1 states another difference of the strip heights for k = {size}")
    macros["LimitGapMin"] = f"{math.floor(min(gaps) * 1e4) / 1e4:.4f}"
    macros["LimitGapMax"] = f"{math.ceil(max(gaps) * 1e4) / 1e4:.4f}"
    macros["LimitStepFirst"] = f"{best[ks[0]][0] - best[ks[1]][0]:.3f}"
    macros["LimitStepLast"] = f"{best[ks[-2]][0] - best[ks[-1]][0]:.3f}"
    limits_table = tabular(
        "l" + "c" * len(ks),
        ["$k$", *(f"${k}$" for k in ks)],
        [
            ["$h$", *(f"${in_tenths(best[k][1])}$" for k in ks)],
            ["Value", *(f"${best[k][0]:.4f}$" for k in ks)],
        ],
    )

    # numbers.tex gets the macros that the paper uses, in its text or in the value of another of them;
    # the other entries of macros are values for the sentences of the README files
    tex = sorted(name for name in os.listdir(path("paper", "tex")) if name.endswith(".tex"))
    text = "".join(visible(("paper", "tex", name)) for name in tex if name != "numbers.tex")
    used = set()
    while True:
        more = {name for name in macros if re.search(rf"\\{name}(?![A-Za-z])", text)} - used
        if not more:
            break
        used |= more
        text += "".join(macros[name] for name in more)
    lines = ["% Written by tools/paper_numbers.py from the records in runs/; do not edit."]
    lines += [f"\\newcommand{{\\{name}}}{{{value}}}" for name, value in macros.items() if name in used]
    head = [
        "| Spec file | k | h | Total A₀ | Bound (rounded up) | Threshold |",
        "|---|---|---|---|---|---|",
    ]
    targets = {
        "numbers.tex": "\n".join(lines) + "\n",
        "results_table.tex": results_table,
        "controls_table.tex": controls_table,
        "limits_table.tex": limits_table,
    }
    return targets, "\n".join(head + readme) + "\n", records, names, agreement, costs, lean, macros


def readme_times(table, names):
    """The paragraph of README.md, between its two markers, on how long a check takes: the times of the
    first runs under Windows for the largest k, and the times of the C checker under Linux.  The paper
    does not give running times.  (That the C checker was built with MSVC under Windows and with gcc
    under Linux is not in runs/times.txt.)"""

    def first(checker, name):
        threads, elapsed, _ = table[checker, name, "windows"][0]
        return threads, elapsed

    main, before = names[-1], names[-2]
    (c_threads, c_time), (rust_threads, rust_time) = first("c", main), first("rust", main)
    python_threads, python_time = first("python", main)
    if CHECKERS != ("python", "c", "rust") or c_threads != rust_threads:
        fail("README.md gives one number of threads for the C and the Rust checker")
    if python_time <= max(c_time, rust_time):
        fail("README.md gives the Python checker as the slowest of the three")
    linux = table.get(("c", main, "linux"), [])
    if not linux or any(threads != c_threads for threads, _, _ in linux):
        fail(f"README.md gives times of the C checker for {main} under Linux, on the threads of Windows")
    linux_minutes = sorted({f"{elapsed / 60:.0f}" for _, elapsed, _ in linux}, key=int)
    if len(linux_minutes) > 2:
        linux_minutes = [f"between {linux_minutes[0]}", linux_minutes[-1]]
    if max(first(checker, name)[1] for checker in CHECKERS for name in names[:-2]) >= 60:
        fail("README.md says that the spec files before the last two take less than a minute")
    compiled = sorted({f"{first(checker, before)[1] / 60:.0f}" for checker in ("c", "rust")}, key=int)
    text = (
        f"On a desktop computer the check of `{main}.txt` took {c_time / 60:.0f} minutes with the C checker "
        f"built with MSVC under Windows ({' and '.join(linux_minutes)} minutes built with gcc under Linux) "
        f"and {rust_time / 60:.0f} minutes with the Rust checker, on {c_threads} threads each, and "
        f"{python_time / 3600:.1f} hours with the Python checker on {python_threads} processes. The spec "
        f"files up to `{names[-3]}.txt` take less than a minute, and `{before}.txt` takes about "
        f"{' to '.join(compiled)} minutes with the C or the Rust checker and "
        f"{first('python', before)[1] / 60:.0f} with the Python checker (`runs/times.txt`)."
    )
    return textwrap.fill(text, width=105) + "\n"


def runs_sentence():
    """The sentence of Section 5.2 on repeated runs (check_repeats tests it against runs/times.txt)."""
    sentence = "Each program was run at least twice for each $k$"
    if not ONCE:
        return sentence + ". All runs printed the same result."
    ((checker, name),) = ONCE
    sentence += f", except the {LABELS[checker]} program for $k={name[1:]}$, which was run once."
    return sentence + " All runs printed the same result."


def readme_runs_sentence():
    """The sentence of README.md on repeated runs: the facts of runs_sentence, for the same spec files."""
    sentence = "Every checker was run at least twice on each of `k5.txt` to `k9.txt`"
    if ONCE:
        ((checker, name),) = ONCE
        sentence += f", except the {LABELS[checker]} checker on `{name}.txt`, which was run once"
    return sentence + "; all runs printed the same lines (`runs/times.txt`)."


REACH = {1: "one standard error", 2: "two standard errors", 3: "three standard errors"}


def agreement_sentence(agreement):
    """The sentences of controls/README.md on the simulated values of the rule, after checking that the
    records bear them out.  Section 5.3 of the paper has the first of them, and says after it that some
    of the values lie above the bound and that the bound exceeds the value of the rule by less than one
    standard error.  Each entry of agreement is (k, a, b, c): the simulated value minus the upper end of
    the bracket, minus its lower end and minus the bound, in standard errors.  (That the bound exceeds
    the lower end of the bracket by less than a standard error, as the last sentence says, is checked in
    controls.)  If the records change so that the check fails, the sentences are to be written anew, here,
    in controls/README.md and in the paper."""
    worst = max(max(above, -below, 0.0) for _, above, below, _ in agreement)
    over = {k: excess for k, _, _, excess in agreement if excess > 0}
    # the standard errors are printed with one or two digits, so an excess up to 1.05 is "about one"
    if worst > 2 or sorted(over) != [5, 6, 8] or max(over.values()) > 1.05:
        fail(
            "controls/README.md says that the simulated values of the rule lie within two standard errors "
            "of their brackets, and above the bound for k = 5, 6 and 8 only, by about one standard error "
            "at most"
        )
    return (
        "The simulated values of the rule lie within two standard errors of their brackets. For $k=5$, $6$ "
        "and $8$ they lie above the bound of \\cref{thm:computation}, none by more than about one standard "
        "error. This is to be expected in some cases: the bound exceeds the value of the rule by less than "
        "one standard error."
    )


def cost_sentences(costs):
    """The sentences of Section 5.3 on the cost of the rule in the simulated blocks (the first samples).
    Each entry is (k, mean cost, standard error, bound).  The second samples, which controls/README.md
    reports, must lie within two standard errors of their bounds as well."""

    def reach(sample):
        worst = max(abs(cost - bound) / error for _, cost, error, bound in sample)
        if worst > 2:
            fail("a simulated cost of the rule lies more than two standard errors from its bound")
        return REACH[math.ceil(worst)]

    first, second = costs
    if [k for k, *_ in second] != [8, 9]:
        fail("the sentence on the second sample of blocks is written for k = 8 and k = 9")
    reach(second)  # the second samples, too, lie within two standard errors of their bounds
    if any(3 * error >= 3e-5 for k, _, error, _ in first if k > FULL_BRACKET):
        fail("Section 5.3 says that 3e-5 is more than three standard errors of the simulated cost")
    return (
        "For $k=8$ and $k=9$ an error in the total that changed the bound by $3\\cdot10^{-5}$, which is "
        "more than three standard errors, would very probably show in this estimate",
        f"For $k={first[-1][0]}$ it gave $\\SimCostMain$, against the bound $\\MainBoundShort$, and for "
        f"every $k$ it lies within {reach(first)} of the bound.",
    )


def mutation_sentence():
    """The two sentences of checkers/TESTS.md on the wrong versions of the checkers, how many of the Python
    checker there are and how many of the C and of the Rust checker the tests do not detect, from the four
    summary lines of runs/mutation_test.txt (Python, C under Linux, Rust, C under Windows, in this order)."""
    record = read("runs", "mutation_test.txt")
    commands = re.findall(r"^\$ .*?(\w+\.py(?: \w+)?) +\((\w+)", record, re.MULTILINE)
    if commands != [
        ("mutation_test.py", "Windows"),
        ("mutation_test_compiled.py c", "Linux"),
        ("mutation_test_compiled.py rust", "Windows"),
        ("mutation_test_compiled.py c", "Windows"),
    ]:
        fail("runs/mutation_test.txt does not hold the four runs in the expected order")
    counts = re.findall(r"^(\d+) of (\d+) mutants detected$", record, re.MULTILINE)
    if len(counts) != 4 or counts[0][0] != counts[0][1]:
        fail("checkers/TESTS.md says that the tests detect every wrong version of the Python checker")
    (c_found, c_all), (rust_found, rust_all), (windows_found, windows_all) = (
        (int(a), int(b)) for a, b in counts[1:]
    )
    if c_found >= c_all or rust_found >= rust_all:
        fail("checkers/TESTS.md says that some wrong versions of the C and the Rust checker are not detected")
    # the lists say which wrong versions are not detected, and on which systems
    with open(path("checkers", "mutants_c.json"), encoding="utf-8") as handle:
        c_list = [entry for entry in json.load(handle) if "undetected" in entry]
    with open(path("checkers", "rust", "mutants.json"), encoding="utf-8") as handle:
        rust_list = [entry for entry in json.load(handle) if "undetected" in entry]
    posix_only = [entry for entry in c_list if entry.get("undetected_on") == "posix"]
    if any("undetected_on" in entry for entry in rust_list) or len(rust_list) != rust_all - rust_found:
        fail("the list of wrong versions of the Rust checker does not agree with the record")
    if len(c_list) != c_all - c_found or any(e.get("undetected_on", "posix") != "posix" for e in c_list):
        fail("the list of wrong versions of the C checker does not agree with the record")
    if (windows_all, windows_all - windows_found) != (c_all, len(c_list) - len(posix_only)):
        fail("the list of wrong versions of the C checker does not agree with the record under Windows")
    return (
        f"- `mutation_test.py` makes {counts[0][1]} wrong versions of the Python checker and confirms that "
        "the tests above detect every one.",
        f"- Of the {c_all} wrong versions of the C checker {len(c_list)} are not detected under Linux and "
        f"{len(c_list) - len(posix_only)} under Windows, and of the {rust_all} of the Rust checker "
        f"{len(rust_list)}.",
    )


def lean_statements(lean, par):
    """What README.md and Sections 1.3 and 5.2 must say about Lean, with or without a record of its build."""
    if lean is None:
        return [(("README.md",), "No part of the proof has been formalised in a proof assistant.")]
    if lean != par["k"]:
        fail("the paragraph on Lean in Section 5.2 says that Lean evaluated every k")
    pieces, hours, threads = lean_pieces(f"k{lean}")
    readme, intro = ("README.md",), ("paper", "tex", "sec1_intro.tex")
    computation = ("paper", "tex", "sec5_computation.tex")
    return [
        (readme, f"For k = 5 to {lean} the totals are also proved in Lean 4"),
        (
            readme,
            f"for k = {lean} it was run once, in {pieces} pieces that took {hours} hours on {threads} "
            "threads",
        ),
        (intro, "The total for $k=\\MainK$ was also confirmed in the proof assistant Lean"),
        (intro, "that the Lean kernel does not check and that was run once"),
        (computation, "For $k=5,\\dots,\\LeanMaxK$ the totals were also"),
        (computation, "For $k=\\LeanMaxK$ the evaluation was run once."),
    ]


def plain(tex):
    """A value of numbers.tex as the README files write it."""
    for old, new in (("\\pm", " ± "), ("\\cdot10^{", "·10^"), ("{,}", ","), ("{", ""), ("}", ""), ("$", "")):
        tex = tex.replace(old, new)
    return tex


def controls_readme(names, agreement, costs, macros, strip):
    """The sentences of controls/README.md that state a number or a comparison of the records, as pairs
    (file, text), with the numbers written as that file writes them."""
    value = {name: plain(text) for name, text in macros.items()}
    first, second = costs
    within = REACH[math.ceil(max(abs(cost - bound) / error for _, cost, error, bound in first))]
    texts = [
        f"by a relative margin between {value['IntegralMarginMin']} and {value['IntegralMarginMax']}",
        f"must have total mass 1; the largest error was {value['IntegralMassError']}",
        f"For the {value['IntegralShortKeys']} keys with one gap or two gaps the integral was computed",
        f"differ by at most {value['IntegralDifference']} in relative terms",
        f"by a relative margin between {value['BracketMarginMin']} and {value['BracketMarginMax']}",
        "the sample averages agree with the averages over all cells to within 10^-9",
        f"is least near h = {value['StripLeast']}, not at √3",
        f"{value['DongCaoShortest']} against their 0.87426",
        f"standard errors are at most {value['LimitError']}",
        "Three or four heights were tried for each k",
        f"For k ≤ {FULL_BRACKET} the average is over all cells.",
        f"The script draws {value['SimBlocks']} independent blocks for each k",
        plain(agreement_sentence(agreement).replace("\\cref{thm:computation}", "Theorem 5.1")).replace(
            "k=", "k = "
        ),
        f"For k = {first[-1][0]} it gave {value['SimCostMain']}, against the bound "
        f"{value['MainBoundShort']}, and for every k it lies within {within} of the bound.",
        f"for k = {second[0][0]} and k = {second[1][0]}, gave {value['SimCostSecondEight']} and "
        f"{value['SimCostSecondNine']}, against the bounds {value['BoundEightShort']} and "
        f"{value['BoundNineShort']}",
        f"For h = {strip['hn']}/{strip['hd']}, a fraction close to √3, and ν = {strip['nu']}, with "
        f"M = {strip['M']} and T = {strip['T']} as for the results",
        f"gave the bound {value['ControlBHH']}…, and numerical integration gave {value['StripIntegral']}… "
        f"for the same quantity, lower by {value['StripExcess']}",
        f"For h = √3 the integration gave {value['StripIntegralRoot']}…",
        f"once with {value['TourStripsShort']} strips and once with {value['TourStripsLong']}",
        f"for {value['DongCaoSamples']} blocks",
        f"was {value['DongCaoBound']}, which agrees",
        f"value {value['DongCaoRule']}, and in the same blocks the rule lost {value['DongCaoGap']} against",
        f"from {value['LimitSamples']} blocks",
        "for k = 7 and k = 9 the next lower height gives a value larger by less than 0.0001",
        f"between {value['LimitGapMin']} and {value['LimitGapMax']}",
    ]
    return [(("controls", "README.md"), text) for text in texts]


def readme_statements(names, pars, threshold):
    """Further statements of the README files that repeat a record, as pairs (file, text): the threshold
    in the first paragraphs of README.md; the commands for the last three spec files in
    checkers/README.md, and for the last one in README.md, with the numbers of threads or processes of
    the first runs under Windows (the times that readme_times gives belong to these); and what
    controls/README.md says of the record of controls/plain_sums.c beyond what plain_sentences has."""
    name, table = names[-1], times()
    par = pars[name]
    k, m, n = par["k"], par["m"], par["n"]
    count, orders, step = plain_record(name, par)
    if 10 <= step % 100 <= 20 or step % 10 != 3:
        fail("controls/README.md writes the step of plain_sums.c as an ordinal number that ends in 3")
    commands = {
        "c": "./cchk",
        "rust": "checkers/rust/target/release/rchk",
        "python": "python checkers/check_bound.py",
    }
    readme, checkers, controls = ("README.md",), ("checkers", "README.md"), ("controls", "README.md")
    statements = [
        (readme, f"The paper proves β < {threshold}"),
        (readme, f"that the number is below {threshold} is the result of the computation"),
        (readme, f"The bound is A₀·h₂ / ({n}^(k+1)·2^32·k·h₁) for h = h₁/h₂"),
        (
            controls,
            f"for every {step}rd cell ({orders} of the {n ** (k + 1):,} cells of a gap tuple) a second time "
            f"by going through all {math.factorial(k - 1):,} orders",
        ),
        (controls, f"The {count} equal the stored ones (`runs/plain_{name}.txt`)"),
        (controls, f"It recomputes the {count} cell sums for k = {k} named above"),
        (controls, f"`{m**5} cell sums of {n**6} cells each: {m**5} equal to the stored sums, 0 different`"),
    ]
    if pars["k5"]["k"] != 5 or (pars["k5"]["m"], pars["k5"]["n"]) != (m, n):
        fail("controls/README.md gives the last line of plain_sums.c for k = 5 and the cells of the results")
    for checker, command in commands.items():
        lines = []
        for spec in names[-3:]:
            threads = table[checker, spec, "windows"][0][0]
            lines.append(f"{command} data/specs/{spec}.txt -j {threads}")
        statements.append((readme, lines[-1] + "\n```"))
        if checker == "python":
            lines[-1] += f" --log {name}.log"
        statements.append((checkers, "\n".join(lines) + "\n```"))
    return statements


def check_lines(targets):
    """The sentence of paper/README.md on what this script prints with --check: one line for each target
    and one for README.md."""
    tables = [name for name in targets if name.endswith("_table.tex")]
    if set(targets) != {"numbers.tex", *tables}:
        fail("paper/README.md says that the targets are numbers.tex and tables")
    return (
        f"prints {NUMERALS[len(targets) + 1]} lines `agrees with the records:`, one for each file "
        f"(`paper/tex/numbers.tex`, the {NUMERALS[len(tables)]} tables and the top-level `README.md`)"
    )


def stated(records, names, agreement, costs, lean, macros):
    """Statements of the paper and of the README files that repeat the spec files or a record, as pairs
    (file, text that must occur in it; a difference in white space alone does not count)."""
    pars = {name: records[name]["par"] for name in (*names, "bhh")}
    par = pars[names[-1]]
    m, n, b = par["m"], par["n"], par["b"]
    shared = ("M", "b", "m", "n", "nu", "T")
    if any(pars[name][key] != par[key] for name in names for key in shared):
        fail("the spec files of the results do not share their parameters")
    if (pars["k5"]["hn"], pars["k5"]["hd"]) != (2, 1):
        fail("the paper states h = 2 for k = 5")
    intro = ("paper", "tex", "sec1_intro.tex")
    computation = ("paper", "tex", "sec5_computation.tex")
    remarks = ("paper", "tex", "sec6_remarks.tex")
    strip = pars["bhh"]
    if (strip["k"], strip["m"], strip["n"], strip["M"], strip["T"]) != (2, 1, 1, par["M"], par["T"]):
        fail("controls/README.md states other parameters for the strip bound")
    threshold = decimal(par["theta_n"], par["theta_d"], 4, True)
    with open(path("data", "tests", "EXPECTED.txt"), encoding="ascii") as handle:
        inputs_count = sum(1 for line in handle if line.strip())
    with open(path("paper", "figures", "fig_strip.pdf"), "rb") as handle:
        if f"/Subject (k = {par['k']}, h = {par['hn']}/{par['hd']})".encode("ascii") not in handle.read():
            fail("the figure of the strip was not drawn for the largest k (paper/figures/make_figures.py)")
    return [
        *lean_statements(lean, par),
        *controls_readme(names, agreement, costs, macros, strip),
        (
            remarks,
            "For $k=6,\\dots,9$ the strip heights of \\cref{tab:limits} are higher by $1/10$ than those of "
            "\\cref{thm:computation}",
        ),
        (remarks, "for $k=7$ and $k=9$ the next lower height gives a value larger by less than $0.0001$"),
        (
            remarks,
            "The shortest-path value reported in \\cite{DongCao2026} is $0.87426$, from a sample of "
            "$5\\cdot10^6$ blocks",
        ),
        (computation, agreement_sentence(agreement).partition(" For ")[0]),
        (
            computation,
            "Some lie above the bound of \\cref{thm:computation}, as is to be expected: the bound exceeds "
            "the value of the rule by less than one standard error.",
        ),
        *((computation, text) for text in cost_sentences(costs)),
        (computation, "\\Cref{thm:main} leaves a margin of more than $\\MainMargin$ above the bound"),
        (computation, runs_sentence()),
        (("README.md",), readme_runs_sentence()),
        (computation, earlier_sentence()),
        *plain_sentences(par, plain_record(names[-1], par)[0]),
        (computation, "on a mesh twice as fine as that of the computation"),
        (computation, "with standard errors below $10^{-9}$"),
        (computation, "The samples for the different $k$ were drawn with one seed"),
        *((("checkers", "TESTS.md"), text) for text in mutation_sentence()),
        *readme_statements(names, pars, threshold),
        (
            ("README.md",),
            f"the bound, {decimal(*records[names[-1]]['fraction'], 5, False)}…, is below the threshold "
            f"{threshold}, so",
        ),
        (computation, f"For each of the {NUMERALS[len(names)]} computations of \\cref{{thm:computation}}"),
        (intro, f"a grid of $12^5\\cdot20^6\\approx{power_of_ten(DONG_CAO_CELLS)}$ cells"),
        (intro, f"against $0.8810$ from the grid of ${power_of_ten(DONG_CAO_CELLS)}$ cells"),
        (("checkers", "TESTS.md"), f"`make_tests.py` writes {inputs_count} test inputs"),
        (intro, "starting from $\\beta<\\BoundFiveUp$ for $k=5$ and $h=2$"),
        (intro, f"${m}^5\\cdot{n}^6\\approx\\CellsFive$"),
        (
            ("paper", "tex", "abstract.tex"),
            f"$\\CellsFive$ cells then give a better bound than their ${power_of_ten(DONG_CAO_CELLS)}$ cells",
        ),
        (computation, f"We take $M={par['M']}$, so that $\\delta=1/{par['M']}$, and $m={m}$ gap cells"),
        (computation, f"gap cells with $(b_1,b_2,b_3)=({b[1]},{b[2]},{b[3]})$, that is"),
        (computation, f"together with $n={n}$ height cells, $\\nu={par['nu']}$ and $T={par['T']}$"),
        (
            ("README.md",),
            f"from the parameters in the spec file `data/specs/{names[-1]}.txt`, compares the results "
            f"with the values file `data/values/{names[-1]}.txt`, and prints\n\n```\n"
            + records[names[-1]]["text"]
            + "```\n\nThe check has succeeded if it prints these five lines and ends with status 0.",
        ),
    ]


def different_lines(current, content, most=12):
    """The lines in which a file as it stands differs from what the records give, for the message of
    --check: at most `most` of them, each cut to 150 characters."""
    if current is None:
        return ["    the file does not exist"]
    old, new = current.splitlines(), content.splitlines()
    lines = [
        f"    {tag} {line[:150]}"
        for tag, mine, other in (("as it stands:", old, set(new)), ("from the records:", new, set(old)))
        for line in mine
        if line not in other
    ]
    return lines[:most] + ([f"    ... and {len(lines) - most} more lines"] if len(lines) > most else [])


def visible(parts):
    """A file of the paper or the README without its comments, so that a sentence in a comment does
    not count as stated."""
    text = read(*parts).replace("\r\n", "\n")
    if parts[-1].endswith(".tex"):
        return re.sub(r"(?<!\\)%.*", "", text)
    return re.sub(r"<!--.*?-->", "", text, flags=re.DOTALL)


def main(argv):
    sys.stdout.reconfigure(errors="backslashreplace")  # a console may lack the letter beta
    if argv not in ([], ["--check"]):
        raise SystemExit(__doc__)
    check = argv == ["--check"]
    targets, results, records, names, agreement, costs, lean, macros = numbers()
    status = 0
    statements = stated(records, names, agreement, costs, lean, macros)
    statements.append((("paper", "README.md"), check_lines(targets)))
    for parts, text in statements:
        if " ".join(text.split()) not in " ".join(visible(parts).split()):
            print(f"MISSING in {'/'.join(parts)}: {text}")
            status = 1
    new_readme = read("README.md")
    blocks = ((BEGIN, END, results), (TIMES_BEGIN, TIMES_END, readme_times(times(), names)))
    for begin, end, content in blocks:
        if new_readme.count(begin) != 1 or new_readme.count(end) != 1:
            fail(f"README.md needs the markers {begin} and {end} once each")
        head, rest = new_readme.split(begin)
        new_readme = head + begin + "\n" + content + end + rest.split(end)[1]
    files = [(("paper", "tex", name), content) for name, content in targets.items()]
    files.append((("README.md",), new_readme))
    for parts, content in files:
        name = "/".join(parts)
        current = read(*parts) if os.path.exists(path(*parts)) else None
        if check:
            if current != content:
                print(f"DIFFERS from the records: {name}")
                for line in different_lines(current, content):
                    print(line)
                status = 1
            else:
                print(f"agrees with the records: {name}")
        elif current != content:
            with open(path(*parts), "w", encoding="utf-8", newline="") as handle:
                handle.write(content)
            print(f"wrote {name}")
        else:
            print(f"unchanged: {name}")
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
