#!/usr/bin/env python3
"""Mutation tests for the C and the Rust checker: wrong versions of each must be detected.

The mutants are listed in checkers/mutants_c.json and checkers/rust/mutants.json.  Each is one
replacement of text in a source file: a rounding goes the wrong way, a lower bound is used where an
upper bound is needed, a term of the bound is dropped, or a test of the input is weakened.  For every
mutant this script builds the program in a temporary folder and runs it on data/specs/tiny.txt,
rounding.txt, bhh.txt, k4.txt and k5.txt and on the test inputs of data/tests/ (make_tests.py).  A
mutant is detected if an exit status is not the expected one, or if the lines printed for an accepted
input are not those of the unmodified program.  A mutant of the Rust program that the inputs do not
detect is also given to the unit tests of the crate (cargo test); the C program has no unit tests.  The
unmodified program is built and run first and must pass.

A few mutants cannot be detected by these inputs, for instance a removed overflow check, which no input
that all checkers must treat alike can reach.  They stay in the lists with an entry "undetected" that
gives the reason ("undetected_on" limits it to one platform, posix or nt).  The script prints one line
for each mutant and ends with status 0 if every mutant is detected except those, and those are not.
Before the first mutant is built, the text of every mutant is looked up in the unmodified source, where
it must occur exactly once.

usage:  mutation_test_compiled.py c       (needs a C compiler; CC names it, default gcc)
        mutation_test_compiled.py rust    (needs cargo)
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")
WORKERS = 4  # inputs run at the same time
SUFFIX = ".exe" if os.name == "nt" else ""


def inputs():
    """The spec files to run, with the exit status that each must give."""
    with open(os.path.join(DATA, "tests", "EXPECTED.txt"), encoding="ascii") as handle:
        expected = [line.split() for line in handle if line.strip()]
    names = ("tiny", "rounding", "bhh", "k4", "k5")
    cases = [(os.path.join(DATA, "specs", f"{name}.txt"), 0) for name in names]
    return cases + [(os.path.join(DATA, "tests", f"{name}.txt"), int(status)) for name, status in expected]


def prepare(language, folder):
    """Copy the sources into the folder; return the mutants, the source folder and the program to be built."""
    if language == "c":
        shutil.copy(os.path.join(HERE, "cchk.c"), folder)
        with open(os.path.join(HERE, "mutants_c.json"), encoding="utf-8") as handle:
            mutants = json.load(handle)
        for mutant in mutants:
            mutant.setdefault("file", "cchk.c")
        return mutants, folder, os.path.join(folder, "cchk" + SUFFIX)
    crate = os.path.join(HERE, "rust")
    root = os.path.join(folder, "checkers", "rust")  # the unit tests read ../../data/ from here
    shutil.copytree(crate, root, ignore=shutil.ignore_patterns("target", "mutants.json"))
    for part in ("specs", "values"):
        os.makedirs(os.path.join(folder, "data", part))
        shutil.copy(os.path.join(DATA, part, "tiny.txt"), os.path.join(folder, "data", part))
    with open(os.path.join(crate, "mutants.json"), encoding="utf-8") as handle:
        mutants = json.load(handle)
    return mutants, root, os.path.join(root, "target", "release", "rchk" + SUFFIX)


def unit_tests_fail(language, folder):
    """Whether the unit tests of the program in the folder fail (the C program has none)."""
    if language == "c":
        return False
    command = ["cargo", "test", "--release", "--quiet", "--locked", "--offline"]
    return subprocess.run(command, cwd=folder, capture_output=True, check=False).returncode != 0


def build(language, folder):
    """Build the program in the folder; return whether the build succeeded."""
    if language == "c":
        command = [os.environ.get("CC", "gcc"), "-O2", "cchk.c", "-o", "cchk" + SUFFIX]
    else:
        command = ["cargo", "build", "--release", "--quiet", "--locked", "--offline"]
    try:
        return subprocess.run(command, cwd=folder, capture_output=True, check=False).returncode == 0
    except FileNotFoundError:
        raise SystemExit(f"mutation_test_compiled: the program {command[0]} was not found") from None


def read_source(root, mutant):
    """The path and the text of the source file that a mutant changes."""
    path = os.path.join(root, *mutant["file"].split("/"))
    with open(path, encoding="utf-8", newline="") as handle:
        return path, handle.read()


def run_all(program, cases):
    """For every case the exit status and, if it is 0, the lines printed (line ends as LF)."""

    def run(case):
        try:
            done = subprocess.run([program, case[0]], capture_output=True, check=False, timeout=600)
        except subprocess.TimeoutExpired:
            return -1, b""  # a mutant that does not end is detected
        return done.returncode, done.stdout.replace(b"\r\n", b"\n") if done.returncode == 0 else b""

    with ThreadPoolExecutor(max_workers=WORKERS) as pool:
        return list(pool.map(run, cases))


def main(argv):
    if len(argv) != 1 or argv[0] not in ("c", "rust"):
        raise SystemExit(__doc__)
    language = argv[0]
    cases = inputs()
    undetected = unexpected = 0
    with tempfile.TemporaryDirectory() as folder:
        mutants, root, program = prepare(language, folder)
        for number, mutant in enumerate(mutants, start=1):
            found = read_source(root, mutant)[1].count(mutant["old"])
            if found != 1:
                raise SystemExit(f"mutation_test_compiled: mutant {number}: the text occurs {found} times")
        if not build(language, root):
            raise SystemExit("mutation_test_compiled: the unmodified program does not build")
        reference = run_all(program, cases)
        if [status for status, _ in reference] != [status for _, status in cases]:
            raise SystemExit("mutation_test_compiled: the unmodified program fails a test")
        if unit_tests_fail(language, root):
            raise SystemExit("mutation_test_compiled: the unmodified program fails its unit tests")
        print(f"unmodified program: passes {len(cases)} tests", flush=True)
        for number, mutant in enumerate(mutants, start=1):
            path, source = read_source(root, mutant)
            with open(path, "w", encoding="utf-8", newline="") as handle:
                handle.write(source.replace(mutant["old"], mutant["new"]))
            if not build(language, root):
                verdict = "does not build"
            elif run_all(program, cases) != reference:
                verdict = "detected"
            elif unit_tests_fail(language, root):
                verdict = "detected by the unit tests only"
            else:
                verdict = "NOT DETECTED"
            undetected += not verdict.startswith("detected")
            excused = "undetected" in mutant and mutant.get("undetected_on", os.name) == os.name
            if excused and verdict == "NOT DETECTED":
                verdict = f"not detected, as stated in the list ({mutant['undetected']})"
            elif excused or not verdict.startswith("detected"):
                verdict += "  <-- NOT AS STATED IN THE LIST"
                unexpected += 1
            print(f"{number:2d}  {mutant['description']}: {verdict}", flush=True)
            with open(path, "w", encoding="utf-8", newline="") as handle:
                handle.write(source)
    print(f"{len(mutants) - undetected} of {len(mutants)} mutants detected")
    return 1 if unexpected else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
