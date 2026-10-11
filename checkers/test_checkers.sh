#!/usr/bin/env bash
# Runs the checkers on the small spec files and on the test inputs of data/tests/, and compares their
# exit statuses and the lines they print.
#
# usage:  bash checkers/test_checkers.sh        (from any folder; run checkers/make_tests.py first)
#
# The Python checker is always tested; PYTHON names the interpreter (default: python).  The C checker is
# tested if ./cchk or ./cchk.exe exists in the top folder (the first of the two that can be run), the
# Rust checker if it has been built in checkers/rust/target/release/.  CCHK and RCHK name other programs
# to use instead, or are set to "none" to leave a checker out.  The first line printed names the
# programs that are tested.  For every input
#   - the exit status must be the expected one: 0 accepted, 1 rejected, 2 malformed;
#   - with status 0 the checkers must print the same five lines, the last one being ACCEPTED;
#   - with status 1 the last line printed must begin with "REJECTED:";
#   - with status 2 nothing may be printed on standard output.
# Line ends are compared as LF, whatever the platform.  The script ends with status 0 if every test passes.
# With JOBS=N in the environment every checker is called with "-j N"; the results must be the same.
set -u

PYTHON=${PYTHON:-python}
cd "$(dirname "$0")/.." || exit 2
if ! command -v "$PYTHON" >/dev/null 2>&1; then
    echo "test_checkers: $PYTHON was not found; set PYTHON to the name of the interpreter" >&2
    exit 2
fi

checkers=(python)
c_checker=${CCHK:-}
if [ -z "$c_checker" ]; then
    for candidate in ./cchk ./cchk.exe; do
        if [ -x "$candidate" ]; then
            c_checker=$candidate
            break
        fi
    done
fi
[ "$c_checker" = none ] && c_checker=
[ -n "$c_checker" ] && checkers+=(c)
rust_checker=${RCHK:-}
if [ -z "$rust_checker" ]; then
    for candidate in checkers/rust/target/release/rchk checkers/rust/target/release/rchk.exe; do
        if [ -x "$candidate" ]; then
            rust_checker=$candidate
            break
        fi
    done
fi
[ "$rust_checker" = none ] && rust_checker=
[ -n "$rust_checker" ] && checkers+=(rust)

if [ ! -e data/tests/EXPECTED.txt ]; then
    echo "test_checkers: data/tests/ is missing; run checkers/make_tests.py first" >&2
    exit 2
fi

jobs=()
[ -n "${JOBS:-}" ] && jobs=(-j "$JOBS")

run_checker() { # run_checker CHECKER SPEC: the lines printed on standard output; returns the exit status
    # The standard input is closed off: a program that read it would swallow the list of inputs below.
    case $1 in
    python) "$PYTHON" -B checkers/check_bound.py "$2" ${jobs[@]+"${jobs[@]}"} 2>/dev/null </dev/null | tr -d '\r' ;;
    c) "$c_checker" "$2" ${jobs[@]+"${jobs[@]}"} 2>/dev/null </dev/null | tr -d '\r' ;;
    rust) "$rust_checker" "$2" ${jobs[@]+"${jobs[@]}"} 2>/dev/null </dev/null | tr -d '\r' ;;
    esac
    return "${PIPESTATUS[0]}"
}

tests=0
failures=0
fail() {
    echo "FAILED  $*"
    failures=$((failures + 1))
}

check() { # check SPEC EXPECTED-STATUS
    local spec=$1 expected=$2 checker output status last reference=
    for checker in "${checkers[@]}"; do
        tests=$((tests + 1))
        output=$(run_checker "$checker" "$spec")
        status=$?
        last=${output##*$'\n'}
        if [ "$status" -ne "$expected" ]; then
            fail "$checker $spec: status $status, expected $expected"
        elif [ "$expected" -eq 0 ] && [ "$last" != ACCEPTED ]; then
            fail "$checker $spec: the last line is not ACCEPTED"
        elif [ "$expected" -eq 0 ] && [ "$(printf '%s\n' "$output" | wc -l)" -ne 5 ]; then
            fail "$checker $spec: not five lines"
        elif [ "$expected" -eq 1 ] && [ "${last#REJECTED:}" = "$last" ]; then
            fail "$checker $spec: the last line does not begin with REJECTED:"
        elif [ "$expected" -eq 2 ] && [ -n "$output" ]; then
            fail "$checker $spec: output on standard output with status 2"
        fi
        if [ "$expected" -eq 0 ]; then
            if [ "$checker" = "${checkers[0]}" ]; then
                reference=$output
            elif [ "$output" != "$reference" ]; then
                fail "$checker $spec: the lines differ from those of ${checkers[0]}"
            fi
        fi
    done
}

echo "checkers: python ($PYTHON)${c_checker:+, c ($c_checker)}${rust_checker:+, rust ($rust_checker)}${JOBS:+; each with -j $JOBS}"
for name in tiny rounding bhh k4; do
    check "data/specs/$name.txt" 0
done
while read -r name expected; do
    case $expected in
    0 | 1 | 2) check "data/tests/$name.txt" "$expected" ;;
    *)
        tests=$((tests + 1))
        fail "data/tests/EXPECTED.txt: the line of '$name' does not end with a status 0, 1 or 2"
        ;;
    esac
done <data/tests/EXPECTED.txt

echo "$((tests - failures)) of $tests tests passed"
[ "$failures" -eq 0 ] || echo "where a checker failed on an input, run it on that file by hand: the reason is on its standard error"
[ "$failures" -eq 0 ]
