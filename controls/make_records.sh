#!/usr/bin/env bash
# Makes the records of the controls in runs/ (Section 5.3 and Table 6.1 of the paper, and README.md here).
#
# usage:  bash controls/make_records.sh NAME...        (from any folder)
#
# NAME is one or more of
#   strip      the strip constant by numerical integration           -> runs/strip_integral.txt
#   bracket    the two-sided bracket for every k                      -> runs/bracket_k5.txt, ...
#   bracketK   the bracket for one k: bracket5, ..., bracket9
#   segments   every table entry against a numerical integral, for every k
#                                                                     -> runs/segments_k5.txt, ...
#   segmentsK  the same for one k: segments5, ..., segments9
#   blocks     simulated blocks for every k                           -> runs/blocks_k5.txt, ...
#   blocksK    simulated blocks for one k: blocks5, ..., blocks9
#   second     a second sample of simulated blocks, with another seed, for every k above 7
#                                                                     -> runs/blocks_k8_second.txt, ...
#   secondK    the second sample for one k: second8, second9
#   tour       the tour of Theorem 2.2 on simulated points, for the largest k, with 2000 and 8000 strips
#                                                                     -> runs/tour_k9_2000.txt, runs/tour_k9_8000.txt
#   limits     shortest paths for k = 5, ..., 10                      -> runs/limits.txt
#   dongcao    the setting of Dong and Cao for k = 5                  -> runs/dongcao_setting.txt
#   plain      cell sums of a sample of gap tuples for the largest k, from the definition
#                                                                     -> runs/plain_k9.txt
#
# "Every k" is every k from 5 to 9 for which data/specs/ holds a spec file, and "the largest k" is the
# last of them.  The bracket covers every entry of the table; up to k = 7 it also sums both brackets over
# all cells (for larger k these sums would take days, and the simulated blocks give them on a sample).
#
# The script writes over the records that are in runs/ without comparing: most records contain their
# running time, so a new record differs from the stored one in that line even if every number agrees.
# A record is first written to runs/FILE.part and moved into place when its control has ended with
# status 0; if a control fails, the script stops with that status and the .part file holds what it printed.
#
# PYTHON names the interpreter (default: python); it needs numpy, numba, scipy and mpmath.  The programs
# use as many threads as NUMBA_NUM_THREADS allows.  The seeds are fixed, so the numbers are reproduced
# exactly with the same versions of numpy and numba; the first line of a record gives the versions of
# python, numpy and numba that were used.
# The bracket for k = 7 keeps a log, runs/bracket_k7.log, while it runs.  An interrupted run is continued
# by repeating the command and takes the sums in the log as they stand; delete the log first if the record
# is to come from one run.  A run that ends removes the log.
# BLOCKS is the number of simulated blocks of each record of "blocks" and "second", SAMPLES that of each
# line of "limits"; with a tenth of them these records are ten times faster and their standard errors
# three times larger.  The other records do not depend on the two numbers.
#
# Times on our computer (a desktop computer that was running other jobs; 2 to 8 threads): about an
# hour and a quarter for "blocks", two and a half hours for "second", two hours for "limits", forty
# minutes for the bracket of k = 7, ten minutes each for "strip" and "tour", two minutes for the
# segments of each k, and less than a minute for each of the rest.
#
# The record "plain" needs no Python but a C compiler, named by CC (default: gcc); its first line names
# the compiler.  PLAIN_OPENMP is the option that turns OpenMP on (default: -fopenmp; set it to the empty
# string for a compiler without OpenMP, and the program then uses one thread).  PLAIN_COUNT gap tuples are
# drawn from PLAIN_SEED, and PLAIN_THREADS threads are used; a gap tuple takes some minutes for k = 9.
set -euo pipefail
trap 'status=$?; [ "$status" -eq 0 ] || echo "make_records.sh: status $status (see runs/*.part)" >&2' EXIT

PYTHON=${PYTHON:-python}
BLOCKS=${BLOCKS:-400000000}  # simulated blocks for the rule
SAMPLES=${SAMPLES:-40000000} # simulated blocks for each line of runs/limits.txt
FULL_BRACKET=7               # the largest k for which the brackets are summed over all cells
SECOND_SEED=20261010         # the seed of the second sample of blocks (the first has the default seed)
PLAIN_COUNT=${PLAIN_COUNT:-10}
PLAIN_SEED=${PLAIN_SEED:-20261009}
PLAIN_THREADS=${PLAIN_THREADS:-4}
PLAIN_OPENMP=${PLAIN_OPENMP--fopenmp}
if [ "$#" -eq 0 ]; then
    echo "usage: bash controls/make_records.sh NAME...   (the names are listed at the top of the script)" >&2
    trap - EXIT
    exit 2
fi
cd "$(dirname "$0")/.."
mkdir -p runs

results=()
for k in 5 6 7 8 9; do
    if [ -e "data/specs/k$k.txt" ]; then
        results+=("$k")
        largest=$k
    fi
done

header() {
    "$PYTHON" -B -c "import sys, numpy, numba, scipy, mpmath; print('# python', sys.version.split()[0], 'numpy', numpy.__version__, 'numba', numba.__version__)" || {
        echo "make_records.sh: '$PYTHON' must be a Python with numpy, numba, scipy and mpmath (set PYTHON to name it)" >&2
        return 3
    }
}

record() { # record FILE COMMAND...: run the command and write its output, with the command, to runs/FILE
    local file=runs/$1
    shift
    {
        header
        echo "# $*"
        "$PYTHON" -B "$@"
    } | tr -d '\r' >"$file.part"
    mv "$file.part" "$file"
    echo "wrote $file"
}

bracket() { # bracket K
    if [ "$1" -lt "$FULL_BRACKET" ]; then
        record "bracket_k$1.txt" controls/bracket.py "data/specs/k$1.txt" 2 --rule
    elif [ "$1" -eq "$FULL_BRACKET" ]; then
        record "bracket_k$1.txt" controls/bracket.py "data/specs/k$1.txt" 2 --rule --log "runs/bracket_k$1.log"
        rm "runs/bracket_k$1.log"
    else
        record "bracket_k$1.txt" controls/bracket.py "data/specs/k$1.txt" 2
    fi
}

segments() { # segments K
    record "segments_k$1.txt" controls/segment_integral.py "data/specs/k$1.txt"
}

blocks() { # blocks K
    record "blocks_k$1.txt" controls/simulate.py "data/specs/k$1.txt" blocks "$BLOCKS"
}

second() { # second K
    record "blocks_k${1}_second.txt" controls/simulate.py "data/specs/k$1.txt" blocks "$BLOCKS" "$SECOND_SEED"
}

for name in "$@"; do
    case $name in
    strip)
        record strip_integral.txt controls/strip_integral.py
        ;;
    bracket)
        for k in "${results[@]}"; do bracket "$k"; done
        ;;
    bracket[5-9])
        bracket "${name#bracket}"
        ;;
    segments)
        for k in "${results[@]}"; do segments "$k"; done
        ;;
    segments[5-9])
        segments "${name#segments}"
        ;;
    blocks)
        for k in "${results[@]}"; do blocks "$k"; done
        ;;
    blocks[5-9])
        blocks "${name#blocks}"
        ;;
    second)
        for k in "${results[@]}"; do
            if [ "$k" -gt "$FULL_BRACKET" ]; then second "$k"; fi
        done
        ;;
    second[8-9])
        second "${name#second}"
        ;;
    tour)
        for strips in 2000 8000; do
            record "tour_k${largest}_$strips.txt" controls/simulate.py "data/specs/k$largest.txt" tour "$strips"
        done
        ;;
    limits)
        {
            header
            echo "# controls/simulate.py shortest K H $SAMPLES, for the values of K and H below"
            while read -r k heights; do
                for h in $heights; do
                    "$PYTHON" -B controls/simulate.py shortest "$k" "$h" "$SAMPLES"
                done
            done <<'EOF'
5 19/10 2 21/10
6 19/10 2 21/10 22/10
7 2 21/10 22/10 23/10
8 21/10 22/10 23/10
9 21/10 22/10 23/10 24/10
10 22/10 23/10 24/10
EOF
        } | tr -d '\r' >runs/limits.txt.part
        mv runs/limits.txt.part runs/limits.txt
        echo "wrote runs/limits.txt"
        ;;
    dongcao)
        record dongcao_setting.txt controls/dongcao_setting.py
        ;;
    plain)
        cc=${CC:-gcc}
        # shellcheck disable=SC2086  # PLAIN_OPENMP may be empty
        "$cc" -std=c11 -O2 $PLAIN_OPENMP controls/plain_sums.c -o controls/plain_sums
        version=$("$cc" --version 2>/dev/null | head -n 1) || true
        {
            echo "# ${version:-$cc (a compiler that prints no version)}"
            echo "# controls/plain_sums data/values/k$largest.txt $PLAIN_COUNT $PLAIN_SEED -j $PLAIN_THREADS"
            controls/plain_sums "data/values/k$largest.txt" "$PLAIN_COUNT" "$PLAIN_SEED" -j "$PLAIN_THREADS"
        } | tr -d '\r' >"runs/plain_k$largest.txt.part"
        mv "runs/plain_k$largest.txt.part" "runs/plain_k$largest.txt"
        rm controls/plain_sums
        echo "wrote runs/plain_k$largest.txt"
        ;;
    *)
        echo "unknown record: $name (the names are listed at the top of the script)" >&2
        trap - EXIT
        exit 2
        ;;
    esac
done
