#!/bin/sh
# Builds everything and runs the executable on k5, k6, k7, and prints a log of the form of
# runs/final_build3.out.
#
#   sh runs/build_all.sh > runs/build_all.out 2>&1          everything (see README.md for the times)
#   sh runs/build_all.sh quick                              the libraries, the small cases and k = 5 only
#
# Needed: Lean 4.31.0 with lake on the PATH (elan reads the file lean-toolchain).  Nothing is
# downloaded.  The spec files are looked for in ../data/specs; set SPECS to use another place.
# The evaluations by TSPShared use the thread pool of lean, whose size is the number in the line
# weakLeanArgs of lakefile.toml; those by the older routine use 4 worker threads (the numeral in
# their proofs); the executable is given THREADS (default 4).  An interrupted run can be started
# again: lake keeps what is built, and the executable continues from its lists of cell sums
# runs/new_*.sums.  (python runs/run_pieces.py TAG builds the pieces of one evaluation with a record
# of each piece; this script uses lake alone.)
cd "$(dirname "$0")/.." || exit 1
export LEAN_NUM_THREADS=1
SPECS=${SPECS:-../data/specs}
THREADS=${THREADS:-4}
MODE=${1:-all}

echo "== sequence ($MODE) started $(date)"
sha256sum TSPBound/Spec.lean

run() { echo "== $1 start $(date)"; lake build "$1"; echo "== $1 exit $? end $(date)"; }
exe() {
  echo "== exe $1 -j $THREADS --shared start $(date)"
  lake exe tspcheck "$SPECS/$1.txt" -j "$THREADS" --shared --log "runs/new_$1.sums" > "runs/new_$1.out"
  echo "== exe $1 exit $? end $(date)"
  cat "runs/new_$1.out"
}

run TSPBound
run TSPShared
run tspcheck
run Results.Params
run Results.Exact
run Results.Small
run Results.K5S
if [ "$MODE" = quick ]; then
  exe k5
  sha256sum TSPBound/Spec.lean
  echo "== quick sequence done $(date)"
  exit 0
fi
run Results.K6S
run Results.K7S
run Results.K8S
exe k5
exe k6
exe k7
run Results.K9S
# the older routine
run Results.K5
run Results.K6
run Results.K7
for i in 0 1 2 3; do for j in 0 1 2 3; do
  run Results.K8.A$i$j
done; done
run Results.K8
run Results.K5P
run Results
echo "== Results.Axioms start $(date)"
lake build Results.Axioms > runs/new_axioms.txt 2>&1
echo "== Results.Axioms exit $? end $(date)"
cat runs/new_axioms.txt
sha256sum TSPBound/Spec.lean
echo "== all done $(date)"
