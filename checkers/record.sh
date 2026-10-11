#!/usr/bin/env bash
# Runs a checker on a spec file and records the run in runs/.
#
# usage:  bash checkers/record.sh CHECKER PLATFORM THREADS NAME COMMAND...
#   e.g.  bash checkers/record.sh c linux 8 k7 ./cchk data/specs/k7.txt -j 8
#
# COMMAND is run from the top folder of the repository.  The lines it prints on standard output are
# stored as runs/CHECKER_NAME.txt, with LF line ends whatever the platform.  If that file exists already,
# the new output must equal it byte for byte; otherwise the script stops with status 1 and keeps the new
# output as runs/CHECKER_NAME.txt.new.  A row
#     CHECKER NAME PLATFORM THREADS SECONDS SHA256
# is appended to runs/times.txt.  All three checkers print the same lines for the same spec file, so the
# SHA-256 of a spec file is the same in every row.
#
# Needs GNU coreutils (date with %N, sha256sum); under macOS they come with the package coreutils.
set -eu

if [ $# -lt 5 ]; then
    sed -n '2,15p' "$0" >&2
    exit 2
fi
checker=$1 platform=$2 threads=$3 name=$4
shift 4
cd "$(dirname "$0")/.."
mkdir -p runs
record=runs/${checker}_${name}.txt

start=$(date +%s.%N)
status=0
"$@" >"$record.raw" || status=$?
finish=$(date +%s.%N)
tr -d '\r' <"$record.raw" >"$record.new"
rm "$record.raw"
if [ "$status" -ne 0 ]; then
    echo "record.sh: the command ended with status $status; output kept in $record.new" >&2
    exit 1
fi
if [ -e "$record" ] && ! cmp -s "$record" "$record.new"; then
    echo "record.sh: the output differs from $record; kept as $record.new" >&2
    exit 1
fi
mv "$record.new" "$record"
elapsed=$(awk -v a="$start" -v b="$finish" 'BEGIN { printf "%.1f", b - a }')
digest=$(sha256sum "$record" | cut -d' ' -f1)
[ -e runs/times.txt ] || echo "# checker spec platform threads seconds sha256-of-the-printed-lines" >runs/times.txt
echo "$checker $name $platform $threads $elapsed $digest" >>runs/times.txt
echo "recorded $record ($elapsed s)"
