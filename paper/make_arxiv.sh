#!/usr/bin/env bash
# Makes paper/build/arxiv.tar.gz, the source of the paper as arXiv takes it: all files in one folder, with
# the bibliography as main.bbl.  The bundle is then compiled from scratch in a second folder, as a test.
#
# usage:  bash paper/make_arxiv.sh        (run bash paper/build.sh first; needs pdflatex)
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
out="$here/build/arxiv"
test_dir="$here/build/arxiv_test"
rm -rf "$out" "$test_dir"
mkdir -p "$out" "$test_dir"

cp "$here"/tex/*.tex "$out"/
cp "$here"/figures/*.pdf "$out"/
cp "$here/build/main.bbl" "$out"/
# The figures lie next to main.tex in the bundle.
grep -v '^\\graphicspath' "$here/tex/main.tex" >"$out/main.tex"

if tar --version 2>/dev/null | grep -q "GNU tar"; then # no name of a user or group in the bundle
    tar --owner=0 --group=0 --numeric-owner -czf "$here/build/arxiv.tar.gz" -C "$out" .
else # bsdtar
    tar --uid 0 --gid 0 --uname '' --gname '' -czf "$here/build/arxiv.tar.gz" -C "$out" .
fi

tar -xzf "$here/build/arxiv.tar.gz" -C "$test_dir"
cd "$test_dir"
for _ in 1 2 3; do
    pdflatex -interaction=nonstopmode -halt-on-error main.tex >pdflatex.out || {
        tail -n 30 pdflatex.out
        exit 1
    }
done
echo "files in the bundle:   $(tar -tzf "$here/build/arxiv.tar.gz" | grep -c -v '/$')"
echo "undefined references:  $(grep -c 'undefined' main.log || true)"
echo "pages:                 $(tr -d '\r\n' <main.log | grep -o '([0-9]* pages, [0-9]* bytes)' | grep -o '^([0-9]*' | tr -d '(')"
