#!/usr/bin/env bash
# Build paper/main.pdf from paper/tex/.  Needs pdflatex and bibtex on the PATH.
# usage:  bash paper/build.sh
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
build="$here/build"
mkdir -p "$build"
cd "$here/tex"
run() {
    pdflatex -interaction=nonstopmode -halt-on-error -output-directory="$build" main.tex >"$build/pdflatex.out" || {
        tail -n 30 "$build/pdflatex.out"
        exit 1
    }
}
run
(cd "$build" && BIBINPUTS="$here/tex" bibtex main >bibtex.out) || { # the style is that of the system
    cat "$build/bibtex.out"
    exit 1
}
run
run
for _ in 1 2 3; do # until the cross-references have settled
    grep -q "Rerun to get" "$build/main.log" || break
    run
done
if grep -q "Rerun to get" "$build/main.log"; then
    echo "build.sh: the cross-references have not settled (see $build/main.log)" >&2
    exit 1
fi
cp "$build/main.pdf" "$here/main.pdf"
echo "overfull boxes:       $(grep -c '^Overfull' "$build/main.log" || true)"
echo "undefined references: $(grep -c 'undefined' "$build/main.log" || true)"
echo "pages:                $(tr -d '\r\n' <"$build/main.log" | grep -o '([0-9]* pages, [0-9]* bytes)' | grep -o '^([0-9]*' | tr -d '(')"
