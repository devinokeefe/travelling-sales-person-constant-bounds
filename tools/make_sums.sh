#!/usr/bin/env bash
# Writes SHA256SUMS.txt: the SHA-256 of every file of the repository except itself, build products and
# what interrupted runs leave behind (the same files that .gitignore names; a change there must be
# repeated here).
#
# usage:  bash tools/make_sums.sh        (from any folder; needs sha256sum, as in GNU coreutils)
#
# `sha256sum -c SHA256SUMS.txt` in the top folder then checks the files.  Every line is written as
# "HASH  PATH", also where sha256sum marks binary mode with "HASH *PATH" (as it does under Git Bash), so
# that the list is the same on every platform.
set -euo pipefail

cd "$(dirname "$0")/.."
find . -type f \
    ! -path './.git/*' ! -path './SHA256SUMS.txt' ! -path './SHA256SUMS.txt.part' \
    ! -path './checkers/rust/target/*' ! -path './paper/build/*' ! -path '*/__pycache__/*' \
    ! -path './.ruff_cache/*' ! -path './lean/.lake/*' ! -path './cchk' ! -path './cchk.exe' \
    ! -path './plain_sums' ! -path './plain_sums.exe' ! -path './controls/plain_sums' \
    ! -path './controls/plain_sums.exe' ! -path './lean/runs/new_*' \
    ! -path './lean/runs/build_all.out' ! -path './lean/runs/*_pieces/*' \
    ! -path './lean/runs/*_stale/*' ! -path './lean/runs/*.pid' ! -path './lean/runs/*_STOP' \
    ! -path './lean/runs/*_threads.txt' ! -path '*/.venv/*' ! -path '*/venv/*' \
    ! -path '*/.vscode/*' ! -name '.DS_Store' \
    ! -name '*.obj' ! -name '*.log' ! -name '*.part' ! -name '*.new' ! -name '*.raw' |
    LC_ALL=C sort | cut -c3- | tr '\n' '\0' | xargs -0 sha256sum |
    sed 's/^\([0-9a-f]\{64\}\) \*/\1  /' >SHA256SUMS.txt.part
mv SHA256SUMS.txt.part SHA256SUMS.txt
echo "wrote SHA256SUMS.txt for $(wc -l <SHA256SUMS.txt) files"
