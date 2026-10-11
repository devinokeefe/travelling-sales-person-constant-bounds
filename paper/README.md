# The paper

`main.pdf` is the paper, and `tex/` holds its LaTeX source. The commands are run from the top folder.

## Building

`bash paper/build.sh` builds `paper/main.pdf` and writes over the stored file; the new file differs from
it at least in its date. It needs pdflatex and bibtex with the class amsart and the packages named at the
head of `paper/tex/main.tex`, all of which TeX Live and MiKTeX provide.

`python paper/figures/make_figures.py` draws the figure again and writes over the stored one (needs
numpy, numba and matplotlib; about a minute).

`bash paper/make_arxiv.sh` makes the source bundle for arXiv in `paper/build/`, from files that
`paper/build.sh` leaves there, so it must be run after that script.

## The numbers of the paper

Most numbers of the paper that come from a computation are LaTeX macros or table entries, which
`python tools/paper_numbers.py` derives from the records in `runs/`. It writes `paper/tex/numbers.tex`,
the tables `paper/tex/*_table.tex` and, in the top-level `README.md`, the table of results and the
paragraph on running times. With `--check` it compares these files as they stand with what the records
give, and writes nothing. It needs no packages.

Some numbers are written out in the text. For these the script checks a list of sentences that repeat
parameters or values of the records (its function `stated`): sentences of the paper's source, of the
top-level `README.md`, of `checkers/README.md`, `checkers/TESTS.md` and `controls/README.md`, and of
this file. It checks nothing else of the text. It compares the records of the Lean development with the
Lean sources and with the records of the checkers. It cannot tell whether a record is the output of the
run that it names, and it does not compare `paper/main.pdf` with the source.

With `--check` it has succeeded if it prints five lines `agrees with the records:`, one for each file
(`paper/tex/numbers.tex`, the three tables and the top-level `README.md`), and ends with status 0. A
line that begins with `MISSING`, `DIFFERS` or `paper_numbers:` names what does not agree.
