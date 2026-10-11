# Records of the runs

This folder holds the records: what the programs printed and, for the checkers, how long each run took.
The table says which record belongs to which claim.

| Claim, and where it is made | Record |
|---|---|
| Theorem 5.1 of the paper, the totals | `python_k5.txt`, `c_k5.txt`, `rust_k5.txt`, and likewise for `k6` to `k9` |
| Section 5.2, repeated runs; the top-level `README.md`, running times | `times.txt` |
| Section 5.2, the earlier versions of the checkers | `earlier/` (`earlier/README.md`) |
| The top-level `README.md` and `controls/README.md` only, cell sums for k = 9 recomputed by a separate program | `plain_k9.txt` |
| Section 5.2, the check in Lean | not here but in `lean/runs/`: `k5s_done.txt` to `k9s_done.txt` with the outputs `…_run.out` (for k = 5 in three parts, `k5s_run1.out` to `k5s_run3.out`), `axioms.txt`, `sources_at_end.txt`; `final_build3.out` for the older routine (`lean/README.md` describes them all) |
| Section 5.3, the segments by numerical integration | `segments_k5.txt` to `segments_k9.txt` |
| Section 5.3 and Table 5.1, the bracket | `bracket_k5.txt` to `bracket_k9.txt`; for k = 8 and 9 the bracket of the rule also uses `blocks_k8.txt`, `blocks_k9.txt` and the totals (`controls/README.md`) |
| Section 5.3 and Table 5.1, simulated blocks | `blocks_k5.txt` to `blocks_k9.txt` |
| `controls/README.md` only, the second sample of simulated blocks | `blocks_k8_second.txt`, `blocks_k9_second.txt` |
| `controls/README.md` only, the strip bound | `python_bhh.txt`, `c_bhh.txt`, `rust_bhh.txt`, `strip_integral.txt` |
| `controls/README.md` only, the tour of the proof on simulated points | `tour_k9_2000.txt`, `tour_k9_8000.txt` |
| Section 6.1 and `controls/README.md`, the cells of Dong and Cao | `dongcao_setting.txt` |
| Table 6.1 and `controls/README.md`, shortest paths | `limits.txt` |
| The small spec files (not in the paper) | `python_NAME.txt`, `c_NAME.txt`, `rust_NAME.txt` for `tiny`, `rounding`, `k4` |
| Tests and mutation tests (`checkers/TESTS.md`) | `tests.txt`, `mutation_test.txt` |

Each record of a checker (`python_*.txt`, `c_*.txt`, `rust_*.txt`) holds the five lines that the checker
printed on standard output, with LF line ends. `times.txt` has one line for each run of a checker that
was made with `checkers/record.sh`; its first line names the columns, and the SHA-256 is that of the
five lines. The times were measured on a desktop computer that was running other jobs.

`python tools/paper_numbers.py --check` compares the numbers of the paper and of the documents with
these records (`paper/README.md`).
