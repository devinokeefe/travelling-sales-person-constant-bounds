/-
The routine that evaluates together the gap tuples that differ only in the first and the last gap
("shared paths" in full), with its proofs.  A library of its own, beside `TSPBound`, so that
`TSPBound` and everything that was built from it stay exactly as they were.
-/
import TSPShared.Impl
import TSPShared.Correct
import TSPShared.Theorems
