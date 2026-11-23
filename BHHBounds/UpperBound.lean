import BHHBounds.Upper.ToBHHBase
import BHHBounds.Upper.Cert4

/-!
# End-to-End Formal Upper Bound for the Planar Euclidean TSP (BHH) Constant

Proves unconditionally, with zero external hypotheses beyond `IsBHHConstant β`:
```
  β ≤ (8549326 : ℝ) / 10 ^ 7
```
(i.e. `β ≤ 0.8549326`), via a bandwidth-4 concave dynamic-programming strip automaton,
rational exponential-bin cost verification, Poisson renewal and superposition coupling,
serpentine tour stitching, and dominated convergence.
-/

namespace BHHBounds

open BHHBounds.Upper

/-- **Headline Upper Bound:** Every Beardwood–Halton–Hammersley constant `β`
(`IsBHHConstant β`) satisfies `β ≤ 8549326 / 10^7 = 0.8549326`, unconditionally. -/
theorem bhh_upper_bound (β : ℝ) (hβ : IsBHHConstant β) :
    β ≤ (8549326 : ℝ) / 10 ^ 7 :=
  bhh_upper_of_dp
    (fun u z => (dpPotential4[encUZ u z]! : ℝ) / (costScale : ℝ))
    ((8549326 : ℝ) / 10 ^ 7)
    dpOp_dpPotential4_le
    β hβ

end BHHBounds
