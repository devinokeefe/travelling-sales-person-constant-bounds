import BHHBounds.Asymptotics
import BHHBounds.Upper.PoissonCoupling

/-!
# Bridge from Bandwidth-4 Concave DP Certificate to `BHHBounds.IsBHHConstant`

Proves `bhh_upper_of_dp`: given any potential `V` and bound `uBound` satisfying the
bandwidth-4 concave DP inequality `dpOp automaton4 edgeCost4 V ≤ V + uBound`, every
Beardwood–Halton–Hammersley constant `β` (`BHHBounds.IsBHHConstant β`) satisfies
`β ≤ uBound`, with no additional hypotheses.
-/

namespace BHHBounds.Upper

open Filter

/-- Any concave DP certificate `(V, uBound)` for `automaton4` implies `β ≤ uBound` for every
BHH constant `β`. -/
theorem bhh_upper_of_dp
    (V : Fin 56 → Window 3 4 6 → ℝ) (uBound : ℝ)
    (hfp : ∀ u' z', dpOp automaton4 edgeCost4 V u' z' ≤ V u' z' + uBound) :
    ∀ β : ℝ, BHHBounds.IsBHHConstant β → β ≤ uBound := by
  intro β hβ
  have hexp_lim : Tendsto (fun n : ℕ => expectedTourLen n / Real.sqrt (n : ℝ)) atTop (nhds β) :=
    BHHBounds.expectedTourLength_div_sqrt_tendsto hβ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨N, hN⟩ := expectedTourLen_div_sqrt_le_of_dp V uBound hfp ε hε
  exact le_of_tendsto hexp_lim (Filter.eventually_atTop.mpr ⟨N, hN⟩)

end BHHBounds.Upper
