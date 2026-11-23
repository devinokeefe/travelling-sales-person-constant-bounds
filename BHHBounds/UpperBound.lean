import BHHBounds.Asymptotics
import BHHBounds.Upper.Cert4
import BHHBounds.Upper.PoissonCoupling

/-!
# The upper bound `β ≤ 0.8549326`
-/

namespace BHHBounds

open BHHBounds.Upper

/-- `0.8549326` is an asymptotic upper bound for `expectedTourLength n / √n`. -/
theorem expectedTourLength_upper_bound :
    ∀ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
      expectedTourLength n / Real.sqrt (n : ℝ) ≤ (8549326 : ℝ) / 10 ^ 7 + ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := expectedTourLength_div_sqrt_le_of_dp
    (fun u z => (dpPotential4[encUZ u z]! : ℝ) / (costScale : ℝ))
    ((8549326 : ℝ) / 10 ^ 7) dpOp_dpPotential4_le ε hε
  exact Filter.eventually_atTop.mpr ⟨N, hN⟩

/-- Every BHH constant `β` satisfies `β ≤ 0.8549326`. -/
theorem bhh_upper_bound (β : ℝ) (hβ : IsBHHConstant β) : β ≤ (8549326 : ℝ) / 10 ^ 7 :=
  le_of_forall_pos_le_add fun ε hε =>
    le_of_tendsto (expectedTourLength_div_sqrt_tendsto hβ) (expectedTourLength_upper_bound ε hε)

end BHHBounds
