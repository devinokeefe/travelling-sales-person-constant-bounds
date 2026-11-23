import BHHBounds.Cert.AllShards
import BHHBounds.Cert.BaseSound
import BHHBounds.Cert.BoxSound
import BHHBounds.Dual.Expectation

/-!
# The lower bound `0.650928770 ≤ β`
-/

namespace BHHBounds

open BHHBounds.Cert BHHBounds.Dual

/-- `0.650928770` is an asymptotic lower bound for `expectedTourLength n / √n`. -/
theorem expectedTourLength_lower_bound :
    ∀ ε > 0, ∀ᶠ n : ℕ in Filter.atTop,
      (650928770 : ℝ) / 10 ^ 9 - ε ≤ expectedTourLength n / Real.sqrt (n : ℝ) := by
  intro ε hε
  have hpot : ValidStepPot stepPotRho stepPotW := validStepPot_of_bool stepPot_valid_bool
  have hboxes : ∀ b ∈ allBoxes, ValidBox stepPotRho stepPotW b := fun b hb =>
    validBox_of_bool (List.all_eq_true.mp allBoxes_valid_bool b hb)
  have hdisj : PairwiseDisjointBoxes allBoxes := pairwiseDisjointBoxes_of_bool allBoxes_disjoint_bool
  have hbase := baseVerifyInt_le_baseIntegral hpot (nD := 1500) (by decide)
  have htri := verifyShardInt_le_planIntegral hpot hboxes
  have htot : (650928770 : ℝ) / 10 ^ 9 ≤
      (baseVerifyInt stepPotRho stepPotW 1500 : ℝ) / 10 ^ 9 +
      (verifyShardInt stepPotRho stepPotW angleTable40 allBoxes : ℝ) / 10 ^ 9 := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast total_cert_verified) (by positivity)
  filter_upwards [eventually_base_add_trianglePlan_le
    (certActiveMask stepPotRho stepPotW angleTable40) hpot hboxes hdisj ε hε] with n hn
  linarith

/-- Every BHH constant `β` satisfies `0.650928770 ≤ β`. -/
theorem bhh_lower_bound (β : ℝ) (hβ : IsBHHConstant β) : (650928770 : ℝ) / 10 ^ 9 ≤ β :=
  le_of_eventually_expectedTourLength hβ expectedTourLength_lower_bound

end BHHBounds
