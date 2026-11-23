import BHHBounds.Upper.Cert4Spec

/-!
# Verified Bandwidth-4 Concave DP Certificate (`U = 0.8549326`)

Evaluates the computable fixed-point checker `checkFixedPoint4` on
`(dpPotential4, upperBoundInt4)` and derives the real-valued concave DP bound
`dpOp_dpPotential4_le`.
-/

namespace BHHBounds.Upper

/-- Verified bandwidth-4 concave DP certificate (`U = 8549326 / 10^7 = 0.8549326`). -/
theorem checkFixedPoint4_dpPotential4 :
    checkFixedPoint4 dpPotential4 upperBoundInt4 = true := by
  native_decide

/-- Real-valued DP fixed-point inequality for `U = 8549326 / 10^7`. -/
theorem dpOp_dpPotential4_le :
    ∀ (u : Fin 56) (z : Window 3 4 6),
      dpOp automaton4 edgeCost4 (fun v w => (dpPotential4[encUZ v w]! : ℝ) / (costScale : ℝ)) u z ≤
        (dpPotential4[encUZ u z]! : ℝ) / (costScale : ℝ) + (8549326 : ℝ) / 10 ^ 7 := by
  intro u z
  have h := checkFixedPoint4_sound checkFixedPoint4_dpPotential4 u z
  have hU : (upperBoundInt4 : ℝ) / (costScale : ℝ) = (8549326 : ℝ) / 10 ^ 7 := by
    norm_num [costScale, upperBoundInt4]
  rwa [hU] at h

end BHHBounds.Upper
