/-
Two facts about auxiliary definitions of `Spec` that its comments refer to and that the other proofs
do not need: `cdiv` is the ceiling of the quotient, and `tuples` lists no tuple twice.
(`ceilSqrt_spec` is in `Correct/Table.lean`; `minOf_spec`, `mem_tuples`, `mem_orders` are in
`Correct/Basic.lean`.)
-/
import TSPBound.Correct.Basic

namespace Correct
open Spec

/-- For `b > 0`, `cdiv a b` is the least `q` with `a ≤ b·q`, that is, `ceil(a / b)`. -/
theorem cdiv_spec {a b : Nat} (hb : 0 < b) :
    a ≤ b * cdiv a b ∧ ∀ q, a ≤ b * q → cdiv a b ≤ q := by
  unfold cdiv
  constructor
  · have h := Nat.div_add_mod (a + (b - 1)) b
    have h2 := Nat.mod_lt (a + (b - 1)) hb
    omega
  · intro q hq
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul hb]
    rw [Nat.succ_mul, Nat.mul_comm q b]
    omega

/-- No tuple occurs twice in `tuples len n`.  With `mem_tuples`: each tuple of length `len` with
entries below `n` occurs exactly once. -/
theorem nodup_tuples (len n : Nat) : (tuples len n).Nodup := by
  induction len with
  | zero => simp [tuples]
  | succ len ih =>
    unfold List.Nodup at ih ⊢
    simp only [tuples]
    rw [List.pairwise_flatMap]
    refine ⟨fun x _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact ih.imp (fun h h' => h (List.cons.inj h').2)
    · refine (List.pairwise_lt_range (n := n)).imp ?_
      intro a b hab x hx y hy hxy
      rw [List.mem_map] at hx hy
      obtain ⟨s, _, rfl⟩ := hx
      obtain ⟨t, _, rfl⟩ := hy
      have := (List.cons.inj hxy).1
      omega

end Correct
