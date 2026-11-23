import BHHBounds.Dual.PoissonIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Soundness of the Triangle-Moat Fixed-Point Verifier (`verifyBoxInt`, `verifyShardInt`)

Proves:
1. `certActiveMask`: the deterministic boolean level-activation mask matching `boxLevelsLoop`.
2. `buildBoxGeom_sound`: geometric, potential, circumdisk, norm-squared, angle-sector dot-product,
   and box-weight soundness of `buildBoxGeom`.
3. `levelPenaltyHi_sound`: polar-coordinate upper bound on `levelCrossPen` via `shellPenLoop`,
   `sectorShellsLoop`, and `vertexSectorsLoop`.
4. `verifyBoxInt_le_boxIntegral` & `verifyShardInt_le_planIntegral`:
   `(verifyShardInt rho w angleTable40 boxes : ℝ) / 10^9 ≤
     trianglePlanIntegral rho w (certActiveMask rho w angleTable40) boxes`.
-/

open MeasureTheory Set Real
open scoped ENNReal Classical
open BHHBounds.Geometry
open BHHBounds.Dual

namespace BHHBounds.Cert

private lemma toR_lt_toR {a b : Int} (h : a < b) : toR a < toR b :=
  div_lt_div_of_pos_right (by exact_mod_cast h) S_pos

private lemma toR_mul_int (k a : Int) : toR (k * a) = (k : ℝ) * toR a := by
  unfold toR; push_cast; ring

private lemma triVerts_0 (L : ℝ) (pt : Pt) : triVerts L pt 0 = (0, 0) := rfl
private lemma triVerts_1 (L : ℝ) (pt : Pt) : triVerts L pt 1 = (L, 0) := rfl
private lemma triVerts_2 (L : ℝ) (pt : Pt) : triVerts L pt 2 = (L * pt.1, L * pt.2) := rfl

/-- Deterministic level-activation mask matching `boxLevelsLoop`: level `(rj, yj)` is activated
iff `2 * (yj - yPrev) > levelPenaltyHi ...`. -/
def certActiveMask (rho w : Array Int) (ang : AngleTable) : BoxCert → Int → Int → Int → Bool :=
  fun b yPrev rj yj =>
    let g := buildBoxGeom rho w ang b
    let wMax := w.getD (rho.size - 1) 0
    decide (2 * (yj - yPrev) > levelPenaltyHi rho w ang g wMax yPrev rj yj)

/-! ## Section 1: Elementary Analytic & Measure-Theoretic Helpers -/

private lemma expNegLo_nonneg' (x : Int) : 0 ≤ expNegLo x := by
  unfold expNegLo
  by_cases h1 : x ≤ 0
  · rw [if_pos h1]; decide
  · rw [if_neg h1]
    dsimp only
    by_cases h2 : (x / 250000).toNat > 64
    · rw [if_pos h2]
    · rw [if_neg h2]
      split_ifs with h3
      · exact le_rfl
      · push Not at h3
        exact mulLo_nonneg (le_of_lt h3) (powLo_nonneg _ (by decide))

private lemma expNegHi_nonneg' (x : Int) : 0 ≤ expNegHi x := by
  by_cases hx : 0 ≤ x
  · exact nonneg_of_toR_nonneg ((Real.exp_nonneg _).trans (le_expNegHi hx))
  · unfold expNegHi; rw [if_pos (by omega)]; decide

private lemma setIntegral_le_of_setLIntegral_le {A : Set Pt} (hA : MeasurableSet A)
    {F : Pt → ℝ} (hnn : ∀ v ∈ A, 0 ≤ F v) {C : ℝ} (hC : 0 ≤ C)
    (hle : ∫⁻ v in A, ENNReal.ofReal (F v) ≤ ENNReal.ofReal C) :
    ∫ v in A, F v ≤ C := by
  by_cases hInt : IntegrableOn F A volume
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hA hnn) hInt.aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rwa [ENNReal.toReal_ofReal hC] at h
  · rw [integral_undef hInt]; exact hC

private lemma setLIntegral_Ioo_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioo a c, g x = (∫⁻ x in Ioo a b, g x) + ∫⁻ x in Ioo b c, g x := by
  have hsub : Ioo a c =ᵐ[volume] (Ioo a b ∪ Ioo b c : Set ℝ) := by
    rw [Filter.EventuallyEq, ae_iff]
    have h1 : {x : ℝ | ¬ ((x ∈ Ioo a c) = (x ∈ Ioo a b ∪ Ioo b c))} ⊆ {b} := by
      intro x hx
      simp only [Set.mem_setOf_eq, eq_iff_iff, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff] at hx ⊢
      by_contra hne
      apply hx
      constructor
      · intro ⟨hax, hxc⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨hax, hlt⟩
        · exact Or.inr ⟨hgt, hxc⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
    exact measure_mono_null h1 Real.volume_singleton
  have hdisj : Disjoint (Ioo a b) (Ioo b c) :=
    Set.disjoint_left.mpr fun _ h1 h2 => by linarith [h1.2, h2.1]
  rw [setLIntegral_congr hsub, lintegral_union measurableSet_Ioo hdisj]

private lemma triCrossCoeff_nonneg {rho w : Array Int} (hpot : ValidStepPot rho w)
    {p yPrev yj d : ℝ} (hy : yPrev ≤ yj) (k : Fin rho.size) :
    0 ≤ triCrossCoeff w p yPrev yj d k.val := by
  unfold triCrossCoeff
  have hdw := stepPot_dw_nonneg hpot k
  have hle : toR (wPrev w k.val) ≤ toR (w.getD k.val 0) := by linarith
  have hmono : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
      max 0 (p + yj + t₁ - d) - max 0 (p + yPrev + t₁ - d) ≤
      max 0 (p + yj + t₂ - d) - max 0 (p + yPrev + t₂ - d) := by
    intro t₁ t₂ ht
    rcases le_total 0 (p + yj + t₁ - d) with h1 | h1 <;>
    rcases le_total 0 (p + yPrev + t₂ - d) with h2 | h2
    · rw [max_eq_right h1, max_eq_right (show 0 ≤ p + yj + t₂ - d by linarith), max_eq_right h2]
      linarith [le_max_right (0 : ℝ) (p + yPrev + t₁ - d)]
    · rw [max_eq_right h1, max_eq_right (show 0 ≤ p + yj + t₂ - d by linarith), max_eq_left h2]
      linarith [le_max_left (0 : ℝ) (p + yPrev + t₁ - d)]
    · rw [max_eq_left h1, max_eq_left (show p + yPrev + t₁ - d ≤ 0 by linarith), sub_self]
      exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
    · rw [max_eq_left h1, max_eq_left (show p + yPrev + t₁ - d ≤ 0 by linarith), sub_self]
      exact sub_nonneg.mpr (max_le_max_left 0 (by linarith))
  linarith [hmono (toR (wPrev w k.val)) (toR (w.getD k.val 0)) hle]

private lemma quad_bounds_on_Icc {sa sb s mLo mVal mHi q2Lo q2Val q2Hi : ℝ}
    (hsa : 0 ≤ sa) (hs1 : sa ≤ s) (hs2 : s ≤ sb)
    (hm1 : mLo ≤ mVal) (hm2 : mVal ≤ mHi) (hq1 : q2Lo ≤ q2Val) (hq2 : q2Val ≤ q2Hi) :
    let sStar := max sa (min sb mHi)
    sStar ^ 2 - 2 * sStar * mHi + q2Lo ≤ s ^ 2 - 2 * s * mVal + q2Val ∧
    s ^ 2 - 2 * s * mVal + q2Val ≤
      max (sa ^ 2 - 2 * sa * mLo + q2Hi) (sb ^ 2 - 2 * sb * mLo + q2Hi) := by
  have hs0 : 0 ≤ s := hsa.trans hs1
  constructor
  · have hstep1 : s ^ 2 - 2 * s * mHi + q2Lo ≤ s ^ 2 - 2 * s * mVal + q2Val := by nlinarith
    have hmin : (max sa (min sb mHi) - mHi) ^ 2 ≤ (s - mHi) ^ 2 := by
      rcases le_total mHi sa with h1 | h1
      · rw [min_eq_right (h1.trans (hs1.trans hs2)), max_eq_left h1]; nlinarith
      · rcases le_total sb mHi with h2 | h2
        · rw [min_eq_left h2, max_eq_right (hs1.trans hs2)]; nlinarith
        · rw [min_eq_right h2, max_eq_right h1, sub_self, zero_pow two_ne_zero]; exact sq_nonneg _
    nlinarith
  · have hstep1 : s ^ 2 - 2 * s * mVal + q2Val ≤ s ^ 2 - 2 * s * mLo + q2Hi := by nlinarith
    set fa := sa ^ 2 - 2 * sa * mLo + q2Hi
    set fb := sb ^ 2 - 2 * sb * mLo + q2Hi
    set M := max fa fb
    have hfa : fa ≤ M := le_max_left _ _
    have hfb : fb ≤ M := le_max_right _ _
    by_cases heq : sa = sb
    · have hse : s = sa := by linarith
      subst hse; exact hstep1.trans hfa
    · have hlt : 0 < sb - sa := by linarith [lt_of_le_of_ne (hs1.trans hs2) heq]
      have hconv : (sb - sa) * (s ^ 2 - 2 * s * mLo + q2Hi) ≤
          (sb - s) * fa + (s - sa) * fb := by
        dsimp only [fa, fb]
        nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr hs2)]
      have hM : (sb - s) * fa + (s - sa) * fb ≤ (sb - sa) * M := by
        nlinarith [sub_nonneg.mpr hs1, sub_nonneg.mpr hs2]
      have hle : s ^ 2 - 2 * s * mLo + q2Hi ≤ M := by nlinarith
      exact hstep1.trans hle

private lemma exit_radius_bound {r s mLo mVal q2Val q2Hi : ℝ}
    (hr0 : 0 ≤ r) (hsr : r < s) (hout : r ^ 2 < s ^ 2 - 2 * s * mVal + q2Val)
    (hmLo : mLo ≤ mVal) (hqHi : q2Val ≤ q2Hi) (hmr : mLo ≤ r) :
    mLo + Real.sqrt (mLo ^ 2 + r ^ 2 - q2Hi) < s := by
  have hs0 : 0 < s := lt_of_le_of_lt hr0 hsr
  have hsm : 0 < s - mLo := by linarith
  have hsq : mLo ^ 2 + r ^ 2 - q2Hi < (s - mLo) ^ 2 := by nlinarith
  have hrt : Real.sqrt (mLo ^ 2 + r ^ 2 - q2Hi) < s - mLo := by
    rw [Real.sqrt_lt' hsm]; exact hsq
  linarith

private lemma dot_le_euclidNorm (q : Pt) (θ : ℝ) :
    q.1 * Real.cos θ + q.2 * Real.sin θ ≤ euclidNorm q := by
  have hsq : (q.1 * Real.cos θ + q.2 * Real.sin θ) ^ 2 ≤ q.1 ^ 2 + q.2 ^ 2 := by
    have hcs := Real.cos_sq_add_sin_sq θ
    have h1 : (q.1 * Real.cos θ + q.2 * Real.sin θ) ^ 2 +
        (q.1 * Real.sin θ - q.2 * Real.cos θ) ^ 2 = (q.1 ^ 2 + q.2 ^ 2) * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
      ring
    rw [hcs, mul_one] at h1
    nlinarith [sq_nonneg (q.1 * Real.sin θ - q.2 * Real.cos θ)]
  unfold euclidNorm
  exact (le_abs_self _).trans (by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hsq)

private lemma sqDist_polar_shift (p q : Pt) (s θ : ℝ) :
    sqDist (p.1 + s * Real.cos θ, p.2 + s * Real.sin θ) q =
      s ^ 2 - 2 * s * ((q.1 - p.1) * Real.cos θ + (q.2 - p.2) * Real.sin θ) +
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
  unfold sqDist
  have hcs := Real.cos_sq_add_sin_sq θ
  calc (p.1 + s * Real.cos θ - q.1) ^ 2 + (p.2 + s * Real.sin θ - q.2) ^ 2
      = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) -
        2 * s * ((q.1 - p.1) * Real.cos θ + (q.2 - p.2) * Real.sin θ) +
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by ring
    _ = s ^ 2 - 2 * s * ((q.1 - p.1) * Real.cos θ + (q.2 - p.2) * Real.sin θ) +
        ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by rw [hcs, mul_one]

/-- Angle-sector trigonometric bounds for `θ ∈ Ioo (it * 2π/40) ((it + 1) * 2π/40)`:
writing `θ = tm + u` with `tm = (2 * it + 1) * π / 40`, we have `|u| ≤ π/40`, hence
`toR chLo ≤ cos u` and `|sin u| ≤ toR shHi`. -/
private lemma sector_trig_bounds (it : Fin 40) {θ : ℝ}
    (hθ : θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40))) :
    let tm : ℝ := ((2 * it.val + 1 : Nat) : ℝ) * Real.pi / 40
    let u : ℝ := θ - tm
    θ = tm + u ∧
    toR (angleTable40.cmLo.getD it.val 0) ≤ Real.cos tm ∧
    Real.cos tm ≤ toR (angleTable40.cmHi.getD it.val 0) ∧
    toR (angleTable40.smLo.getD it.val 0) ≤ Real.sin tm ∧
    Real.sin tm ≤ toR (angleTable40.smHi.getD it.val 0) ∧
    0 ≤ angleTable40.chLo ∧
    toR angleTable40.chLo ≤ Real.cos u ∧
    |Real.sin u| ≤ toR angleTable40.shHi := by
  intro tm u
  have hang := angleTable40_sound
  have hit := hang.2.2 it
  have hu_abs : |u| ≤ Real.pi / 40 := by
    rw [abs_le]
    dsimp only [u, tm]
    have h1 := hθ.1
    have h2 := hθ.2
    push_cast at h1 h2 ⊢
    constructor <;> linarith
  have hpi40_le : Real.pi / 40 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hcos_u : Real.cos (Real.pi / 40) ≤ Real.cos u := by
    rw [← Real.cos_abs u]
    exact Real.antitoneOn_cos ⟨abs_nonneg u, hu_abs.trans (by linarith [Real.pi_pos])⟩
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hu_abs
  have hsin_u : |Real.sin u| ≤ Real.sin (Real.pi / 40) := by
    have habs_sin : |Real.sin u| = Real.sin |u| := by
      rcases le_total 0 u with hu | hu
      · rw [abs_of_nonneg hu, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu
          ((abs_of_nonneg hu ▸ hu_abs).trans (by linarith [Real.pi_pos])))]
      · rw [abs_of_nonpos hu, Real.sin_neg]
        have hsin_nn : 0 ≤ Real.sin (-u) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
            ((abs_of_nonpos hu ▸ hu_abs).trans (by linarith [Real.pi_pos]))
        have hsin_le : Real.sin u ≤ 0 := by rw [Real.sin_neg] at hsin_nn; linarith
        exact abs_of_nonpos hsin_le
    rw [habs_sin]
    exact Real.monotoneOn_sin ⟨by linarith [Real.pi_pos, abs_nonneg u], hu_abs.trans hpi40_le⟩
      ⟨by linarith [Real.pi_pos], hpi40_le⟩ hu_abs
  refine ⟨by dsimp only [u]; ring, hit.1, hit.2.1, hit.2.2.1, hit.2.2.2,
    by unfold angleTable40; decide, hang.2.1.1.trans hcos_u, hsin_u.trans hang.2.1.2⟩

/-! ## Section 2: `buildBoxGeom` Soundness -/

/-- Helper: `Array.ofFn` followed by `Array.map` lookup at `it < n`. -/
private lemma getD_map_ofFn {α β : Type} {n : Nat} (f : Fin n → α) (g : α → β) (d : β)
    (it : Fin n) : ((Array.ofFn f).map g).getD it.val d = g (f it) := by
  simp [Array.getD, it.isLt]

/-- Package of all geometric guarantees produced by `buildBoxGeom rho w angleTable40 b`
for any canonical triangle `(L, pt) ∈ boxRegion b`. -/
private structure BoxGeomSound (rho w : Array Int) (b : BoxCert) (g : BoxGeom) (L : ℝ) (pt : Pt) : Prop where
  p0_le : triVertPot rho w L pt 0 ≤ toR g.pi01Max
  p1_le : triVertPot rho w L pt 1 ≤ toR g.pi01Max
  p2_le : triVertPot rho w L pt 2 ≤ toR g.pi2Max
  radB_nn : 0 ≤ g.radB
  enc_le : ∀ u : Fin 3, euclidDist (triVerts L pt u) (toR b.cx, toR b.cy) ≤ toR g.radB
  -- Squared distances for edges `(0,1)`, `(0,2)`, `(1,2)` and center offsets `C - P u`
  q2_01 : (g.q2Lo01 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 0) (triVerts L pt 1) ∧
          sqDist (triVerts L pt 0) (triVerts L pt 1) ≤ (g.q2Hi01 : ℝ) / (S : ℝ) ^ 2
  q2_02 : (g.q2Lo02 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 0) (triVerts L pt 2) ∧
          sqDist (triVerts L pt 0) (triVerts L pt 2) ≤ (g.q2Hi02 : ℝ) / (S : ℝ) ^ 2
  q2_12 : (g.q2Lo12 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 1) (triVerts L pt 2) ∧
          sqDist (triVerts L pt 1) (triVerts L pt 2) ≤ (g.q2Hi12 : ℝ) / (S : ℝ) ^ 2
  cq2_0 : (g.cq2Lo0 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 0) (toR b.cx, toR b.cy)
  cq2_1 : (g.cq2Lo1 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 1) (toR b.cx, toR b.cy)
  cq2_2 : (g.cq2Lo2 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 2) (toR b.cx, toR b.cy)
  -- Dot-product bounds on every angular sector `it : Fin 40`
  dot_01 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    toR (g.mLo01.getD it.val 0) ≤
      ((triVerts L pt 1).1 - (triVerts L pt 0).1) * Real.cos θ +
      ((triVerts L pt 1).2 - (triVerts L pt 0).2) * Real.sin θ ∧
    ((triVerts L pt 1).1 - (triVerts L pt 0).1) * Real.cos θ +
      ((triVerts L pt 1).2 - (triVerts L pt 0).2) * Real.sin θ ≤ toR (g.mHi01.getD it.val 0)
  dot_02 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    toR (g.mLo02.getD it.val 0) ≤
      ((triVerts L pt 2).1 - (triVerts L pt 0).1) * Real.cos θ +
      ((triVerts L pt 2).2 - (triVerts L pt 0).2) * Real.sin θ ∧
    ((triVerts L pt 2).1 - (triVerts L pt 0).1) * Real.cos θ +
      ((triVerts L pt 2).2 - (triVerts L pt 0).2) * Real.sin θ ≤ toR (g.mHi02.getD it.val 0)
  dot_10 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    toR (g.mLo10.getD it.val 0) ≤
      ((triVerts L pt 0).1 - (triVerts L pt 1).1) * Real.cos θ +
      ((triVerts L pt 0).2 - (triVerts L pt 1).2) * Real.sin θ ∧
    ((triVerts L pt 0).1 - (triVerts L pt 1).1) * Real.cos θ +
      ((triVerts L pt 0).2 - (triVerts L pt 1).2) * Real.sin θ ≤ toR (g.mHi10.getD it.val 0)
  dot_12 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    toR (g.mLo12.getD it.val 0) ≤
      ((triVerts L pt 2).1 - (triVerts L pt 1).1) * Real.cos θ +
      ((triVerts L pt 2).2 - (triVerts L pt 1).2) * Real.sin θ ∧
    ((triVerts L pt 2).1 - (triVerts L pt 1).1) * Real.cos θ +
      ((triVerts L pt 2).2 - (triVerts L pt 1).2) * Real.sin θ ≤ toR (g.mHi12.getD it.val 0)
  dot_20 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    toR (g.mLo20.getD it.val 0) ≤
      ((triVerts L pt 0).1 - (triVerts L pt 2).1) * Real.cos θ +
      ((triVerts L pt 0).2 - (triVerts L pt 2).2) * Real.sin θ ∧
    ((triVerts L pt 0).1 - (triVerts L pt 2).1) * Real.cos θ +
      ((triVerts L pt 0).2 - (triVerts L pt 2).2) * Real.sin θ ≤ toR (g.mHi20.getD it.val 0)
  dot_21 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    toR (g.mLo21.getD it.val 0) ≤
      ((triVerts L pt 1).1 - (triVerts L pt 2).1) * Real.cos θ +
      ((triVerts L pt 1).2 - (triVerts L pt 2).2) * Real.sin θ ∧
    ((triVerts L pt 1).1 - (triVerts L pt 2).1) * Real.cos θ +
      ((triVerts L pt 1).2 - (triVerts L pt 2).2) * Real.sin θ ≤ toR (g.mHi21.getD it.val 0)
  dot_c0 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    (toR b.cx - (triVerts L pt 0).1) * Real.cos θ +
      (toR b.cy - (triVerts L pt 0).2) * Real.sin θ ≤ toR (g.mcHi0.getD it.val 0)
  dot_c1 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    (toR b.cx - (triVerts L pt 1).1) * Real.cos θ +
      (toR b.cy - (triVerts L pt 1).2) * Real.sin θ ≤ toR (g.mcHi1.getD it.val 0)
  dot_c2 : ∀ (it : Fin 40) (θ : ℝ),
    θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
    (toR b.cx - (triVerts L pt 2).1) * Real.cos θ +
      (toR b.cy - (triVerts L pt 2).2) * Real.sin θ ≤ toR (g.mcHi2.getD it.val 0)

private lemma buildBoxGeom_sound {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {L : ℝ} {pt : Pt} (hmem : (L, pt) ∈ boxRegion b) :
    BoxGeomSound rho w b (buildBoxGeom rho w angleTable40 b) L pt := by
  have hql := boxRegion_mem_quarterLens hb hmem
  rcases hmem with ⟨hl0, hl1, hx0, hx1, hy0, hy1⟩
  have hl0_nn : 0 ≤ b.l0 := le_of_lt hb.l0_pos
  have hl1_nn : 0 ≤ b.l1 := by have := hb.l0_lt_l1; omega
  have hx1_nn : 0 ≤ b.x1 := by have := hb.x0_nonneg; have := hb.x0_lt_x1; omega
  have hy1_nn : 0 ≤ b.y1 := by have := hb.y0_nonneg; have := hb.y0_lt_y1; omega
  -- Coordinate interval enclosures for `P 2 = (L * pt.1, L * pt.2)` and `P 2 - P 1 = (-L * (1 - pt.1), L * pt.2)`
  have hqx0 : toR (mulLo b.l0 b.x0) ≤ L * pt.1 :=
    mulLo_le.trans (mul_le_mul (le_of_lt hl0) (le_of_lt hx0) (toR_nonneg hb.x0_nonneg) (le_of_lt hql.1))
  have hqx1 : L * pt.1 ≤ toR (mulHi b.l1 b.x1) :=
    (mul_le_mul (le_of_lt hl1) (le_of_lt hx1) (le_of_lt hql.2.1) (toR_nonneg hl1_nn)).trans le_mulHi
  have hqy0 : toR (mulLo b.l0 b.y0) ≤ L * pt.2 :=
    mulLo_le.trans (mul_le_mul (le_of_lt hl0) (le_of_lt hy0) (toR_nonneg hb.y0_nonneg) (le_of_lt hql.1))
  have hqy1 : L * pt.2 ≤ toR (mulHi b.l1 b.y1) :=
    (mul_le_mul (le_of_lt hl1) (le_of_lt hy1) (le_of_lt hql.2.2.2.1) (toR_nonneg hl1_nn)).trans le_mulHi
  have homx_lo : toR (S - b.x1) ≤ 1 - pt.1 := by rw [toR_sub, toR_S]; linarith
  have homx_hi : 1 - pt.1 ≤ toR (S - b.x0) := by rw [toR_sub, toR_S]; linarith
  have homx1_nn : 0 ≤ S - b.x1 := by have := hb.x1_le_half; unfold S; omega
  have homx0_nn : 0 ≤ S - b.x0 := by have := hb.x1_le_half; have := hb.x0_lt_x1; unfold S; omega
  have hr12x0 : toR (-mulHi b.l1 (S - b.x0)) ≤ L * pt.1 - L := by
    rw [toR_neg]
    have h1 : L * (1 - pt.1) ≤ toR (mulHi b.l1 (S - b.x0)) :=
      (mul_le_mul (le_of_lt hl1) homx_hi (by linarith [hql.2.2.1]) (toR_nonneg hl1_nn)).trans le_mulHi
    linarith
  have hr12x1 : L * pt.1 - L ≤ toR (-mulLo b.l0 (S - b.x1)) := by
    rw [toR_neg]
    have h1 : toR (mulLo b.l0 (S - b.x1)) ≤ L * (1 - pt.1) :=
      mulLo_le.trans (mul_le_mul (le_of_lt hl0) homx_lo (toR_nonneg homx1_nn) (le_of_lt hql.1))
    linarith
  -- Helper: `|a - x| ≤ toR (max (a - lo).natAbs (hi - a).natAbs)` whenever `toR lo ≤ x ≤ toR hi`
  have habs_box : ∀ (a lo hi : Int) (x : ℝ), toR lo ≤ x → x ≤ toR hi →
      |x - toR a| ≤ ((max (a - lo).natAbs (hi - a).natAbs : Int) : ℝ) / (S : ℝ) := by
    intro a lo hi x hlo hhi
    rw [abs_le]
    set m : Int := max (a - lo).natAbs (hi - a).natAbs
    have hm1 : a - lo ≤ m := by dsimp only [m]; omega
    have hm2 : hi - a ≤ m := by dsimp only [m]; omega
    have h1 : toR a - toR lo ≤ toR m := by rw [← toR_sub]; exact toR_le_toR hm1
    have h2 : toR hi - toR a ≤ toR m := by rw [← toR_sub]; exact toR_le_toR hm2
    unfold toR at hlo hhi h1 h2 ⊢
    constructor <;> linarith
  -- Helper: `mkDot` soundness for any box `[x0, x1] × [y0, y1]`
  have hmkDot : ∀ (x0 x1 y0 y1 : Int) (x y : ℝ),
      toR x0 ≤ x → x ≤ toR x1 → toR y0 ≤ y → y ≤ toR y1 →
      ∀ (it : Fin 40) (θ : ℝ),
        θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
        let pairs := Array.ofFn (n := angleTable40.nT) fun jt =>
          dotIntervalInt x0 x1 y0 y1
            (angleTable40.cmLo.getD jt.val 0) (angleTable40.cmHi.getD jt.val 0)
            (angleTable40.smLo.getD jt.val 0) (angleTable40.smHi.getD jt.val 0)
            angleTable40.chLo angleTable40.shHi
        toR ((pairs.map Prod.fst).getD it.val 0) ≤ x * Real.cos θ + y * Real.sin θ ∧
        x * Real.cos θ + y * Real.sin θ ≤ toR ((pairs.map Prod.snd).getD it.val 0) := by
    intro x0 x1 y0 y1 x y hx0' hx1' hy0' hy1' it θ hθ
    have htrig := sector_trig_bounds it hθ
    have hdot := dotIntervalInt_sound hx0' hx1' hy0' hy1'
      htrig.2.1 htrig.2.2.1 htrig.2.2.2.1 htrig.2.2.2.2.1
      htrig.2.2.2.2.2.1 htrig.2.2.2.2.2.2.1 htrig.2.2.2.2.2.2.2
    rw [← htrig.1] at hdot
    have hnT : angleTable40.nT = 40 := rfl
    dsimp only
    rw [getD_map_ofFn _ Prod.fst 0 ⟨it.val, by rw [hnT]; exact it.isLt⟩,
        getD_map_ofFn _ Prod.snd 0 ⟨it.val, by rw [hnT]; exact it.isLt⟩]
    exact hdot
  -- Now construct `BoxGeomSound` field by field!
  refine {
    p0_le := by
      unfold buildBoxGeom triVertPot; dsimp only
      rw [hb.pi01_eq]; exact stepPot_le_evalStepPot hpot (le_of_lt hl1)
    p1_le := by
      unfold buildBoxGeom triVertPot; dsimp only
      rw [hb.pi01_eq]; exact stepPot_le_evalStepPot hpot (le_of_lt hl1)
    p2_le := by
      unfold buildBoxGeom triVertPot; dsimp only
      refine stepPot_le_evalStepPot hpot ?_
      have hn2 : euclidNorm (1 - pt.1, pt.2) ≤ toR (sqrtSqHi ((S - b.x0) * (S - b.x0) + b.y1 * b.y1)) := by
        have h1 := le_sqrtSqHi ((S - b.x0) * (S - b.x0) + b.y1 * b.y1)
        have h2 : (((S - b.x0) * (S - b.x0) + b.y1 * b.y1 : Int) : ℝ) / (S : ℝ) ^ 2 =
            (toR (S - b.x0)) ^ 2 + (toR b.y1) ^ 2 := by unfold toR; push_cast; ring
        rw [h2] at h1
        have hsq : (1 - pt.1) ^ 2 + pt.2 ^ 2 ≤ (toR (S - b.x0)) ^ 2 + (toR b.y1) ^ 2 := by
          have h1x : 0 ≤ 1 - pt.1 := by linarith [hql.2.2.1]
          nlinarith [hql.2.2.2.1, homx_hi, hy1]
        exact (Real.sqrt_le_sqrt hsq).trans h1
      exact (mul_le_mul (le_of_lt hl1) hn2 (Real.sqrt_nonneg _) (toR_nonneg hl1_nn)).trans le_mulHi
    radB_nn := by
      unfold buildBoxGeom; dsimp only
      exact le_max_of_le_left (sqrtSqHi_nonneg _)
    enc_le := by
      intro u
      unfold buildBoxGeom; dsimp only
      fin_cases u
      · -- u = 0: `(0, 0)` to `(cx, cy)`
        refine le_trans ?_ (toR_le_toR (le_max_left _ _))
        have h1 := le_sqrtSqHi ((b.cx.natAbs : Int) * b.cx.natAbs + (b.cy.natAbs : Int) * b.cy.natAbs)
        have h2 : (((b.cx.natAbs : Int) * b.cx.natAbs + (b.cy.natAbs : Int) * b.cy.natAbs : Int) : ℝ) / (S : ℝ) ^ 2 =
            sqDist (triVerts L pt 0) (toR b.cx, toR b.cy) := by
          have hcx : (b.cx.natAbs : Int) * (b.cx.natAbs : Int) = b.cx * b.cx := Int.natAbs_mul_self
          have hcy : (b.cy.natAbs : Int) * (b.cy.natAbs : Int) = b.cy * b.cy := Int.natAbs_mul_self
          rw [hcx, hcy]
          unfold triVerts sqDist toR; simp only [Matrix.cons_val_zero, zero_sub, neg_sq]
          push_cast; ring
        rw [h2] at h1; exact h1
      · -- u = 1: `(L, 0)` to `(cx, cy)`
        refine le_trans ?_ (toR_le_toR ((le_max_left _ _).trans (le_max_right _ _)))
        set dx1 : Int := max (b.cx - b.l0).natAbs (b.l1 - b.cx).natAbs
        have h1 := le_sqrtSqHi (dx1 * dx1 + (b.cy.natAbs : Int) * b.cy.natAbs)
        have hx_abs := habs_box b.cx b.l0 b.l1 L (le_of_lt hl0) (le_of_lt hl1)
        have hsq : sqDist (triVerts L pt 1) (toR b.cx, toR b.cy) ≤
            ((dx1 * dx1 + (b.cy.natAbs : Int) * b.cy.natAbs : Int) : ℝ) / (S : ℝ) ^ 2 := by
          have hcy : (b.cy.natAbs : Int) * (b.cy.natAbs : Int) = b.cy * b.cy := Int.natAbs_mul_self
          rw [hcy]
          unfold triVerts sqDist; simp only [Matrix.cons_val_one, Matrix.cons_val_zero, zero_sub, neg_sq]
          have h1x : (L - toR b.cx) ^ 2 ≤ ((dx1 : ℝ) / (S : ℝ)) ^ 2 := by
            rw [← sq_abs (L - toR b.cx)]
            exact pow_le_pow_left₀ (abs_nonneg _) hx_abs 2
          have h2y : (toR b.cy) ^ 2 = ((b.cy : ℝ) * (b.cy : ℝ)) / (S : ℝ) ^ 2 := by
            unfold toR; ring
          have hdx' : ((dx1 : ℝ) / (S : ℝ)) ^ 2 = ((dx1 : ℝ) * (dx1 : ℝ)) / (S : ℝ) ^ 2 := by ring
          push_cast; rw [add_div]; linarith
        exact (Real.sqrt_le_sqrt hsq).trans h1
      · -- u = 2: `(L * pt.1, L * pt.2)` to `(cx, cy)`
        refine le_trans ?_ (toR_le_toR ((le_max_right _ _).trans (le_max_right _ _)))
        set dx2 : Int := max (b.cx - mulLo b.l0 b.x0).natAbs (mulHi b.l1 b.x1 - b.cx).natAbs
        set dy2 : Int := max (b.cy - mulLo b.l0 b.y0).natAbs (mulHi b.l1 b.y1 - b.cy).natAbs
        have h1 := le_sqrtSqHi (dx2 * dx2 + dy2 * dy2)
        have hx_abs := habs_box b.cx (mulLo b.l0 b.x0) (mulHi b.l1 b.x1) (L * pt.1) hqx0 hqx1
        have hy_abs := habs_box b.cy (mulLo b.l0 b.y0) (mulHi b.l1 b.y1) (L * pt.2) hqy0 hqy1
        have hsq : sqDist (triVerts L pt 2) (toR b.cx, toR b.cy) ≤
            ((dx2 * dx2 + dy2 * dy2 : Int) : ℝ) / (S : ℝ) ^ 2 := by
          rw [triVerts_2]; unfold sqDist
          have h1x : (L * pt.1 - toR b.cx) ^ 2 ≤ ((dx2 : ℝ) / (S : ℝ)) ^ 2 := by
            rw [← sq_abs (L * pt.1 - toR b.cx)]
            exact pow_le_pow_left₀ (abs_nonneg _) hx_abs 2
          have h1y : (L * pt.2 - toR b.cy) ^ 2 ≤ ((dy2 : ℝ) / (S : ℝ)) ^ 2 := by
            rw [← sq_abs (L * pt.2 - toR b.cy)]
            exact pow_le_pow_left₀ (abs_nonneg _) hy_abs 2
          push_cast; rw [add_div]
          have hx' : (dx2 : ℝ) * (dx2 : ℝ) / (S : ℝ) ^ 2 = ((dx2 : ℝ) / (S : ℝ)) ^ 2 := by ring
          have hy' : (dy2 : ℝ) * (dy2 : ℝ) / (S : ℝ) ^ 2 = ((dy2 : ℝ) / (S : ℝ)) ^ 2 := by ring
          linarith
        exact (Real.sqrt_le_sqrt hsq).trans h1
    q2_01 := by
      unfold buildBoxGeom; dsimp only
      have h := boxNorm2LoHi_sound (le_of_lt hl0) (le_of_lt hl1) (by rw [toR_zero]) (by rw [toR_zero])
      have hsq : sqDist (triVerts L pt 0) (triVerts L pt 1) = L ^ 2 + 0 ^ 2 := by
        unfold triVerts sqDist; simp
      rwa [hsq]
    q2_02 := by
      unfold buildBoxGeom; dsimp only
      have h := boxNorm2LoHi_sound hqx0 hqx1 hqy0 hqy1
      have hsq : sqDist (triVerts L pt 0) (triVerts L pt 2) = (L * pt.1) ^ 2 + (L * pt.2) ^ 2 := by
        unfold triVerts sqDist; simp
      rwa [hsq]
    q2_12 := by
      unfold buildBoxGeom; dsimp only
      have h := boxNorm2LoHi_sound hr12x0 hr12x1 hqy0 hqy1
      have hsq : sqDist (triVerts L pt 1) (triVerts L pt 2) = (L * pt.1 - L) ^ 2 + (L * pt.2) ^ 2 := by
        unfold triVerts sqDist; simp; ring
      rwa [hsq]
    cq2_0 := by
      unfold buildBoxGeom; dsimp only
      have h := boxNorm2LoHi_sound (le_rfl : toR b.cx ≤ toR b.cx) le_rfl (le_rfl : toR b.cy ≤ toR b.cy) le_rfl
      have hsq : sqDist (triVerts L pt 0) (toR b.cx, toR b.cy) = (toR b.cx) ^ 2 + (toR b.cy) ^ 2 := by
        unfold triVerts sqDist; simp
      rw [hsq]; exact h.1
    cq2_1 := by
      unfold buildBoxGeom; dsimp only
      have h := boxNorm2LoHi_sound (x0 := b.cx - b.l1) (x1 := b.cx - b.l0) (y0 := b.cy) (y1 := b.cy)
        (x := toR b.cx - L) (y := toR b.cy)
        (by rw [toR_sub]; linarith) (by rw [toR_sub]; linarith) le_rfl le_rfl
      have hsq : sqDist (triVerts L pt 1) (toR b.cx, toR b.cy) = (toR b.cx - L) ^ 2 + (toR b.cy) ^ 2 := by
        unfold triVerts sqDist; simp; ring
      rw [hsq]; exact h.1
    cq2_2 := by
      unfold buildBoxGeom; dsimp only
      have h := boxNorm2LoHi_sound (x0 := b.cx - mulHi b.l1 b.x1) (x1 := b.cx - mulLo b.l0 b.x0)
        (y0 := b.cy - mulHi b.l1 b.y1) (y1 := b.cy - mulLo b.l0 b.y0)
        (x := toR b.cx - L * pt.1) (y := toR b.cy - L * pt.2)
        (by rw [toR_sub]; linarith) (by rw [toR_sub]; linarith)
        (by rw [toR_sub]; linarith) (by rw [toR_sub]; linarith)
      have hsq : sqDist (triVerts L pt 2) (toR b.cx, toR b.cy) =
          (toR b.cx - L * pt.1) ^ 2 + (toR b.cy - L * pt.2) ^ 2 := by
        unfold triVerts sqDist; simp; ring
      rw [hsq]; exact h.1
    dot_01 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero]
      exact hmkDot b.l0 b.l1 0 0 L 0 (le_of_lt hl0) (le_of_lt hl1) (by rw [toR_zero]) (by rw [toR_zero]) it θ hθ
    dot_02 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_two, Matrix.cons_val_zero, sub_zero]
      exact hmkDot (mulLo b.l0 b.x0) (mulHi b.l1 b.x1) (mulLo b.l0 b.y0) (mulHi b.l1 b.y1)
        (L * pt.1) (L * pt.2) hqx0 hqx1 hqy0 hqy1 it θ hθ
    dot_10 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_one, Matrix.cons_val_zero, zero_sub, sub_self]
      exact hmkDot (-b.l1) (-b.l0) 0 0 (-L) 0 (by rw [toR_neg]; linarith) (by rw [toR_neg]; linarith)
        (by rw [toR_zero]) (by rw [toR_zero]) it θ hθ
    dot_12 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero]
      exact hmkDot (-mulHi b.l1 (S - b.x0)) (-mulLo b.l0 (S - b.x1)) (mulLo b.l0 b.y0) (mulHi b.l1 b.y1)
        (L * pt.1 - L) (L * pt.2) hr12x0 hr12x1 hqy0 hqy1 it θ hθ
    dot_20 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_two, Matrix.cons_val_zero, zero_sub]
      exact hmkDot (-mulHi b.l1 b.x1) (-mulLo b.l0 b.x0) (-mulHi b.l1 b.y1) (-mulLo b.l0 b.y0)
        (-(L * pt.1)) (-(L * pt.2)) (by rw [toR_neg]; linarith) (by rw [toR_neg]; linarith)
        (by rw [toR_neg]; linarith) (by rw [toR_neg]; linarith) it θ hθ
    dot_21 := fun it θ hθ => by
      unfold buildBoxGeom; rw [triVerts_1, triVerts_2]
      have h1 : (L, (0 : ℝ)).1 - (L * pt.1, L * pt.2).1 = -(L * pt.1 - L) := by dsimp only; ring
      have h2 : (L, (0 : ℝ)).2 - (L * pt.1, L * pt.2).2 = -(L * pt.2) := by dsimp only; ring
      rw [h1, h2]
      exact hmkDot (-(-mulLo b.l0 (S - b.x1))) (-(-mulHi b.l1 (S - b.x0))) (-mulHi b.l1 b.y1) (-mulLo b.l0 b.y0)
        (-(L * pt.1 - L)) (-(L * pt.2))
        (by rw [toR_neg]; linarith) (by rw [toR_neg]; linarith)
        (by rw [toR_neg]; linarith) (by rw [toR_neg]; linarith) it θ hθ
    dot_c0 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_zero, sub_zero]
      exact (hmkDot b.cx b.cx b.cy b.cy (toR b.cx) (toR b.cy) le_rfl le_rfl le_rfl le_rfl it θ hθ).2
    dot_c1 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero]
      exact (hmkDot (b.cx - b.l1) (b.cx - b.l0) b.cy b.cy (toR b.cx - L) (toR b.cy)
        (by rw [toR_sub]; linarith) (by rw [toR_sub]; linarith) le_rfl le_rfl it θ hθ).2
    dot_c2 := fun it θ hθ => by
      unfold buildBoxGeom triVerts; simp only [Matrix.cons_val_two]
      exact (hmkDot (b.cx - mulHi b.l1 b.x1) (b.cx - mulLo b.l0 b.x0)
        (b.cy - mulHi b.l1 b.y1) (b.cy - mulLo b.l0 b.y0) (toR b.cx - L * pt.1) (toR b.cy - L * pt.2)
        (by rw [toR_sub]; linarith) (by rw [toR_sub]; linarith)
        (by rw [toR_sub]; linarith) (by rw [toR_sub]; linarith) it θ hθ).2
  }

/-! ## Section 3: Polar Shell & Sector Loop Soundness (`levelPenaltyHi_sound`) -/

/-- Exact value of the inner survival upper bound `qHi` used inside `shellPenLoop`. -/
private def shellQHi (rho : Array Int) (rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin : Int) (ki : Nat) : Int :=
  let rk := rho.getD ki 0
  if rk == 0 then S
  else
    let g0 : Nat := if sb ≤ rk then 1 else 0
    let g1 : Nat := if dMaxA ≤ rk then 1 else 0
    let g2 : Nat := if dMaxB ≤ rk then 1 else 0
    let guar := g0 + g1 + g2
    if guar ≥ 2 then 0
    else
      let aRkLo := mulLo piLo (mulLo rk rk)
      let vc := max 0 (aRkLo - circleInterHi dcMin rk rEnc)
      let iu := circleInterHi sa rk rj + circleInterHi dMinA rk rj + circleInterHi dMinB rk rj
      let vu := max 0 (aRkLo - iu)
      let vLo := max vc vu
      let ev := expNegHi vLo
      if guar == 1 then ev else mulHi (S + vLo) ev

private lemma shellQHi_nonneg (rho : Array Int) (rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin : Int)
    (ki : Nat) :
    0 ≤ shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki := by
  unfold shellQHi
  dsimp only
  by_cases h0 : (rho.getD ki 0 == 0) = true
  · rw [if_pos h0]; decide
  · rw [if_neg h0]
    by_cases h1 : (if sb ≤ rho.getD ki 0 then 1 else 0) + (if dMaxA ≤ rho.getD ki 0 then 1 else 0) +
        (if dMaxB ≤ rho.getD ki 0 then 1 else 0) ≥ 2
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : (((if sb ≤ rho.getD ki 0 then 1 else 0) + (if dMaxA ≤ rho.getD ki 0 then 1 else 0) +
          (if dMaxB ≤ rho.getD ki 0 then 1 else 0)) == 1) = true
      · rw [if_pos h2]; exact expNegHi_nonneg' _
      · rw [if_neg h2]; exact mulHi_nonneg (by unfold S; omega) (expNegHi_nonneg' _)

/-- Soundness of the per-`(ki)` survival upper bound in `shellPenLoop`. -/
private lemma shellQHi_sound {rho w : Array Int} (hpot : ValidStepPot rho w)
    {P : Fin 3 → Pt} {C v : Pt} {rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin : Int}
    {u a b : Fin 3} (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (hrj_pos : 0 < rj) (hrEnc : 0 ≤ rEnc) (hsa_nn : 0 ≤ sa) (hdMinA_nn : 0 ≤ dMinA)
    (hdMinB_nn : 0 ≤ dMinB) (hdcMin_nn : 0 ≤ dcMin)
    (henc : triUnion P (toR rj) ⊆ disk C (toR rEnc))
    (hu_lo : toR sa ≤ euclidDist v (P u)) (hu_hi : euclidDist v (P u) ≤ toR sb)
    (ha_lo : toR dMinA ≤ euclidDist v (P a)) (ha_hi : euclidDist v (P a) ≤ toR dMaxA)
    (hb_lo : toR dMinB ≤ euclidDist v (P b)) (hb_hi : euclidDist v (P b) ≤ toR dMaxB)
    (hc_lo : toR dcMin ≤ euclidDist v C)
    (ki : Fin rho.size) :
    extSurvProb (triHitCount P v (toR (rho.getD ki.val 0)))
      (volume (disk v (toR (rho.getD ki.val 0)) \ triUnion P (toR rj))).toReal ≤
    toR (shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki.val) := by
  unfold shellQHi
  set rk := rho.getD ki.val 0
  have hrk_nn : 0 ≤ rk := hpot.rho_nonneg ki.isLt
  have hV_nn : 0 ≤ (volume (disk v (toR rk) \ triUnion P (toR rj))).toReal := ENNReal.toReal_nonneg
  dsimp only
  by_cases hrk0 : (rk == 0) = true
  · rw [if_pos hrk0, toR_S]; exact extSurvProb_le_one _ hV_nn
  · rw [if_neg hrk0]
    set g0 : Nat := if sb ≤ rk then 1 else 0
    set g1 : Nat := if dMaxA ≤ rk then 1 else 0
    set g2 : Nat := if dMaxB ≤ rk then 1 else 0
    set guar := g0 + g1 + g2
    -- Prove `guar ≤ triHitCount P v (toR rk)`!
    have hguar_le : guar ≤ triHitCount P v (toR rk) := by
      have huniv : (Finset.univ : Finset (Fin 3)) = {u, a, b} := by
        ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        omega
      have hcard : triHitCount P v (toR rk) =
          (if euclidDist v (P u) ≤ toR rk then 1 else 0) +
          (if euclidDist v (P a) ≤ toR rk then 1 else 0) +
          (if euclidDist v (P b) ≤ toR rk then 1 else 0) := by
        unfold triHitCount
        rw [huniv, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
        split_ifs <;> simp [hua, hub, hab, Finset.card_insert_of_notMem]
      have hg0 : g0 ≤ if euclidDist v (P u) ≤ toR rk then 1 else 0 := by
        dsimp only [g0]; split_ifs with h1 h2
        · exact le_rfl
        · exfalso; exact h2 (hu_hi.trans (toR_le_toR h1))
        · exact Nat.zero_le _
        · exact le_rfl
      have hg1 : g1 ≤ if euclidDist v (P a) ≤ toR rk then 1 else 0 := by
        dsimp only [g1]; split_ifs with h1 h2
        · exact le_rfl
        · exfalso; exact h2 (ha_hi.trans (toR_le_toR h1))
        · exact Nat.zero_le _
        · exact le_rfl
      have hg2 : g2 ≤ if euclidDist v (P b) ≤ toR rk then 1 else 0 := by
        dsimp only [g2]; split_ifs with h1 h2
        · exact le_rfl
        · exfalso; exact h2 (hb_hi.trans (toR_le_toR h1))
        · exact Nat.zero_le _
        · exact le_rfl
      dsimp only [guar]; omega
    by_cases hge2 : guar ≥ 2
    · rw [if_pos hge2, toR_zero]
      unfold extSurvProb; rw [if_pos (by omega)]
    · rw [if_neg hge2]
      set aRkLo := mulLo piLo (mulLo rk rk)
      set vc := max 0 (aRkLo - circleInterHi dcMin rk rEnc)
      set iu := circleInterHi sa rk rj + circleInterHi dMinA rk rj + circleInterHi dMinB rk rj
      set vu := max 0 (aRkLo - iu)
      set vLo := max vc vu
      set ev := expNegHi vLo
      have haRk_le : toR aRkLo ≤ Real.pi * (toR rk) ^ 2 := by
        have hsq : toR (mulLo rk rk) ≤ (toR rk) ^ 2 := by rw [sq]; exact mulLo_le
        calc toR aRkLo ≤ toR piLo * toR (mulLo rk rk) := mulLo_le
          _ ≤ Real.pi * (toR rk) ^ 2 :=
              mul_le_mul piLo_le_pi hsq (toR_nonneg (mulLo_nonneg hrk_nn hrk_nn)) (le_of_lt Real.pi_pos)
      -- Bound `toR vc ≤ V` via `triUnion ⊆ disk C rEnc`!
      have hvc_le : toR vc ≤ (volume (disk v (toR rk) \ triUnion P (toR rj))).toReal := by
        dsimp only [vc]; rw [toR_max, toR_zero]
        refine max_le hV_nn ?_
        have hfin_d : volume (disk v (toR rk)) ≠ ⊤ := by
          rw [volume_disk _ (toR_nonneg hrk_nn)]; exact ENNReal.ofReal_ne_top
        have hfin_diff : volume (disk v (toR rk) \ triUnion P (toR rj)) ≠ ⊤ :=
          ne_of_lt ((measure_mono Set.sdiff_subset).trans_lt (lt_top_iff_ne_top.mpr hfin_d))
        have hfin_int : volume (disk v (toR rk) ∩ disk C (toR rEnc)) ≠ ⊤ :=
          ne_of_lt ((measure_mono Set.inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin_d))
        have hcov : disk v (toR rk) ⊆ (disk v (toR rk) \ triUnion P (toR rj)) ∪ (disk v (toR rk) ∩ disk C (toR rEnc)) := by
          intro z hz
          by_cases hU : z ∈ triUnion P (toR rj)
          · exact Or.inr ⟨hz, henc hU⟩
          · exact Or.inl ⟨hz, hU⟩
        have hmeas_le : volume (disk v (toR rk)) ≤
            volume (disk v (toR rk) \ triUnion P (toR rj)) + volume (disk v (toR rk) ∩ disk C (toR rEnc)) :=
          (measure_mono hcov).trans (measure_union_le _ _)
        have hreal_le := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin_diff, hfin_int⟩) hmeas_le
        rw [ENNReal.toReal_add hfin_diff hfin_int, volume_disk _ (toR_nonneg hrk_nn),
            ENNReal.toReal_ofReal (by positivity),
            volume_disk_inter v C (toR_nonneg hrk_nn) (toR_nonneg hrEnc),
            ENNReal.toReal_ofReal (diskInterArea_nonneg (euclidDist v C) (toR rk) (toR rEnc))] at hreal_le
        have hinter_le : diskInterArea (euclidDist v C) (toR rk) (toR rEnc) ≤
            toR (circleInterHi dcMin rk rEnc) :=
          (diskInterArea_antitone_d (toR_nonneg hrk_nn) (toR_nonneg hrEnc) (toR_nonneg hdcMin_nn) hc_lo).trans
            (circleInterHi_sound hdcMin_nn hrk_nn hrEnc)
        rw [toR_sub]; linarith
      -- Bound `toR vu ≤ V` via `volume_disk_sdiff_union_ge_unionBound`!
      have hvu_le : toR vu ≤ (volume (disk v (toR rk) \ triUnion P (toR rj))).toReal := by
        dsimp only [vu]; rw [toR_max, toR_zero]
        refine max_le hV_nn ?_
        have hub_vol := volume_disk_sdiff_union_ge_unionBound P v (toR_nonneg (le_of_lt hrj_pos)) (toR_nonneg hrk_nn)
        have hfin_diff : volume (disk v (toR rk) \ triUnion P (toR rj)) ≠ ⊤ :=
          ne_of_lt ((measure_mono Set.sdiff_subset).trans_lt (by
            rw [volume_disk _ (toR_nonneg hrk_nn)]; exact ENNReal.ofReal_lt_top))
        have hub_real : Real.pi * (toR rk) ^ 2 - ∑ x : Fin 3, diskInterArea (euclidDist v (P x)) (toR rk) (toR rj) ≤
            (volume (disk v (toR rk) \ triUnion P (toR rj))).toReal := by
          by_cases hpos : 0 ≤ Real.pi * (toR rk) ^ 2 - ∑ x : Fin 3, diskInterArea (euclidDist v (P x)) (toR rk) (toR rj)
          · have h := ENNReal.toReal_mono hfin_diff hub_vol
            rwa [ENNReal.toReal_ofReal hpos] at h
          · linarith
        have hsum3 : (∑ x : Fin 3, diskInterArea (euclidDist v (P x)) (toR rk) (toR rj)) =
            diskInterArea (euclidDist v (P u)) (toR rk) (toR rj) +
            diskInterArea (euclidDist v (P a)) (toR rk) (toR rj) +
            diskInterArea (euclidDist v (P b)) (toR rk) (toR rj) := by
          have huniv : (Finset.univ : Finset (Fin 3)) = {u, a, b} := by
            ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]; omega
          rw [huniv, Finset.sum_insert (by simp [hua, hub]), Finset.sum_insert (by simp [hab]),
              Finset.sum_singleton]; ring
        have hiu_u : diskInterArea (euclidDist v (P u)) (toR rk) (toR rj) ≤ toR (circleInterHi sa rk rj) :=
          (diskInterArea_antitone_d (toR_nonneg hrk_nn) (toR_nonneg (le_of_lt hrj_pos)) (toR_nonneg hsa_nn) hu_lo).trans
            (circleInterHi_sound hsa_nn hrk_nn (le_of_lt hrj_pos))
        have hiu_a : diskInterArea (euclidDist v (P a)) (toR rk) (toR rj) ≤ toR (circleInterHi dMinA rk rj) :=
          (diskInterArea_antitone_d (toR_nonneg hrk_nn) (toR_nonneg (le_of_lt hrj_pos)) (toR_nonneg hdMinA_nn) ha_lo).trans
            (circleInterHi_sound hdMinA_nn hrk_nn (le_of_lt hrj_pos))
        have hiu_b : diskInterArea (euclidDist v (P b)) (toR rk) (toR rj) ≤ toR (circleInterHi dMinB rk rj) :=
          (diskInterArea_antitone_d (toR_nonneg hrk_nn) (toR_nonneg (le_of_lt hrj_pos)) (toR_nonneg hdMinB_nn) hb_lo).trans
            (circleInterHi_sound hdMinB_nn hrk_nn (le_of_lt hrj_pos))
        rw [toR_sub]; dsimp only [iu]; rw [toR_add, toR_add]; linarith
      have hvLo_nn : 0 ≤ vLo := le_max_of_le_left (le_max_left _ _)
      have hvLo_le : toR vLo ≤ (volume (disk v (toR rk) \ triUnion P (toR rj))).toReal := by
        dsimp only [vLo]; rw [toR_max]; exact max_le hvc_le hvu_le
      have hanti := extSurvProb_antitone hguar_le (toR_nonneg hvLo_nn) hvLo_le
      refine hanti.trans ?_
      have hev_ge : Real.exp (-toR vLo) ≤ toR ev := le_expNegHi hvLo_nn
      unfold extSurvProb
      rw [if_neg hge2]
      by_cases hg1 : guar = 1
      · simp only [hg1, ↓reduceIte, beq_self_eq_true]; exact hev_ge
      · have hbeq : (guar == 1) = false := by simp [hg1]
        rw [if_neg hg1, hbeq]; simp only [Bool.false_eq_true, ↓reduceIte]
        have h1 : (1 + toR vLo) * Real.exp (-toR vLo) ≤ toR (S + vLo) * toR ev := by
          rw [toR_add, toR_S]
          exact mul_le_mul_of_nonneg_left hev_ge (by linarith [toR_nonneg hvLo_nn])
        exact h1.trans le_mulHi

private lemma shellPenLoop_nondec (rho w : Array Int)
    (pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin : Int) :
    ∀ (ki : Nat) (p0 a0 : Int),
      a0 ≤ shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki p0 a0 := by
  intro ki
  induction hd : rho.size - ki generalizing ki with
  | zero =>
    intro p0 a0; rw [shellPenLoop, if_pos (by omega)]
  | succ d ih =>
    intro p0 a0
    rw [shellPenLoop, if_neg (by omega)]
    dsimp only
    by_cases hskip : pu + yj + w.getD ki 0 ≤ sa
    · rw [if_pos hskip]; exact ih (ki + 1) (by omega) p0 a0
    · rw [if_neg hskip]
      by_cases hpos : intDPosNum sa sb (pu + yj + w.getD ki 0) - intDPosNum sa sb (pu + yPrev + w.getD ki 0) - p0 > 0
      · rw [if_pos hpos]
        set da := intDPosNum sa sb (pu + yj + w.getD ki 0) - intDPosNum sa sb (pu + yPrev + w.getD ki 0) - p0
        have hq_nn : 0 ≤ shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki :=
          shellQHi_nonneg rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki
        have hda_nn : 0 ≤ (da + 999999) / 1000000 := Int.ediv_nonneg (by omega) (by decide)
        have hterm_nn : 0 ≤ (((da + 999999) / 1000000) *
            shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki + 999999) / 1000000 :=
          Int.ediv_nonneg (by nlinarith) (by decide)
        change a0 ≤ shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin (ki + 1) _
          (a0 + (((da + 999999) / 1000000) * shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki + 999999) / 1000000)
        exact (le_add_of_nonneg_right hterm_nn).trans (ih (ki + 1) (by omega) _ _)
      · rw [if_neg hpos]; exact ih (ki + 1) (by omega) _ a0

/-- Pure real-algebra soundness of `shellPenLoop`: bounds the finite sum over `k ≥ ki`
of exact radial integrals times `toR (shellQHi k)`. -/
private lemma shellPenLoop_sum_ge {rho w : Array Int} (hpot : ValidStepPot rho w)
    {pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin : Int}
    (hy : yPrev < yj) (hsa_nn : 0 ≤ sa) (hclear : pu + yj ≤ sa) (hsab : sa ≤ sb) :
    ∀ (ki : Nat) (acc : Int), ki ≤ rho.size →
      let prevInt := if ki = 0 then 0
        else intDPosNum sa sb (pu + yj + wPrev w ki) - intDPosNum sa sb (pu + yPrev + wPrev w ki)
      ∑ k ∈ Finset.univ.filter (fun x : Fin rho.size => ki ≤ x.val),
        (∫ s in (toR sa)..(toR sb), s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val) *
          toR (shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin k.val) ≤
        ((shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki prevInt acc - acc : Int) : ℝ) /
          (6 * (S : ℝ) ^ 2) := by
  intro ki acc hki
  have hint_diff : ∀ t : Int,
      ((intDPosNum sa sb (pu + yj + t) - intDPosNum sa sb (pu + yPrev + t) : Int) : ℝ) / (6 * (S : ℝ) ^ 3) =
      ∫ s in (toR sa)..(toR sb), s * (max 0 (toR pu + toR yj + toR t - s) -
        max 0 (toR pu + toR yPrev + toR t - s)) := by
    intro t
    have h1 := intDPosNum_eq (a := sa) (b := sb) (c := pu + yj + t) hsab
    have h2 := intDPosNum_eq (a := sa) (b := sb) (c := pu + yPrev + t) hsab
    simp only [toR_add] at h1 h2
    have hsub := intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun s : ℝ => s * max 0 (toR pu + toR yj + toR t - s)).intervalIntegrable (μ := volume) (toR sa) (toR sb))
      ((by fun_prop : Continuous fun s : ℝ => s * max 0 (toR pu + toR yPrev + toR t - s)).intervalIntegrable (μ := volume) (toR sa) (toR sb))
    push_cast; rw [sub_div, h1, h2, ← hsub]
    refine intervalIntegral.integral_congr fun s _ => by ring
  induction hn : rho.size - ki generalizing ki acc with
  | zero =>
    have hkeq : ki = rho.size := by omega
    subst hkeq
    dsimp only
    rw [shellPenLoop, if_pos le_rfl, sub_self, Int.cast_zero, zero_div]
    have hemp : (Finset.univ.filter fun x : Fin rho.size => rho.size ≤ x.val) = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
    simp [hemp]
  | succ m ih =>
    have hklt : ki < rho.size := by omega
    let kf : Fin rho.size := ⟨ki, hklt⟩
    dsimp only
    set prevInt := if ki = 0 then 0
      else intDPosNum sa sb (pu + yj + wPrev w ki) - intDPosNum sa sb (pu + yPrev + wPrev w ki)
    rw [shellPenLoop, if_neg (by omega)]
    dsimp only
    set wk := w.getD ki 0
    have hfilt_eq : (Finset.univ.filter fun x : Fin rho.size => ki ≤ x.val) =
        insert kf (Finset.univ.filter fun x : Fin rho.size => ki + 1 ≤ x.val) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff, kf]; omega
    have hnotmem : kf ∉ Finset.univ.filter (fun x : Fin rho.size => ki + 1 ≤ x.val) := by simp [kf]
    have hprev_eq_wPrev : prevInt =
        intDPosNum sa sb (pu + yj + wPrev w ki) - intDPosNum sa sb (pu + yPrev + wPrev w ki) := by
      dsimp only [prevInt]
      by_cases h0 : ki = 0
      · subst h0
        simp only [↓reduceIte, wPrev, add_zero]
        unfold intDPosNum
        rw [if_pos (by omega : pu + yj ≤ sa), if_pos (by omega : pu + yPrev ≤ sa), sub_self]
      · simp [h0]
    have hnext_prev : (if ki + 1 = 0 then 0
        else intDPosNum sa sb (pu + yj + wPrev w (ki + 1)) -
          intDPosNum sa sb (pu + yPrev + wPrev w (ki + 1))) =
        intDPosNum sa sb (pu + yj + wk) - intDPosNum sa sb (pu + yPrev + wk) := by
      simp [wPrev, wk]
    have hwp_le : wPrev w ki ≤ wk := by
      have := stepPot_dw_nonneg hpot kf
      rw [← toR_sub] at this; have := nonneg_of_toR_nonneg this
      dsimp only [kf] at this; dsimp only [wk]; omega
    rw [hfilt_eq, Finset.sum_insert hnotmem]
    by_cases hskip : pu + yj + wk ≤ sa
    · rw [if_pos hskip]
      have hcur0 : intDPosNum sa sb (pu + yj + wk) - intDPosNum sa sb (pu + yPrev + wk) = 0 := by
        unfold intDPosNum; rw [if_pos hskip, if_pos (by omega), sub_self]
      have hprev0 : prevInt = 0 := by
        rw [hprev_eq_wPrev]
        unfold intDPosNum; rw [if_pos (by omega), if_pos (by omega), sub_self]
      have hzero : ∫ s in (toR sa)..(toR sb), s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s ki = 0 := by
        have hcongr : ∫ s in (toR sa)..(toR sb), s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s ki =
            ∫ _ in (toR sa)..(toR sb), (0 : ℝ) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [Set.uIcc_of_le (toR_le_toR hsab)] at hs
          unfold triCrossCoeff
          have hs1 : toR pu + toR yj + toR wk ≤ s := by
            have := toR_le_toR hskip; rw [toR_add, toR_add] at this; linarith [hs.1]
          rw [max_eq_left (by linarith), max_eq_left (by linarith [toR_le_toR (le_of_lt hy)]),
              max_eq_left (by linarith [toR_le_toR hwp_le]),
              max_eq_left (by linarith [toR_le_toR (le_of_lt hy), toR_le_toR hwp_le])]
          ring
        rw [hcongr]; simp
      dsimp only [kf]; rw [hzero, zero_mul, zero_add]
      have hih := ih (ki + 1) acc (by omega) (by omega)
      rw [hnext_prev, hcur0] at hih
      rw [hprev0]; exact hih
    · rw [if_neg hskip]
      set curInt := intDPosNum sa sb (pu + yj + wk) - intDPosNum sa sb (pu + yPrev + wk)
      set da := curInt - prevInt
      set qHi := shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki
      set deltaAcc : Int := if da > 0 then (((da + 999999) / 1000000) * qHi + 999999) / 1000000 else 0
      set acc' := if da > 0 then acc + (((da + 999999) / 1000000) * qHi + 999999) / 1000000 else acc
      have hacc'_eq : acc' = acc + deltaAcc := by dsimp only [acc', deltaAcc]; split_ifs <;> ring
      have hda_eq : (da : ℝ) / (6 * (S : ℝ) ^ 3) =
          ∫ s in (toR sa)..(toR sb), s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s ki := by
        dsimp only [da, curInt]; rw [hprev_eq_wPrev]
        have h1 := hint_diff wk
        have h2 := hint_diff (wPrev w ki)
        have hcont : ∀ t : Int, Continuous (fun s : ℝ => s * (max 0 (toR pu + toR yj + toR t - s) -
            max 0 (toR pu + toR yPrev + toR t - s))) := fun t => by fun_prop
        have hsub := intervalIntegral.integral_sub
          ((hcont wk).intervalIntegrable (μ := volume) (toR sa) (toR sb))
          ((hcont (wPrev w ki)).intervalIntegrable (μ := volume) (toR sa) (toR sb))
        push_cast at h1 h2 ⊢; rw [sub_div, h1, h2, ← hsub]
        refine intervalIntegral.integral_congr fun s _ => ?_
        unfold triCrossCoeff; dsimp only [wk]; ring
      have hda_nn : 0 ≤ da := by
        have hint_nn : 0 ≤ ∫ s in (toR sa)..(toR sb), s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s ki :=
          intervalIntegral.integral_nonneg (toR_le_toR hsab) fun s hs =>
            mul_nonneg ((toR_nonneg hsa_nn).trans hs.1) (triCrossCoeff_nonneg hpot (toR_le_toR (le_of_lt hy)) kf)
        rw [← hda_eq] at hint_nn
        have hden : (0 : ℝ) < 6 * (S : ℝ) ^ 3 := mul_pos (by norm_num) (pow_pos S_pos 3)
        have : (0 : ℝ) ≤ (da : ℝ) := by
          by_contra hlt; push Not at hlt; linarith [div_neg_of_neg_of_pos hlt hden]
        exact_mod_cast this
      have hqHi_nn : 0 ≤ qHi := shellQHi_nonneg rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin ki
      have hterm_le :
          (∫ s in (toR sa)..(toR sb), s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s ki) * toR qHi ≤
          (deltaAcc : ℝ) / (6 * (S : ℝ) ^ 2) := by
        rw [← hda_eq]
        by_cases hda_pos : da > 0
        · have hdel : deltaAcc = (((da + 999999) / 1000000) * qHi + 999999) / 1000000 := by
            dsimp only [deltaAcc]; rw [if_pos hda_pos]
          rw [hdel]
          have h1 := real_div_le_int_cdiv (a := da) (b := 1000000) (by decide)
          rw [show da + 1000000 - 1 = da + 999999 by omega] at h1
          have h2 := real_div_le_int_cdiv (a := ((da + 999999) / 1000000) * qHi) (b := 1000000) (by decide)
          rw [show ((da + 999999) / 1000000) * qHi + 1000000 - 1 =
              ((da + 999999) / 1000000) * qHi + 999999 by omega] at h2
          have h3 : (da : ℝ) / (6 * (S : ℝ) ^ 3) * toR qHi ≤
              ((((da + 999999) / 1000000) * qHi : Int) : ℝ) / (1000000 : ℝ) / (6 * (S : ℝ) ^ 2) := by
            unfold toR S; push_cast at h1 ⊢
            have hqR : (0 : ℝ) ≤ (qHi : ℝ) := by exact_mod_cast hqHi_nn
            have hm := mul_le_mul_of_nonneg_right h1 hqR
            have hden : (0 : ℝ) < 6 * (1000000 : ℝ) ^ 3 := by norm_num
            have hdiv := div_le_div_of_nonneg_right hm (le_of_lt hden)
            linarith [show (da : ℝ) / (6 * (1000000 : ℝ) ^ 3) * ((qHi : ℝ) / 1000000) =
                ((da : ℝ) / 1000000 * (qHi : ℝ)) / (6 * (1000000 : ℝ) ^ 3) by ring,
              show ((((da + 999999) / 1000000 : Int) : ℝ) * (qHi : ℝ)) / 1000000 / (6 * (1000000 : ℝ) ^ 2) =
                ((((da + 999999) / 1000000 : Int) : ℝ) * (qHi : ℝ)) / (6 * (1000000 : ℝ) ^ 3) by ring]
          have h4 := div_le_div_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 6 * (S : ℝ) ^ 2)
          push_cast at h3 h4; linarith
        · have hda0 : da = 0 := by omega
          have hdel0 : deltaAcc = 0 := by dsimp only [deltaAcc]; rw [if_neg hda_pos]
          rw [hda0, hdel0]; simp
      have hih := ih (ki + 1) acc' (by omega) (by omega)
      rw [hnext_prev] at hih
      have htel :
          ((shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin (ki + 1) curInt acc' - acc : Int) : ℝ) /
            (6 * (S : ℝ) ^ 2) =
          (deltaAcc : ℝ) / (6 * (S : ℝ) ^ 2) +
          ((shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin (ki + 1) curInt acc' - acc' : Int) : ℝ) /
            (6 * (S : ℝ) ^ 2) := by
        rw [hacc'_eq]; push_cast; ring
      change _ ≤ ((shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin (ki + 1) curInt acc' - acc : Int) : ℝ) /
          (6 * (S : ℝ) ^ 2)
      rw [htel]
      dsimp only [kf]
      linarith

/-- Radial `lintegral` soundness of `shellPenLoop` on a single shell `[sa, sb]`. -/
private lemma shellPenLoop_lintegral_ge {rho w : Array Int} (hpot : ValidStepPot rho w)
    {P : Fin 3 → Pt} {C : Pt} {pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin : Int}
    {u a b : Fin 3} (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (hy : yPrev < yj) (hrj_pos : 0 < rj) (hclear : pu + yj ≤ rj) (hrj_sa : rj ≤ sa) (hsab : sa ≤ sb)
    (hrEnc : 0 ≤ rEnc) (hdMinA_nn : 0 ≤ dMinA) (hdMinB_nn : 0 ≤ dMinB) (hdcMin_nn : 0 ≤ dcMin)
    (henc : triUnion P (toR rj) ⊆ disk C (toR rEnc))
    {θ : ℝ}
    (hdist : ∀ s ∈ Ioo (toR sa) (toR sb),
      let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
      v ∉ triUnion P (toR rj) →
      toR dMinA ≤ euclidDist v (P a) ∧ euclidDist v (P a) ≤ toR dMaxA ∧
      toR dMinB ≤ euclidDist v (P b) ∧ euclidDist v (P b) ≤ toR dMaxB ∧
      toR dcMin ≤ euclidDist v C)
    (acc : Int) :
    ∫⁻ s in Ioo (toR sa) (toR sb),
      ENNReal.ofReal (
        let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
        if v ∉ triUnion P (toR rj) then
          s * ∑ k : Fin rho.size,
            triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
            extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
        else 0) ≤
    ENNReal.ofReal
      (((shellPenLoop rho w pu yPrev yj rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin 0 0 acc - acc : Int) : ℝ) /
        (6 * (S : ℝ) ^ 2)) := by
  have hsa_nn : 0 ≤ sa := by omega
  let upper : ℝ → ℝ := fun s =>
    s * ∑ k : Fin rho.size,
      triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
      toR (shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin k.val)
  have hpt : ∀ s ∈ Ioo (toR sa) (toR sb),
      ENNReal.ofReal (
        let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
        if v ∉ triUnion P (toR rj) then
          s * ∑ k : Fin rho.size,
            triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
            extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
        else 0) ≤ ENNReal.ofReal (upper s) := by
    intro s hs
    refine ENNReal.ofReal_le_ofReal ?_
    dsimp only [upper]
    have hs0 : 0 ≤ s := (toR_nonneg hsa_nn).trans (le_of_lt hs.1)
    by_cases hv : ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) ∉ triUnion P (toR rj)
    · rw [if_pos hv]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hs0
      have hdv := hdist s hs hv
      have hdu : euclidDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P u) = s := by
        unfold euclidDist sqDist
        have hcs := Real.cos_sq_add_sin_sq θ
        have hsq : ((P u).1 + s * Real.cos θ - (P u).1) ^ 2 +
            ((P u).2 + s * Real.sin θ - (P u).2) ^ 2 = s ^ 2 := by
          calc ((P u).1 + s * Real.cos θ - (P u).1) ^ 2 +
              ((P u).2 + s * Real.sin θ - (P u).2) ^ 2
              = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
            _ = s ^ 2 := by rw [hcs, mul_one]
        rw [hsq, Real.sqrt_sq hs0]
      exact mul_le_mul_of_nonneg_left
        (shellQHi_sound hpot hua hub hab hrj_pos hrEnc hsa_nn hdMinA_nn hdMinB_nn hdcMin_nn
          henc (by rw [hdu]; exact le_of_lt hs.1) (by rw [hdu]; exact le_of_lt hs.2)
          hdv.1 hdv.2.1 hdv.2.2.1 hdv.2.2.2.1 hdv.2.2.2.2 k)
        (triCrossCoeff_nonneg hpot (toR_le_toR (le_of_lt hy)) k)
    · rw [if_neg hv]
      exact mul_nonneg hs0 (Finset.sum_nonneg fun k _ =>
        mul_nonneg (triCrossCoeff_nonneg hpot (toR_le_toR (le_of_lt hy)) k)
          (toR_nonneg (shellQHi_nonneg _ _ _ _ _ _ _ _ _ _ _)))
  refine (setLIntegral_mono' measurableSet_Ioo hpt).trans ?_
  have hcont : Continuous upper := by
    dsimp only [upper]
    refine continuous_id.mul (continuous_finsetSum _ fun k _ => ?_)
    unfold triCrossCoeff; fun_prop
  have hnn : ∀ s ∈ Ioo (toR sa) (toR sb), 0 ≤ upper s := fun s hs =>
    mul_nonneg ((toR_nonneg hsa_nn).trans (le_of_lt hs.1)) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (triCrossCoeff_nonneg hpot (toR_le_toR (le_of_lt hy)) k)
        (toR_nonneg (shellQHi_nonneg _ _ _ _ _ _ _ _ _ _ _)))
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      (ae_restrict_of_forall_mem measurableSet_Ioo hnn),
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (toR_le_toR hsab)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpull : (∫ s in (toR sa)..(toR sb), upper s) =
      ∑ k : Fin rho.size,
        (∫ s in (toR sa)..(toR sb), s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val) *
          toR (shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin k.val) := by
    have hcongr : ∀ s, upper s = ∑ k : Fin rho.size,
        (s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val) *
          toR (shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin k.val) := fun s => by
      dsimp only [upper]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hcongr]
    rw [intervalIntegral.integral_finsetSum fun k _ =>
        ((by unfold triCrossCoeff; fun_prop : Continuous fun s : ℝ =>
          (s * triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val) *
            toR (shellQHi rho rj rEnc sa sb dMinA dMaxA dMinB dMaxB dcMin k.val)).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun k _ => intervalIntegral.integral_mul_const _ _
  rw [hpull]
  have hsum := shellPenLoop_sum_ge hpot (pu := pu) (rj := rj) (rEnc := rEnc) (dMinA := dMinA) (dMaxA := dMaxA)
    (dMinB := dMinB) (dMaxB := dMaxB) (dcMin := dcMin) hy hsa_nn (by omega) hsab 0 acc (Nat.zero_le _)
  simp only [Nat.zero_le, Finset.filter_true, ↓reduceIte] at hsum
  exact hsum

private lemma sectorShellsLoop_nondec (rho w : Array Int)
    (pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo : Int) :
    ∀ (kIdx : Nat) (sa acc : Int),
      acc ≤ sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo kIdx sa acc := by
  intro kIdx
  induction hd : rho.size + 1 - kIdx generalizing kIdx with
  | zero =>
    intro sa acc
    rw [sectorShellsLoop]
    by_cases h1 : sa ≥ sMax
    · rw [if_pos h1]
    · rw [if_neg h1, if_neg (by omega)]
      dsimp only
      rw [if_pos (Or.inr (by omega))]
      exact shellPenLoop_nondec rho w pu yPrev yj rj rEnc sa _ _ _ _ _ _ 0 0 acc
  | succ d ih =>
    intro sa acc
    rw [sectorShellsLoop]
    by_cases h1 : sa ≥ sMax
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : kIdx < rho.size ∧ rho.getD kIdx 0 ≤ sa
      · rw [if_pos h2]; exact ih (kIdx + 1) (by omega) sa acc
      · rw [if_neg h2]
        dsimp only
        have h3 := shellPenLoop_nondec rho w pu yPrev yj rj rEnc sa
          (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax))
          (max rj (sqrtSqLo (max 0 (max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) maHi) * max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) maHi) - 2 * max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) maHi) * maHi + q2aLo))))
          (sqrtSqHi (max 0 (max (sa * sa - 2 * sa * maLo + q2aHi) ((min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) * (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) - 2 * (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) * maLo + q2aHi))))
          (max rj (sqrtSqLo (max 0 (max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) mbHi) * max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) mbHi) - 2 * max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) mbHi) * mbHi + q2bLo))))
          (sqrtSqHi (max 0 (max (sa * sa - 2 * sa * mbLo + q2bHi) ((min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) * (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) - 2 * (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) * mbLo + q2bHi))))
          (sqrtSqLo (max 0 (max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) mch) * max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) mch) - 2 * max sa (min (min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax)) mch) * mch + cq2Lo)))
          0 0 acc
        by_cases h4 : min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax) ≥ sMax ∨ kIdx ≥ rho.size
        · rw [if_pos h4]; exact h3
        · rw [if_neg h4]; exact h3.trans (ih (kIdx + 1) (by omega) _ _)

/-- Soundness of `sectorShellsLoop` over the radial interval `(toR sa, toR sMax)`. -/
private lemma sectorShellsLoop_ge {rho w : Array Int} (hpot : ValidStepPot rho w)
    {P : Fin 3 → Pt} {C : Pt} {pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo : Int}
    {u a b : Fin 3} (hua : u ≠ a) (hub : u ≠ b) (hab : a ≠ b)
    (hy : yPrev < yj) (hrj_pos : 0 < rj) (hclear : pu + yj ≤ rj) (hrEnc : 0 ≤ rEnc)
    (henc : triUnion P (toR rj) ⊆ disk C (toR rEnc))
    {θ : ℝ}
    (hq2a : (q2aLo : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (P u) (P a) ∧ sqDist (P u) (P a) ≤ (q2aHi : ℝ) / (S : ℝ) ^ 2)
    (hq2b : (q2bLo : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (P u) (P b) ∧ sqDist (P u) (P b) ≤ (q2bHi : ℝ) / (S : ℝ) ^ 2)
    (hcq2 : (cq2Lo : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (P u) C)
    (hma : toR maLo ≤ ((P a).1 - (P u).1) * Real.cos θ + ((P a).2 - (P u).2) * Real.sin θ ∧
           ((P a).1 - (P u).1) * Real.cos θ + ((P a).2 - (P u).2) * Real.sin θ ≤ toR maHi)
    (hmb : toR mbLo ≤ ((P b).1 - (P u).1) * Real.cos θ + ((P b).2 - (P u).2) * Real.sin θ ∧
           ((P b).1 - (P u).1) * Real.cos θ + ((P b).2 - (P u).2) * Real.sin θ ≤ toR mbHi)
    (hmc : (C.1 - (P u).1) * Real.cos θ + (C.2 - (P u).2) * Real.sin θ ≤ toR mch) :
    ∀ (kIdx : Nat) (sa acc : Int), rj ≤ sa →
      ∫⁻ s in Ioo (toR sa) (toR sMax),
        ENNReal.ofReal (
          let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
          if v ∉ triUnion P (toR rj) then
            s * ∑ k : Fin rho.size,
              triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
              extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
          else 0) ≤
      ENNReal.ofReal
        (((sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo
            kIdx sa acc - acc : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) := by
  intro kIdx
  induction hd : rho.size + 1 - kIdx generalizing kIdx with
  | zero =>
    intro sa acc hsa
    rw [sectorShellsLoop]
    by_cases hge : sa ≥ sMax
    · rw [if_pos hge, sub_self, Int.cast_zero, zero_div, ENNReal.ofReal_zero]
      rw [Set.Ioo_eq_empty (not_lt.mpr (toR_le_toR hge))]; simp
    · rw [if_neg hge, if_neg (by omega)]
      dsimp only
      have hsb_eq : min sMax (if kIdx < rho.size then rho.getD kIdx 0 else sMax) = sMax := by
        rw [if_neg (by omega), min_self]
      rw [if_pos (Or.inr (by omega)), hsb_eq]
      have hsa_nn : 0 ≤ sa := by omega
      have hsab : sa ≤ sMax := by omega
      refine shellPenLoop_lintegral_ge hpot hua hub hab hy hrj_pos hclear hsa hsab hrEnc
        (le_max_of_le_left (le_of_lt hrj_pos)) (le_max_of_le_left (le_of_lt hrj_pos))
        (sqrtSqLo_nonneg _) henc (fun s hs hv => ?_) acc
      have hsqA : sqDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P a) =
          s ^ 2 - 2 * s * (((P a).1 - (P u).1) * Real.cos θ + ((P a).2 - (P u).2) * Real.sin θ) +
            sqDist (P u) (P a) := by
        rw [sqDist_polar_shift]; unfold sqDist; ring
      have hsqB : sqDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P b) =
          s ^ 2 - 2 * s * (((P b).1 - (P u).1) * Real.cos θ + ((P b).2 - (P u).2) * Real.sin θ) +
            sqDist (P u) (P b) := by
        rw [sqDist_polar_shift]; unfold sqDist; ring
      have hsqC : sqDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) C =
          s ^ 2 - 2 * s * ((C.1 - (P u).1) * Real.cos θ + (C.2 - (P u).2) * Real.sin θ) +
            sqDist (P u) C := by
        rw [sqDist_polar_shift]; unfold sqDist; ring
      have hqA := quad_bounds_on_Icc (toR_nonneg hsa_nn) (le_of_lt hs.1) (le_of_lt hs.2)
        hma.1 hma.2 hq2a.1 hq2a.2
      have hqB := quad_bounds_on_Icc (toR_nonneg hsa_nn) (le_of_lt hs.1) (le_of_lt hs.2)
        hmb.1 hmb.2 hq2b.1 hq2b.2
      have hqC := (quad_bounds_on_Icc (toR_nonneg hsa_nn) (le_of_lt hs.1) (le_of_lt hs.2)
        (le_rfl : ((C.1 - (P u).1) * Real.cos θ + (C.2 - (P u).2) * Real.sin θ) ≤ _) hmc hcq2 le_rfl).1
      have hcast_quad : ∀ (x m q : Int),
          (toR x) ^ 2 - 2 * toR x * toR m + (q : ℝ) / (S : ℝ) ^ 2 =
            ((x * x - 2 * x * m + q : Int) : ℝ) / (S : ℝ) ^ 2 := by
        intro x m q; unfold toR; push_cast; ring
      have hsqrt_lo : ∀ (d2 : Int) (val : ℝ), 0 ≤ val → (d2 : ℝ) / (S : ℝ) ^ 2 ≤ val →
          toR (sqrtSqLo (max 0 d2)) ≤ Real.sqrt val := by
        intro d2 val hval hd2
        refine (sqrtSqLo_le (max 0 d2)).trans (Real.sqrt_le_sqrt ?_)
        rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ))]
        simp only [Int.cast_zero, zero_div]
        exact max_le hval hd2
      have hsqrt_hi : ∀ (d2 : Int) (val : ℝ), val ≤ (d2 : ℝ) / (S : ℝ) ^ 2 →
          Real.sqrt val ≤ toR (sqrtSqHi (max 0 d2)) := by
        intro d2 val hd2
        refine (Real.sqrt_le_sqrt ?_).trans (le_sqrtSqHi (max 0 d2))
        rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ))]
        simp only [Int.cast_zero, zero_div]
        exact hd2.trans (le_max_right _ _)
      have hstar : ∀ (m : Int), toR (max sa (min sMax m)) = max (toR sa) (min (toR sMax) (toR m)) := by
        intro m; rw [toR_max, toR_min]
      have houtA : toR rj ≤ euclidDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P a) := by
        by_contra hlt; push Not at hlt
        exact hv (Set.mem_iUnion.mpr ⟨a, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp (le_of_lt hlt)⟩)
      have houtB : toR rj ≤ euclidDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P b) := by
        by_contra hlt; push Not at hlt
        exact hv (Set.mem_iUnion.mpr ⟨b, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp (le_of_lt hlt)⟩)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [toR_max]; refine max_le houtA ?_
        unfold euclidDist; rw [hsqA]
        refine hsqrt_lo _ _ (hsqA ▸ sqDist_nonneg _ _) ?_
        rw [← hcast_quad, hstar]; exact hqA.1
      · unfold euclidDist; rw [hsqA]
        refine hsqrt_hi _ _ ?_
        rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ)), ← hcast_quad, ← hcast_quad]
        exact hqA.2
      · rw [toR_max]; refine max_le houtB ?_
        unfold euclidDist; rw [hsqB]
        refine hsqrt_lo _ _ (hsqB ▸ sqDist_nonneg _ _) ?_
        rw [← hcast_quad, hstar]; exact hqB.1
      · unfold euclidDist; rw [hsqB]
        refine hsqrt_hi _ _ ?_
        rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ)), ← hcast_quad, ← hcast_quad]
        exact hqB.2
      · unfold euclidDist; rw [hsqC]
        refine hsqrt_lo _ _ (hsqC ▸ sqDist_nonneg _ _) ?_
        rw [← hcast_quad, hstar]; exact hqC
  | succ d ih =>
    intro sa acc hsa
    rw [sectorShellsLoop]
    by_cases hge : sa ≥ sMax
    · rw [if_pos hge, sub_self, Int.cast_zero, zero_div, ENNReal.ofReal_zero]
      rw [Set.Ioo_eq_empty (not_lt.mpr (toR_le_toR hge))]; simp
    · rw [if_neg hge]
      by_cases hskip : kIdx < rho.size ∧ rho.getD kIdx 0 ≤ sa
      · rw [if_pos hskip]; exact ih (kIdx + 1) (by omega) sa acc hsa
      · rw [if_neg hskip]
        dsimp only
        set nextRho := if kIdx < rho.size then rho.getD kIdx 0 else sMax
        set sb := min sMax nextRho
        have hsa_nn : 0 ≤ sa := by omega
        have hsab : sa ≤ sb := by
          dsimp only [sb, nextRho]
          by_cases hk : kIdx < rho.size
          · rw [if_pos hk]; have : sa < rho.getD kIdx 0 := by omega
            exact le_min (by omega) (le_of_lt this)
          · rw [if_neg hk, min_self]; omega
        have hsb_le : sb ≤ sMax := min_le_left _ _
        -- Bounds on shell `[sa, sb]`
        have hdist_shell : ∀ s ∈ Ioo (toR sa) (toR sb),
            let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
            v ∉ triUnion P (toR rj) →
            toR (max rj (sqrtSqLo (max 0 (max sa (min sb maHi) * max sa (min sb maHi) - 2 * max sa (min sb maHi) * maHi + q2aLo)))) ≤
              euclidDist v (P a) ∧
            euclidDist v (P a) ≤
              toR (sqrtSqHi (max 0 (max (sa * sa - 2 * sa * maLo + q2aHi) (sb * sb - 2 * sb * maLo + q2aHi)))) ∧
            toR (max rj (sqrtSqLo (max 0 (max sa (min sb mbHi) * max sa (min sb mbHi) - 2 * max sa (min sb mbHi) * mbHi + q2bLo)))) ≤
              euclidDist v (P b) ∧
            euclidDist v (P b) ≤
              toR (sqrtSqHi (max 0 (max (sa * sa - 2 * sa * mbLo + q2bHi) (sb * sb - 2 * sb * mbLo + q2bHi)))) ∧
            toR (sqrtSqLo (max 0 (max sa (min sb mch) * max sa (min sb mch) - 2 * max sa (min sb mch) * mch + cq2Lo))) ≤
              euclidDist v C := by
          intro s hs
          dsimp only
          intro hv
          have hsqA : sqDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P a) =
              s ^ 2 - 2 * s * (((P a).1 - (P u).1) * Real.cos θ + ((P a).2 - (P u).2) * Real.sin θ) +
                sqDist (P u) (P a) := by rw [sqDist_polar_shift]; unfold sqDist; ring
          have hsqB : sqDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P b) =
              s ^ 2 - 2 * s * (((P b).1 - (P u).1) * Real.cos θ + ((P b).2 - (P u).2) * Real.sin θ) +
                sqDist (P u) (P b) := by rw [sqDist_polar_shift]; unfold sqDist; ring
          have hsqC : sqDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) C =
              s ^ 2 - 2 * s * ((C.1 - (P u).1) * Real.cos θ + (C.2 - (P u).2) * Real.sin θ) +
                sqDist (P u) C := by rw [sqDist_polar_shift]; unfold sqDist; ring
          have hqA := quad_bounds_on_Icc (toR_nonneg hsa_nn) (le_of_lt hs.1) (le_of_lt hs.2)
            hma.1 hma.2 hq2a.1 hq2a.2
          have hqB := quad_bounds_on_Icc (toR_nonneg hsa_nn) (le_of_lt hs.1) (le_of_lt hs.2)
            hmb.1 hmb.2 hq2b.1 hq2b.2
          have hqC := (quad_bounds_on_Icc (toR_nonneg hsa_nn) (le_of_lt hs.1) (le_of_lt hs.2)
            (le_rfl : ((C.1 - (P u).1) * Real.cos θ + (C.2 - (P u).2) * Real.sin θ) ≤ _) hmc hcq2 le_rfl).1
          have hcast_quad : ∀ (x m q : Int),
              (toR x) ^ 2 - 2 * toR x * toR m + (q : ℝ) / (S : ℝ) ^ 2 =
                ((x * x - 2 * x * m + q : Int) : ℝ) / (S : ℝ) ^ 2 := by
            intro x m q; unfold toR; push_cast; ring
          have hsqrt_lo : ∀ (d2 : Int) (val : ℝ), 0 ≤ val → (d2 : ℝ) / (S : ℝ) ^ 2 ≤ val →
              toR (sqrtSqLo (max 0 d2)) ≤ Real.sqrt val := by
            intro d2 val hval hd2
            refine (sqrtSqLo_le (max 0 d2)).trans (Real.sqrt_le_sqrt ?_)
            rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ))]
            simp only [Int.cast_zero, zero_div]; exact max_le hval hd2
          have hsqrt_hi : ∀ (d2 : Int) (val : ℝ), val ≤ (d2 : ℝ) / (S : ℝ) ^ 2 →
              Real.sqrt val ≤ toR (sqrtSqHi (max 0 d2)) := by
            intro d2 val hd2
            refine (Real.sqrt_le_sqrt ?_).trans (le_sqrtSqHi (max 0 d2))
            rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ))]
            simp only [Int.cast_zero, zero_div]; exact hd2.trans (le_max_right _ _)
          have hstar : ∀ (m : Int), toR (max sa (min sb m)) = max (toR sa) (min (toR sb) (toR m)) := by
            intro m; rw [toR_max, toR_min]
          have houtA : toR rj ≤ euclidDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P a) := by
            by_contra hlt; push Not at hlt
            exact hv (Set.mem_iUnion.mpr ⟨a, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp (le_of_lt hlt)⟩)
          have houtB : toR rj ≤ euclidDist ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ) (P b) := by
            by_contra hlt; push Not at hlt
            exact hv (Set.mem_iUnion.mpr ⟨b, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp (le_of_lt hlt)⟩)
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [toR_max]; refine max_le houtA ?_
            unfold euclidDist; rw [hsqA]; refine hsqrt_lo _ _ (hsqA ▸ sqDist_nonneg _ _) ?_
            rw [← hcast_quad, hstar]; exact hqA.1
          · unfold euclidDist; rw [hsqA]; refine hsqrt_hi _ _ ?_
            rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ)), ← hcast_quad, ← hcast_quad]
            exact hqA.2
          · rw [toR_max]; refine max_le houtB ?_
            unfold euclidDist; rw [hsqB]; refine hsqrt_lo _ _ (hsqB ▸ sqDist_nonneg _ _) ?_
            rw [← hcast_quad, hstar]; exact hqB.1
          · unfold euclidDist; rw [hsqB]; refine hsqrt_hi _ _ ?_
            rw [Int.cast_max, ← max_div_div_right (sq_nonneg (S : ℝ)), ← hcast_quad, ← hcast_quad]
            exact hqB.2
          · unfold euclidDist; rw [hsqC]; refine hsqrt_lo _ _ (hsqC ▸ sqDist_nonneg _ _) ?_
            rw [← hcast_quad, hstar]; exact hqC
        set acc' := shellPenLoop rho w pu yPrev yj rj rEnc sa sb
          (max rj (sqrtSqLo (max 0 (max sa (min sb maHi) * max sa (min sb maHi) - 2 * max sa (min sb maHi) * maHi + q2aLo))))
          (sqrtSqHi (max 0 (max (sa * sa - 2 * sa * maLo + q2aHi) (sb * sb - 2 * sb * maLo + q2aHi))))
          (max rj (sqrtSqLo (max 0 (max sa (min sb mbHi) * max sa (min sb mbHi) - 2 * max sa (min sb mbHi) * mbHi + q2bLo))))
          (sqrtSqHi (max 0 (max (sa * sa - 2 * sa * mbLo + q2bHi) (sb * sb - 2 * sb * mbLo + q2bHi))))
          (sqrtSqLo (max 0 (max sa (min sb mch) * max sa (min sb mch) - 2 * max sa (min sb mch) * mch + cq2Lo)))
          0 0 acc
        have hshell := shellPenLoop_lintegral_ge hpot hua hub hab hy hrj_pos hclear hsa hsab hrEnc
          (le_max_of_le_left (le_of_lt hrj_pos)) (le_max_of_le_left (le_of_lt hrj_pos))
          (sqrtSqLo_nonneg _) henc hdist_shell acc
        by_cases hdone : sb ≥ sMax ∨ kIdx ≥ rho.size
        · rw [if_pos hdone]
          have hsb_eq : sb = sMax := by
            rcases hdone with h1 | h2
            · omega
            · dsimp only [sb, nextRho]; rw [if_neg (by omega), min_self]
          rw [← hsb_eq]; exact hshell
        · rw [if_neg hdone]
          rw [setLIntegral_Ioo_split (toR_le_toR hsab) (toR_le_toR hsb_le)]
          have hrest := ih (kIdx + 1) (by omega) sb acc' (by omega)
          have hacc'_ge : acc ≤ acc' := shellPenLoop_nondec _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 0 acc
          have hres_ge : acc' ≤ sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch
              q2aLo q2aHi q2bLo q2bHi cq2Lo (kIdx + 1) sb acc' :=
            sectorShellsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (kIdx + 1) sb acc'
          refine (add_le_add hshell hrest).trans ?_
          rw [← ENNReal.ofReal_add
            (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hacc'_ge) (by positivity))
            (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hres_ge) (by positivity))]
          refine ENNReal.ofReal_le_ofReal ?_
          push_cast; exact le_of_eq (by ring)

private lemma vertexSectorsLoop_nondec (rho w : Array Int) (g : BoxGeom) (nT u : Nat)
    (pu yPrev yj rj rEnc sMax : Int) :
    ∀ (it : Nat) (acc : Int),
      acc ≤ vertexSectorsLoop rho w g nT u pu yPrev yj rj rEnc sMax it acc := by
  intro it
  induction hd : nT - it generalizing it with
  | zero =>
    intro acc; rw [vertexSectorsLoop, if_pos (by omega)]
  | succ d ih =>
    intro acc
    rw [vertexSectorsLoop, if_neg (by omega)]
    dsimp only
    set maLo := if u == 0 then g.mLo01.getD it 0 else if u == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0
    set mbLo := if u == 0 then g.mLo02.getD it 0 else if u == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0
    set q2aHi := if u == 0 then g.q2Hi01 else if u == 1 then g.q2Hi01 else g.q2Hi02
    set q2bHi := if u == 0 then g.q2Hi02 else if u == 1 then g.q2Hi12 else g.q2Hi12
    set sStart := max rj (max (if maLo * maLo + rj * rj - q2aHi > 0 then maLo + sqrtSqLo (maLo * maLo + rj * rj - q2aHi) else rj)
        (if mbLo * mbLo + rj * rj - q2bHi > 0 then mbLo + sqrtSqLo (mbLo * mbLo + rj * rj - q2bHi) else rj))
    by_cases hlt : sStart < sMax
    · rw [if_pos hlt]
      exact (sectorShellsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ acc).trans
        (ih (it + 1) (by omega) _)
    · rw [if_neg hlt]; exact ih (it + 1) (by omega) acc

/-- Soundness of `vertexSectorsLoop` over angular range `θ ∈ Ioo (it * 2π/40) (2π)` for one vertex `u`. -/
private lemma vertexSectorsLoop_ge {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {L : ℝ} {pt : Pt} (hmem : (L, pt) ∈ boxRegion b)
    {g : BoxGeom} (hg : BoxGeomSound rho w b g L pt)
    {u : Fin 3} {pu yPrev yj rj : Int}
    (hy : yPrev < yj) (hrj_l1 : b.l1 < rj) (hclear : pu + yj ≤ rj) :
    let wMax := w.getD (rho.size - 1) 0
    let sMax := pu + yj + wMax
    let rEnc := rj + g.radB
    ∀ (it : Nat) (acc : Int), it ≤ 40 →
      ∫⁻ θ in Ioo ((it : ℝ) * (2 * Real.pi / 40)) (2 * Real.pi),
        ∫⁻ s in Ioi (0 : ℝ),
          ENNReal.ofReal (
            let P := triVerts L pt
            let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
            if v ∉ triUnion P (toR rj) then
              s * ∑ k : Fin rho.size,
                triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
                extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                  (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
            else 0) ≤
      ENNReal.ofReal
        (toR angleTable40.dtHi *
          (((vertexSectorsLoop rho w g 40 u.val pu yPrev yj rj rEnc sMax it acc - acc : Int) : ℝ) /
            (6 * (S : ℝ) ^ 2))) := by
  intro wMax sMax rEnc
  have hql := boxRegion_mem_quarterLens hb hmem
  have hrj_pos : 0 < rj := by have := hb.l0_pos; have := hb.l0_lt_l1; omega
  have hrEnc_nn : 0 ≤ rEnc := by dsimp only [rEnc]; linarith [hg.radB_nn]
  have henc : triUnion (triVerts L pt) (toR rj) ⊆ disk (toR b.cx, toR b.cy) (toR rEnc) := by
    intro v hv
    rcases Set.mem_iUnion.mp hv with ⟨x, hx⟩
    have hx' : euclidDist v (triVerts L pt x) ≤ toR rj :=
      (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mpr hx
    exact (euclidDist_le_iff (toR_nonneg hrEnc_nn)).mp <|
      calc euclidDist v (toR b.cx, toR b.cy)
          ≤ euclidDist v (triVerts L pt x) + euclidDist (triVerts L pt x) (toR b.cx, toR b.cy) :=
            euclidDist_triangle _ _ _
        _ ≤ toR rj + toR g.radB := add_le_add hx' (hg.enc_le x)
        _ = toR rEnc := by dsimp only [rEnc]; rw [toR_add]
  have hdt_le : 2 * Real.pi / 40 ≤ toR angleTable40.dtHi := angleTable40_sound.1
  have hdt_nn : 0 ≤ toR angleTable40.dtHi := le_trans (by positivity) hdt_le
  -- Every edge length of `triVerts L pt` is `≤ L < toR rj`.
  have hedge_le : ∀ x y : Fin 3, euclidDist (triVerts L pt x) (triVerts L pt y) ≤ toR rj := by
    have hL_nn : 0 ≤ L := (toR_nonneg (le_of_lt hb.l0_pos)).trans (le_of_lt hmem.1)
    have hL_lt : L < toR rj := hmem.2.1.trans (toR_lt_toR hrj_l1)
    have hd01 : euclidDist (triVerts L pt 0) (triVerts L pt 1) = L := by
      rw [triVerts_0, triVerts_1]; unfold euclidDist sqDist; simp [Real.sqrt_sq hL_nn]
    have hd02 : euclidDist (triVerts L pt 0) (triVerts L pt 2) ≤ L := by
      rw [triVerts_0, triVerts_2]; unfold euclidDist sqDist
      have hsq : ((0 : ℝ) - L * pt.1) ^ 2 + ((0 : ℝ) - L * pt.2) ^ 2 = L ^ 2 * (pt.1 ^ 2 + pt.2 ^ 2) := by ring
      have h1 : pt.1 ^ 2 + pt.2 ^ 2 ≤ 1 := by nlinarith [hql.2.1, hql.2.2.1, hql.2.2.2.2]
      dsimp only; rw [hsq]; refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1 (sq_nonneg L))).trans ?_
      rw [mul_one, Real.sqrt_sq hL_nn]
    have hd12 : euclidDist (triVerts L pt 1) (triVerts L pt 2) ≤ L := by
      rw [triVerts_1, triVerts_2]; unfold euclidDist sqDist
      have hsq : (L - L * pt.1) ^ 2 + ((0 : ℝ) - L * pt.2) ^ 2 = L ^ 2 * ((1 - pt.1) ^ 2 + pt.2 ^ 2) := by ring
      dsimp only; rw [hsq]; refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (le_of_lt hql.2.2.2.2) (sq_nonneg L))).trans ?_
      rw [mul_one, Real.sqrt_sq hL_nn]
    intro x y
    have h01 : euclidDist (triVerts L pt 0) (triVerts L pt 1) ≤ toR rj := hd01.le.trans (le_of_lt hL_lt)
    have h02 : euclidDist (triVerts L pt 0) (triVerts L pt 2) ≤ toR rj := hd02.trans (le_of_lt hL_lt)
    have h12 : euclidDist (triVerts L pt 1) (triVerts L pt 2) ≤ toR rj := hd12.trans (le_of_lt hL_lt)
    fin_cases x <;> fin_cases y
    · rw [euclidDist_self]; exact toR_nonneg (le_of_lt hrj_pos)
    · exact h01
    · exact h02
    · rw [euclidDist_symm]; exact h01
    · rw [euclidDist_self]; exact toR_nonneg (le_of_lt hrj_pos)
    · exact h12
    · rw [euclidDist_symm]; exact h02
    · rw [euclidDist_symm]; exact h12
    · rw [euclidDist_self]; exact toR_nonneg (le_of_lt hrj_pos)
  -- Helper for one sector `it : Fin 40` and fixed `θ` in sector `it`:
  -- bounds the inner radial `Ioi 0` integral by the `sectorShellsLoop` increment!
  have hsector_inner : ∀ (it : Fin 40) (acc : Int) {θ : ℝ},
      θ ∈ Ioo ((it.val : ℝ) * (2 * Real.pi / 40)) (((it.val + 1 : Nat) : ℝ) * (2 * Real.pi / 40)) →
      let q2aLo := if u.val == 0 then g.q2Lo01 else if u.val == 1 then g.q2Lo01 else g.q2Lo02
      let q2aHi := if u.val == 0 then g.q2Hi01 else if u.val == 1 then g.q2Hi01 else g.q2Hi02
      let q2bLo := if u.val == 0 then g.q2Lo02 else if u.val == 1 then g.q2Lo12 else g.q2Lo12
      let q2bHi := if u.val == 0 then g.q2Hi02 else if u.val == 1 then g.q2Hi12 else g.q2Hi12
      let cq2Lo := if u.val == 0 then g.cq2Lo0 else if u.val == 1 then g.cq2Lo1 else g.cq2Lo2
      let maLo := if u.val == 0 then g.mLo01.getD it.val 0 else if u.val == 1 then g.mLo10.getD it.val 0 else g.mLo20.getD it.val 0
      let maHi := if u.val == 0 then g.mHi01.getD it.val 0 else if u.val == 1 then g.mHi10.getD it.val 0 else g.mHi20.getD it.val 0
      let mbLo := if u.val == 0 then g.mLo02.getD it.val 0 else if u.val == 1 then g.mLo12.getD it.val 0 else g.mLo21.getD it.val 0
      let mbHi := if u.val == 0 then g.mHi02.getD it.val 0 else if u.val == 1 then g.mHi12.getD it.val 0 else g.mHi21.getD it.val 0
      let mch := if u.val == 0 then g.mcHi0.getD it.val 0 else if u.val == 1 then g.mcHi1.getD it.val 0 else g.mcHi2.getD it.val 0
      let r2 := rj * rj
      let discA := maLo * maLo + r2 - q2aHi
      let sA := if discA > 0 then maLo + sqrtSqLo discA else rj
      let discB := mbLo * mbLo + r2 - q2bHi
      let sB := if discB > 0 then mbLo + sqrtSqLo discB else rj
      let sStart := max rj (max sA sB)
      let acc' :=
        if sStart < sMax then
          sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo
            0 sStart acc
        else acc
      ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (
          let P := triVerts L pt
          let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
          if v ∉ triUnion P (toR rj) then
            s * ∑ k : Fin rho.size,
              triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
              extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
          else 0) ≤
      ENNReal.ofReal (((acc' - acc : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) := by
    intro it acc θ hθ q2aLo q2aHi q2bLo q2bHi cq2Lo maLo maHi mbLo mbHi mch r2 discA sA discB sB sStart acc'
    -- Pick the two other vertices `(a, b)` for `u` and unpack `hg`!
    let a : Fin 3 := if u = 0 then 1 else 0
    let b' : Fin 3 := if u = 2 then 1 else 2
    have hua : u ≠ a := by fin_cases u <;> decide
    have hub : u ≠ b' := by fin_cases u <;> decide
    have hab : a ≠ b' := by fin_cases u <;> decide
    have hq2a : (q2aLo : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt u) (triVerts L pt a) ∧
        sqDist (triVerts L pt u) (triVerts L pt a) ≤ (q2aHi : ℝ) / (S : ℝ) ^ 2 := by
      fin_cases u
      · exact hg.q2_01
      · change (g.q2Lo01 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 1) (triVerts L pt 0) ∧
            sqDist (triVerts L pt 1) (triVerts L pt 0) ≤ (g.q2Hi01 : ℝ) / (S : ℝ) ^ 2
        rw [sqDist_symm]; exact hg.q2_01
      · change (g.q2Lo02 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 2) (triVerts L pt 0) ∧
            sqDist (triVerts L pt 2) (triVerts L pt 0) ≤ (g.q2Hi02 : ℝ) / (S : ℝ) ^ 2
        rw [sqDist_symm]; exact hg.q2_02
    have hq2b : (q2bLo : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt u) (triVerts L pt b') ∧
        sqDist (triVerts L pt u) (triVerts L pt b') ≤ (q2bHi : ℝ) / (S : ℝ) ^ 2 := by
      fin_cases u
      · exact hg.q2_02
      · exact hg.q2_12
      · change (g.q2Lo12 : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt 2) (triVerts L pt 1) ∧
            sqDist (triVerts L pt 2) (triVerts L pt 1) ≤ (g.q2Hi12 : ℝ) / (S : ℝ) ^ 2
        rw [sqDist_symm]; exact hg.q2_12
    have hcq2 : (cq2Lo : ℝ) / (S : ℝ) ^ 2 ≤ sqDist (triVerts L pt u) (toR b.cx, toR b.cy) := by
      fin_cases u
      · exact hg.cq2_0
      · exact hg.cq2_1
      · exact hg.cq2_2
    have hma : toR maLo ≤ ((triVerts L pt a).1 - (triVerts L pt u).1) * Real.cos θ +
        ((triVerts L pt a).2 - (triVerts L pt u).2) * Real.sin θ ∧
        ((triVerts L pt a).1 - (triVerts L pt u).1) * Real.cos θ +
        ((triVerts L pt a).2 - (triVerts L pt u).2) * Real.sin θ ≤ toR maHi := by
      fin_cases u
      · exact hg.dot_01 it θ hθ
      · exact hg.dot_10 it θ hθ
      · exact hg.dot_20 it θ hθ
    have hmb : toR mbLo ≤ ((triVerts L pt b').1 - (triVerts L pt u).1) * Real.cos θ +
        ((triVerts L pt b').2 - (triVerts L pt u).2) * Real.sin θ ∧
        ((triVerts L pt b').1 - (triVerts L pt u).1) * Real.cos θ +
        ((triVerts L pt b').2 - (triVerts L pt u).2) * Real.sin θ ≤ toR mbHi := by
      fin_cases u
      · exact hg.dot_02 it θ hθ
      · exact hg.dot_12 it θ hθ
      · exact hg.dot_21 it θ hθ
    have hmc : (toR b.cx - (triVerts L pt u).1) * Real.cos θ +
        (toR b.cy - (triVerts L pt u).2) * Real.sin θ ≤ toR mch := by
      fin_cases u
      · exact hg.dot_c0 it θ hθ
      · exact hg.dot_c1 it θ hθ
      · exact hg.dot_c2 it θ hθ
    -- Show the integrand vanishes outside `Ioo (toR sStart) (toR sMax)`!
    have hvanish : ∀ s ∈ Ioi (0 : ℝ), s ∉ Ioo (toR sStart) (toR sMax) →
        ENNReal.ofReal (
          let P := triVerts L pt
          let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
          if v ∉ triUnion P (toR rj) then
            s * ∑ k : Fin rho.size,
              triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
              extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
          else 0) = 0 := by
      intro s hs hnot
      rw [ENNReal.ofReal_eq_zero]
      dsimp only
      by_cases hv : ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ) ∉
          triUnion (triVerts L pt) (toR rj)
      · rw [if_pos hv]
        have hs_gt_rj : toR rj < s := by
          by_contra hle; push Not at hle
          have hdu : euclidDist ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ)
              (triVerts L pt u) = s := by
            unfold euclidDist sqDist
            have hcs := Real.cos_sq_add_sin_sq θ
            have hsq : ((triVerts L pt u).1 + s * Real.cos θ - (triVerts L pt u).1) ^ 2 +
                ((triVerts L pt u).2 + s * Real.sin θ - (triVerts L pt u).2) ^ 2 = s ^ 2 := by
              calc _ = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
                _ = s ^ 2 := by rw [hcs, mul_one]
            rw [hsq, Real.sqrt_sq (le_of_lt hs)]
          exact hv (Set.mem_iUnion.mpr ⟨u, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp (by rw [hdu]; exact hle)⟩)
        have hs_gt_sA : toR sA < s := by
          dsimp only [sA]
          split_ifs with hda
          · have houtA : (toR rj) ^ 2 <
                s ^ 2 - 2 * s * (((triVerts L pt a).1 - (triVerts L pt u).1) * Real.cos θ +
                  ((triVerts L pt a).2 - (triVerts L pt u).2) * Real.sin θ) +
                sqDist (triVerts L pt u) (triVerts L pt a) := by
              have h1 : toR rj < euclidDist ((triVerts L pt u).1 + s * Real.cos θ,
                  (triVerts L pt u).2 + s * Real.sin θ) (triVerts L pt a) := by
                by_contra hle; push Not at hle
                exact hv (Set.mem_iUnion.mpr ⟨a, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp hle⟩)
              have hnnA := euclidDist_nonneg ((triVerts L pt u).1 + s * Real.cos θ,
                (triVerts L pt u).2 + s * Real.sin θ) (triVerts L pt a)
              have hsq := sq_lt_sq' (by linarith [toR_nonneg (le_of_lt hrj_pos), hnnA]) h1
              rw [euclidDist_sq, sqDist_polar_shift] at hsq
              have hsym : ((triVerts L pt a).1 - (triVerts L pt u).1) ^ 2 +
                  ((triVerts L pt a).2 - (triVerts L pt u).2) ^ 2 = sqDist (triVerts L pt u) (triVerts L pt a) := by
                unfold sqDist; ring
              linarith
            have hmrA : toR maLo ≤ toR rj := by
              have hdot := dot_le_euclidNorm
                ((triVerts L pt a).1 - (triVerts L pt u).1, (triVerts L pt a).2 - (triVerts L pt u).2) θ
              have hnorm : euclidNorm ((triVerts L pt a).1 - (triVerts L pt u).1,
                  (triVerts L pt a).2 - (triVerts L pt u).2) = euclidDist (triVerts L pt a) (triVerts L pt u) := rfl
              linarith [hma.1, hdot, hnorm, hedge_le a u]
            have hex := exit_radius_bound (toR_nonneg (le_of_lt hrj_pos)) hs_gt_rj houtA hma.1 hq2a.2 hmrA
            have hrt : toR (sqrtSqLo discA) ≤
                Real.sqrt ((toR maLo) ^ 2 + (toR rj) ^ 2 - (q2aHi : ℝ) / (S : ℝ) ^ 2) := by
              refine (sqrtSqLo_le discA).trans (Real.sqrt_le_sqrt ?_)
              dsimp only [discA, r2]; unfold toR; push_cast; ring_nf; exact le_rfl
            rw [toR_add]; linarith
          · exact hs_gt_rj
        have hs_gt_sB : toR sB < s := by
          dsimp only [sB]
          split_ifs with hdb
          · have houtB : (toR rj) ^ 2 <
                s ^ 2 - 2 * s * (((triVerts L pt b').1 - (triVerts L pt u).1) * Real.cos θ +
                  ((triVerts L pt b').2 - (triVerts L pt u).2) * Real.sin θ) +
                sqDist (triVerts L pt u) (triVerts L pt b') := by
              have h1 : toR rj < euclidDist ((triVerts L pt u).1 + s * Real.cos θ,
                  (triVerts L pt u).2 + s * Real.sin θ) (triVerts L pt b') := by
                by_contra hle; push Not at hle
                exact hv (Set.mem_iUnion.mpr ⟨b', (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp hle⟩)
              have hnnB := euclidDist_nonneg ((triVerts L pt u).1 + s * Real.cos θ,
                (triVerts L pt u).2 + s * Real.sin θ) (triVerts L pt b')
              have hsq := sq_lt_sq' (by linarith [toR_nonneg (le_of_lt hrj_pos), hnnB]) h1
              rw [euclidDist_sq, sqDist_polar_shift] at hsq
              have hsym : ((triVerts L pt b').1 - (triVerts L pt u).1) ^ 2 +
                  ((triVerts L pt b').2 - (triVerts L pt u).2) ^ 2 = sqDist (triVerts L pt u) (triVerts L pt b') := by
                unfold sqDist; ring
              linarith
            have hmrB : toR mbLo ≤ toR rj := by
              have hdot := dot_le_euclidNorm
                ((triVerts L pt b').1 - (triVerts L pt u).1, (triVerts L pt b').2 - (triVerts L pt u).2) θ
              have hnorm : euclidNorm ((triVerts L pt b').1 - (triVerts L pt u).1,
                  (triVerts L pt b').2 - (triVerts L pt u).2) = euclidDist (triVerts L pt b') (triVerts L pt u) := rfl
              linarith [hmb.1, hdot, hnorm, hedge_le b' u]
            have hex := exit_radius_bound (toR_nonneg (le_of_lt hrj_pos)) hs_gt_rj houtB hmb.1 hq2b.2 hmrB
            have hrt : toR (sqrtSqLo discB) ≤
                Real.sqrt ((toR mbLo) ^ 2 + (toR rj) ^ 2 - (q2bHi : ℝ) / (S : ℝ) ^ 2) := by
              refine (sqrtSqLo_le discB).trans (Real.sqrt_le_sqrt ?_)
              dsimp only [discB, r2]; unfold toR; push_cast; ring_nf; exact le_rfl
            rw [toR_add]; linarith
          · exact hs_gt_rj
        have hs_gt_start : toR sStart < s := by
          dsimp only [sStart]; rw [toR_max, toR_max]; exact max_lt hs_gt_rj (max_lt hs_gt_sA hs_gt_sB)
        have hs_ge_sMax : toR sMax ≤ s := by
          by_contra hlt; push Not at hlt; exact hnot ⟨hs_gt_start, hlt⟩
        set vPt : Pt := ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ)
        have hsum0 : ∑ k : Fin rho.size,
            triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
            extSurvProb (triHitCount (triVerts L pt) vPt (toR (rho.getD k.val 0)))
              (volume (disk vPt (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          have hwk_le : w.getD k.val 0 ≤ wMax := hpot.w_le_of_le (by omega) (by have := hpot.size_pos; omega)
          have hwp_le : wPrev w k.val ≤ wMax := by
            have := stepPot_dw_nonneg hpot k; rw [← toR_sub] at this
            have := nonneg_of_toR_nonneg this; omega
          have hs1 : toR pu + toR yj + toR wMax ≤ s := by
            dsimp only [sMax] at hs_ge_sMax; rw [toR_add, toR_add] at hs_ge_sMax; exact hs_ge_sMax
          have htc0 : triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val = 0 := by
            unfold triCrossCoeff
            rw [max_eq_left (by linarith [toR_le_toR hwk_le]),
                max_eq_left (by linarith [toR_le_toR hwk_le, toR_le_toR (le_of_lt hy)]),
                max_eq_left (by linarith [toR_le_toR hwp_le]),
                max_eq_left (by linarith [toR_le_toR hwp_le, toR_le_toR (le_of_lt hy)])]
            ring
          rw [htc0, zero_mul]
        rw [hsum0, mul_zero]
      · rw [if_neg hv]
    have hstart_pos : 0 < toR sStart :=
      (by rw [← toR_zero]; exact toR_lt_toR hrj_pos : (0 : ℝ) < toR rj).trans_le (toR_le_toR (le_max_left _ _))
    have hsub : Ioo (toR sStart) (toR sMax) ⊆ Ioi (0 : ℝ) :=
      fun s hs => hstart_pos.trans hs.1
    have hrestrict : ∫⁻ s in Ioi (0 : ℝ),
        ENNReal.ofReal (
          let P := triVerts L pt
          let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
          if v ∉ triUnion P (toR rj) then
            s * ∑ k : Fin rho.size,
              triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
              extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
          else 0) =
        ∫⁻ s in Ioo (toR sStart) (toR sMax),
          ENNReal.ofReal (
            let P := triVerts L pt
            let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
            if v ∉ triUnion P (toR rj) then
              s * ∑ k : Fin rho.size,
                triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
                extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                  (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
            else 0) := by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
      refine lintegral_congr fun s => ?_
      by_cases hs1 : s ∈ Ioo (toR sStart) (toR sMax)
      · rw [Set.indicator_of_mem (hsub hs1), Set.indicator_of_mem hs1]
      · rw [Set.indicator_of_notMem hs1]
        by_cases hs0 : s ∈ Ioi (0 : ℝ)
        · rw [Set.indicator_of_mem hs0]; exact hvanish s hs0 hs1
        · rw [Set.indicator_of_notMem hs0]
    rw [hrestrict]
    dsimp only [acc']
    by_cases hlt : sStart < sMax
    · rw [if_pos hlt]
      exact sectorShellsLoop_ge hpot hua hub hab hy hrj_pos hclear hrEnc_nn henc
        hq2a hq2b hcq2 hma hmb hmc 0 sStart acc (le_max_left _ _)
    · rw [if_neg hlt, sub_self, Int.cast_zero, zero_div, ENNReal.ofReal_zero]
      rw [Set.Ioo_eq_empty (not_lt.mpr (toR_le_toR (not_lt.mp hlt)))]; simp
  -- Induction on `40 - it`!
  intro it acc hit
  induction hd : 40 - it generalizing it acc with
  | zero =>
    have hieq : it = 40 := by omega
    subst hieq
    rw [vertexSectorsLoop, if_pos le_rfl, sub_self, Int.cast_zero, zero_div, mul_zero, ENNReal.ofReal_zero]
    have h2pi : (40 : ℝ) * (2 * Real.pi / 40) = 2 * Real.pi := by ring
    rw [Nat.cast_ofNat, h2pi, Set.Ioo_self]; simp
  | succ d ih =>
    have hilt : it < 40 := by omega
    rw [vertexSectorsLoop, if_neg (by omega)]
    dsimp only
    have hsplit_le1 : (it : ℝ) * (2 * Real.pi / 40) ≤ ((it + 1 : Nat) : ℝ) * (2 * Real.pi / 40) := by
      push_cast; nlinarith [Real.pi_pos]
    have hsplit_le2 : ((it + 1 : Nat) : ℝ) * (2 * Real.pi / 40) ≤ 2 * Real.pi := by
      have : (it + 1 : ℝ) ≤ 40 := by exact_mod_cast (show it + 1 ≤ 40 by omega)
      push_cast; nlinarith [Real.pi_pos]
    rw [setLIntegral_Ioo_split hsplit_le1 hsplit_le2]
    set acc' :=
      let q2aLo := if u.val == 0 then g.q2Lo01 else if u.val == 1 then g.q2Lo01 else g.q2Lo02
      let q2aHi := if u.val == 0 then g.q2Hi01 else if u.val == 1 then g.q2Hi01 else g.q2Hi02
      let q2bLo := if u.val == 0 then g.q2Lo02 else if u.val == 1 then g.q2Lo12 else g.q2Lo12
      let q2bHi := if u.val == 0 then g.q2Hi02 else if u.val == 1 then g.q2Hi12 else g.q2Hi12
      let cq2Lo := if u.val == 0 then g.cq2Lo0 else if u.val == 1 then g.cq2Lo1 else g.cq2Lo2
      let maLo := if u.val == 0 then g.mLo01.getD it 0 else if u.val == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0
      let maHi := if u.val == 0 then g.mHi01.getD it 0 else if u.val == 1 then g.mHi10.getD it 0 else g.mHi20.getD it 0
      let mbLo := if u.val == 0 then g.mLo02.getD it 0 else if u.val == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0
      let mbHi := if u.val == 0 then g.mHi02.getD it 0 else if u.val == 1 then g.mHi12.getD it 0 else g.mHi21.getD it 0
      let mch := if u.val == 0 then g.mcHi0.getD it 0 else if u.val == 1 then g.mcHi1.getD it 0 else g.mcHi2.getD it 0
      let r2 := rj * rj
      let discA := maLo * maLo + r2 - q2aHi
      let sA := if discA > 0 then maLo + sqrtSqLo discA else rj
      let discB := mbLo * mbLo + r2 - q2bHi
      let sB := if discB > 0 then mbLo + sqrtSqLo discB else rj
      let sStart := max rj (max sA sB)
      if sStart < sMax then
        sectorShellsLoop rho w pu yPrev yj rj rEnc sMax maLo maHi mbLo mbHi mch q2aLo q2aHi q2bLo q2bHi cq2Lo
          0 sStart acc
      else acc
    have hacc'_ge : acc ≤ acc' := by
      dsimp only [acc']
      by_cases hlt :
          max rj (max (if (if u.val == 0 then g.mLo01.getD it 0 else if u.val == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0) *
                (if u.val == 0 then g.mLo01.getD it 0 else if u.val == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0) +
                rj * rj - (if u.val == 0 then g.q2Hi01 else if u.val == 1 then g.q2Hi01 else g.q2Hi02) > 0 then
              (if u.val == 0 then g.mLo01.getD it 0 else if u.val == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0) +
                sqrtSqLo ((if u.val == 0 then g.mLo01.getD it 0 else if u.val == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0) *
                  (if u.val == 0 then g.mLo01.getD it 0 else if u.val == 1 then g.mLo10.getD it 0 else g.mLo20.getD it 0) +
                  rj * rj - (if u.val == 0 then g.q2Hi01 else if u.val == 1 then g.q2Hi01 else g.q2Hi02))
            else rj)
            (if (if u.val == 0 then g.mLo02.getD it 0 else if u.val == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0) *
                (if u.val == 0 then g.mLo02.getD it 0 else if u.val == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0) +
                rj * rj - (if u.val == 0 then g.q2Hi02 else if u.val == 1 then g.q2Hi12 else g.q2Hi12) > 0 then
              (if u.val == 0 then g.mLo02.getD it 0 else if u.val == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0) +
                sqrtSqLo ((if u.val == 0 then g.mLo02.getD it 0 else if u.val == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0) *
                  (if u.val == 0 then g.mLo02.getD it 0 else if u.val == 1 then g.mLo12.getD it 0 else g.mLo21.getD it 0) +
                  rj * rj - (if u.val == 0 then g.q2Hi02 else if u.val == 1 then g.q2Hi12 else g.q2Hi12))
            else rj)) < sMax
      · rw [if_pos hlt]; exact sectorShellsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 _ acc
      · rw [if_neg hlt]
    have hfin_ge : acc' ≤ vertexSectorsLoop rho w g 40 u.val pu yPrev yj rj rEnc sMax (it + 1) acc' :=
      vertexSectorsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ (it + 1) acc'
    have h1 :
        ∫⁻ θ in Ioo ((it : ℝ) * (2 * Real.pi / 40)) (((it + 1 : Nat) : ℝ) * (2 * Real.pi / 40)),
          ∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (
              let P := triVerts L pt
              let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
              if v ∉ triUnion P (toR rj) then
                s * ∑ k : Fin rho.size,
                  triCrossCoeff w (toR pu) (toR yPrev) (toR yj) s k.val *
                  extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                    (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
              else 0) ≤
        ENNReal.ofReal (toR angleTable40.dtHi * (((acc' - acc : Int) : ℝ) / (6 * (S : ℝ) ^ 2))) := by
      refine (setLIntegral_mono' measurableSet_Ioo fun θ hθ =>
        hsector_inner ⟨it, hilt⟩ acc hθ).trans ?_
      rw [setLIntegral_const, Real.volume_Ioo]
      have hlen : (((it + 1 : Nat) : ℝ) * (2 * Real.pi / 40) - (it : ℝ) * (2 * Real.pi / 40)) =
          2 * Real.pi / 40 := by push_cast; ring
      rw [hlen, ← ENNReal.ofReal_mul (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hacc'_ge) (by positivity))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hdt_le (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hacc'_ge) (by positivity))
    have h2 := ih (it + 1) acc' (by omega) (by omega)
    refine (add_le_add h1 h2).trans ?_
    rw [← ENNReal.ofReal_add
      (mul_nonneg hdt_nn (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hacc'_ge) (by positivity)))
      (mul_nonneg hdt_nn (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hfin_ge) (by positivity)))]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast; exact le_of_eq (by ring)

/-- Auxiliary: `evalStepPot` is nonnegative and monotone on a `ValidStepPot`. -/
private lemma evalStepPot_nonneg {rho w : Array Int} (hpot : ValidStepPot rho w) (m : Int) :
    0 ≤ evalStepPot rho w m := by
  have h := stepPot_le_evalStepPot hpot (r := toR m) le_rfl
  exact nonneg_of_toR_nonneg ((stepPot_nonneg hpot _).trans h)

private lemma evalStepPot_mono {rho w : Array Int} (hpot : ValidStepPot rho w) {m₁ m₂ : Int}
    (hm : m₁ ≤ m₂) : evalStepPot rho w m₁ ≤ evalStepPot rho w m₂ := by
  have h1 := evalStepPotAux_eq hpot m₁ 0 (Nat.zero_le _) (fun _ hj => absurd hj (Nat.not_lt_zero _))
  have h2 := evalStepPotAux_eq hpot m₂ 0 (Nat.zero_le _) (fun _ hj => absurd hj (Nat.not_lt_zero _))
  unfold evalStepPot
  simp only [↓reduceIte] at h1 h2
  rw [h1, h2]
  by_cases he1 : ∃ k : Nat, k < rho.size ∧ rho.getD k 0 < m₁
  · have he2 : ∃ k : Nat, k < rho.size ∧ rho.getD k 0 < m₂ := by
      rcases he1 with ⟨k1, hk1, hlt1⟩; exact ⟨k1, hk1, lt_of_lt_of_le hlt1 hm⟩
    rw [if_pos he1, if_pos he2]
    rcases he1 with ⟨k1, hk1, hlt1⟩
    have hsub : (Finset.range rho.size).filter (fun k => rho.getD k 0 < m₁) ⊆
        (Finset.range rho.size).filter (fun k => rho.getD k 0 < m₂) := by
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hr, hl⟩
      exact Finset.mem_filter.mpr ⟨hr, lt_of_lt_of_le hl hm⟩
    have hcard := Finset.card_le_card hsub
    have hcard2_le : ((Finset.range rho.size).filter (fun k => rho.getD k 0 < m₂)).card ≤ rho.size :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by rw [Finset.card_range])
    have hcard1_pos : 0 < ((Finset.range rho.size).filter (fun k => rho.getD k 0 < m₁)).card :=
      Finset.card_pos.mpr ⟨k1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk1, hlt1⟩⟩
    exact hpot.w_le_of_le (by omega) (by omega)
  · rw [if_neg he1]
    by_cases he2 : ∃ k : Nat, k < rho.size ∧ rho.getD k 0 < m₂
    · rw [if_pos he2]
      rcases he2 with ⟨k2, hk2, hlt2⟩
      have hcard2_le : ((Finset.range rho.size).filter (fun k => rho.getD k 0 < m₂)).card ≤ rho.size :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans (by rw [Finset.card_range])
      have hcard2_pos : 0 < ((Finset.range rho.size).filter (fun k => rho.getD k 0 < m₂)).card :=
        Finset.card_pos.mpr ⟨k2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk2, hlt2⟩⟩
      exact hpot.w_nonneg (by omega)
    · rw [if_neg he2]

private lemma levelPenaltyHi_nonneg (rho w : Array Int) (ang : AngleTable) (g : BoxGeom)
    (wMax yPrev rj yj : Int) (hdt : 0 ≤ ang.dtHi) :
    0 ≤ levelPenaltyHi rho w ang g wMax yPrev rj yj := by
  unfold levelPenaltyHi
  by_cases h1 : 2 * wMax ≤ rj
  · rw [if_pos h1]
  · rw [if_neg h1]
    dsimp only
    set p0 := if g.pi01Max + yj + wMax > rj then
        vertexSectorsLoop rho w g ang.nT 0 g.pi01Max yPrev yj rj (rj + g.radB) (g.pi01Max + yj + wMax) 0 0 else 0
    set p1 := if g.pi01Max + yj + wMax > rj then
        vertexSectorsLoop rho w g ang.nT 1 g.pi01Max yPrev yj rj (rj + g.radB) (g.pi01Max + yj + wMax) 0 p0 else p0
    set p2 := if g.pi2Max + yj + wMax > rj then
        vertexSectorsLoop rho w g ang.nT 2 g.pi2Max yPrev yj rj (rj + g.radB) (g.pi2Max + yj + wMax) 0 p1 else p1
    have hp0 : 0 ≤ p0 := by
      dsimp only [p0]; split_ifs
      · exact vertexSectorsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ 0 0
      · exact le_rfl
    have hp1 : 0 ≤ p1 := by
      dsimp only [p1]; split_ifs
      · exact hp0.trans (vertexSectorsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ 0 p0)
      · exact hp0
    have hp2 : 0 ≤ p2 := by
      dsimp only [p2]; split_ifs
      · exact hp1.trans (vertexSectorsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ 0 p1)
      · exact hp1
    exact Int.ediv_nonneg (by nlinarith) (by decide)

/-- Soundness of `levelPenaltyHi`: for every canonical triangle `(L, pt) ∈ boxRegion b`,
`levelCrossPen rho w yPrev rj yj L pt ≤ toR (levelPenaltyHi ...)`. -/
lemma levelPenaltyHi_sound {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) {L : ℝ} {pt : Pt} (hmem : (L, pt) ∈ boxRegion b)
    {yPrev rj yj : Int} (_hyPrev_nn : 0 ≤ yPrev) (hy : yPrev < yj)
    (hrj_l1 : b.l1 < rj)
    (hhalf : 2 * ((buildBoxGeom rho w angleTable40 b).pi01Max + yj) ≤ rj) :
    let g := buildBoxGeom rho w angleTable40 b
    let wMax := w.getD (rho.size - 1) 0
    levelCrossPen rho w yPrev rj yj L pt ≤ toR (levelPenaltyHi rho w angleTable40 g wMax yPrev rj yj) := by
  intro g wMax
  have hg := buildBoxGeom_sound hpot hb hmem
  have hrj_pos : 0 < rj := by have := hb.l0_pos; have := hb.l0_lt_l1; omega
  have hpi01_nn : 0 ≤ g.pi01Max := evalStepPot_nonneg hpot _
  have hpi2_nn : 0 ≤ g.pi2Max := evalStepPot_nonneg hpot _
  have hpi2_le_01 : g.pi2Max ≤ g.pi01Max := by
    dsimp only [g, buildBoxGeom]
    have hsq_le : (S - b.x0) * (S - b.x0) + b.y1 * b.y1 ≤ S * S := hb.in_quarterLens
    have hrt_le : sqrtSqHi ((S - b.x0) * (S - b.x0) + b.y1 * b.y1) ≤ S := by
      set n := (S - b.x0) * (S - b.x0) + b.y1 * b.y1
      unfold sqrtSqHi
      by_cases hle0 : n ≤ 0
      · rw [if_pos hle0]; unfold S; omega
      · rw [if_neg hle0]
        dsimp only
        have hn_le : n.toNat ≤ 1000000 * 1000000 := by
          have : n ≤ 1000000 * 1000000 := by unfold S at hsq_le; exact hsq_le
          omega
        have hnat_le : natSqrt n.toNat ≤ 1000000 := by
          by_contra hgt; push Not at hgt
          have hsq := (natSqrt_spec n.toNat).1
          have hge : 1000001 * 1000001 ≤ n.toNat := (Nat.mul_le_mul hgt hgt).trans hsq
          omega
        by_cases heq : (natSqrt n.toNat * natSqrt n.toNat == n.toNat) = true
        · rw [if_pos heq]; rw [Int.ofNat_eq_natCast]; unfold S; omega
        · rw [if_neg heq]; rw [Int.ofNat_eq_natCast]
          have hlt : natSqrt n.toNat < 1000000 := by
            by_contra hge
            have he : natSqrt n.toNat = 1000000 := by omega
            have hsq := (natSqrt_spec n.toNat).1
            rw [he] at hsq
            have hbeq : (natSqrt n.toNat * natSqrt n.toNat == n.toNat) = true := by
              rw [he]; exact beq_iff_eq.mpr (by omega)
            exact heq hbeq
          unfold S; omega
    have hd12_le : mulHi b.l1 (sqrtSqHi ((S - b.x0) * (S - b.x0) + b.y1 * b.y1)) ≤ b.l1 := by
      have hl1_nn : 0 ≤ b.l1 := by have := hb.l0_pos; have := hb.l0_lt_l1; omega
      have hmul_le : b.l1 * sqrtSqHi ((S - b.x0) * (S - b.x0) + b.y1 * b.y1) ≤ b.l1 * S :=
        Int.mul_le_mul_of_nonneg_left hrt_le hl1_nn
      unfold mulHi
      have : (b.l1 * sqrtSqHi ((S - b.x0) * (S - b.x0) + b.y1 * b.y1) + S - 1) / S ≤
          (b.l1 * S + S - 1) / S := Int.ediv_le_ediv (by decide) (by omega)
      have hS_eq : (b.l1 * S + S - 1) / S = b.l1 := by unfold S; omega
      omega
    exact (evalStepPot_mono hpot hd12_le).trans (le_of_eq hb.pi01_eq.symm)
  have hclear01 : g.pi01Max + yj ≤ rj := by dsimp only [g] at hhalf ⊢; omega
  have hclear2 : g.pi2Max + yj ≤ rj := by omega
  have hpen_nn : 0 ≤ toR (levelPenaltyHi rho w angleTable40 g wMax yPrev rj yj) :=
    toR_nonneg (levelPenaltyHi_nonneg rho w angleTable40 g wMax yPrev rj yj (by unfold angleTable40; decide))
  -- Apply `setIntegral_le_of_setLIntegral_le`!
  have hA_meas : MeasurableSet (triUnion (triVerts L pt) (toR rj))ᶜ :=
    MeasurableSet.compl (MeasurableSet.iUnion fun u => measurableSet_disk _ _)
  have hF_nn : ∀ v ∈ (triUnion (triVerts L pt) (toR rj))ᶜ,
      0 ≤ ∑ u : Fin 3, ∑ k : Fin rho.size,
        triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
          (euclidDist v (triVerts L pt u)) k.val *
        extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
          (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal :=
    fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (triCrossCoeff_nonneg hpot (toR_le_toR (le_of_lt hy)) k)
        (extSurvProb_nonneg _ ENNReal.toReal_nonneg)
  unfold levelCrossPen
  refine setIntegral_le_of_setLIntegral_le hA_meas hF_nn hpen_nn ?_
  -- Branch on `2 * wMax ≤ rj`
  unfold levelPenaltyHi
  by_cases h2w : 2 * wMax ≤ rj
  · rw [if_pos h2w, toR_zero, ENNReal.ofReal_zero]
    have hzero : ∀ v ∈ (triUnion (triVerts L pt) (toR rj))ᶜ,
        ENNReal.ofReal (∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) = 0 := by
      intro v hv
      rw [ENNReal.ofReal_eq_zero]
      have hsum0 : (∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) = 0 := by
        refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun k _ => ?_
        have hdu : toR rj < euclidDist v (triVerts L pt u) := by
          by_contra hle; push Not at hle
          exact hv (Set.mem_iUnion.mpr ⟨u, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp hle⟩)
        have hpu_le : triVertPot rho w L pt u ≤ toR g.pi01Max := by
          fin_cases u
          · exact hg.p0_le
          · exact hg.p1_le
          · exact hg.p2_le.trans (toR_le_toR hpi2_le_01)
        have hwk_le : w.getD k.val 0 ≤ wMax := hpot.w_le_of_le (by omega) (by have := hpot.size_pos; omega)
        have hwp_le : wPrev w k.val ≤ wMax := by
          have := stepPot_dw_nonneg hpot k; rw [← toR_sub] at this
          have := nonneg_of_toR_nonneg this; omega
        have hbd : triVertPot rho w L pt u + toR yj + toR wMax ≤ toR rj := by
          have h1 : toR g.pi01Max + toR yj ≤ toR rj / 2 := by
            have := toR_le_toR hhalf; rw [toR_mul_int, toR_add] at this; push_cast at this; linarith
          have h2 : toR wMax ≤ toR rj / 2 := by
            have := toR_le_toR h2w; rw [toR_mul_int] at this; push_cast at this; linarith
          linarith
        have htc0 : triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val = 0 := by
          unfold triCrossCoeff
          rw [max_eq_left (by linarith [toR_le_toR hwk_le]),
              max_eq_left (by linarith [toR_le_toR hwk_le, toR_le_toR (le_of_lt hy)]),
              max_eq_left (by linarith [toR_le_toR hwp_le]),
              max_eq_left (by linarith [toR_le_toR hwp_le, toR_le_toR (le_of_lt hy)])]
          ring
        rw [htc0, zero_mul]
      rw [hsum0]
    rw [setLIntegral_congr_fun hA_meas hzero]; simp
  · rw [if_neg h2w]
    dsimp only
    -- Step 1: Bound `triVertPot u` by `pu u` (`g.pi01Max`, `g.pi01Max`, `g.pi2Max`) using `sum_triCrossCoeff_mono_p`!
    let puOf : Fin 3 → Int := fun u => match u with | ⟨0, _⟩ => g.pi01Max | ⟨1, _⟩ => g.pi01Max | ⟨2, _⟩ => g.pi2Max
    have hmono_pt : ∀ v ∈ (triUnion (triVerts L pt) (toR rj))ᶜ,
        ENNReal.ofReal (∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) ≤
        ∑ u : Fin 3, ENNReal.ofReal (∑ k : Fin rho.size,
          triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) := by
      intro v hv
      have hsum_le : (∑ u : Fin 3, ∑ k : Fin rho.size,
          triCrossCoeff w (triVertPot rho w L pt u) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) ≤
          ∑ u : Fin 3, ∑ k : Fin rho.size,
            triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
              (euclidDist v (triVerts L pt u)) k.val *
            extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hdu : toR rj < euclidDist v (triVerts L pt u) := by
          by_contra hle; push Not at hle
          exact hv (Set.mem_iUnion.mpr ⟨u, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp hle⟩)
        have hpu_le : triVertPot rho w L pt u ≤ toR (puOf u) := by
          fin_cases u
          · exact hg.p0_le
          · exact hg.p1_le
          · exact hg.p2_le
        have hcl : toR (puOf u) + toR yj ≤ euclidDist v (triVerts L pt u) := by
          have : puOf u + yj ≤ rj := by fin_cases u <;> dsimp only [puOf] <;> omega
          have := toR_le_toR this; rw [toR_add] at this; linarith
        refine sum_triCrossCoeff_mono_p hpot hpu_le (toR_le_toR (le_of_lt hy)) hcl
          (q := fun k => extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k 0)))
            (volume (disk v (toR (rho.getD k 0)) \ triUnion (triVerts L pt) (toR rj))).toReal)
          (fun k _ => extSurvProb_nonneg _ ENNReal.toReal_nonneg) (fun k hk => ?_)
        have hr_le : toR (rho.getD k 0) ≤ toR (rho.getD (k + 1) 0) :=
          toR_le_toR (hpot.rho_le_of_le (Nat.le_succ k) hk)
        have hhit_le : triHitCount (triVerts L pt) v (toR (rho.getD k 0)) ≤
            triHitCount (triVerts L pt) v (toR (rho.getD (k + 1) 0)) := by
          unfold triHitCount
          exact Finset.card_le_card fun x hx => by
            rcases Finset.mem_filter.mp hx with ⟨hu, hle⟩
            exact Finset.mem_filter.mpr ⟨hu, hle.trans hr_le⟩
        have hvol_le : (volume (disk v (toR (rho.getD k 0)) \ triUnion (triVerts L pt) (toR rj))).toReal ≤
            (volume (disk v (toR (rho.getD (k + 1) 0)) \ triUnion (triVerts L pt) (toR rj))).toReal := by
          have hsub : disk v (toR (rho.getD k 0)) ⊆ disk v (toR (rho.getD (k + 1) 0)) := by
            intro z hz
            have h1 : 0 ≤ toR (rho.getD k 0) := toR_nonneg (hpot.rho_nonneg (by omega))
            exact hz.trans (pow_le_pow_left₀ h1 hr_le 2)
          refine ENNReal.toReal_mono ?_ (measure_mono (Set.sdiff_subset_sdiff_left hsub))
          exact ne_of_lt ((measure_mono Set.sdiff_subset).trans_lt (by
            rw [volume_disk _ (toR_nonneg (hpot.rho_nonneg hk))]; exact ENNReal.ofReal_lt_top))
        exact extSurvProb_antitone hhit_le ENNReal.toReal_nonneg hvol_le
      refine (ENNReal.ofReal_le_ofReal hsum_le).trans ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun u _ => Finset.sum_nonneg fun k _ =>
        mul_nonneg (triCrossCoeff_nonneg hpot (toR_le_toR (le_of_lt hy)) k)
          (extSurvProb_nonneg _ ENNReal.toReal_nonneg)]
    have hvol_meas : ∀ k : Fin rho.size,
        Measurable (fun v : Pt =>
          (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) := by
      intro k
      let Sset : Set (Pt × Pt) := {p : Pt × Pt | sqDist p.2 p.1 ≤ (toR (rho.getD k.val 0)) ^ 2 ∧
          p.2 ∉ triUnion (triVerts L pt) (toR rj)}
      have hset : MeasurableSet Sset := by
        refine MeasurableSet.inter ?_ (MeasurableSet.preimage hA_meas measurable_snd)
        exact (isClosed_le (by unfold sqDist; fun_prop : Continuous fun p : Pt × Pt => sqDist p.2 p.1)
          continuous_const).measurableSet
      have hlint : Measurable (fun v : Pt => ∫⁻ z : Pt, Sset.indicator 1 (v, z)) :=
        (measurable_const.indicator hset).lintegral_prod_right'
      have heq : (fun v : Pt => (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) =
          fun v : Pt => (∫⁻ z : Pt, Sset.indicator 1 (v, z)).toReal := by
        ext v; congr 1
        rw [← lintegral_indicator_one (MeasurableSet.diff (measurableSet_disk _ _) hA_meas.of_compl)]
        refine lintegral_congr fun z => ?_
        by_cases h : (v, z) ∈ Sset
        · simp [Sset, disk, Set.indicator]
        · simp [Sset, disk, Set.indicator]
      rw [heq]; exact hlint.ennreal_toReal
    have hhit_meas : ∀ k : Fin rho.size,
        Measurable (fun v : Pt => triHitCount (triVerts L pt) v (toR (rho.getD k.val 0))) := by
      intro k
      have heq : (fun v : Pt => triHitCount (triVerts L pt) v (toR (rho.getD k.val 0))) =
          fun v : Pt => ∑ x : Fin 3, if euclidDist v (triVerts L pt x) ≤ toR (rho.getD k.val 0) then 1 else 0 := by
        ext v; unfold triHitCount; rw [Finset.card_filter]
      rw [heq]
      refine Finset.measurable_sum _ fun x _ => Measurable.ite ?_ measurable_const measurable_const
      exact (isClosed_le (continuous_euclidDist.comp (continuous_id.prodMk continuous_const))
        continuous_const).measurableSet
    have hterm_meas : ∀ u : Fin 3,
        Measurable (fun v : Pt => ENNReal.ofReal (∑ k : Fin rho.size,
          triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
            (euclidDist v (triVerts L pt u)) k.val *
          extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
            (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal)) := by
      intro u
      refine Measurable.ennreal_ofReal (Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_)
      · unfold triCrossCoeff euclidDist sqDist; fun_prop
      · unfold extSurvProb
        refine Measurable.ite (measurableSet_le measurable_const (hhit_meas k)) measurable_const ?_
        refine Measurable.ite ((hhit_meas k) (MeasurableSet.singleton 1))
          (Real.continuous_exp.measurable.comp (hvol_meas k).neg)
          ((measurable_const.add (hvol_meas k)).mul (Real.continuous_exp.measurable.comp (hvol_meas k).neg))
    refine (setLIntegral_mono' hA_meas hmono_pt).trans ?_
    rw [lintegral_finsetSum _ fun u _ => hterm_meas u]
    -- Step 3: Bound each vertex `u ∈ {0, 1, 2}` by polar coordinates + `vertexSectorsLoop_ge`!
    set rEnc := rj + g.radB
    set p0 := if g.pi01Max + yj + wMax > rj then
        vertexSectorsLoop rho w g 40 0 g.pi01Max yPrev yj rj rEnc (g.pi01Max + yj + wMax) 0 0 else 0
    set p1 := if g.pi01Max + yj + wMax > rj then
        vertexSectorsLoop rho w g 40 1 g.pi01Max yPrev yj rj rEnc (g.pi01Max + yj + wMax) 0 p0 else p0
    set p2 := if g.pi2Max + yj + wMax > rj then
        vertexSectorsLoop rho w g 40 2 g.pi2Max yPrev yj rj rEnc (g.pi2Max + yj + wMax) 0 p1 else p1
    have hvertex_le : ∀ (u : Fin 3) (acc : Int),
        ∫⁻ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
          ENNReal.ofReal (∑ k : Fin rho.size,
            triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
              (euclidDist v (triVerts L pt u)) k.val *
            extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) ≤
        ENNReal.ofReal (toR angleTable40.dtHi *
          (((let sMax := puOf u + yj + wMax
             (if sMax > rj then vertexSectorsLoop rho w g 40 u.val (puOf u) yPrev yj rj rEnc sMax 0 acc else acc) - acc : Int) : ℝ) /
            (6 * (S : ℝ) ^ 2))) := by
      intro u acc
      set sMax := puOf u + yj + wMax
      have hclear_u : puOf u + yj ≤ rj := by fin_cases u <;> dsimp only [puOf] <;> omega
      -- Convert to full-plane `lintegral`, translate by `P u`, apply `lintegral_polar_eq` + Tonelli!
      let F : Pt → ℝ≥0∞ := fun v =>
        ENNReal.ofReal (if v ∉ triUnion (triVerts L pt) (toR rj) then
          ∑ k : Fin rho.size,
            triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
              (euclidDist v (triVerts L pt u)) k.val *
            extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal
        else 0)
      have hF_meas : Measurable F := by
        dsimp only [F]
        have h0 : (fun v : Pt => ENNReal.ofReal (if v ∉ triUnion (triVerts L pt) (toR rj) then
            ∑ k : Fin rho.size,
              triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
                (euclidDist v (triVerts L pt u)) k.val *
              extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
                (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal
            else 0)) =
          (triUnion (triVerts L pt) (toR rj))ᶜ.indicator (fun v : Pt => ENNReal.ofReal (∑ k : Fin rho.size,
            triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
              (euclidDist v (triVerts L pt u)) k.val *
            extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal)) := by
          ext v; by_cases hv : v ∉ triUnion (triVerts L pt) (toR rj)
          · have hv' : v ∈ (triUnion (triVerts L pt) (toR rj))ᶜ := hv
            rw [Set.indicator_of_mem hv', if_pos hv]
          · have hv' : v ∉ (triUnion (triVerts L pt) (toR rj))ᶜ := hv
            rw [Set.indicator_of_notMem hv', if_neg hv, ENNReal.ofReal_zero]
        rw [h0]; exact (hterm_meas u).indicator hA_meas
      have hset_eq : ∫⁻ v in (triUnion (triVerts L pt) (toR rj))ᶜ,
          ENNReal.ofReal (∑ k : Fin rho.size,
            triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj)
              (euclidDist v (triVerts L pt u)) k.val *
            extSurvProb (triHitCount (triVerts L pt) v (toR (rho.getD k.val 0)))
              (volume (disk v (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal) =
          ∫⁻ v : Pt, F v := by
        rw [← lintegral_indicator hA_meas]
        refine lintegral_congr fun v => ?_
        dsimp only [F]
        by_cases hv : v ∉ triUnion (triVerts L pt) (toR rj)
        · have hv' : v ∈ (triUnion (triVerts L pt) (toR rj))ᶜ := hv
          rw [Set.indicator_of_mem hv', if_pos hv]
        · have hv' : v ∉ (triUnion (triVerts L pt) (toR rj))ᶜ := hv
          rw [Set.indicator_of_notMem hv', if_neg hv, ENNReal.ofReal_zero]
      rw [hset_eq]
      -- Translate by `triVerts L pt u`
      let Fu : Pt → ℝ≥0∞ := fun z => F ((triVerts L pt u).1 + z.1, (triVerts L pt u).2 + z.2)
      have hFu_meas : Measurable Fu :=
        hF_meas.comp ((measurable_const.add measurable_fst).prodMk (measurable_const.add measurable_snd))
      have htrans : ∫⁻ v : Pt, F v = ∫⁻ z : Pt, Fu z := by
        rw [show (volume : Measure Pt) = volume.prod volume from rfl,
            MeasureTheory.lintegral_prod F hF_meas.aemeasurable,
            MeasureTheory.lintegral_prod Fu hFu_meas.aemeasurable]
        dsimp only [Fu]
        rw [← MeasureTheory.lintegral_add_left_eq_self (fun x => ∫⁻ y : ℝ, F (x, y)) (triVerts L pt u).1]
        refine lintegral_congr fun x => ?_
        exact (MeasureTheory.lintegral_add_left_eq_self (fun y => F ((triVerts L pt u).1 + x, y)) (triVerts L pt u).2).symm
      rw [htrans, lintegral_polar_eq hFu_meas]
      -- Swap `s` and `θ` by Tonelli!
      have hswap : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal s *
          ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi), Fu (s * Real.cos θ, s * Real.sin θ) =
          ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi),
            ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (
                let P := triVerts L pt
                let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
                if v ∉ triUnion P (toR rj) then
                  s * ∑ k : Fin rho.size,
                    triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj) s k.val *
                    extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                      (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
                else 0) := by
        have hmul_in : ∀ s ∈ Ioi (0 : ℝ),
            ENNReal.ofReal s * ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi), Fu (s * Real.cos θ, s * Real.sin θ) =
            ∫⁻ θ in Ioo (0 : ℝ) (2 * Real.pi), ENNReal.ofReal s * Fu (s * Real.cos θ, s * Real.sin θ) :=
          fun s _ => (lintegral_const_mul _ (hFu_meas.comp
            ((measurable_const.mul Real.continuous_cos.measurable).prodMk
              (measurable_const.mul Real.continuous_sin.measurable)))).symm
        rw [setLIntegral_congr_fun measurableSet_Ioi hmul_in]
        have hjoint : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * Fu (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :=
          (ENNReal.measurable_ofReal.comp measurable_fst).mul (hFu_meas.comp
            ((measurable_fst.mul (Real.continuous_cos.measurable.comp measurable_snd)).prodMk
              (measurable_fst.mul (Real.continuous_sin.measurable.comp measurable_snd))))
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
        refine setLIntegral_congr_fun measurableSet_Ioo fun θ _ =>
          setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        dsimp only [Fu, F]
        have hs0 : 0 ≤ s := le_of_lt hs
        rw [← ENNReal.ofReal_mul hs0]
        congr 1
        by_cases hv : ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ) ∉
            triUnion (triVerts L pt) (toR rj)
        · rw [if_pos hv, if_pos hv]
          have hdu : euclidDist ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ)
              (triVerts L pt u) = s := by
            unfold euclidDist sqDist
            have hcs := Real.cos_sq_add_sin_sq θ
            have hsq : ((triVerts L pt u).1 + s * Real.cos θ - (triVerts L pt u).1) ^ 2 +
                ((triVerts L pt u).2 + s * Real.sin θ - (triVerts L pt u).2) ^ 2 = s ^ 2 := by
              calc _ = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
                _ = s ^ 2 := by rw [hcs, mul_one]
            rw [hsq, Real.sqrt_sq hs0]
          rw [hdu]
        · rw [if_neg hv, if_neg hv, mul_zero]
      rw [hswap]
      dsimp only
      by_cases hsMax_gt : sMax > rj
      · rw [if_pos hsMax_gt]
        have hv := vertexSectorsLoop_ge hpot hb hmem hg (u := u) hy hrj_l1 hclear_u 0 acc (by decide)
        simp only [Nat.cast_zero, zero_mul] at hv
        exact hv
      · rw [if_neg hsMax_gt, sub_self, Int.cast_zero, zero_div, mul_zero, ENNReal.ofReal_zero]
        have hzero : ∀ θ ∈ Ioo (0 : ℝ) (2 * Real.pi),
            ∫⁻ s in Ioi (0 : ℝ),
              ENNReal.ofReal (
                let P := triVerts L pt
                let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
                if v ∉ triUnion P (toR rj) then
                  s * ∑ k : Fin rho.size,
                    triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj) s k.val *
                    extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                      (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
                else 0) = 0 := by
          intro θ _
          have h0 : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal (
              let P := triVerts L pt
              let v : Pt := ((P u).1 + s * Real.cos θ, (P u).2 + s * Real.sin θ)
              if v ∉ triUnion P (toR rj) then
                s * ∑ k : Fin rho.size,
                  triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj) s k.val *
                  extSurvProb (triHitCount P v (toR (rho.getD k.val 0)))
                    (volume (disk v (toR (rho.getD k.val 0)) \ triUnion P (toR rj))).toReal
              else 0) = 0 := by
            intro s hs
            rw [ENNReal.ofReal_eq_zero]; dsimp only
            by_cases hv : ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ) ∉
                triUnion (triVerts L pt) (toR rj)
            · rw [if_pos hv]
              have hs_gt : toR rj < s := by
                by_contra hle; push Not at hle
                have hdu : euclidDist ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ)
                    (triVerts L pt u) = s := by
                  unfold euclidDist sqDist
                  have hcs := Real.cos_sq_add_sin_sq θ
                  have hsq : ((triVerts L pt u).1 + s * Real.cos θ - (triVerts L pt u).1) ^ 2 +
                      ((triVerts L pt u).2 + s * Real.sin θ - (triVerts L pt u).2) ^ 2 = s ^ 2 := by
                    calc _ = s ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
                      _ = s ^ 2 := by rw [hcs, mul_one]
                  rw [hsq, Real.sqrt_sq (le_of_lt hs)]
                exact hv (Set.mem_iUnion.mpr ⟨u, (euclidDist_le_iff (toR_nonneg (le_of_lt hrj_pos))).mp (by rw [hdu]; exact hle)⟩)
              have hs_ge : toR (puOf u) + toR yj + toR wMax ≤ s := by
                have hle : toR sMax ≤ toR rj := toR_le_toR (by omega)
                dsimp only [sMax] at hle; rw [toR_add, toR_add] at hle; linarith
              set vPt : Pt := ((triVerts L pt u).1 + s * Real.cos θ, (triVerts L pt u).2 + s * Real.sin θ)
              have hsum0 : ∑ k : Fin rho.size,
                  triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj) s k.val *
                  extSurvProb (triHitCount (triVerts L pt) vPt (toR (rho.getD k.val 0)))
                    (volume (disk vPt (toR (rho.getD k.val 0)) \ triUnion (triVerts L pt) (toR rj))).toReal = 0 := by
                refine Finset.sum_eq_zero fun k _ => ?_
                have hwk_le : w.getD k.val 0 ≤ wMax := hpot.w_le_of_le (by omega) (by have := hpot.size_pos; omega)
                have hwp_le : wPrev w k.val ≤ wMax := by
                  have := stepPot_dw_nonneg hpot k; rw [← toR_sub] at this
                  have := nonneg_of_toR_nonneg this; omega
                have htc0 : triCrossCoeff w (toR (puOf u)) (toR yPrev) (toR yj) s k.val = 0 := by
                  unfold triCrossCoeff
                  rw [max_eq_left (by linarith [toR_le_toR hwk_le]),
                      max_eq_left (by linarith [toR_le_toR hwk_le, toR_le_toR (le_of_lt hy)]),
                      max_eq_left (by linarith [toR_le_toR hwp_le]),
                      max_eq_left (by linarith [toR_le_toR hwp_le, toR_le_toR (le_of_lt hy)])]
                  ring
                rw [htc0, zero_mul]
              rw [hsum0, mul_zero]
            · rw [if_neg hv]
          rw [setLIntegral_congr_fun measurableSet_Ioi h0]; simp
        rw [setLIntegral_congr_fun measurableSet_Ioo hzero]; simp
    -- Step 4: Sum over `u = 0, 1, 2` and apply `real_div_le_int_cdiv` for `/ 6000000000000`!
    rw [Fin.sum_univ_three]
    have h0 := hvertex_le 0 0
    have h1 := hvertex_le 1 p0
    have h2 := hvertex_le 2 p1
    have hp0_nn : 0 ≤ p0 := by
      dsimp only [p0]; split_ifs
      · exact vertexSectorsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ 0 0
      · exact le_rfl
    have hp1_ge : p0 ≤ p1 := by
      dsimp only [p1]; split_ifs
      · exact vertexSectorsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ 0 p0
      · exact le_rfl
    have hp2_ge : p1 ≤ p2 := by
      dsimp only [p2]; split_ifs
      · exact vertexSectorsLoop_nondec _ _ _ _ _ _ _ _ _ _ _ 0 p1
      · exact le_rfl
    have hdt_nn : 0 ≤ toR angleTable40.dtHi := toR_nonneg (by unfold angleTable40; decide)
    refine (add_le_add (add_le_add h0 h1) h2).trans ?_
    rw [← ENNReal.ofReal_add
      (mul_nonneg hdt_nn (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hp0_nn) (by positivity)))
      (mul_nonneg hdt_nn (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hp1_ge) (by positivity))),
      ← ENNReal.ofReal_add
      (add_nonneg
        (mul_nonneg hdt_nn (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hp0_nn) (by positivity)))
        (mul_nonneg hdt_nn (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hp1_ge) (by positivity))))
      (mul_nonneg hdt_nn (div_nonneg (by exact_mod_cast Int.sub_nonneg_of_le hp2_ge) (by positivity)))]
    refine ENNReal.ofReal_le_ofReal ?_
    have htel : toR angleTable40.dtHi * (((p0 - 0 : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) +
        toR angleTable40.dtHi * (((p1 - p0 : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) +
        toR angleTable40.dtHi * (((p2 - p1 : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) =
        ((angleTable40.dtHi * p2 : Int) : ℝ) / (6000000000000 : ℝ) / (S : ℝ) := by
      unfold toR S; push_cast; ring
    have hang_nT : angleTable40.nT = 40 := rfl
    simp only [hang_nT]
    change toR angleTable40.dtHi * (((p0 - 0 : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) +
        toR angleTable40.dtHi * (((p1 - p0 : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) +
        toR angleTable40.dtHi * (((p2 - p1 : Int) : ℝ) / (6 * (S : ℝ) ^ 2)) ≤
        toR ((angleTable40.dtHi * p2 + 5999999999999) / 6000000000000)
    rw [htel]
    have hcdiv := real_div_le_int_cdiv (a := angleTable40.dtHi * p2) (b := 6000000000000) (by decide)
    rw [show angleTable40.dtHi * p2 + 6000000000000 - 1 = angleTable40.dtHi * p2 + 5999999999999 by omega] at hcdiv
    unfold toR
    exact div_le_div_of_nonneg_right hcdiv (le_of_lt S_pos)

/-! ## Section 4: Measurability, Box Weight, and `verifyBoxInt` / `verifyShardInt` Soundness -/

private lemma measurable_unionDiskArea_tri (r : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ => unionDiskArea (triVerts p.1 (p.2.1, p.2.2)) r) := by
  let Sset : Set ((ℝ × ℝ × ℝ) × Pt) :=
    {q | ∃ u : Fin 3, sqDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u) ≤ r ^ 2}
  have hset : MeasurableSet Sset := by
    have heq : Sset = ⋃ u : Fin 3, {q : (ℝ × ℝ × ℝ) × Pt |
        sqDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u) ≤ r ^ 2} := by
      ext q; simp [Sset]
    rw [heq]
    refine MeasurableSet.iUnion fun u => ?_
    have hcont : Continuous (fun q : (ℝ × ℝ × ℝ) × Pt =>
        sqDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u)) := by
      fin_cases u <;> unfold triVerts sqDist <;> simp <;> fun_prop
    exact (isClosed_le hcont continuous_const).measurableSet
  have hlint : Measurable (fun p : ℝ × ℝ × ℝ => ∫⁻ z : Pt, Sset.indicator 1 (p, z)) :=
    (measurable_const.indicator hset).lintegral_prod_right'
  have heq : (fun p : ℝ × ℝ × ℝ => unionDiskArea (triVerts p.1 (p.2.1, p.2.2)) r) =
      fun p => (∫⁻ z : Pt, Sset.indicator 1 (p, z)).toReal := by
    ext p
    unfold unionDiskArea
    congr 1
    have hU_meas : MeasurableSet (⋃ u : Fin 3, disk (triVerts p.1 (p.2.1, p.2.2) u) r) :=
      MeasurableSet.iUnion fun u => measurableSet_disk _ _
    rw [← lintegral_indicator_one hU_meas]
    refine lintegral_congr fun z => ?_
    by_cases h : (p, z) ∈ Sset
    · have h' : z ∈ ⋃ u : Fin 3, disk (triVerts p.1 (p.2.1, p.2.2) u) r := Set.mem_iUnion.mpr h
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h]; rfl
    · have h' : z ∉ ⋃ u : Fin 3, disk (triVerts p.1 (p.2.1, p.2.2) u) r := fun hm => h (by simpa [Sset, disk] using hm)
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  rw [heq]; exact hlint.ennreal_toReal

private lemma stronglyMeasurable_levelCrossPen (rho w : Array Int) (yPrev rj yj : Int) :
    StronglyMeasurable (fun p : ℝ × ℝ × ℝ => levelCrossPen rho w yPrev rj yj p.1 (p.2.1, p.2.2)) := by
  have hstep_meas : Measurable (stepPot rho w) := by
    unfold stepPot
    refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const
  have hpot_meas : ∀ u : Fin 3, Measurable (fun p : ℝ × ℝ × ℝ => triVertPot rho w p.1 (p.2.1, p.2.2) u) := by
    intro u; fin_cases u
    · exact hstep_meas.comp measurable_fst
    · exact hstep_meas.comp measurable_fst
    · exact hstep_meas.comp (by unfold euclidNorm; fun_prop)
  have hvert_cont : ∀ u : Fin 3, Continuous (fun p : ℝ × ℝ × ℝ => triVerts p.1 (p.2.1, p.2.2) u) := by
    intro u; fin_cases u
    · exact continuous_const
    · exact continuous_fst.prodMk continuous_const
    · exact (continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
        (continuous_fst.mul (continuous_snd.comp continuous_snd))
  have hsq_cont : ∀ u : Fin 3, Continuous (fun q : (ℝ × ℝ × ℝ) × Pt =>
      sqDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u)) := by
    intro u; unfold sqDist
    have hc : Continuous (fun q : (ℝ × ℝ × ℝ) × Pt => triVerts q.1.1 (q.1.2.1, q.1.2.2) u) :=
      (hvert_cont u).comp continuous_fst
    have hc1 : Continuous (fun q : (ℝ × ℝ × ℝ) × Pt => (triVerts q.1.1 (q.1.2.1, q.1.2.2) u).1) :=
      continuous_fst.comp hc
    have hc2 : Continuous (fun q : (ℝ × ℝ × ℝ) × Pt => (triVerts q.1.1 (q.1.2.1, q.1.2.2) u).2) :=
      continuous_snd.comp hc
    fun_prop
  have hdist_cont : ∀ u : Fin 3, Continuous (fun q : (ℝ × ℝ × ℝ) × Pt =>
      euclidDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u)) :=
    fun u => Real.continuous_sqrt.comp (hsq_cont u)
  have hout_meas : MeasurableSet {q : (ℝ × ℝ × ℝ) × Pt |
      q.2 ∉ triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj)} := by
    have heq : {q : (ℝ × ℝ × ℝ) × Pt | q.2 ∉ triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj)} =
        (⋃ u : Fin 3, {q : (ℝ × ℝ × ℝ) × Pt | sqDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u) ≤ (toR rj) ^ 2})ᶜ := by
      ext q; simp [triUnion, disk]
    rw [heq]
    exact MeasurableSet.compl (MeasurableSet.iUnion fun u => (isClosed_le (hsq_cont u) continuous_const).measurableSet)
  have hhit_meas : ∀ k : Fin rho.size, Measurable (fun q : (ℝ × ℝ × ℝ) × Pt =>
      triHitCount (triVerts q.1.1 (q.1.2.1, q.1.2.2)) q.2 (toR (rho.getD k.val 0))) := by
    intro k
    have heq : (fun q : (ℝ × ℝ × ℝ) × Pt =>
        triHitCount (triVerts q.1.1 (q.1.2.1, q.1.2.2)) q.2 (toR (rho.getD k.val 0))) =
        fun q => ∑ u : Fin 3, if euclidDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u) ≤ toR (rho.getD k.val 0) then 1 else 0 := by
      ext q; unfold triHitCount; rw [Finset.card_filter]
    rw [heq]
    exact Finset.measurable_sum _ fun u _ =>
      Measurable.ite (isClosed_le (hdist_cont u) continuous_const).measurableSet measurable_const measurable_const
  have hvol_meas : ∀ k : Fin rho.size, Measurable (fun q : (ℝ × ℝ × ℝ) × Pt =>
      (volume (disk q.2 (toR (rho.getD k.val 0)) \
        triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj))).toReal) := by
    intro k
    let Rset : Set (((ℝ × ℝ × ℝ) × Pt) × Pt) :=
      {r | sqDist r.2 r.1.2 ≤ (toR (rho.getD k.val 0)) ^ 2 ∧
        r.2 ∉ triUnion (triVerts r.1.1.1 (r.1.1.2.1, r.1.1.2.2)) (toR rj)}
    have hset : MeasurableSet Rset := by
      refine MeasurableSet.inter ?_ ?_
      · exact (isClosed_le (by unfold sqDist; fun_prop : Continuous fun r : ((ℝ × ℝ × ℝ) × Pt) × Pt => sqDist r.2 r.1.2)
          continuous_const).measurableSet
      · exact hout_meas.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hlint : Measurable (fun q : (ℝ × ℝ × ℝ) × Pt => ∫⁻ z : Pt, Rset.indicator 1 (q, z)) :=
      (measurable_const.indicator hset).lintegral_prod_right'
    have heq : (fun q : (ℝ × ℝ × ℝ) × Pt =>
        (volume (disk q.2 (toR (rho.getD k.val 0)) \
          triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj))).toReal) =
        fun q => (∫⁻ z : Pt, Rset.indicator 1 (q, z)).toReal := by
      ext q; congr 1
      have hdm : MeasurableSet (disk q.2 (toR (rho.getD k.val 0)) \
          triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj)) :=
        MeasurableSet.diff (measurableSet_disk _ _) (MeasurableSet.iUnion fun u => measurableSet_disk _ _)
      rw [← lintegral_indicator_one hdm]
      refine lintegral_congr fun z => ?_
      by_cases h : (q, z) ∈ Rset
      · simp [Rset, disk, Set.indicator]
      · simp [Rset, disk, Set.indicator]
    rw [heq]; exact hlint.ennreal_toReal
  let G : (ℝ × ℝ × ℝ) × Pt → ℝ :=
    {q : (ℝ × ℝ × ℝ) × Pt | q.2 ∉ triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj)}.indicator
      (fun q => ∑ u : Fin 3, ∑ k : Fin rho.size,
        triCrossCoeff w (triVertPot rho w q.1.1 (q.1.2.1, q.1.2.2) u) (toR yPrev) (toR yj)
          (euclidDist q.2 (triVerts q.1.1 (q.1.2.1, q.1.2.2) u)) k.val *
        extSurvProb (triHitCount (triVerts q.1.1 (q.1.2.1, q.1.2.2)) q.2 (toR (rho.getD k.val 0)))
          (volume (disk q.2 (toR (rho.getD k.val 0)) \
            triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj))).toReal)
  have hG_meas : Measurable G := by
    refine Measurable.indicator ?_ hout_meas
    refine Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
    · unfold triCrossCoeff
      have hp : Measurable (fun q : (ℝ × ℝ × ℝ) × Pt => triVertPot rho w q.1.1 (q.1.2.1, q.1.2.2) u) :=
        (hpot_meas u).comp measurable_fst
      have hd := (hdist_cont u).measurable
      exact ((measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd)).sub
        (measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd))).sub
        ((measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd)).sub
        (measurable_const.max (((hp.add measurable_const).add measurable_const).sub hd)))
    · unfold extSurvProb
      refine Measurable.ite (measurableSet_le measurable_const (hhit_meas k)) measurable_const ?_
      refine Measurable.ite ((hhit_meas k) (MeasurableSet.singleton 1))
        (Real.continuous_exp.measurable.comp (hvol_meas k).neg)
        ((measurable_const.add (hvol_meas k)).mul (Real.continuous_exp.measurable.comp (hvol_meas k).neg))
  have hsm := hG_meas.stronglyMeasurable.integral_prod_right' (ν := volume)
  have heq : (fun p : ℝ × ℝ × ℝ => levelCrossPen rho w yPrev rj yj p.1 (p.2.1, p.2.2)) =
      fun p => ∫ v : Pt, G (p, v) := by
    ext p
    unfold levelCrossPen
    have hU_meas : MeasurableSet (triUnion (triVerts p.1 (p.2.1, p.2.2)) (toR rj))ᶜ :=
      MeasurableSet.compl (MeasurableSet.iUnion fun u => measurableSet_disk _ _)
    rw [← MeasureTheory.integral_indicator hU_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only [G]
    by_cases hv : v ∈ (triUnion (triVerts p.1 (p.2.1, p.2.2)) (toR rj))ᶜ
    · have hv' : (p, v) ∈ {q : (ℝ × ℝ × ℝ) × Pt | q.2 ∉ triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj)} := hv
      rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv']
    · have hv' : (p, v) ∉ {q : (ℝ × ℝ × ℝ) × Pt | q.2 ∉ triUnion (triVerts q.1.1 (q.1.2.1, q.1.2.2)) (toR rj)} := hv
      rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv']
  rw [heq]; exact hsm

/-- Soundness of `g.boxWeight12`: `(g.boxWeight12 : ℝ) / 10^12 ≤ ∫ L, ∫ x, ∫ y, 4 π L^3`. -/
private lemma boxWeight12_le {rho w : Array Int} {b : BoxCert} (hb : ValidBox rho w b) :
    ((buildBoxGeom rho w angleTable40 b).boxWeight12 : ℝ) / (10 ^ 12 : ℝ) ≤
      ∫ L in (toR b.l0)..(toR b.l1),
        ∫ _x in (toR b.x0)..(toR b.x1),
          ∫ _y in (toR b.y0)..(toR b.y1), (4 * Real.pi * L ^ 3) := by
  have hint_eq : (∫ L in (toR b.l0)..(toR b.l1),
      ∫ _x in (toR b.x0)..(toR b.x1),
        ∫ _y in (toR b.y0)..(toR b.y1), (4 * Real.pi * L ^ 3)) =
      Real.pi * ((toR b.l1) ^ 4 - (toR b.l0) ^ 4) * (toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0) := by
    simp_rw [intervalIntegral.integral_const, smul_eq_mul]
    have hpull : (∫ L in (toR b.l0)..(toR b.l1),
        (toR b.x1 - toR b.x0) * ((toR b.y1 - toR b.y0) * (4 * Real.pi * L ^ 3))) =
        (toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0) * (4 * Real.pi) *
          ∫ L in (toR b.l0)..(toR b.l1), L ^ 3 := by
      have hcongr : ∀ L : ℝ, (toR b.x1 - toR b.x0) * ((toR b.y1 - toR b.y0) * (4 * Real.pi * L ^ 3)) =
          ((toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0) * (4 * Real.pi)) * L ^ 3 := fun L => by ring
      simp_rw [hcongr, intervalIntegral.integral_const_mul]
    rw [hpull, integral_pow]
    ring
  rw [hint_eq]
  unfold buildBoxGeom
  dsimp only
  set l1_4 := b.l1 * b.l1 * b.l1 * b.l1
  set l0_4 := b.l0 * b.l0 * b.l0 * b.l0
  set dxy := (b.x1 - b.x0) * (b.y1 - b.y0)
  set w1 := ((l1_4 - l0_4) * dxy) / 1000000000000000000
  have hl0_nn : 0 ≤ b.l0 := le_of_lt hb.l0_pos
  have hl1_gt : b.l0 < b.l1 := hb.l0_lt_l1
  have hl4_nn : 0 ≤ l1_4 - l0_4 := by
    have hfac : l1_4 - l0_4 = (b.l1 - b.l0) * (b.l1 + b.l0) * (b.l1 * b.l1 + b.l0 * b.l0) := by
      dsimp only [l1_4, l0_4]; ring
    rw [hfac]
    exact mul_nonneg (mul_nonneg (by omega) (by omega)) (by nlinarith)
  have hdxy_nn : 0 ≤ dxy := mul_nonneg (by have := hb.x0_lt_x1; omega) (by have := hb.y0_lt_y1; omega)
  have hw1_nn : 0 ≤ w1 := Int.ediv_nonneg (mul_nonneg hl4_nn hdxy_nn) (by decide)
  have hdiv1 := int_ediv_le_real_div (a := (l1_4 - l0_4) * dxy) (b := 1000000000000000000) (by decide)
  have hdiv2 := int_ediv_le_real_div (a := w1 * piLo) (b := 1000000000000) (by decide)
  have h1 : (((w1 * piLo) / 1000000000000 : Int) : ℝ) / (10 ^ 12 : ℝ) ≤
      ((w1 : ℝ) / (10 ^ 18 : ℝ)) * toR piLo := by
    have h2 := div_le_div_of_nonneg_right hdiv2 (by positivity : (0 : ℝ) ≤ 10 ^ 12)
    unfold toR S; push_cast at h2 ⊢
    linarith [show ((w1 : ℝ) * (piLo : ℝ)) / 1000000000000 / 10 ^ 12 =
        (w1 : ℝ) / 10 ^ 18 * ((piLo : ℝ) / 1000000) by ring]
  have h2 : (w1 : ℝ) / (10 ^ 18 : ℝ) ≤
      ((toR b.l1) ^ 4 - (toR b.l0) ^ 4) * (toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0) := by
    have h := div_le_div_of_nonneg_right hdiv1 (by positivity : (0 : ℝ) ≤ 10 ^ 18)
    dsimp only [l1_4, l0_4, dxy] at h
    unfold toR S; push_cast at h ⊢
    linarith [show (((b.l1 : ℝ) * b.l1 * b.l1 * b.l1 - b.l0 * b.l0 * b.l0 * b.l0) *
        ((b.x1 - b.x0) * (b.y1 - b.y0))) / 1000000000000000000 / 10 ^ 18 =
        (((b.l1 : ℝ) / 1000000) ^ 4 - ((b.l0 : ℝ) / 1000000) ^ 4) *
        ((b.x1 : ℝ) / 1000000 - (b.x0 : ℝ) / 1000000) *
        ((b.y1 : ℝ) / 1000000 - (b.y0 : ℝ) / 1000000) by ring]
  have h3 : ((w1 : ℝ) / (10 ^ 18 : ℝ)) * toR piLo ≤
      (((toR b.l1) ^ 4 - (toR b.l0) ^ 4) * (toR b.x1 - toR b.x0) * (toR b.y1 - toR b.y0)) * Real.pi :=
    mul_le_mul h2 piLo_le_pi (toR_nonneg (by unfold piLo; decide)) (by
      have hl := toR_lt_toR hl1_gt; have hl0r := toR_nonneg hl0_nn
      have hx := toR_lt_toR hb.x0_lt_x1; have hy := toR_lt_toR hb.y0_lt_y1
      have h4 : 0 ≤ (toR b.l1) ^ 4 - (toR b.l0) ^ 4 := by
        have hfac : (toR b.l1) ^ 4 - (toR b.l0) ^ 4 =
            (toR b.l1 - toR b.l0) * (toR b.l1 + toR b.l0) * ((toR b.l1) ^ 2 + (toR b.l0) ^ 2) := by ring
        rw [hfac]
        exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      exact mul_nonneg (mul_nonneg h4 (by linarith)) (by linarith))
  linarith

/-- Soundness of `boxLevelsLoop` for a valid box `b`. -/
private lemma boxLevelsLoop_le {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) :
    let g := buildBoxGeom rho w angleTable40 b
    let wMax := w.getD (rho.size - 1) 0
    ∀ (lvls : List (Int × Int)) (rPrev yPrev acc : Int),
      b.l1 ≤ rPrev → 0 ≤ yPrev → LevelsValid g.pi01Max rPrev yPrev lvls →
      ((boxLevelsLoop rho w angleTable40 b g wMax lvls rPrev yPrev acc - acc : Int) : ℝ) / (10 ^ 9 : ℝ) ≤
        boxLevelsIntegral rho w (certActiveMask rho w angleTable40) b lvls yPrev := by
  intro g wMax lvls
  induction lvls with
  | nil =>
    intro rPrev yPrev acc _ _ _
    simp [boxLevelsLoop, boxLevelsIntegral]
  | cons head rest ih =>
    rcases head with ⟨rj, yj⟩
    intro rPrev yPrev acc hrPrev hyPrev hlv
    rcases hlv with ⟨hr_lt, hy_lt, hhalf, hrest⟩
    rw [boxLevelsLoop, if_neg (by omega), boxLevelsIntegral]
    dsimp only
    set areaHi := triAreaHi b.l0 b.l1 b.x0 b.x1 b.y0 b.y1 rj
    set survLo := expNegLo areaHi
    set dy := yj - yPrev
    set penHi := levelPenaltyHi rho w angleTable40 g wMax yPrev rj yj
    set bracketLo := max 0 (2 * dy - penHi)
    set gain9 := if bracketLo > 0 then (g.boxWeight12 * survLo * bracketLo) / 1000000000000000 else 0
    have hih := ih rj yj (acc + gain9) (by omega) (by omega) hrest
    have hsplit : ((boxLevelsLoop rho w angleTable40 b g wMax rest rj yj (acc + gain9) - acc : Int) : ℝ) / (10 ^ 9 : ℝ) =
        (gain9 : ℝ) / (10 ^ 9 : ℝ) +
        ((boxLevelsLoop rho w angleTable40 b g wMax rest rj yj (acc + gain9) - (acc + gain9) : Int) : ℝ) / (10 ^ 9 : ℝ) := by
      push_cast; ring
    rw [hsplit]
    refine add_le_add ?_ hih
    -- Match `certActiveMask` with `bracketLo > 0`!
    by_cases hact : 2 * dy > penHi
    · have hmask : certActiveMask rho w angleTable40 b yPrev rj yj = true := by
        unfold certActiveMask; exact decide_eq_true hact
      rw [if_pos hmask]
      have hbr_pos : bracketLo > 0 := by dsimp only [bracketLo]; omega
      have hbr_eq : bracketLo = 2 * dy - penHi := by dsimp only [bracketLo]; omega
      have hgain_eq : gain9 = (g.boxWeight12 * survLo * bracketLo) / 1000000000000000 := by
        dsimp only [gain9]; rw [if_pos hbr_pos]
      rw [hgain_eq]
      -- Step 1: Bound `(gain9 : ℝ) / 10^9 ≤ (g.boxWeight12 / 10^12) * toR survLo * toR bracketLo`!
      have hdiv := int_ediv_le_real_div (a := g.boxWeight12 * survLo * bracketLo) (b := 1000000000000000) (by decide)
      have hstep1 : (((g.boxWeight12 * survLo * bracketLo) / 1000000000000000 : Int) : ℝ) / (10 ^ 9 : ℝ) ≤
          ((g.boxWeight12 : ℝ) / (10 ^ 12 : ℝ)) * (toR survLo * toR bracketLo) := by
        have h := div_le_div_of_nonneg_right hdiv (by positivity : (0 : ℝ) ≤ 10 ^ 9)
        unfold toR S; push_cast at h ⊢
        linarith [show ((g.boxWeight12 : ℝ) * survLo * bracketLo) / 1000000000000000 / 10 ^ 9 =
            (g.boxWeight12 : ℝ) / 10 ^ 12 * ((survLo : ℝ) / 1000000 * ((bracketLo : ℝ) / 1000000)) by ring]
      -- Step 2: Multiply `boxWeight12_le` by `toR survLo * toR bracketLo ≥ 0`!
      have hsurv_nn : 0 ≤ toR survLo := toR_nonneg (expNegLo_nonneg' _)
      have hbr_nn : 0 ≤ toR bracketLo := toR_nonneg (by omega)
      have hstep2 : ((g.boxWeight12 : ℝ) / (10 ^ 12 : ℝ)) * (toR survLo * toR bracketLo) ≤
          ∫ L in (toR b.l0)..(toR b.l1),
            ∫ _x in (toR b.x0)..(toR b.x1),
              ∫ _y in (toR b.y0)..(toR b.y1),
                (4 * Real.pi * L ^ 3) * (toR survLo * toR bracketLo) := by
        have hbw := mul_le_mul_of_nonneg_right (boxWeight12_le hb) (mul_nonneg hsurv_nn hbr_nn)
        refine hbw.trans_eq ?_
        simp_rw [← intervalIntegral.integral_mul_const]
      -- Step 3: Pointwise lower bound on `boxRegion b` + iterated `setIntegral_mono_on`!
      have hl_le : toR b.l0 ≤ toR b.l1 := toR_le_toR (le_of_lt hb.l0_lt_l1)
      have hx_le : toR b.x0 ≤ toR b.x1 := toR_le_toR (le_of_lt hb.x0_lt_x1)
      have hy_le : toR b.y0 ≤ toR b.y1 := toR_le_toR (le_of_lt hb.y0_lt_y1)
      have hpt_le : ∀ L ∈ Ioo (toR b.l0) (toR b.l1), ∀ x ∈ Ioo (toR b.x0) (toR b.x1),
          ∀ y ∈ Ioo (toR b.y0) (toR b.y1),
          (4 * Real.pi * L ^ 3) * (toR survLo * toR bracketLo) ≤
          (4 * Real.pi * L ^ 3) *
            Real.exp (-unionDiskArea (triVerts L (x, y)) (toR rj)) *
            (2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L (x, y)) := by
        intro L hL x hx y hy_mem
        have hmem : (L, (x, y)) ∈ boxRegion b := ⟨hL.1, hL.2, hx.1, hx.2, hy_mem.1, hy_mem.2⟩
        have hql := boxRegion_mem_quarterLens hb hmem
        have hL_nn : 0 ≤ L := le_of_lt hql.1
        have harea : unionDiskArea (triVerts L (x, y)) (toR rj) ≤ toR areaHi :=
          triAreaHi_sound (le_of_lt hb.l0_pos) hb.x0_nonneg hb.y0_nonneg hql.1
            (hL.2.trans (toR_lt_toR (by omega))) (le_of_lt hL.1) (le_of_lt hL.2)
            (le_of_lt hx.1) (le_of_lt hx.2) (le_of_lt hy_mem.1) (le_of_lt hy_mem.2) hql.2
        have hsurv : toR survLo ≤ Real.exp (-unionDiskArea (triVerts L (x, y)) (toR rj)) :=
          (expNegLo_le (nonneg_of_toR_nonneg (ENNReal.toReal_nonneg.trans harea))).trans
            (Real.exp_le_exp.mpr (neg_le_neg harea))
        have hpen := levelPenaltyHi_sound hpot hb hmem hyPrev hy_lt (by omega) hhalf
        have hbr_le : toR bracketLo ≤ 2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L (x, y) := by
          rw [hbr_eq, toR_sub, toR_mul_int, toR_sub]; push_cast; linarith
        have h4L_nn : 0 ≤ 4 * Real.pi * L ^ 3 :=
          mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (pow_nonneg hL_nn 3)
        rw [mul_assoc (4 * Real.pi * L ^ 3)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hsurv hbr_le hbr_nn (Real.exp_nonneg _)) h4L_nn
      -- Boundedness & measurability of the integrand on `boxRegion b`!
      let F : ℝ × ℝ × ℝ → ℝ := fun p =>
        (4 * Real.pi * p.1 ^ 3) *
          Real.exp (-unionDiskArea (triVerts p.1 (p.2.1, p.2.2)) (toR rj)) *
          (2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj p.1 (p.2.1, p.2.2))
      have hF_sm : StronglyMeasurable F := by
        have h1 : StronglyMeasurable (fun p : ℝ × ℝ × ℝ => 4 * Real.pi * p.1 ^ 3) := by fun_prop
        have h2 : StronglyMeasurable (fun p : ℝ × ℝ × ℝ =>
            Real.exp (-unionDiskArea (triVerts p.1 (p.2.1, p.2.2)) (toR rj))) :=
          (Real.continuous_exp.measurable.comp (measurable_unionDiskArea_tri (toR rj)).neg).stronglyMeasurable
        have h3 : StronglyMeasurable (fun p : ℝ × ℝ × ℝ =>
            2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj p.1 (p.2.1, p.2.2)) :=
          stronglyMeasurable_const.sub (stronglyMeasurable_levelCrossPen rho w yPrev rj yj)
        exact (h1.mul h2).mul h3
      have hF_bd : ∀ L ∈ Ioo (toR b.l0) (toR b.l1), ∀ x ∈ Ioo (toR b.x0) (toR b.x1),
          ∀ y ∈ Ioo (toR b.y0) (toR b.y1),
          ‖F (L, x, y)‖ ≤ (4 * Real.pi * (toR b.l1) ^ 3) * (2 * (toR yj - toR yPrev)) := by
        intro L hL x hx y hy_mem
        have hmem : (L, (x, y)) ∈ boxRegion b := ⟨hL.1, hL.2, hx.1, hx.2, hy_mem.1, hy_mem.2⟩
        have hL_nn : 0 ≤ L := (toR_nonneg (le_of_lt hb.l0_pos)).trans (le_of_lt hL.1)
        have hL_le : L ≤ toR b.l1 := le_of_lt hL.2
        have hL1_nn : 0 ≤ toR b.l1 := hL_nn.trans hL_le
        have hexp_le : Real.exp (-unionDiskArea (triVerts L (x, y)) (toR rj)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr ENNReal.toReal_nonneg)
        have hpen_nn : 0 ≤ levelCrossPen rho w yPrev rj yj L (x, y) := by
          unfold levelCrossPen
          exact setIntegral_nonneg
            (MeasurableSet.compl (MeasurableSet.iUnion fun u => measurableSet_disk _ _))
            fun v _ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun k _ =>
              mul_nonneg (triCrossCoeff_nonneg hpot (toR_le_toR (le_of_lt hy_lt)) k)
                (extSurvProb_nonneg _ ENNReal.toReal_nonneg)
        have h4L_nn : 0 ≤ 4 * Real.pi * L ^ 3 :=
          mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (pow_nonneg hL_nn 3)
        have h4L1_nn : 0 ≤ 4 * Real.pi * (toR b.l1) ^ 3 :=
          mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)) (pow_nonneg hL1_nn 3)
        have hF_nn : 0 ≤ F (L, x, y) :=
          le_trans (mul_nonneg h4L_nn (mul_nonneg hsurv_nn hbr_nn)) (hpt_le L hL x hx y hy_mem)
        rw [Real.norm_of_nonneg hF_nn]
        dsimp only [F]
        have h4 : 4 * Real.pi * L ^ 3 ≤ 4 * Real.pi * (toR b.l1) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL_nn hL_le 3) (by positivity)
        have hbr2 : 2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L (x, y) ≤
            2 * (toR yj - toR yPrev) := by linarith
        have hbr2_nn : 0 ≤ 2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L (x, y) := by
          have := levelPenaltyHi_sound hpot hb hmem hyPrev hy_lt (by omega) hhalf
          have h0 : (0 : ℝ) ≤ toR bracketLo := hbr_nn
          rw [hbr_eq, toR_sub, toR_mul_int, toR_sub] at h0; push_cast at h0; linarith
        calc (4 * Real.pi * L ^ 3) * Real.exp (-unionDiskArea (triVerts L (x, y)) (toR rj)) *
              (2 * (toR yj - toR yPrev) - levelCrossPen rho w yPrev rj yj L (x, y))
            ≤ (4 * Real.pi * (toR b.l1) ^ 3) * 1 * (2 * (toR yj - toR yPrev)) := by
              refine mul_le_mul (mul_le_mul h4 hexp_le (Real.exp_nonneg _) h4L1_nn) hbr2 hbr2_nn (by linarith)
          _ = (4 * Real.pi * (toR b.l1) ^ 3) * (2 * (toR yj - toR yPrev)) := by ring
      set M := (4 * Real.pi * (toR b.l1) ^ 3) * (2 * (toR yj - toR yPrev))
      have hInt_y : ∀ L ∈ Ioo (toR b.l0) (toR b.l1), ∀ x ∈ Ioo (toR b.x0) (toR b.x1),
          IntegrableOn (fun y => F (L, x, y)) (Ioo (toR b.y0) (toR b.y1)) volume := by
        intro L hL x hx
        refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
          (hF_sm.comp_measurable (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable M
          (ae_restrict_of_forall_mem measurableSet_Ioo fun y hy_m => hF_bd L hL x hx y hy_m)
      have hSM_x : StronglyMeasurable (fun lx : ℝ × ℝ => ∫ y in Ioo (toR b.y0) (toR b.y1), F (lx.1, lx.2, y)) := by
        have hcomp : StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => F (q.1.1, q.1.2, q.2)) :=
          hF_sm.comp_measurable ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
        exact hcomp.integral_prod_right' (ν := volume.restrict (Ioo (toR b.y0) (toR b.y1)))
      have hInt_x : ∀ L ∈ Ioo (toR b.l0) (toR b.l1),
          IntegrableOn (fun x => ∫ y in Ioo (toR b.y0) (toR b.y1), F (L, x, y))
            (Ioo (toR b.x0) (toR b.x1)) volume := by
        intro L hL
        refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
          (hSM_x.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable (M * (toR b.y1 - toR b.y0))
          (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_)
        calc ‖∫ y in Ioo (toR b.y0) (toR b.y1), F (L, x, y)‖
            ≤ ∫ y in Ioo (toR b.y0) (toR b.y1), ‖F (L, x, y)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ _y in Ioo (toR b.y0) (toR b.y1), M :=
              setIntegral_mono_on (hInt_y L hL x hx).norm (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
                measurableSet_Ioo fun y hy_m => hF_bd L hL x hx y hy_m
          _ = M * (toR b.y1 - toR b.y0) := by
              rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
                  ENNReal.toReal_ofReal (sub_nonneg.mpr hy_le), mul_comm]
      have hSM_L : StronglyMeasurable (fun L : ℝ => ∫ x in Ioo (toR b.x0) (toR b.x1),
          ∫ y in Ioo (toR b.y0) (toR b.y1), F (L, x, y)) :=
        hSM_x.integral_prod_right' (ν := volume.restrict (Ioo (toR b.x0) (toR b.x1)))
      have hInt_L : IntegrableOn (fun L => ∫ x in Ioo (toR b.x0) (toR b.x1),
          ∫ y in Ioo (toR b.y0) (toR b.y1), F (L, x, y)) (Ioo (toR b.l0) (toR b.l1)) volume := by
        refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
          hSM_L.aestronglyMeasurable (M * (toR b.y1 - toR b.y0) * (toR b.x1 - toR b.x0))
          (ae_restrict_of_forall_mem measurableSet_Ioo fun L hL => ?_)
        calc ‖∫ x in Ioo (toR b.x0) (toR b.x1), ∫ y in Ioo (toR b.y0) (toR b.y1), F (L, x, y)‖
            ≤ ∫ x in Ioo (toR b.x0) (toR b.x1), ‖∫ y in Ioo (toR b.y0) (toR b.y1), F (L, x, y)‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ _x in Ioo (toR b.x0) (toR b.x1), (M * (toR b.y1 - toR b.y0)) :=
              setIntegral_mono_on (hInt_x L hL).norm (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
                measurableSet_Ioo fun x hx => by
                  calc ‖∫ y in Ioo (toR b.y0) (toR b.y1), F (L, x, y)‖
                      ≤ ∫ y in Ioo (toR b.y0) (toR b.y1), ‖F (L, x, y)‖ := norm_integral_le_integral_norm _
                    _ ≤ ∫ _y in Ioo (toR b.y0) (toR b.y1), M :=
                        setIntegral_mono_on (hInt_y L hL x hx).norm
                          (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
                          measurableSet_Ioo fun y hy_m => hF_bd L hL x hx y hy_m
                    _ = M * (toR b.y1 - toR b.y0) := by
                        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
                            ENNReal.toReal_ofReal (sub_nonneg.mpr hy_le), mul_comm]
          _ = M * (toR b.y1 - toR b.y0) * (toR b.x1 - toR b.x0) := by
              rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioo,
                  ENNReal.toReal_ofReal (sub_nonneg.mpr hx_le), mul_comm]
      have hstep3 : (∫ L in (toR b.l0)..(toR b.l1),
          ∫ _x in (toR b.x0)..(toR b.x1),
            ∫ _y in (toR b.y0)..(toR b.y1), (4 * Real.pi * L ^ 3) * (toR survLo * toR bracketLo)) ≤
          levelGain rho w b yPrev rj yj := by
        unfold levelGain
        simp_rw [intervalIntegral.integral_of_le hl_le, intervalIntegral.integral_of_le hx_le,
          intervalIntegral.integral_of_le hy_le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine setIntegral_mono_on ?_ hInt_L measurableSet_Ioo fun L hL => ?_
        · have hcontL : Continuous (fun L : ℝ =>
              ∫ _x in Ioo (toR b.x0) (toR b.x1),
                ∫ _y in Ioo (toR b.y0) (toR b.y1), (4 * Real.pi * L ^ 3) * (toR survLo * toR bracketLo)) := by
            simp_rw [setIntegral_const, smul_eq_mul]
            fun_prop
          exact hcontL.integrableOn_Icc.mono_set Ioo_subset_Icc_self
        · refine setIntegral_mono_on ?_ (hInt_x L hL) measurableSet_Ioo fun x hx => ?_
          · exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
          · exact setIntegral_mono_on
              (integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))
              (hInt_y L hL x hx) measurableSet_Ioo fun y hy_m => hpt_le L hL x hx y hy_m
      exact (hstep1.trans hstep2).trans hstep3
    · have hmask : certActiveMask rho w angleTable40 b yPrev rj yj = false := by
        unfold certActiveMask; exact decide_eq_false hact
      rw [if_neg (by simp [hmask])]
      have hbr0 : ¬ bracketLo > 0 := by dsimp only [bracketLo]; omega
      have hgain0 : gain9 = 0 := by dsimp only [gain9]; rw [if_neg hbr0]
      rw [hgain0]; simp

/-- Soundness of `verifyBoxInt` for a valid box `b`. -/
theorem verifyBoxInt_le_boxIntegral {rho w : Array Int} (hpot : ValidStepPot rho w)
    {b : BoxCert} (hb : ValidBox rho w b) :
    (verifyBoxInt rho w angleTable40 b : ℝ) / (10 ^ 9 : ℝ) ≤
      boxIntegral rho w (certActiveMask rho w angleTable40) b := by
  unfold verifyBoxInt boxIntegral
  have hk : ¬ (rho.size == 0 ∨ w.size != rho.size) := by
    have h1 := hpot.size_pos; have h2 := hpot.size_eq
    simp only [beq_iff_eq, bne_iff_ne, ne_eq, not_or, not_not]; exact ⟨by omega, h2⟩
  have hdom1 : ¬ (b.l0 < 0 ∨ b.l1 ≤ b.l0 ∨ b.x0 < 0 ∨ b.x1 ≤ b.x0 ∨ b.x1 > 500000) := by
    have := hb.l0_pos; have := hb.l0_lt_l1; have := hb.x0_nonneg
    have := hb.x0_lt_x1; have := hb.x1_le_half; omega
  have hdom2 : ¬ (b.y0 < 0 ∨ b.y1 ≤ b.y0) := by
    have := hb.y0_nonneg; have := hb.y0_lt_y1; omega
  have hdom3 : ¬ ((S - b.x0) * (S - b.x0) + b.y1 * b.y1 > S * S) := by
    have := hb.in_quarterLens; omega
  rw [if_neg hk, if_neg hdom1, if_neg hdom2, if_neg hdom3]
  have hlv : LevelsValid (buildBoxGeom rho w angleTable40 b).pi01Max b.l1 0 b.levels := by
    unfold buildBoxGeom; dsimp only; rw [hb.pi01_eq]; exact hb.levels_valid
  have h := boxLevelsLoop_le hpot hb b.levels b.l1 0 0 le_rfl le_rfl hlv
  simpa using h

/-- Soundness of `verifyShardInt` over a list of valid boxes. -/
theorem verifyShardInt_le_planIntegral {rho w : Array Int} (hpot : ValidStepPot rho w)
    {boxes : List BoxCert} (hboxes : ∀ b ∈ boxes, ValidBox rho w b) :
    (verifyShardInt rho w angleTable40 boxes : ℝ) / (10 ^ 9 : ℝ) ≤
      trianglePlanIntegral rho w (certActiveMask rho w angleTable40) boxes := by
  have hfold : ∀ (bs : List BoxCert) (acc : Int), (∀ b ∈ bs, ValidBox rho w b) →
      ((bs.foldl (fun a b => a + verifyBoxInt rho w angleTable40 b) acc - acc : Int) : ℝ) / (10 ^ 9 : ℝ) ≤
        trianglePlanIntegral rho w (certActiveMask rho w angleTable40) bs := by
    intro bs
    induction bs with
    | nil =>
      intro acc _
      simp [trianglePlanIntegral]
    | cons b rest ih =>
      intro acc hb_all
      simp only [List.foldl_cons, trianglePlanIntegral_cons]
      have hb := hb_all b List.mem_cons_self
      have hrest := ih (acc + verifyBoxInt rho w angleTable40 b) fun x hx =>
        hb_all x (List.mem_cons_of_mem b hx)
      have hbox := verifyBoxInt_le_boxIntegral hpot hb
      have hsplit : ((rest.foldl (fun a b => a + verifyBoxInt rho w angleTable40 b)
            (acc + verifyBoxInt rho w angleTable40 b) - acc : Int) : ℝ) / (10 ^ 9 : ℝ) =
          (verifyBoxInt rho w angleTable40 b : ℝ) / (10 ^ 9 : ℝ) +
          ((rest.foldl (fun a b => a + verifyBoxInt rho w angleTable40 b)
            (acc + verifyBoxInt rho w angleTable40 b) - (acc + verifyBoxInt rho w angleTable40 b) : Int) : ℝ) / (10 ^ 9 : ℝ) := by
        push_cast; ring
      rw [hsplit]
      linarith
  unfold verifyShardInt
  have h := hfold boxes 0 hboxes
  simpa using h

end BHHBounds.Cert
