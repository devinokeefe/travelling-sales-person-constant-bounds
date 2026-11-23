import BHHBounds.Dual.BaseLimit
import BHHBounds.Dual.TriangleLimit

/-!
# Expectation Assembly: `baseIntegral + trianglePlanIntegral ≤ β`

Integrates the deterministic pointwise dual bound (`FiniteN.pointwise_dual_lower_bound`) over
`unitSquarePi n`, combines the 1D base limits (`BaseLimit.baseTerm1_lower_tendsto`,
`BaseLimit.basePen_upper_tendsto`) with the finite sum of triangle-moat level limits
(`TriangleLimit.levelGain_tendsto`), and concludes `baseIntegral rho w + trianglePlanIntegral rho w act boxes ≤ β`
for every BHH constant `β` via `le_of_eventually_expectedTourLength`.
-/

open MeasureTheory Set Real Filter Finset Topology
open scoped ENNReal Classical
open BHHBounds.Geometry
open BHHBounds.Cert

namespace BHHBounds.Dual

noncomputable section

/-- Integrability of `X ↦ tourLength X / √n` under `unitSquarePi n` (bounded a.e. by `8`). -/
private lemma integrable_tourLength_div_sqrt {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun X : Fin n → Pt => tourLength X / Real.sqrt (n : ℝ)) (unitSquarePi n) := by
  have hae : ∀ᵐ X ∂(unitSquarePi n), ∀ i : Fin n, X i ∈ unitSquare := by
    refine ae_all_iff.mpr fun i => ?_
    exact (MeasureTheory.measurePreserving_eval (fun _ : Fin n => unitSquareMeasure) i).quasiMeasurePreserving.ae
      ae_mem_unitSquareMeasure
  refine Integrable.of_bound
    ((measurable_tourLength n).div_const (Real.sqrt (n : ℝ))).aestronglyMeasurable 8 ?_
  filter_upwards [hae] with X hX
  have hnn : 0 ≤ tourLength X / Real.sqrt (n : ℝ) :=
    div_nonneg (tourLength_nonneg X) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsn1 : 1 ≤ Real.sqrt (n : ℝ) := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn1
  have hsn_pos : 0 < Real.sqrt (n : ℝ) := by linarith
  rw [div_le_iff₀ hsn_pos]
  linarith [tourLength_unitSquare_le X hX]

/-- Helper: every triple `(yPrev, rj, yj)` in `boxLevelTriples lvls y0` satisfies the invariants
required by `levelGain_tendsto`. -/
private lemma boxLevelTriples_invariants {pi01 : Int} :
    ∀ (lvls : List (Int × Int)) (rPrev yPrev : Int),
      LevelsValid pi01 rPrev yPrev lvls → 0 ≤ yPrev →
      ∀ lv ∈ boxLevelTriples lvls yPrev,
        0 ≤ lv.1 ∧ lv.1 < lv.2.2 ∧ rPrev < lv.2.1 ∧ 2 * (pi01 + lv.2.2) ≤ lv.2.1 := by
  intro lvls
  induction lvls with
  | nil => intro _ _ _ _ lv hmem; simp [boxLevelTriples] at hmem
  | cons p rest ih =>
    rcases p with ⟨rj, yj⟩
    intro rPrev yPrev hlv hy0 lv hmem
    rcases hlv with ⟨hr_lt, hy_lt, hhalf, hrest⟩
    simp only [boxLevelTriples, List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact ⟨hy0, hy_lt, hr_lt, hhalf⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ih rj yj hrest (by omega) lv htail
      exact ⟨h1, h2, lt_trans hr_lt h3, h4⟩

/-- Helper: existence of a uniform interior buffer radius `Rbuf` large enough for `(rho, w)` and
every box and level in `boxes`. -/
private lemma exists_uniform_Rbuf {rho w : Array Int} (hpot : ValidStepPot rho w)
    (boxes : List BoxCert) :
    ∃ Rbuf : ℝ, 0 ≤ Rbuf ∧
      (∀ i < rho.size, toR (rho.getD i 0) ≤ Rbuf) ∧
      2 * toR (w.getD (rho.size - 1) 0) ≤ Rbuf ∧
      (∀ i < rho.size, 2 * toR (w.getD (rho.size - 1) 0) + toR (rho.getD i 0) ≤ Rbuf) ∧
      (∀ b ∈ boxes, ∀ lv ∈ boxLevelTriples b.levels 0,
        toR b.l1 + toR lv.2.1 ≤ Rbuf ∧
        ∀ i < rho.size,
          toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR lv.2.2 + toR (rho.getD i 0) ≤ Rbuf) := by
  have hsize := hpot.size_pos
  have hwMax_nn : 0 ≤ toR (w.getD (rho.size - 1) 0) := toR_nonneg (hpot.w_nonneg (by omega))
  have hrhoMax_nn : 0 ≤ toR (rho.getD (rho.size - 1) 0) := toR_nonneg (hpot.rho_nonneg (by omega))
  have hrho_le : ∀ i < rho.size, toR (rho.getD i 0) ≤ toR (rho.getD (rho.size - 1) 0) := fun i hi =>
    toR_le_toR (hpot.rho_le_of_le (by omega) (by omega))
  -- Induct on `boxes` to get a uniform upper bound on box quantities
  have hboxes_bound : ∃ M : ℝ, 0 ≤ M ∧
      ∀ b ∈ boxes, ∀ lv ∈ boxLevelTriples b.levels 0,
        toR b.l1 + toR lv.2.1 ≤ M ∧
        toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR lv.2.2 + toR (rho.getD (rho.size - 1) 0) ≤ M := by
    induction boxes with
    | nil => exact ⟨0, le_rfl, fun _ h => by simp at h⟩
    | cons b bs ih =>
      obtain ⟨Mbs, hMbs0, hMbs⟩ := ih
      have hlv_bound : ∀ ls : List (Int × Int × Int), ∃ Mb : ℝ, 0 ≤ Mb ∧
          ∀ lv ∈ ls, toR b.l1 + toR lv.2.1 ≤ Mb ∧
            toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR lv.2.2 + toR (rho.getD (rho.size - 1) 0) ≤ Mb := by
        intro ls
        induction ls with
        | nil => exact ⟨0, le_rfl, fun _ h => by simp at h⟩
        | cons lv lvs ihl =>
          obtain ⟨M1, hM1, h1⟩ := ihl
          refine ⟨max M1 (max (toR b.l1 + toR lv.2.1)
            (toR b.l1 + 2 * toR (w.getD (rho.size - 1) 0) + toR lv.2.2 + toR (rho.getD (rho.size - 1) 0))),
            le_trans hM1 (le_max_left _ _), fun lv' hmem => ?_⟩
          rcases List.mem_cons.mp hmem with rfl | htail
          · exact ⟨le_trans (le_max_left _ _) (le_max_right _ _),
              le_trans (le_max_right _ _) (le_max_right _ _)⟩
          · exact ⟨(h1 lv' htail).1.trans (le_max_left _ _), (h1 lv' htail).2.trans (le_max_left _ _)⟩
      obtain ⟨Mb, hMb0, hMb⟩ := hlv_bound (boxLevelTriples b.levels 0)
      refine ⟨max Mbs Mb, le_trans hMbs0 (le_max_left _ _), fun b' hb' lv hlv => ?_⟩
      rcases List.mem_cons.mp hb' with rfl | htail
      · exact ⟨(hMb lv hlv).1.trans (le_max_right _ _), (hMb lv hlv).2.trans (le_max_right _ _)⟩
      · exact ⟨(hMbs b' htail lv hlv).1.trans (le_max_left _ _), (hMbs b' htail lv hlv).2.trans (le_max_left _ _)⟩
  obtain ⟨M, hM0, hM⟩ := hboxes_bound
  let Rbuf : ℝ := max M (2 * toR (w.getD (rho.size - 1) 0) + toR (rho.getD (rho.size - 1) 0))
  refine ⟨Rbuf, le_trans hM0 (le_max_left _ _), ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := hrho_le i hi
    have h2 : toR (rho.getD (rho.size - 1) 0) ≤ Rbuf := by
      dsimp only [Rbuf]; linarith [le_max_right M (2 * toR (w.getD (rho.size - 1) 0) + toR (rho.getD (rho.size - 1) 0))]
    linarith
  · dsimp only [Rbuf]; linarith [le_max_right M (2 * toR (w.getD (rho.size - 1) 0) + toR (rho.getD (rho.size - 1) 0))]
  · intro i hi
    have h1 := hrho_le i hi
    have h2 : 2 * toR (w.getD (rho.size - 1) 0) + toR (rho.getD (rho.size - 1) 0) ≤ Rbuf := le_max_right _ _
    linarith
  · intro b hb lv hlv
    have ⟨h1, h2⟩ := hM b hb lv hlv
    refine ⟨h1.trans (le_max_left _ _), fun i hi => ?_⟩
    have h3 := hrho_le i hi
    have h4 : M ≤ Rbuf := le_max_left _ _
    linarith

/-- Helper: finite list sum of convergent sequences converges to the sum of their limits. -/
private lemma tendsto_list_sum {α : Type*} (ls : List α) (f : α → ℕ → ℝ) (L : α → ℝ)
    (hf : ∀ a ∈ ls, Tendsto (f a) atTop (nhds (L a))) :
    Tendsto (fun n : ℕ => (ls.map fun a => f a n).sum) atTop (nhds (ls.map L).sum) := by
  induction ls with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a List.mem_cons_self).add (ih fun x hx => hf x (List.mem_cons_of_mem a hx))

/-- Helper: finite list sum of integrable functions is integrable. -/
private lemma integrable_list_sum {α Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ls : List α) (f : α → Ω → ℝ) (hf : ∀ a ∈ ls, Integrable (f a) μ) :
    Integrable (fun ω => (ls.map fun a => f a ω).sum) μ := by
  induction ls with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a List.mem_cons_self).add (ih fun x hx => hf x (List.mem_cons_of_mem a hx))

/-- Helper: Bochner integral commutes with `List.sum` of integrable functions. -/
private lemma integral_list_sum {α Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (ls : List α) (f : α → Ω → ℝ) (hf : ∀ a ∈ ls, Integrable (f a) μ) :
    ∫ ω, (ls.map fun a => f a ω).sum ∂μ = (ls.map fun a => ∫ ω, f a ω ∂μ).sum := by
  induction ls with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrest_int := integrable_list_sum rest f fun x hx => hf x (List.mem_cons_of_mem a hx)
    rw [integral_add (hf a List.mem_cons_self) hrest_int, ih fun x hx => hf x (List.mem_cons_of_mem a hx)]

/-- **Main Expectation Theorem:** For every BHH constant `β`, every valid step potential `(rho, w)`,
and every pairwise-disjoint list `boxes` of valid certified triangle boxes under any boolean
activation mask `act`:
`baseIntegral rho w + trianglePlanIntegral rho w act boxes ≤ β`. -/
theorem bhh_ge_base_add_trianglePlan {β : ℝ} (hβ : IsBHHConstant β)
    {rho w : Array Int} {boxes : List BoxCert}
    (act : BoxCert → Int → Int → Int → Bool)
    (hpot : ValidStepPot rho w)
    (hboxes : ∀ b ∈ boxes, ValidBox rho w b)
    (hdisj : PairwiseDisjointBoxes boxes) :
    baseIntegral rho w + trianglePlanIntegral rho w act boxes ≤ β := by
  obtain ⟨Rbuf, hRbuf_nn, hRbuf_rho, hRbuf_w, hRbuf_r, hRbuf_box⟩ := exists_uniform_Rbuf hpot boxes
  obtain ⟨fBase1, hfBase1_le, hfBase1_lim⟩ := baseTerm1_lower_tendsto hpot hRbuf_nn hRbuf_rho
  obtain ⟨gBasePen, hgBasePen_ge, hgBasePen_lim⟩ := basePen_upper_tendsto hpot hRbuf_nn hRbuf_w hRbuf_r
  -- Single level term as a function of `n` and `X`
  let lvIntegrand : (n : ℕ) → (hn : 4 ≤ n) → BoxCert → (Int × Int × Int) → (Fin n → Pt) → ℝ :=
    fun n hn b lv X =>
      if act b lv.1 lv.2.1 lv.2.2 then
        (1 / (n : ℝ)) * ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
          if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t ∧
              (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                toR lv.2.1 < rescaledDist X x z) then
            2 * (toR lv.2.2 - toR lv.1) -
              ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.2.2 +
                    stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                 max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.1 +
                    stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
          else 0
      else 0
  let lvExpect : BoxCert → (Int × Int × Int) → ℕ → ℝ := fun b lv n =>
    if hn : 4 ≤ n then ∫ X : Fin n → Pt, lvIntegrand n hn b lv X ∂(unitSquarePi n) else 0
  let boxExpect : BoxCert → ℕ → ℝ := fun b n =>
    ((boxLevelTriples b.levels 0).map fun lv => lvExpect b lv n).sum
  let planExpect : ℕ → ℝ := fun n => (boxes.map fun b => boxExpect b n).sum
  -- 1. Convergence of `planExpect n → trianglePlanIntegral rho w act boxes`
  have hplan_lim : Tendsto planExpect atTop (nhds (trianglePlanIntegral rho w act boxes)) := by
    unfold trianglePlanIntegral planExpect
    refine tendsto_list_sum boxes boxExpect (boxIntegral rho w act) fun b hb => ?_
    unfold boxIntegral boxExpect
    rw [boxLevelsIntegral_eq_sum_triples rho w act b b.levels 0]
    refine tendsto_list_sum (boxLevelTriples b.levels 0) (lvExpect b)
      (fun lv => if act b lv.1 lv.2.1 lv.2.2 then levelGain rho w b lv.1 lv.2.1 lv.2.2 else 0) fun lv hlv => ?_
    by_cases hact : act b lv.1 lv.2.1 lv.2.2 = true
    · rw [if_pos hact]
      have hinv := boxLevelTriples_invariants b.levels b.l1 0 (hboxes b hb).levels_valid le_rfl lv hlv
      have hbuf := hRbuf_box b hb lv hlv
      have ht := levelGain_tendsto hpot (hboxes b hb) hinv.1 hinv.2.1 hinv.2.2.1 hinv.2.2.2
        hRbuf_nn hbuf.1 hbuf.2
      refine ht.congr fun n => ?_
      dsimp only [lvExpect]
      by_cases hn4 : 4 ≤ n
      · rw [dif_pos hn4, dif_pos hn4]
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        dsimp only [lvIntegrand]
        rw [if_pos hact]
      · rw [dif_neg hn4, dif_neg hn4]
    · rw [if_neg hact]
      have h0 : lvExpect b lv = fun _ => 0 := by
        funext n; dsimp only [lvExpect]
        by_cases hn4 : 4 ≤ n
        · rw [dif_pos hn4]
          have hz : (fun X : Fin n → Pt => lvIntegrand n hn4 b lv X) = fun _ => 0 := by
            funext X; dsimp only [lvIntegrand]; rw [if_neg hact]
          rw [hz, integral_zero]
        · rw [dif_neg hn4]
      rw [h0]; exact tendsto_const_nhds
  -- 2. Combined lower sequence `L_n := fBase1 n - gBasePen n + planExpect n`
  let seqL : ℕ → ℝ := fun n => fBase1 n - gBasePen n + planExpect n
  have hseqL_lim : Tendsto seqL atTop (nhds (baseIntegral rho w + trianglePlanIntegral rho w act boxes)) := by
    have h1 := (hfBase1_lim.sub hgBasePen_lim).add hplan_lim
    have heq : baseTerm1 rho w - (basePenMarg rho w + basePenInter rho w) +
        trianglePlanIntegral rho w act boxes =
        baseIntegral rho w + trianglePlanIntegral rho w act boxes := by
      unfold baseIntegral; ring
    rwa [heq] at h1
  -- 3. For every `n ≥ 4`, `seqL n ≤ expectedTourLength n / √n`
  have hseqL_le : ∀ n : ℕ, 4 ≤ n → seqL n ≤ expectedTourLength n / Real.sqrt (n : ℝ) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hsqn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    -- Integrability of each piece under `unitSquarePi n`
    have hint_b1 := integrable_baseTerm1_integrand hn hpot
    have hint_bp := integrable_basePen_integrand hn hpot
    have hint_lv : ∀ b : BoxCert, ∀ lv : Int × Int × Int, Integrable (lvIntegrand n hn b lv) (unitSquarePi n) := by
      intro b lv; dsimp only [lvIntegrand]
      split_ifs
      · exact integrable_levelGain_integrand hn hpot b lv.1 lv.2.1 lv.2.2 (Rbuf / Real.sqrt (n : ℝ))
      · exact integrable_zero _ _ _
    have hint_box : ∀ b : BoxCert,
        Integrable (fun X : Fin n → Pt => ((boxLevelTriples b.levels 0).map fun lv => lvIntegrand n hn b lv X).sum)
          (unitSquarePi n) := fun b =>
      integrable_list_sum (boxLevelTriples b.levels 0) (fun lv X => lvIntegrand n hn b lv X) fun lv _ => hint_lv b lv
    have hint_plan : Integrable (fun X : Fin n → Pt =>
        (boxes.map fun b => ((boxLevelTriples b.levels 0).map fun lv => lvIntegrand n hn b lv X).sum).sum)
        (unitSquarePi n) :=
      integrable_list_sum boxes _ fun b _ => hint_box b
    have hint_rhs := integrable_tourLength_div_sqrt (n := n) (by omega)
    -- Pointwise inequality divided by `n`: `base1 - basePen + plan ≤ tourLength / √n`
    have hpt : ∀ X : Fin n → Pt,
        ((2 / (n : ℝ)) * ∑ u : Fin n, stepPot rho w (nn2 (by omega) (rescaledDist X) u)) -
        ((1 / (2 * (n : ℝ))) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v)) +
        (boxes.map fun b => ((boxLevelTriples b.levels 0).map fun lv => lvIntegrand n hn b lv X).sum).sum ≤
        tourLength X / Real.sqrt (n : ℝ) := by
      intro X
      have hpw := pointwise_dual_lower_bound hn act hpot hboxes hdisj (Rbuf / Real.sqrt (n : ℝ)) X
      dsimp only at hpw
      have hdiv := div_le_div_of_nonneg_right hpw (le_of_lt hn_pos)
      have hrhs : (Real.sqrt (n : ℝ) * tourLength X) / (n : ℝ) = tourLength X / Real.sqrt (n : ℝ) := by
        rw [div_eq_div_iff (ne_of_gt hn_pos) (ne_of_gt hsqn_pos)]
        calc Real.sqrt (n : ℝ) * tourLength X * Real.sqrt (n : ℝ)
            = tourLength X * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
          _ = tourLength X * (n : ℝ) := by rw [Real.mul_self_sqrt (le_of_lt hn_pos)]
      rw [hrhs] at hdiv
      refine le_trans (le_of_eq ?_) hdiv
      -- Algebraic rearrangement of `1 / n` into each of the three pieces
      have hplan_eq :
          (boxes.map fun b => ((boxLevelTriples b.levels 0).map fun lv => lvIntegrand n hn b lv X).sum).sum =
          ((boxes.map fun b =>
            ∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
              if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t then
                ((boxLevelTriples b.levels 0).map fun lv =>
                  if act b lv.1 lv.2.1 lv.2.2 ∧
                      (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                        toR lv.2.1 < rescaledDist X x z) then
                    2 * (toR lv.2.2 - toR lv.1) -
                      ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.2.2 +
                            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.1 +
                            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
                  else 0).sum
              else 0).sum) / (n : ℝ) := by
        have hlist_div : ∀ (L : List ℝ), (L.map (· / (n : ℝ))).sum = L.sum / (n : ℝ) := fun L => by
          induction L with
          | nil => simp
          | cons a as ih => simp [add_div, ih]
        rw [← hlist_div, List.map_map]
        congr 1
        refine List.map_congr_left fun b _ => ?_
        dsimp only [Function.comp]
        -- Swap `List.sum` over `boxLevelTriples` with `∑ u, ∑ v, ∑ t` and pull out `1 / n`
        have hswap_lv : ∀ (ls : List (Int × Int × Int)),
            (ls.map fun lv => lvIntegrand n hn b lv X).sum =
            (∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
              if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t then
                (ls.map fun lv =>
                  if act b lv.1 lv.2.1 lv.2.2 ∧
                      (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                        toR lv.2.1 < rescaledDist X x z) then
                    2 * (toR lv.2.2 - toR lv.1) -
                      ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.2.2 +
                            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.1 +
                            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
                  else 0).sum
              else 0) / (n : ℝ) := by
          intro ls
          induction ls with
          | nil => simp
          | cons lv lvs ih =>
            simp only [List.map_cons, List.sum_cons, ih]
            have hadd : (∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
                if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t then
                  (if act b lv.1 lv.2.1 lv.2.2 ∧
                      (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                        toR lv.2.1 < rescaledDist X x z) then
                    2 * (toR lv.2.2 - toR lv.1) -
                      ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                        (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.2.2 +
                            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                         max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.1 +
                            stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
                  else 0) +
                  (lvs.map fun lv' =>
                    if act b lv'.1 lv'.2.1 lv'.2.2 ∧
                        (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                          toR lv'.2.1 < rescaledDist X x z) then
                      2 * (toR lv'.2.2 - toR lv'.1) -
                        ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                          (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv'.2.2 +
                              stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                           max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv'.1 +
                              stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
                    else 0).sum
                else 0) =
                (∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
                  if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t then
                    if act b lv.1 lv.2.1 lv.2.2 ∧
                        (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                          toR lv.2.1 < rescaledDist X x z) then
                      2 * (toR lv.2.2 - toR lv.1) -
                        ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                          (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.2.2 +
                              stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                           max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.1 +
                              stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
                    else 0
                  else 0) +
                (∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
                  if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t then
                    (lvs.map fun lv' =>
                      if act b lv'.1 lv'.2.1 lv'.2.2 ∧
                          (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                            toR lv'.2.1 < rescaledDist X x z) then
                        2 * (toR lv'.2.2 - toR lv'.1) -
                          ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                            (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv'.2.2 +
                                stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                             max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv'.1 +
                                stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
                      else 0).sum
                  else 0) := by
              simp_rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun t _ => ?_
              split_ifs <;> ring
            rw [hadd, add_div]
            congr 1
            dsimp only [lvIntegrand]
            rw [one_div_mul_eq_div]
            by_cases hact : act b lv.1 lv.2.1 lv.2.2 = true
            · rw [if_pos hact]
              congr 1
              refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun t _ => ?_
              by_cases hm : MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t
              · by_cases hcl : ∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                    toR lv.2.1 < rescaledDist X x z
                · rw [if_pos ⟨hm, hcl⟩, if_pos hm, if_pos ⟨hact, hcl⟩]
                · rw [if_neg (fun h => hcl h.2), if_pos hm, if_neg (fun h => hcl h.2)]
              · rw [if_neg (fun h => hm h.1), if_neg hm]
            · rw [if_neg hact]
              have hz : (∑ u : Fin n, ∑ v : Fin n, ∑ t : Fin n,
                  if MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t then
                    if act b lv.1 lv.2.1 lv.2.2 ∧
                        (∀ x ∈ ({u, v, t} : Finset (Fin n)), ∀ z ∉ ({u, v, t} : Finset (Fin n)),
                          toR lv.2.1 < rescaledDist X x z) then
                      2 * (toR lv.2.2 - toR lv.1) -
                        ∑ x ∈ ({u, v, t} : Finset (Fin n)), ∑ z ∈ Finset.univ \ ({u, v, t} : Finset (Fin n)),
                          (max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.2.2 +
                              stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z) -
                           max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) x) + toR lv.1 +
                              stepPot rho w (nn2 (by omega) (rescaledDist X) z) - rescaledDist X x z))
                    else 0
                  else 0) = 0 := by
                refine Finset.sum_eq_zero fun u _ => Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun t _ => ?_
                by_cases hm : MatchesBox b (Rbuf / Real.sqrt (n : ℝ)) X u v t
                · rw [if_pos hm, if_neg (fun h => hact h.1)]
                · rw [if_neg hm]
              rw [hz, zero_div]
        exact hswap_lv (boxLevelTriples b.levels 0)
      rw [hplan_eq]
      ring
    -- Integrate both sides over `unitSquarePi n`
    have hint_sub : Integrable (fun X : Fin n → Pt =>
        (2 / (n : ℝ)) * ∑ u : Fin n, stepPot rho w (nn2 (by omega) (rescaledDist X) u) -
        (1 / (2 * (n : ℝ))) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v)) (unitSquarePi n) :=
      hint_b1.sub hint_bp
    have hint_lhs : Integrable (fun X : Fin n → Pt =>
        ((2 / (n : ℝ)) * ∑ u : Fin n, stepPot rho w (nn2 (by omega) (rescaledDist X) u) -
        (1 / (2 * (n : ℝ))) * ∑ u : Fin n, ∑ v ∈ Finset.univ.erase u,
          max 0 (stepPot rho w (nn2 (by omega) (rescaledDist X) u) +
            stepPot rho w (nn2 (by omega) (rescaledDist X) v) - rescaledDist X u v)) +
        (boxes.map fun b => ((boxLevelTriples b.levels 0).map fun lv => lvIntegrand n hn b lv X).sum).sum)
        (unitSquarePi n) :=
      hint_sub.add hint_plan
    have hint_le := MeasureTheory.integral_mono hint_lhs hint_rhs hpt
    rw [integral_add hint_sub hint_plan, integral_sub hint_b1 hint_bp] at hint_le
    have hrhs_eq : ∫ X : Fin n → Pt, tourLength X / Real.sqrt (n : ℝ) ∂(unitSquarePi n) =
        expectedTourLength n / Real.sqrt (n : ℝ) := by
      rw [integral_div]; rfl
    rw [hrhs_eq] at hint_le
    have hplan_int_eq : ∫ X : Fin n → Pt,
          (boxes.map fun b => ((boxLevelTriples b.levels 0).map fun lv => lvIntegrand n hn b lv X).sum).sum
          ∂(unitSquarePi n) = planExpect n := by
      rw [integral_list_sum boxes _ fun b _ => hint_box b]
      unfold planExpect boxExpect lvExpect
      congr 1
      refine List.map_congr_left fun b _ => ?_
      rw [integral_list_sum (boxLevelTriples b.levels 0) _ fun lv _ => hint_lv b lv]
      congr 1
      refine List.map_congr_left fun lv _ => ?_
      rw [dif_pos hn]
    rw [hplan_int_eq] at hint_le
    have hb1 := hfBase1_le n hn
    have hbp := hgBasePen_ge n hn
    dsimp only [seqL]
    linarith
  -- 4. Conclude via `le_of_eventually_expectedTourLength`
  refine le_of_eventually_expectedTourLength hβ fun ε hε => ?_
  have hev := (Metric.tendsto_atTop.mp hseqL_lim) ε hε
  obtain ⟨N, hN⟩ := hev
  filter_upwards [Filter.eventually_ge_atTop (max 4 N)] with n hn
  have hdist := hN n (le_trans (le_max_right 4 N) hn)
  rw [Real.dist_eq, abs_lt] at hdist
  have hle := hseqL_le n (le_trans (le_max_left 4 N) hn)
  linarith

end

end BHHBounds.Dual
