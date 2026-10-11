/-
The integer recipe, transcribed from RECIPE.md, Sections 1 to 8.

Everything here is a definition on natural numbers, written to be compared with RECIPE.md formula by
formula.  Nothing here is meant to be efficient.  The only proofs in this file are the four short
theorems before `V` (`sum_reduce`, `lastPos_spec`, `exists_pos_of_sum_pos`, `sum_reduce_lastCell`),
which Lean needs in order to accept the recursion of Section 4.

On `Nat`, subtraction is truncated (`x - y = 0` if `x < y`) and `x / 0 = 0`; RECIPE.md means ordinary
integer arithmetic and never divides by zero.  The places where this matters, and why the two readings
agree there:

- Sections 1 to 3: the differences in `ncell`, `lo`, `up`, `Clam`, `Cmu`, `W`, `P` and the divisors
  `M·j` and `Q - Rup[n_c]` (also `α·M` and `4ν²` of Section 5).  The conditions are collected in
  `Results.Exact` (`Results/Exact.lean`) and proved there, by evaluation, for the parameter sets
  `k5`, …, `k9` only.
- `b - 1` in `cdiv a b`: not truncated when `b ≥ 1`, that is, whenever the divisor is not zero
  (`Correct.cdiv_spec`).
- `i - 1` in `num` (Section 3): only in the term with the guard `i ≥ 1`.
- `κ_c - 1` in `reduce`: `V` calls `reduce` only at `c = lastCell κ` for a key with sum above 1, and
  there `κ_c > 0` (`lastPos_spec`).
- `m p - 1` in `Tab`: `m p ≥ 1` for every `p`.
- `j - i` in `keyOf`: `E` calls it with the smaller index first.
- `p.k - 1` in `cost`: `k ≥ 2` for allowed parameters (`Allowed`).
- `absDiff x y` is `|x - y|`: of its two truncated differences one is 0.
- `13 - j` and `p.k - g.length` are termination measures only.
- The divisor `(m p) ^ i` and the modulus `m p` in `gapOfIndex` are positive for every `p`.  All other
  divisors are powers of 2.

Differences of integers (`Int`) occur in `sumZ`, `chi` and `G`.
-/

namespace Spec

/-! ## Notation -/

/-- `Σ_{i=0}^{n-1} f(i)`. -/
def sum (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => sum n f + f n

/-- `Σ_{t=a}^{b} f(t)` for integers `a ≤ b` (the empty sum if `b < a`). -/
def sumZ (a b : Int) (f : Int → Nat) : Nat :=
  sum (b - a + 1).toNat (fun u => f (a + (u : Int)))

@[inherit_doc sum] scoped syntax:67 "∑ " ident " < " term:51 ", " term:67 : term
@[inherit_doc sumZ] scoped syntax:67 "∑ " ident " from " term:51 " to " term:51 ", " term:67 : term
macro_rules
  | `(∑ $i:ident < $n, $f) => `(Spec.sum $n (fun $i => $f))
  | `(∑ $i:ident from $a to $b, $f) => `(Spec.sumZ $a $b (fun $i => $f))

/-- `ceil(a / b)`; `a / b` itself is `floor(a / b)`.  See `Correct.cdiv_spec`: for `b > 0` it is the
least `q` with `a ≤ b·q`. -/
def cdiv (a b : Nat) : Nat := (a + (b - 1)) / b

/-- The first `u` among `u₀, u₀ + 1, …, u₀ + fuel` with `P u` (and `u₀ + fuel` if there is none). -/
def leastFrom (P : Nat → Bool) : (fuel u₀ : Nat) → Nat
  | 0, u => u
  | fuel + 1, u => if P u then u else leastFrom P fuel (u + 1)

/-- `ceil_sqrt(A)`: the least `u ≥ 0` with `u² ≥ A`.  (`A² ≥ A`, so the search ends by `u = A`.)
See `Correct.ceilSqrt_spec`. -/
def ceilSqrt (A : Nat) : Nat := leastFrom (fun u => decide (u ^ 2 ≥ A)) A 0

/-- `|x - y|` for natural numbers. -/
def absDiff (x y : Nat) : Nat := (x - y) + (y - x)

/-- The least element of a list (0 for the empty list).  See `Correct.minOf_spec`. -/
def minOf : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: l => min x (minOf (y :: l))

/-- All tuples `(x_1, …, x_len)` with `0 ≤ x_i ≤ n - 1`, in lexicographic order.
See `Correct.mem_tuples` (which lists are members) and `Correct.nodup_tuples` (none occurs twice). -/
def tuples : (len n : Nat) → List (List Nat)
  | 0, _ => [[]]
  | len + 1, n => (List.range n).flatMap (fun x => (tuples len n).map (x :: ·))

/-- All ways of inserting `x` into a list. -/
def inserts (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: l => (x :: y :: l) :: (inserts x l).map (y :: ·)

/-- All orders of the elements of a list.  See `Correct.mem_orders`: the members are exactly the
rearrangements of the list.  (Only a minimum is taken over them, so it does not matter how often each
occurs.) -/
def orders : List Nat → List (List Nat)
  | [] => [[]]
  | x :: l => (orders l).flatMap (inserts x)

/-! ## Section 1: parameters -/

/-- The parameters of a spec file.  `b` holds the boundaries `b_1 < … < b_{m-1}`. -/
structure Params where
  k : Nat
  h1 : Nat
  h2 : Nat
  M : Nat
  b : List Nat
  n : Nat
  nu : Nat
  T : Nat
  theta1 : Nat
  theta2 : Nat
  deriving Repr, DecidableEq

def Q : Nat := 2 ^ 62
def D : Nat := 2 ^ 48
def F : Nat := 2 ^ 32

section
variable (p : Params)

/-- The number `m` of gap cells. -/
def m : Nat := p.b.length + 1

/-- `b_c` for `0 ≤ c ≤ m - 1`, with `b_0 = 0`. -/
def bd (c : Nat) : Nat := (0 :: p.b).getD c 0

/-- `N_T = T·M`. -/
def NT : Nat := p.T * p.M

/-- `n_c = b_{c+1} - b_c` for `0 ≤ c ≤ m - 2`, and `n_{m-1} = N_T`. -/
def ncell (c : Nat) : Nat := if c + 1 < m p then bd p (c + 1) - bd p c else NT p

/-- The allowed ranges of Section 1 (with `k` up to 9). -/
def Allowed : Prop :=
  2 ≤ p.k ∧ p.k ≤ 9 ∧
  0 < p.h1 ∧ p.h1 < 2 ^ 64 ∧ 0 < p.h2 ∧ p.h2 < 2 ^ 64 ∧ Nat.gcd p.h1 p.h2 = 1 ∧
  2 ≤ p.M ∧ p.M ≤ 1024 ∧
  m p ≤ 8 ∧ (0 :: p.b).Pairwise (· < ·) ∧ (∀ x ∈ p.b, x < 2 ^ 64) ∧
  1 ≤ p.n ∧ p.n ≤ 16 ∧
  1 ≤ p.nu ∧ p.nu ≤ 256 ∧
  1 ≤ p.T ∧ p.T ≤ 40 ∧
  0 < p.theta1 ∧ p.theta1 < 2 ^ 64 ∧ 0 < p.theta2 ∧ p.theta2 < 2 ^ 64

instance : Decidable (Allowed p) := by unfold Allowed; infer_instance

/-! ## Section 2: bounds for `e^{-1/M}` and its powers -/

mutual
  /-- `lo_j` for `1 ≤ j ≤ 13`. -/
  def lo (M j : Nat) : Nat :=
    if 13 ≤ j then 0 else Q - cdiv (up M (j + 1)) (M * j)
  termination_by 13 - j
  /-- `up_j` for `1 ≤ j ≤ 13`. -/
  def up (M j : Nat) : Nat :=
    if 13 ≤ j then Q else Q - lo M (j + 1) / (M * j)
  termination_by 13 - j
end

/-- `Rup[i]`. -/
def Rup (M : Nat) : Nat → Nat
  | 0 => Q
  | i + 1 => cdiv (Rup M i * up M 1) Q

/-- `Rlo[i]`. -/
def Rlo (M : Nat) : Nat → Nat
  | 0 => Q
  | i + 1 => Rlo M i * lo M 1 / Q

/-! ## Section 3: weights, cell masses and the tail term -/

/-- `C_λ`. -/
def Clam : Nat := Q - p.M * (Q - up p.M 1)

/-- `C_μ`. -/
def Cmu : Nat := p.M * (Q - lo p.M 1) - lo p.M 1

/-- `num_c(i)` for `0 ≤ i ≤ n_c`. -/
def num (c i : Nat) : Nat :=
  (if i < ncell p c then Rup p.M i * Clam p else 0) + (if i ≥ 1 then Rup p.M (i - 1) * Cmu p else 0)

/-- `W_c(i)` for `0 ≤ i ≤ n_c`: a bounded cell if `c ≤ m - 2`, the last cell if `c = m - 1`. -/
def W (c i : Nat) : Nat :=
  if c + 1 < m p then
    cdiv (cdiv (num p c i) (2 ^ 14)) (Q - Rup p.M (ncell p c))
  else
    cdiv (num p c i) (2 ^ 76) + (if i = NT p then cdiv (Rup p.M (NT p)) (2 ^ 14) else 0)

/-- The cell mass `P_c`. -/
def P (c : Nat) : Nat :=
  if c + 1 < m p then
    cdiv (Rup p.M (bd p c) - Rlo p.M (bd p (c + 1))) (2 ^ 14)
  else
    cdiv (Rup p.M (bd p c)) (2 ^ 14)

/-- The tail term `E_T`. -/
def ET : Nat := cdiv (Rup p.M (NT p)) (2 ^ 30)

/-! ## Section 4: keys and their weight vectors -/

/-- The keys `κ = (κ_0, …, κ_{m-1})` with `1 ≤ κ_0 + … + κ_{m-1} ≤ k`, in lexicographic order. -/
def keys : List (List Nat) :=
  (tuples (m p) (p.k + 1)).filter (fun κ => 1 ≤ κ.sum ∧ κ.sum ≤ p.k)

/-- `b_κ = Σ_c κ_c·b_c`. -/
def bKey (κ : List Nat) : Nat := ∑ c < m p, κ.getD c 0 * bd p c

/-- `len_κ = 1 + Σ_c κ_c·n_c`. -/
def lenKey (κ : List Nat) : Nat := 1 + ∑ c < m p, κ.getD c 0 * ncell p c

/-- The largest index `c < bound` with `κ_c > 0` (0 if there is none). -/
def lastPos (κ : List Nat) : (bound : Nat) → Nat
  | 0 => 0
  | c + 1 => if κ.getD c 0 > 0 then c else lastPos κ c

/-- The largest index `c` with `κ_c > 0`. -/
def lastCell (κ : List Nat) : Nat := lastPos κ κ.length

/-- `κ` with `κ_c` reduced by one. -/
def reduce (κ : List Nat) (c : Nat) : List Nat := κ.set c (κ.getD c 0 - 1)

/- Two lemmas for the termination of `V`: reducing a key at its last cell lowers the sum. -/
theorem sum_reduce (κ : List Nat) (c : Nat) (hc : c < κ.length) (hpos : κ.getD c 0 > 0) :
    (reduce κ c).sum + 1 = κ.sum := by
  unfold reduce
  induction κ generalizing c with
  | nil => simp at hc
  | cons x κ ih =>
    cases c with
    | zero => simp at hpos ⊢; omega
    | succ c =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hc
      simp only [List.getD_cons_succ] at hpos
      have := ih c hc hpos
      simp only [List.getD_cons_succ, List.set_cons_succ, List.sum_cons]
      omega

theorem lastPos_spec (κ : List Nat) (bound : Nat) (h : ∃ c, c < bound ∧ κ.getD c 0 > 0) :
    lastPos κ bound < bound ∧ κ.getD (lastPos κ bound) 0 > 0 := by
  induction bound with
  | zero => obtain ⟨c, hc, _⟩ := h; omega
  | succ b ih =>
    unfold lastPos
    split
    · exact ⟨Nat.lt_succ_self b, by assumption⟩
    · rename_i hb
      obtain ⟨c, hc, hpos⟩ := h
      have hcb : c < b := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h1 | h1
        · exact h1
        · subst h1; exact absurd hpos hb
      have := ih ⟨c, hcb, hpos⟩
      exact ⟨Nat.lt_succ_of_lt this.1, this.2⟩

theorem exists_pos_of_sum_pos (κ : List Nat) (h : κ.sum > 0) : ∃ c, c < κ.length ∧ κ.getD c 0 > 0 := by
  induction κ with
  | nil => simp at h
  | cons x κ ih =>
    by_cases hx : x > 0
    · exact ⟨0, by simp, by simpa using hx⟩
    · have : κ.sum > 0 := by simp only [List.sum_cons] at h; omega
      obtain ⟨c, hc, hpos⟩ := ih this
      exact ⟨c + 1, by simpa using hc, by simpa using hpos⟩

theorem sum_reduce_lastCell (κ : List Nat) (h : ¬ κ.sum ≤ 1) : (reduce κ (lastCell κ)).sum < κ.sum := by
  have := lastPos_spec κ κ.length (exists_pos_of_sum_pos κ (by omega))
  have := sum_reduce κ (lastCell κ) this.1 this.2
  omega

/-- `V_κ(s)` for `0 ≤ s < len_κ`.  A key with a single gap has sum 1 (keys have sum at least 1). -/
def V (κ : List Nat) (s : Nat) : Nat :=
  if _ : κ.sum ≤ 1 then
    W p (lastCell κ) s
  else
    let c := lastCell κ
    let κ' := reduce κ c
    cdiv (∑ i < lenKey p κ', ∑ j < ncell p c + 1, if i + j = s then V κ' i * W p c j else 0) D
termination_by κ.sum
decreasing_by exact sum_reduce_lastCell κ (by assumption)

/-! ## Section 5: height differences and distances -/

/-- `η_i` for `0 ≤ i ≤ ν`. -/
def eta (i : Nat) : Nat := if i = 0 ∨ i = p.nu then 1 else 2

/-- `χ(t)` for `-ν ≤ t ≤ ν`: the sum of `η_i·η_j` over `0 ≤ i, j ≤ ν` with `i - j = t`. -/
def chi (t : Int) : Nat :=
  ∑ i < p.nu + 1, ∑ j < p.nu + 1, if (i : Int) - (j : Int) = t then eta p i * eta p j else 0

/-- `α = h_2²·n·ν`. -/
def alpha : Nat := p.h2 ^ 2 * p.n * p.nu

/-- `γ = M·h_1²`. -/
def gamma : Nat := p.M * p.h1 ^ 2

/-- `Dist(j, τ)`. -/
def Dist (j tau : Nat) : Nat :=
  cdiv (ceilSqrt (((alpha p * j) ^ 2 + (gamma p * tau) ^ 2) * F ^ 2)) (alpha p * p.M)

/-- `G(j, d)` for `0 ≤ j ≤ J` and `0 ≤ d ≤ n - 1`. -/
def G (j d : Nat) : Nat :=
  cdiv (∑ t from -(p.nu : Int) to (p.nu : Int),
          chi p t * Dist p j (Int.natAbs ((d * p.nu : Nat) + t)))
       (4 * p.nu ^ 2)

/-! ## Section 6: the table -/

/-- `Tab(κ, d)`. -/
def Tab (κ : List Nat) (d : Nat) : Nat :=
  cdiv (∑ s < lenKey p κ, V p κ s * G p (bKey p κ + s) d) D + κ.getD (m p - 1) 0 * ET p

/-! ## Section 7: cell sums

A gap tuple `g = (g_1, …, g_k)` is a list of length `k`, so that `g_i` is its entry number `i - 1`.
A height tuple `a = (a_0, …, a_k)` is a list of length `k + 1`. -/

/-- The key `κ(i, j)` for `0 ≤ i < j ≤ k`: it counts the entries of `(g_{i+1}, …, g_j)` by cell. -/
def keyOf (g : List Nat) (i j : Nat) : List Nat :=
  (List.range (m p)).map (fun c => ((g.drop i).take (j - i)).count c)

/-- `E_{ij} = E_{ji} = Tab(κ(i, j), |a_i - a_j|)`. -/
def E (g a : List Nat) (i j : Nat) : Nat :=
  Tab p (keyOf p g (min i j) (max i j)) (absDiff (a.getD i 0) (a.getD j 0))

/-- The length `E(x_0, x_1) + E(x_1, x_2) + … + E(x_{r-1}, x_r)` of the path `x_0, x_1, …, x_r`. -/
def pathLen (E : Nat → Nat → Nat) : List Nat → Nat
  | x :: y :: l => E x y + pathLen E (y :: l)
  | _ => 0

/-- `cost(g, a)`: the minimum over all orders `π` of `{1, …, k - 1}` of the length of the path
`0, π(1), …, π(k-1), k`. -/
def cost (g a : List Nat) : Nat :=
  minOf ((orders (List.range' 1 (p.k - 1))).map (fun π => pathLen (E p g a) (0 :: π ++ [p.k])))

/-- `S_g`: the sum of `cost(g, a)` over all `n^{k+1}` height tuples. -/
def S (g : List Nat) : Nat :=
  ((tuples (p.k + 1) p.n).map (fun a => cost p g a)).sum

/-- The gap tuple with index `g_1 + g_2·m + … + g_k·m^{k-1}`. -/
def gapOfIndex (index : Nat) : List Nat :=
  (List.range p.k).map (fun i => index / (m p) ^ i % m p)

/-- The cell sums in index order (the list after `sums` in a values file). -/
def cellSums : List Nat :=
  (List.range ((m p) ^ p.k)).map (fun index => S p (gapOfIndex p index))

/-! ## Section 8: the total and the test -/

/-- `A_j(g_1, …, g_j)`, where `j` is the length of the list: `A_k(g) = S_g`, and
`A_{j-1}(g_1, …, g_{j-1}) = ceil((Σ_c P_c·A_j(g_1, …, g_{j-1}, c)) / D)`. -/
def A (g : List Nat) : Nat :=
  if p.k ≤ g.length then S p g
  else cdiv (∑ c < m p, P p c * A (g ++ [c])) D
termination_by p.k - g.length
decreasing_by simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- The total `A_0`. -/
def total : Nat := A p []

/-- The test: `A_0·h_2·θ_2 ≤ θ_1·n^{k+1}·F·k·h_1`. -/
def Accepts : Prop :=
  total p * p.h2 * p.theta2 ≤ p.theta1 * p.n ^ (p.k + 1) * F * p.k * p.h1

instance : Decidable (Accepts p) := by unfold Accepts; infer_instance

end

end Spec
