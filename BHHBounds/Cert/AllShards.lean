import BHHBounds.Cert.Data
import BHHBounds.Cert.Shards.Shard00
import BHHBounds.Cert.Shards.Shard01
import BHHBounds.Cert.Shards.Shard02
import BHHBounds.Cert.Shards.Shard03
import BHHBounds.Cert.Shards.Shard04
import BHHBounds.Cert.Shards.Shard05
import BHHBounds.Cert.Shards.Shard06
import BHHBounds.Cert.Shards.Shard07
import BHHBounds.Cert.Shards.Shard08
import BHHBounds.Cert.Shards.Shard09
import BHHBounds.Cert.Shards.Shard10
import BHHBounds.Cert.Shards.Shard11
import BHHBounds.Cert.Shards.Shard12
import BHHBounds.Cert.Shards.Shard13
import BHHBounds.Cert.Shards.Shard14
import BHHBounds.Cert.Shards.Shard15
import BHHBounds.Cert.Shards.Shard16
import BHHBounds.Cert.Shards.Shard17
import BHHBounds.Cert.Shards.Shard18
import BHHBounds.Cert.Shards.Shard19
import BHHBounds.Cert.Shards.Shard20
import BHHBounds.Cert.Shards.Shard21
import BHHBounds.Cert.Shards.Shard22
import BHHBounds.Cert.Shards.Shard23

/-!
# All shards

Concatenates the 24 shards into `allBoxes` (2,923 boxes), adds up their certified gains, and checks
by `native_decide` that the step potential is valid and that the boxes are valid and pairwise
disjoint.
-/

namespace BHHBounds.Cert

open BHHBounds.Cert.Shards

/-- The 2,923 boxes of all 24 shards. -/
def allBoxes : List BoxCert :=
  (((((((((((((((((((((((shard00Boxes ++ shard01Boxes) ++ shard02Boxes) ++ shard03Boxes) ++
    shard04Boxes) ++ shard05Boxes) ++ shard06Boxes) ++ shard07Boxes) ++
    shard08Boxes) ++ shard09Boxes) ++ shard10Boxes) ++ shard11Boxes) ++
    shard12Boxes) ++ shard13Boxes) ++ shard14Boxes) ++ shard15Boxes) ++
    shard16Boxes) ++ shard17Boxes) ++ shard18Boxes) ++ shard19Boxes) ++
    shard20Boxes) ++ shard21Boxes) ++ shard22Boxes) ++ shard23Boxes)

/-! ## Structural checkers -/

def checkMonotoneAux (rho w : Array Int) (i : Nat) : Bool :=
  if i + 1 ≥ rho.size then true
  else
    decide (rho.getD i 0 < rho.getD (i + 1) 0) &&
    decide (w.getD i 0 ≤ w.getD (i + 1) 0) &&
    checkMonotoneAux rho w (i + 1)
termination_by rho.size - i

def isValidStepPotBool (rho w : Array Int) : Bool :=
  decide (0 < rho.size) &&
  decide (w.size = rho.size) &&
  decide (rho.getD 0 0 = 0) &&
  decide (0 ≤ w.getD 0 0) &&
  checkMonotoneAux rho w 0

def levelsValidBool (pi01 rPrev yPrev : Int) : List (Int × Int) → Bool
  | [] => true
  | (rj, yj) :: rest =>
    decide (rPrev < rj) &&
    decide (yPrev < yj) &&
    decide (2 * (pi01 + yj) ≤ rj) &&
    levelsValidBool pi01 rj yj rest

def isValidBoxBool (rho w : Array Int) (b : BoxCert) : Bool :=
  let pi01 := evalStepPot rho w b.l1
  decide (0 < b.l0) &&
  decide (b.l0 < b.l1) &&
  decide (0 ≤ b.x0) &&
  decide (b.x0 < b.x1) &&
  decide (b.x1 ≤ 500000) &&
  decide (0 ≤ b.y0) &&
  decide (b.y0 < b.y1) &&
  decide ((S - b.x0) * (S - b.x0) + b.y1 * b.y1 ≤ S * S) &&
  decide (evalStepPot rho w (b.l1 - 1) = pi01) &&
  levelsValidBool pi01 b.l1 0 b.levels

def boxesDisjointBool (a b : BoxCert) : Bool :=
  decide (a.l1 ≤ b.l0) || decide (b.l1 ≤ a.l0) ||
  decide (a.x1 ≤ b.x0) || decide (b.x1 ≤ a.x0) ||
  decide (a.y1 ≤ b.y0) || decide (b.y1 ≤ a.y0)

def allPairwiseDisjointBool : List BoxCert → Bool
  | [] => true
  | a :: rest => rest.all (boxesDisjointBool a) && allPairwiseDisjointBool rest

/-! ## Structural checks -/

theorem stepPot_valid_bool : isValidStepPotBool stepPotRho stepPotW = true := by
  native_decide

theorem allBoxes_valid_bool : allBoxes.all (isValidBoxBool stepPotRho stepPotW) = true := by
  native_decide

theorem allBoxes_disjoint_bool : allPairwiseDisjointBool allBoxes = true := by
  native_decide

/-! ## Summing the shards -/

private theorem foldl_add_shift {α : Type} (f : α → Int) (xs : List α) (init : Int) :
    xs.foldl (fun acc x => acc + f x) init = init + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, Int.zero_add]
    rw [ih (init + f x), ih (f x)]
    omega

theorem verifyShardInt_append (rho w : Array Int) (ang : AngleTable) (xs ys : List BoxCert) :
    verifyShardInt rho w ang (xs ++ ys) =
      verifyShardInt rho w ang xs + verifyShardInt rho w ang ys := by
  unfold verifyShardInt
  rw [List.foldl_append]
  exact foldl_add_shift (verifyBoxInt rho w ang) ys _

private theorem add_shard_le {f : List BoxCert → Int}
    (hadd : ∀ xs ys, f (xs ++ ys) = f xs + f ys)
    {xs ys : List BoxCert} {a b : Int} (ha : a ≤ f xs) (hb : b ≤ f ys) :
    a + b ≤ f (xs ++ ys) := by
  rw [hadd]; exact Int.add_le_add ha hb

/-- The certified triangle-moat gain of all 24 shards: `5431036 / 10 ^ 9`. -/
theorem allShards_verified :
    5431036 ≤ verifyShardInt stepPotRho stepPotW angleTable40 allBoxes := by
  have hadd := verifyShardInt_append stepPotRho stepPotW angleTable40
  have s01 := add_shard_le hadd shard00_verified shard01_verified
  have s02 := add_shard_le hadd s01 shard02_verified
  have s03 := add_shard_le hadd s02 shard03_verified
  have s04 := add_shard_le hadd s03 shard04_verified
  have s05 := add_shard_le hadd s04 shard05_verified
  have s06 := add_shard_le hadd s05 shard06_verified
  have s07 := add_shard_le hadd s06 shard07_verified
  have s08 := add_shard_le hadd s07 shard08_verified
  have s09 := add_shard_le hadd s08 shard09_verified
  have s10 := add_shard_le hadd s09 shard10_verified
  have s11 := add_shard_le hadd s10 shard11_verified
  have s12 := add_shard_le hadd s11 shard12_verified
  have s13 := add_shard_le hadd s12 shard13_verified
  have s14 := add_shard_le hadd s13 shard14_verified
  have s15 := add_shard_le hadd s14 shard15_verified
  have s16 := add_shard_le hadd s15 shard16_verified
  have s17 := add_shard_le hadd s16 shard17_verified
  have s18 := add_shard_le hadd s17 shard18_verified
  have s19 := add_shard_le hadd s18 shard19_verified
  have s20 := add_shard_le hadd s19 shard20_verified
  have s21 := add_shard_le hadd s20 shard21_verified
  have s22 := add_shard_le hadd s21 shard22_verified
  have s23 := add_shard_le hadd s22 shard23_verified
  exact Int.le_trans (by decide) s23

/-- The base and triangle certificates add up to `650928770 / 10 ^ 9`. -/
theorem total_cert_verified :
    650928770 ≤ baseVerifyInt stepPotRho stepPotW 1500 +
      verifyShardInt stepPotRho stepPotW angleTable40 allBoxes :=
  Int.le_trans (by decide) (Int.add_le_add base_cert_verified allShards_verified)

end BHHBounds.Cert
