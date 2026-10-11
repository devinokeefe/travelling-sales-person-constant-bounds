/-
The parameter sets (spec files `tiny`, `k4`, …, `k9`), and that they are in the allowed ranges.
-/
import TSPBound.Spec

namespace Results
open Spec

/-- `data/specs/tiny.txt`. -/
def tiny : Params :=
  { k := 3, h1 := 2, h2 := 1, M := 16, b := [11, 28], n := 3, nu := 4, T := 12,
    theta1 := 95, theta2 := 100 }

/-- `data/specs/k4.txt`. -/
def k4 : Params :=
  { k := 4, h1 := 2, h2 := 1, M := 128, b := [48, 112, 208], n := 6, nu := 64, T := 16,
    theta1 := 89, theta2 := 100 }

/-- `data/specs/k5.txt`: `k = 5`, `h = 2`, threshold `8789/10000`. -/
def k5 : Params :=
  { k := 5, h1 := 2, h2 := 1, M := 128, b := [48, 112, 208], n := 6, nu := 64, T := 16,
    theta1 := 8789, theta2 := 10000 }

/-- `data/specs/k6.txt`: `k = 6`, `h = 2`, threshold `8729/10000`. -/
def k6 : Params :=
  { k := 6, h1 := 2, h2 := 1, M := 128, b := [48, 112, 208], n := 6, nu := 64, T := 16,
    theta1 := 8729, theta2 := 10000 }

/-- `data/specs/k7.txt`: `k = 7`, `h = 21/10`, threshold `8681/10000`. -/
def k7 : Params :=
  { k := 7, h1 := 21, h2 := 10, M := 128, b := [48, 112, 208], n := 6, nu := 64, T := 16,
    theta1 := 8681, theta2 := 10000 }

/-- `data/specs/k8.txt`: `k = 8`, `h = 21/10`, threshold `8647/10000`. -/
def k8 : Params :=
  { k := 8, h1 := 21, h2 := 10, M := 128, b := [48, 112, 208], n := 6, nu := 64, T := 16,
    theta1 := 8647, theta2 := 10000 }

/-- `data/specs/k9.txt`: `k = 9`, `h = 11/5`, threshold `8618/10000`. -/
def k9 : Params :=
  { k := 9, h1 := 11, h2 := 5, M := 128, b := [48, 112, 208], n := 6, nu := 64, T := 16,
    theta1 := 8618, theta2 := 10000 }

theorem tiny_allowed : Allowed tiny := by decide
theorem k4_allowed : Allowed k4 := by decide
theorem k5_allowed : Allowed k5 := by decide
theorem k6_allowed : Allowed k6 := by decide
theorem k7_allowed : Allowed k7 := by decide
theorem k8_allowed : Allowed k8 := by decide
theorem k9_allowed : Allowed k9 := by decide

end Results
