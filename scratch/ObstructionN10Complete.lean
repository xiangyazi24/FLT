import FLT.Assumptions.MazurProof.DescentObstruction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The `N = 10` obstruction curve, with completeness isolated as an axiom

This scratch file records the "Approach B + axiom" path for the obstruction
curve used in the `ℤ/2 × ℤ/10` exclusion.  The finite local checks are imported
from `DescentObstruction`; the only global arithmetic input here is the
rank-zero/completeness certificate saying that the displayed points are all
rational points.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof
namespace ObstructionN10Complete

/-- The `N = 10` obstruction curve model used by the descent checks. -/
def E20 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := -1
  a₆ := 0

lemma E20_delta : E20.Δ = (80 : ℚ) := by
  norm_num [E20, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E20_isElliptic : E20.IsElliptic where
  isUnit := by
    rw [E20_delta]
    norm_num

abbrev E20Point : Type :=
  WeierstrassCurve.Affine.Point E20

/-- Affine equation for the model `y² = x³ + x² - x`. -/
def E20AffineEquation (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + x ^ 2 - x

def knownAffinePoints : List (ℚ × ℚ) :=
  [(-1, 1), (-1, -1), (0, 0), (1, 1), (1, -1)]

/--
The six known rational points, represented by affine coordinates plus `none`
for the point at infinity.
-/
def knownRationalPointCoords : List (Option (ℚ × ℚ)) :=
  none :: knownAffinePoints.map some

lemma eq_m1_1 : WeierstrassCurve.Affine.Equation E20 (-1 : ℚ) 1 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_m1_m1 : WeierstrassCurve.Affine.Equation E20 (-1 : ℚ) (-1) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_0_0 : WeierstrassCurve.Affine.Equation E20 (0 : ℚ) 0 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_1_1 : WeierstrassCurve.Affine.Equation E20 (1 : ℚ) 1 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

lemma eq_1_m1 : WeierstrassCurve.Affine.Equation E20 (1 : ℚ) (-1) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E20]

noncomputable def Pm1_1 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_m1_1

noncomputable def Pm1_m1 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_m1_m1

noncomputable def P0_0 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_0_0

noncomputable def P1_1 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_1_1

noncomputable def P1_m1 : E20Point :=
  WeierstrassCurve.Affine.Point.mk eq_1_m1

/-- The six known rational points on `E20`, including the point at infinity. -/
noncomputable def knownPoint : Fin 6 → E20Point
  | 0 => 0
  | 1 => Pm1_1
  | 2 => Pm1_m1
  | 3 => P0_0
  | 4 => P1_1
  | 5 => P1_m1

lemma knownAffinePoints_satisfy_equation {p : ℚ × ℚ}
    (hp : p ∈ knownAffinePoints) : E20AffineEquation p.1 p.2 := by
  fin_cases hp <;> norm_num [knownAffinePoints, E20AffineEquation]

def negAffineCoord (p : ℚ × ℚ) : ℚ × ℚ :=
  (p.1, -p.2)

def negRationalPointCoord : Option (ℚ × ℚ) → Option (ℚ × ℚ)
  | none => none
  | some p => some (negAffineCoord p)

lemma knownAffinePoints_closed_under_neg {p : ℚ × ℚ}
    (hp : p ∈ knownAffinePoints) : negAffineCoord p ∈ knownAffinePoints := by
  fin_cases hp <;> norm_num [knownAffinePoints, negAffineCoord]

lemma knownRationalPointCoords_closed_under_neg {p : Option (ℚ × ℚ)}
    (hp : p ∈ knownRationalPointCoords) :
    negRationalPointCoord p ∈ knownRationalPointCoords := by
  fin_cases hp <;>
    norm_num [knownRationalPointCoords, knownAffinePoints, negRationalPointCoord, negAffineCoord]

def IsKnownPoint (P : E20Point) : Prop :=
  P = knownPoint 0 ∨ P = knownPoint 1 ∨ P = knownPoint 2 ∨
    P = knownPoint 3 ∨ P = knownPoint 4 ∨ P = knownPoint 5

/--
Rank-zero/completeness certificate for the obstruction curve.

This is the global arithmetic input: the five affine points above, together
with the point at infinity, are all rational points on `E20`.
-/
axiom E20_rational_points_complete (P : E20Point) : IsKnownPoint P

/-- In this obstruction model, the known rational points are the cuspidal points. -/
def IsCuspidalPoint (P : E20Point) : Prop :=
  IsKnownPoint P

def IsNonCuspidalPoint (P : E20Point) : Prop :=
  ¬ IsCuspidalPoint P

/-- Therefore the obstruction curve has no non-cuspidal rational points. -/
theorem no_non_cuspidal_rational_points :
    ¬ ∃ P : E20Point, IsNonCuspidalPoint P := by
  rintro ⟨P, hP⟩
  exact hP (E20_rational_points_complete P)

end ObstructionN10Complete
end MazurProof
