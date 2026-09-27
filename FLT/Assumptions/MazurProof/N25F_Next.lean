import FLT.Assumptions.MazurProof.CurveZetaFrobeniusOrbitGrading
import FLT.Assumptions.MazurProof.NormalizedProjectiveCurveFrobenius
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientThreeBaseChange

/-!
# Full characteristic-three closed-point grading for the N25 curve

For every positive degree `d`, this carrier takes actual points on the
canonical normalized-projective curve over `CommonField 3 d`, restricts to
points of exact arithmetic-Frobenius period `d`, and quotients by Frobenius
orbit equivalence.  The degree-zero fiber is empty.

The existing degree-one-through-four semantic realization over a common
degree-twelve field remains separate.  This file supplies the full
degreewise carrier needed to connect that realization to a locally finite
closed-point grading.
-/

noncomputable section

namespace MazurProof.N25F_ThreeFullClosedPoints

open CurveZetaEffectiveDivisors
open CurveZetaFrobeniusOrbitGrading
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientThreeBaseChange

/-- Actual points of the characteristic-three canonical curve over
`CommonField 3 (d + 1)`.  The positive exponent keeps the finite-field
structure available uniformly in `d`. -/
abbrev DegreeCurvePointThree (d : ℕ) :=
  CurvePoint canonicalThreeModel (CommonField 3 (d + 1))

/-- Arithmetic Frobenius on the degree-`d + 1` canonical curve points. -/
noncomputable def degreePointFrobeniusThree (d : ℕ) :
    Equiv.Perm (DegreeCurvePointThree d) :=
  pointFrobenius canonicalThreeModel 3 (d + 1)

/-- Every positive-degree canonical curve-point type is finite. -/
noncomputable instance degreeCurvePointThreeFintype (d : ℕ) :
    Fintype (DegreeCurvePointThree d) := by
  have hfinite : Finite (DegreeCurvePointThree d) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite (DegreeCurvePointThree d)

/-- The full characteristic-three closed-point carrier.  Its degree-`n`
fiber for `n > 0` consists of exact-period-`n` Frobenius orbits over
`CommonField 3 n`. -/
noncomputable def fullClosedPointType25Three : ℕ → Type
  | 0 => ULift Empty
  | d + 1 =>
      OrbitClass (degreePointFrobeniusThree d) (d + 1) (Nat.succ_pos d)

/-- Every degree fiber in the characteristic-three carrier is finite. -/
noncomputable instance fullClosedPointType25ThreeFinite (d : ℕ) :
    Finite (fullClosedPointType25Three d) := by
  cases d with
  | zero =>
      change Finite (ULift Empty)
      exact Finite.of_injective ULift.down (by
        intro x y h
        cases x
        cases y
        cases h
        rfl)
  | succ d =>
      change Finite
        (OrbitClass (degreePointFrobeniusThree d) (d + 1) (Nat.succ_pos d))
      exact orbitClassFinite (degreePointFrobeniusThree d)
        (d + 1) (Nat.succ_pos d)

/-- The degree-zero fiber has no closed points. -/
instance fullClosedPointType25ThreeZeroIsEmpty :
    IsEmpty (fullClosedPointType25Three 0) :=
  ⟨fun x => Empty.elim x.down⟩

/-- The locally finite grading by exact Frobenius-orbit degree on the
characteristic-three canonical N25 curve. -/
noncomputable def fullClosedPointGrading25Three : ClosedPointGrading where
  Closed := fullClosedPointType25Three
  finite_closed := fullClosedPointType25ThreeFinite
  empty_degree_zero := fullClosedPointType25ThreeZeroIsEmpty

end MazurProof.N25F_ThreeFullClosedPoints
