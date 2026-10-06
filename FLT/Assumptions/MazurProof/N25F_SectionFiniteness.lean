import FLT.Assumptions.MazurProof.N25F_ZeroDegreeConstants
import FLT.Assumptions.MazurProof.CurveDivisorPicard
import Mathlib.Logic.Equiv.Option

/-! Finiteness of the actual section spaces follows from the genuine binary
constant kernel and fixed-degree effective divisors on the full grading. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_SectionFiniteness
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor N25F_ProjectiveProductFormula
open N25F_RiemannRochSpace N25F_ZeroDegreeConstants
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The nonzero elements of the genuine bounded-pole vector space. -/
abbrev NonzeroSection25Two (D : ProjectiveDivisor25Two) :=
  {f : fullRiemannRochSpace25Two D // f ≠ 0}

private theorem section_value_ne_zero (D : ProjectiveDivisor25Two) (f : NonzeroSection25Two D) :
    (f.1 : CurveField) ≠ 0 := fun h => f.2 (Subtype.ext h)

private def sectionUnit (D : ProjectiveDivisor25Two) (f : NonzeroSection25Two D) :
    Additive CurveFieldˣ :=
  Additive.ofMul (Units.mk0 (f.1 : CurveField) (section_value_ne_zero D f))

private theorem section_divisor_nonneg (D : ProjectiveDivisor25Two) (f : NonzeroSection25Two D) :
    ∀ A, 0 ≤ D A + projectivePrincipalDivisor (sectionUnit D f) A := by
  rcases f.1.property with h | ⟨hf, h⟩
  · exact (section_value_ne_zero D f h).elim
  exact h

private def sectionEffectiveData (D : ProjectiveDivisor25Two) (f : NonzeroSection25Two D) :
    fullClosedPointGrading25Two.EffDiv :=
  Finsupp.mapRange Int.toNat rfl (D + projectivePrincipalDivisor (sectionUnit D f))

private theorem sectionEffectiveData_cast (D : ProjectiveDivisor25Two) (f : NonzeroSection25Two D) :
    fullClosedPointGrading25Two.effectiveToDivisor (sectionEffectiveData D f) =
      D + projectivePrincipalDivisor (sectionUnit D f) := by
  ext A
  change ((D A + projectivePrincipalDivisor (sectionUnit D f) A).toNat : ℤ) = _
  exact Int.natCast_toNat_eq_self.mpr (section_divisor_nonneg D f A)

/-- The effective divisor D+div(f), with its exact full-grading degree. -/
def effectiveDivisorOfNonzeroSection25Two (D : ProjectiveDivisor25Two) (f : NonzeroSection25Two D) :
    fullClosedPointGrading25Two.EffDivOfDegree
      (fullClosedPointGrading25Two.divisorDegree D).toNat := by
  refine ⟨sectionEffectiveData D f, ?_⟩
  have h : (fullClosedPointGrading25Two.divDegree (sectionEffectiveData D f) : ℤ) =
      fullClosedPointGrading25Two.divisorDegree D := by
    rw [← fullClosedPointGrading25Two.divisorDegree_effectiveToDivisor,
      sectionEffectiveData_cast, map_add, projectivePrincipalDivisor_degree_eq_zero, add_zero]
  simpa only [Int.toNat_natCast] using congrArg Int.toNat h

theorem effectiveDivisorOfNonzeroSection25Two_cast
    (D : ProjectiveDivisor25Two) (f : NonzeroSection25Two D) :
    fullClosedPointGrading25Two.effectiveToDivisor (effectiveDivisorOfNonzeroSection25Two D f).1 =
      D + projectivePrincipalDivisor
        (Additive.ofMul (Units.mk0 (f.1 : CurveField) (section_value_ne_zero D f))) :=
  sectionEffectiveData_cast D f

/-- The actual constant-kernel theorem makes the effective-section map injective. -/
theorem effectiveDivisorOfNonzeroSection25Two_injective (D : ProjectiveDivisor25Two) :
    Function.Injective (effectiveDivisorOfNonzeroSection25Two D) := by
  intro f g h
  have he := congrArg (fun E => fullClosedPointGrading25Two.effectiveToDivisor E.1) h
  rw [effectiveDivisorOfNonzeroSection25Two_cast,
    effectiveDivisorOfNonzeroSection25Two_cast] at he
  have hu := fullPrincipalDivisor_injective (add_left_cancel he)
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun u : Additive CurveFieldˣ => (u.toMul : CurveField)) hu

/-- This uses the full grading's uniform fixed-degree finiteness producer. -/
instance nonzeroSection25Two_finite (D : ProjectiveDivisor25Two) : Finite (NonzeroSection25Two D) :=
  Finite.of_injective (effectiveDivisorOfNonzeroSection25Two D)
    (effectiveDivisorOfNonzeroSection25Two_injective D)

instance fullRiemannRochSpace25Two_finite (D : ProjectiveDivisor25Two) :
    Finite (fullRiemannRochSpace25Two D) := by
  classical
  exact Finite.of_equiv (Option (NonzeroSection25Two D))
    (Equiv.optionSubtypeNe (0 : fullRiemannRochSpace25Two D))

/-- Every actual bounded-pole section space is finite-dimensional over F2. -/
instance fullRiemannRochSpace25Two_moduleFinite (D : ProjectiveDivisor25Two) :
    Module.Finite (ZMod 2) (fullRiemannRochSpace25Two D) := by infer_instance

end MazurProof.N25F_SectionFiniteness
