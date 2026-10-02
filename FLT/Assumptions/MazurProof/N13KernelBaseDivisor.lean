import FLT.Assumptions.MazurProof.N13ConstructedReductionClassifier

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

The actual additive specialization kernel, translated by the two finite
cusps C and B, has the literal special divisor C+B. The nonzero code 8
excludes the canonical pencil, so this is equality of divisors, not merely
equality of their classes. The infinity-mark shift is a separate step.
-/

namespace MazurProof.N13KernelBaseDivisor

noncomputable section
open scoped Sym2
open N13SpecialAbelCode N13SpecialCuspReduction N13ConstructedSpecialization

abbrev Kernel := specialization.ker

def baseDivisor : EffectiveDivisorTwo :=
  s(specialCuspEquiv .zeroPlus, specialCuspEquiv .negOneMinus)

def baseTranslate : G :=
  N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint .zeroPlus) +
    N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint .negOneMinus)

theorem baseDivisor_code : divisorCode baseDivisor = 8 := by
  rw [baseDivisor, divisorCode_mk,
    N13.SpecialCuspCodeChecks.pointCode_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp]
  decide

theorem baseDivisor_not_canonical :
    ¬ N13AbelFiberTwoModel.IsCanonical baseDivisor := by
  rintro ⟨b, hb⟩
  have hz : divisorCode baseDivisor = 0 := by
    rw [← hb, divisorCode_canonicalDivisor]
  rw [baseDivisor_code] at hz
  exact (by decide : (8 : ZMod 19) ≠ 0) hz

theorem divisor_eq_base_of_code (D : EffectiveDivisorTwo)
    (h : divisorCode D = 8) : D = baseDivisor := by
  have he := (divisorCode_eq_iff_abelRel D baseDivisor).mp
    (h.trans baseDivisor_code.symm)
  rcases he with he | ⟨_, hb⟩
  · exact he
  · exact (baseDivisor_not_canonical hb).elim

theorem chosen_zero_code : divisorCode (chosenDivisor 0) = 16 := by
  have h := congrArg picCode chosen_zero_specialClass
  change divisorCode (chosenDivisor 0) =
    divisorCode s(N13RationalPointEndgame.specialAnchor,
      N13RationalPointEndgame.specialAnchor) at h
  exact h.trans N13.SpecialCuspCodeChecks.divisorCode_double_anchor

theorem specialization_cusp (c : N13Mumford.Cusp13) :
    specialization (N13RationalPointEndgame.rationalAbel (N13Mumford.cuspPoint c)) =
      pointCode (specialCuspEquiv c) - 8 := by
  rw [specialization_rationalAbel, N13ProperCurveReduction.reduceCurve_cusp]
  change pointCode (specialCuspEquiv c) -
    pointCode (specialCuspEquiv .infinityPlus) = _
  rw [N13.SpecialCuspCodeChecks.pointCode_cusp .infinityPlus]

theorem specialization_baseTranslate : specialization baseTranslate = 8 - 16 := by
  rw [baseTranslate, map_add, specialization_cusp, specialization_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp,
    N13.SpecialCuspCodeChecks.pointCode_cusp]
  decide

theorem chosen_translated_code (z : Kernel) :
    divisorCode (chosenDivisor ((z : G) + baseTranslate)) = 8 := by
  have hz : specialization (z : G) = 0 := z.property
  have ht : specialization ((z : G) + baseTranslate) = 8 - 16 := by
    rw [map_add, hz, zero_add, specialization_baseTranslate]
  change divisorCode (chosenDivisor ((z : G) + baseTranslate)) -
    divisorCode (chosenDivisor 0) = 8 - 16 at ht
  rw [chosen_zero_code] at ht
  exact sub_left_injective ht

/-- The literal special divisor of the same chosen geometric witness. -/
theorem chosen_translated_divisor (z : Kernel) :
    (N13CalibratedChooser.choose ((z : G) + baseTranslate)).specialDivisor =
      baseDivisor :=
  divisor_eq_base_of_code _ (chosen_translated_code z)

end
end MazurProof.N13KernelBaseDivisor
