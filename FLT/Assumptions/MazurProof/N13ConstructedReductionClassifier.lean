import FLT.Assumptions.MazurProof.N13ConstructedSpecialization
import FLT.Assumptions.MazurProof.N13SpecialCuspCodeChecks
import FLT.Assumptions.MazurProof.N13RationalPointEndgame

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Connect the constructed additive specialization to the existing exact
set-valued classifier and compatible-reduction endpoint. Its image is all
ZMod19, witnessed by the named infinity cusp. Separatedness of this actual
kernel, and hence the final rational-point classification, is not claimed.
-/

namespace MazurProof.N13ConstructedReductionClassifier

noncomputable section
open N13ConstructedSpecialization N13SpecialAbelCode

def classifier : N13ReductionClassifier.Data G N13RationalPointEndgame.SpecialSet where
  kernel := specialization.ker
  classify P := (N13CalibratedChooser.choose P).toSpecialPic
  exact P Q := by
    constructor
    · intro h
      change specialization (P - Q) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      have hc := congrArg picCode h
      change divisorCode (chosenDivisor P) = divisorCode (chosenDivisor Q) at hc
      change divisorCode (chosenDivisor P) - divisorCode (chosenDivisor 0) =
        divisorCode (chosenDivisor Q) - divisorCode (chosenDivisor 0)
      rw [hc]
    · intro h
      change specialization (P - Q) = 0 at h
      rw [map_sub] at h
      have he := sub_eq_zero.mp h
      apply picCode_injective
      change divisorCode (chosenDivisor P) = divisorCode (chosenDivisor Q)
      change divisorCode (chosenDivisor P) - divisorCode (chosenDivisor 0) =
        divisorCode (chosenDivisor Q) - divisorCode (chosenDivisor 0) at he
      linear_combination he

/-- The actual existing rational-point endpoint structure is constructed,
with no classifier exactness or point-compatibility input. -/
def compatibleReduction : N13RationalPointEndgame.CompatibleReduction where
  classifier := classifier
  reduceCurve := N13ProperCurveReduction.reduceCurve
  classify_abel := chosen_point_specialClass
  reduce_cusp := N13ProperCurveReduction.reduceCurve_cusp

theorem specialization_infinity_cusp : specialization (N13Arithmetic.AJ13 N13Arithmetic.T) = 3 := by
  change specialization (N13RationalPointEndgame.rationalAbel .infinityMinus) = 3
  rw [specialization_rationalAbel]
  change pointCode (N13SpecialCuspReduction.specialCuspEquiv .infinityMinus) -
      pointCode (N13SpecialCuspReduction.specialCuspEquiv .infinityPlus) = 3
  rw [N13.SpecialCuspCodeChecks.pointCode_cusp, N13.SpecialCuspCodeChecks.pointCode_cusp]
  decide

theorem specialization_surjective : Function.Surjective specialization := by
  intro r
  refine ⟨(13 * r).val • (N13Arithmetic.AJ13 N13Arithmetic.T), ?_⟩
  rw [map_nsmul, specialization_infinity_cusp, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have h13 : (13 : ZMod 19) * 3 = 1 := by decide
  calc
    (13 * r) * 3 = r * ((13 : ZMod 19) * 3) := by ring
    _ = r := by rw [h13, mul_one]

@[simp] theorem classifier_kernel : classifier.kernel = specialization.ker := rfl

end
end MazurProof.N13ConstructedReductionClassifier
