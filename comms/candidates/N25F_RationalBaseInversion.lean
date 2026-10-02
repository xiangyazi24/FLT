import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Field.ZMod
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_RationalBaseInversion

abbrev BasePolynomial := Polynomial (ZMod 2)
abbrev BaseField := FractionRing BasePolynomial

def baseVariable : BaseField := algebraMap BasePolynomial BaseField Polynomial.X

private theorem aeval_baseVariable_injective :
    Function.Injective (Polynomial.aeval baseVariable : BasePolynomial →ₐ[ZMod 2] BaseField) := by
  have h : (Polynomial.aeval baseVariable).toRingHom =
      algebraMap BasePolynomial BaseField := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_zmod _ _
    · change (Polynomial.aeval baseVariable) Polynomial.X = baseVariable
      exact Polynomial.aeval_X baseVariable
  exact (show Function.Injective (Polynomial.aeval baseVariable).toRingHom by
    rw [h]; exact IsFractionRing.injective BasePolynomial BaseField)

private theorem aeval_inverseBaseVariable_injective :
    Function.Injective (Polynomial.aeval baseVariable⁻¹ : BasePolynomial →ₐ[ZMod 2] BaseField) := by
  apply transcendental_iff_injective.mp
  have ht : Transcendental (ZMod 2) baseVariable :=
    transcendental_iff_injective.mpr aeval_baseVariable_injective
  simpa only [Transcendental, IsAlgebraic.inv_iff] using ht

/-- The actual rational-base homomorphism sending t to t^-1. -/
def baseInversionHom : BaseField →ₐ[ZMod 2] BaseField :=
  IsFractionRing.liftAlgHom
    (R := ZMod 2) (A := BasePolynomial) (K := BaseField) (L := BaseField)
    (g := Polynomial.aeval baseVariable⁻¹) aeval_inverseBaseVariable_injective

@[simp]
theorem baseInversionHom_algebraMap (p : BasePolynomial) :
    baseInversionHom (algebraMap BasePolynomial BaseField p) = p.aeval baseVariable⁻¹ := by
  simp [baseInversionHom]

@[simp]
theorem baseInversionHom_variable : baseInversionHom baseVariable = baseVariable⁻¹ := by
  change baseInversionHom (algebraMap BasePolynomial BaseField Polynomial.X) = _
  rw [baseInversionHom_algebraMap, Polynomial.aeval_X]

private theorem baseInversionHom_involution :
    baseInversionHom.comp baseInversionHom = AlgHom.id (ZMod 2) BaseField := by
  apply IsLocalization.algHom_ext (nonZeroDivisors BasePolynomial)
  apply Polynomial.algHom_ext
  change baseInversionHom (baseInversionHom baseVariable) = baseVariable
  rw [baseInversionHom_variable, map_inv₀, baseInversionHom_variable, inv_inv]

/-- Inverting the base variable is an actual involutive rational-field automorphism. -/
def baseInversion : BaseField ≃ₐ[ZMod 2] BaseField :=
  AlgEquiv.ofAlgHom baseInversionHom baseInversionHom
    baseInversionHom_involution baseInversionHom_involution

@[simp]
theorem baseInversion_variable : baseInversion baseVariable = baseVariable⁻¹ :=
  baseInversionHom_variable

theorem baseInversion_involutive : Function.Involutive baseInversion := by
  intro x
  exact AlgHom.congr_fun baseInversionHom_involution x

end MazurProof.N25F_RationalBaseInversion
