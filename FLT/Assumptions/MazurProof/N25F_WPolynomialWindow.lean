import FLT.Assumptions.MazurProof.N25F_PolynomialBasisWindow
import FLT.Assumptions.MazurProof.N25F_BasePolePowers
import FLT.Assumptions.MazurProof.N25F_SectionFiniteness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A concrete independent family in the genuine bounded-pole spaces L((B+n)H). -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_WPolynomialWindow
open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectivePrincipalDivisor N25F_RiemannRochSpace N25F_SectionFiniteness
open N25F_WBasisPoleBound N25F_WBasisPoleSections N25F_BasePolePowers
open N25F_SectionMultiplication N25F_PolynomialBasisWindow
local notation "P" => Polynomial (ZMod 2)
local notation "K" => FractionRing W

/-- The actual four polynomial-basis vectors times the first n+1 base monomials. -/
def wPolynomialWindow25Two (n : ℕ) (ij : Fin 4 × Fin (n + 1)) : K :=
  algebraMap W K (((Polynomial.X : P) ^ ij.2.val) • wPolynomialBasis25Two ij.1)

theorem wPolynomialWindow25Two_linearIndependent (n : ℕ) :
    LinearIndependent (ZMod 2) (wPolynomialWindow25Two n) := by
  letI : IsScalarTower (ZMod 2) P W :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : IsScalarTower (ZMod 2) W K :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  let f : W →ₗ[ZMod 2] K := (IsScalarTower.toAlgHom (ZMod 2) W K).toLinearMap
  have hi := polynomial_basis_window_linearIndependent wPolynomialBasis25Two n
  change LinearIndependent (ZMod 2)
    (f ∘ (fun ij : Fin 4 × Fin (n + 1) => ((Polynomial.X : P) ^ ij.2.val) • wPolynomialBasis25Two ij.1))
  exact hi.map' f (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective W K))

/-- Every member obeys the full pole bound (B+n)H, including every affine atom. -/
theorem wPolynomialWindow25Two_mem (n : ℕ) (ij : Fin 4 × Fin (n + 1)) :
    wPolynomialWindow25Two n ij ∈ fullRiemannRochSpace25Two
      (((wPolynomialBasisPoleBound25Two + n : ℕ) : ℤ) • basePoleDivisor25Two) := by
  have he : wPolynomialWindow25Two n ij =
      (algebraMap W K qz) ^ ij.2.val * algebraMap W K (wPolynomialBasis25Two ij.1) := by
    change algebraMap W K (((Polynomial.X : P) ^ ij.2.val) • wPolynomialBasis25Two ij.1) = _
    rw [Algebra.smul_def, map_mul, basePolynomial_inFunctionField]
    simp only [map_pow, Polynomial.aeval_X]
  rw [he]
  have hm := mul_mem_fullRiemannRochSpace25Two
    ((ij.2.val : ℤ) • basePoleDivisor25Two)
    ((wPolynomialBasisPoleBound25Two : ℤ) • basePoleDivisor25Two)
    ((algebraMap W K qz) ^ ij.2.val) (algebraMap W K (wPolynomialBasis25Two ij.1))
    (qz_pow_mem_basePole_section_space ij.2.val)
    (wPolynomialBasis_mem_uniform_section_space ij.1)
  apply fullRiemannRochSpace25Two_mono _ _ ?_ hm
  intro A
  have hpos : 0 ≤ basePoleDivisor25Two A := by
    have h := basePoleDivisor25Two_nonneg
    change ∀ a, 0 ≤ basePoleDivisor25Two a at h
    exact h A
  have hn : (ij.2.val : ℤ) + (wPolynomialBasisPoleBound25Two : ℤ) ≤
      ((wPolynomialBasisPoleBound25Two + n : ℕ) : ℤ) := by
    have h := ij.2.isLt
    omega
  simpa only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, ← add_mul] using
    mul_le_mul_of_nonneg_right hn hpos

/-- A genuine linear lower bound along the degree-four base-pole divisor.
The constant B is the fixed basis bound, independent of n and of divisor classes. -/
theorem four_mul_succ_le_finrank_basePole_space (n : ℕ) :
    4 * (n + 1) ≤ Module.finrank (ZMod 2)
      (fullRiemannRochSpace25Two
        (((wPolynomialBasisPoleBound25Two + n : ℕ) : ℤ) • basePoleDivisor25Two)) := by
  let v : Fin 4 × Fin (n + 1) →
      fullRiemannRochSpace25Two
        (((wPolynomialBasisPoleBound25Two + n : ℕ) : ℤ) • basePoleDivisor25Two) :=
    fun ij => ⟨wPolynomialWindow25Two n ij, wPolynomialWindow25Two_mem n ij⟩
  have hv : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp (fullRiemannRochSpace25Two _).subtype
    exact wPolynomialWindow25Two_linearIndependent n
  simpa only [Fintype.card_prod, Fintype.card_fin] using hv.fintype_card_le_finrank

/-- The same actual spaces satisfy a coarse linear bound with one fixed constant. -/
theorem four_mul_le_finrank_basePole_add_constant (n : ℕ) :
    4 * n ≤ Module.finrank (ZMod 2)
      (fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) +
        4 * wPolynomialBasisPoleBound25Two := by
  by_cases hn : wPolynomialBasisPoleBound25Two ≤ n
  · have h := four_mul_succ_le_finrank_basePole_space (n - wPolynomialBasisPoleBound25Two)
    have he : wPolynomialBasisPoleBound25Two + (n - wPolynomialBasisPoleBound25Two) = n :=
      Nat.add_sub_of_le hn
    rw [he] at h
    omega
  · omega

end MazurProof.N25F_WPolynomialWindow
