import FLT.Assumptions.MazurProof.N25F_SharpBasis
import FLT.Assumptions.MazurProof.N25F_CoarseLowerBound
import Mathlib.RingTheory.AlgebraTower

/-!
# The sharp Riemann inequality on the N25 curve

The explicit family `b₀, …, b₃` of `N25F_SharpBasis` is `F₂[z]`-independent with
`bᵢ ∈ L(kᵢ B∞)` for `k = (0, 2, 2, 3)`. The monomial windows `zʲ bᵢ`,
`j + kᵢ ≤ n`, therefore give `Σᵢ (n + 1 - kᵢ) ≥ 4n - 3` independent elements of
`L(n B∞)`, so `4n ≤ ℓ(n B∞) + 3`. Feeding this into the existing shifted-ideal
reduction of `N25F_CoarseLowerBound` gives the sharp genus-four Riemann
inequality `deg D ≤ ℓ(D) + 3` for every divisor `D`, replacing the coarse
constant `4 · wPolynomialBasisPoleBound25Two`.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_SharpRiemann

open RationalPointsN25QuotientTwoWOpenPrimeSurjective hiding W
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectiveDivisorDegree N25F_RiemannRochSpace N25F_SectionFiniteness
open N25F_WBasisPoleSections N25F_BasePolePowers N25F_SectionMultiplication
open N25F_AffineNonpositiveRepresentative N25F_ShiftedAffineIdeal
open N25F_KernelSectionInjection N25F_CoarseLowerBound N25F_SharpBasis
open RationalPointsN25QuotientTwoFullClosedPoints N25F_ProjectivePrincipalDivisor

local notation "P" => Polynomial (ZMod 2)
local notation "K" => FractionRing W

/-- Window indices: a basis index `i` and a monomial degree `j ≤ n - kᵢ`. -/
abbrev SharpIndex (n : ℕ) := Σ i : Fin 4, Fin (n + 1 - sharpWeight i)

/-- The window element `zʲ bᵢ` in the function field. -/
def sharpWindow (n : ℕ) (p : SharpIndex n) : K :=
  algebraMap W K (((Polynomial.X : P) ^ p.2.val) • sharpBasis p.1)

/-- The window is `F₂`-independent: monomials are `F₂`-independent in `F₂[z]`,
and the family is `F₂[z]`-independent. -/
theorem sharpWindow_linearIndependent (n : ℕ) :
    LinearIndependent (ZMod 2) (sharpWindow n) := by
  letI : IsScalarTower (ZMod 2) P W :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : IsScalarTower (ZMod 2) W K :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  let f : W →ₗ[ZMod 2] K := (IsScalarTower.toAlgHom (ZMod 2) W K).toLinearMap
  have hmono : LinearIndependent (ZMod 2) (fun j : ℕ => (Polynomial.X : P) ^ j) := by
    simpa [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow] using
      (Polynomial.basisMonomials (ZMod 2)).linearIndependent
  have hprod := linearIndependent_smul hmono sharpBasis_linearIndependent
  let e : SharpIndex n → ℕ × Fin 4 := fun p => (p.2.val, p.1)
  have he : Function.Injective e := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [e, Prod.mk.injEq] at h
    obtain ⟨h2, rfl⟩ := h
    exact Sigma.ext rfl (heq_of_eq (Fin.ext h2))
  change LinearIndependent (ZMod 2)
    (f ∘ ((fun p : ℕ × Fin 4 => (Polynomial.X : P) ^ p.1 • sharpBasis p.2) ∘ e))
  exact (hprod.comp e he).map' f (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective W K))

/-- Each window element lies in `L(n B∞)`. -/
theorem sharpWindow_mem (n : ℕ) (p : SharpIndex n) :
    sharpWindow n p ∈ fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two) := by
  have he : sharpWindow n p =
      (algebraMap W K qz) ^ p.2.val * algebraMap W K (sharpBasis p.1) := by
    change algebraMap W K (((Polynomial.X : P) ^ p.2.val) • sharpBasis p.1) = _
    rw [Algebra.smul_def, map_mul, basePolynomial_inFunctionField]
    simp only [map_pow, Polynomial.aeval_X]
  rw [he]
  have hm := mul_mem_fullRiemannRochSpace25Two
    ((p.2.val : ℤ) • basePoleDivisor25Two)
    ((sharpWeight p.1 : ℤ) • basePoleDivisor25Two)
    ((algebraMap W K qz) ^ p.2.val) (algebraMap W K (sharpBasis p.1))
    (qz_pow_mem_basePole_section_space p.2.val) (sharpBasis_mem p.1)
  apply fullRiemannRochSpace25Two_mono _ _ ?_ hm
  intro A
  have hpos : 0 ≤ basePoleDivisor25Two A := by
    have h := basePoleDivisor25Two_nonneg
    change ∀ a, 0 ≤ basePoleDivisor25Two a at h
    exact h A
  have hn : (p.2.val : ℤ) + (sharpWeight p.1 : ℤ) ≤ (n : ℤ) := by
    have h := p.2.isLt
    omega
  simpa only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, ← add_mul] using
    mul_le_mul_of_nonneg_right hn hpos

theorem four_mul_le_card_sharpIndex_add_three (n : ℕ) :
    4 * n ≤ Fintype.card (SharpIndex n) + 3 := by
  have hc (i : Fin 4) : Fintype.card (Fin (n + 1 - sharpWeight i)) = n + 1 - sharpWeight i := by
    rw [Fintype.card_eq_nat_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  have w0 : sharpWeight 0 = 0 := rfl
  have w1 : sharpWeight 1 = 2 := rfl
  have w2 : sharpWeight 2 = 2 := rfl
  have w3 : sharpWeight 3 = 3 := rfl
  rw [Fintype.card_sigma, Fin.sum_univ_four, hc, hc, hc, hc, w0, w1, w2, w3]
  omega

/-- The sharp count along the base-pole divisor: `ℓ(n B∞) ≥ 4n - 3`. -/
theorem four_mul_le_finrank_basePole_add_three (n : ℕ) :
    4 * n ≤ Module.finrank (ZMod 2)
      (fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two)) + 3 := by
  let v : SharpIndex n → fullRiemannRochSpace25Two ((n : ℤ) • basePoleDivisor25Two) :=
    fun p => ⟨sharpWindow n p, sharpWindow_mem n p⟩
  have hv : LinearIndependent (ZMod 2) v := by
    apply LinearIndependent.of_comp (fullRiemannRochSpace25Two _).subtype
    exact sharpWindow_linearIndependent n
  have h1 := hv.fintype_card_le_finrank
  have h2 := four_mul_le_card_sharpIndex_add_three n
  omega

/-- **Sharp Riemann inequality** on the genus-four N25 curve:
`deg D ≤ ℓ(D) + 3` for every divisor `D`. The proof is the shifted-ideal
reduction of `degree_le_finrank_add_four_basis_bound` with the sharp count
`4n ≤ ℓ(n B∞) + 3` in place of the coarse one. -/
theorem degree_le_finrank_add_three (D : ProjectiveDivisor25Two) :
    fullClosedPointGrading25Two.divisorDegree D ≤
      (Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) : ℤ) + 3 := by
  let E := affineNonpositiveRepresentative25Two D
  obtain ⟨n, hn, hdom⟩ := affineNonpositiveRepresentative25Two_le_basePole_multiple D
  obtain ⟨I, hI, hcount, _⟩ := exists_shifted_affine_ideal D
  have hdim := finrank_basePole_le_section_add_cost n I hI E hcount hdom
  have hbase := four_mul_le_finrank_basePole_add_three n
  have hcost := affine_and_boundary_cost E n I hI hcount hdom
  have hdegree : fullClosedPointGrading25Two.divisorDegree E =
      fullClosedPointGrading25Two.divisorDegree D :=
    affineNonpositiveRepresentative25Two_degree D
  have hrank : Module.finrank (ZMod 2) (fullRiemannRochSpace25Two E) =
      Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) :=
    affineNonpositiveRepresentative25Two_finrank D
  change _ ≤ _ + affineCost I + _ + _ + _ at hdim
  rw [hdegree] at hcost
  rw [hrank] at hdim
  omega

end MazurProof.N25F_SharpRiemann
