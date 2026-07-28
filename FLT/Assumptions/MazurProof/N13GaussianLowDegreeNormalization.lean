import FLT.Assumptions.MazurProof.N13GaussianLocalization
import FLT.Assumptions.MazurProof.N13GaussianLowDegree
import FLT.Assumptions.MazurProof.N13LowDegreeKummerHom
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Primitive integral normalization of low-degree N13 Kummer polynomials

A rational Mumford polynomial of degree at most two need not itself have
`2`-adic integral coefficients.  We clear its `ℤ₂` denominators using the
fraction-ring universal property and then divide by its polynomial content.
The resulting polynomial is primitive, still has degree at most two, and has
nonzero reduction modulo `2`.

Consequently its evaluation at the explicit order generator has a constant
first jet and zero ramified logarithm.  This is the structural local argument
for arbitrary low-degree Mumford representatives; it uses neither a split
root calculation nor a list of residue cases.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13GaussianLowDegreeNormalization

noncomputable section

open N13GaussianLocalization
open N13GaussianOrderTwo
open N13GaussianLowDegree

abbrev Z2 : Type := ℤ_[2]

abbrev Q2 : Type := ℚ_[2]

local instance z2NormalizationMonoid :
    NormalizationMonoid Z2 :=
  UniqueFactorizationMonoid.normalizationMonoid

local instance z2NormalizedGCDMonoid :
    NormalizedGCDMonoid Z2 :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid Z2

/-- Base change of a rational polynomial to `ℚ₂`. -/
def toQ2Polynomial (p : ℚ[X]) : Q2[X] :=
  p.map (algebraMap ℚ Q2)

/-- Clear all `ℤ₂` denominators at once. -/
def integralNormalization (p : ℚ[X]) : Z2[X] :=
  IsLocalization.integerNormalization
    (nonZeroDivisors Z2) (toQ2Polynomial p)

/-- Remove the common `ℤ₂` content after denominator clearing. -/
def primitiveNormalization (p : ℚ[X]) : Z2[X] :=
  (integralNormalization p).primPart

theorem toQ2Polynomial_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    toQ2Polynomial p ≠ 0 := by
  exact
    (Polynomial.map_ne_zero_iff
      (algebraMap ℚ Q2).injective).2 hp

theorem integralNormalization_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    integralNormalization p ≠ 0 := by
  exact
    (IsFractionRing.integerNormalization_eq_zero_iff
      (A := Z2) (K := Q2)).not.mpr
      (toQ2Polynomial_ne_zero hp)

theorem integralNormalization_content_ne_zero
    {p : ℚ[X]} (hp : p ≠ 0) :
    (integralNormalization p).content ≠ 0 := by
  exact
    Polynomial.content_eq_zero_iff.not.mpr
      (integralNormalization_ne_zero hp)

/-- The primitive integral polynomial differs from the original rational
polynomial by one nonzero `ℚ₂` scalar. -/
theorem primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : Q2, c ≠ 0 ∧
      (primitiveNormalization p).map (algebraMap Z2 Q2) =
        C c * toQ2Polynomial p := by
  let U₀ : Z2[X] := integralNormalization p
  let U : Z2[X] := primitiveNormalization p
  obtain ⟨b, hb, hclear⟩ :=
    IsLocalization.integerNormalization_spec
      (nonZeroDivisors Z2) (toQ2Polynomial p)
  have hb0 : b ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbc :
      algebraMap Z2 Q2 b ≠ 0 :=
    (IsFractionRing.injective Z2 Q2).ne hb0
  have hcontent :
      algebraMap Z2 Q2 U₀.content ≠ 0 :=
    (IsFractionRing.injective Z2 Q2).ne
      (integralNormalization_content_ne_zero hp)
  let c : Q2 :=
    (algebraMap Z2 Q2 U₀.content)⁻¹ *
      algebraMap Z2 Q2 b
  refine ⟨c, mul_ne_zero (inv_ne_zero hcontent) hbc, ?_⟩
  have hdecomp :
      U₀.map (algebraMap Z2 Q2) =
        C (algebraMap Z2 Q2 U₀.content) *
          U.map (algebraMap Z2 Q2) := by
    simpa only [U₀, U, integralNormalization,
      primitiveNormalization, Polynomial.map_mul,
      Polynomial.map_C] using
      congrArg (Polynomial.map (algebraMap Z2 Q2))
        U₀.eq_C_content_mul_primPart
  have hcleared :
      U₀.map (algebraMap Z2 Q2) =
        C (algebraMap Z2 Q2 b) * toQ2Polynomial p := by
    simpa only [U₀, integralNormalization,
      Algebra.smul_def, Polynomial.algebraMap_apply] using hclear
  calc
    U.map (algebraMap Z2 Q2) =
        1 * U.map (algebraMap Z2 Q2) := by rw [one_mul]
    _ =
        (C (algebraMap Z2 Q2 U₀.content)⁻¹ *
            C (algebraMap Z2 Q2 U₀.content)) *
          U.map (algebraMap Z2 Q2) := by
      rw [← C_mul, inv_mul_cancel₀ hcontent, C_1, one_mul]
    _ =
        C (algebraMap Z2 Q2 U₀.content)⁻¹ *
          (C (algebraMap Z2 Q2 U₀.content) *
            U.map (algebraMap Z2 Q2)) := by ring
    _ =
        C (algebraMap Z2 Q2 U₀.content)⁻¹ *
          (C (algebraMap Z2 Q2 b) * toQ2Polynomial p) := by
      rw [← hdecomp, hcleared]
    _ =
        (C (algebraMap Z2 Q2 U₀.content)⁻¹ *
          C (algebraMap Z2 Q2 b)) * toQ2Polynomial p := by ring
    _ = C c * toQ2Polynomial p := by
      rw [← C_mul]

theorem primitiveNormalization_natDegree_le
    {p : ℚ[X]} (hdeg : p.natDegree ≤ 2) :
    (primitiveNormalization p).natDegree ≤ 2 := by
  rw [primitiveNormalization, Polynomial.natDegree_primPart]
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_contra hcoeff
  have hnU :
      n ∈ (integralNormalization p).support :=
    Polynomial.mem_support_iff.mpr hcoeff
  have hnp :
      n ∈ (toQ2Polynomial p).support :=
    IsLocalization.integerNormalization_support
      (nonZeroDivisors Z2) (toQ2Polynomial p) hnU
  have hnle :
      n ≤ (toQ2Polynomial p).natDegree :=
    Polynomial.le_natDegree_of_mem_supp n hnp
  have hmapdeg :
      (toQ2Polynomial p).natDegree ≤ 2 :=
    Polynomial.natDegree_map_le.trans hdeg
  omega

/-- Primitivity prevents all coefficients from vanishing modulo `2`. -/
theorem residuePolynomial_primitiveNormalization_ne_zero
    (p : ℚ[X]) :
    residuePolynomial (primitiveNormalization p) ≠ 0 := by
  let U : Z2[X] := primitiveNormalization p
  intro hzero
  have hle :
      U.contentIdeal ≤ RingHom.ker PadicInt.toZMod := by
    rw [Polynomial.contentIdeal_def, Ideal.span_le]
    intro z hz
    obtain ⟨n, -, rfl⟩ :=
      Polynomial.mem_coeffs_iff.mp hz
    change PadicInt.toZMod (U.coeff n) = 0
    have hcoeff :=
      congrArg
        (fun q : (ZMod 2)[X] => q.coeff n) hzero
    simpa [residuePolynomial, U] using hcoeff
  have htop : U.contentIdeal = ⊤ :=
    (Polynomial.isPrimitive_iff_contentIdeal_eq_top U).mp
      (integralNormalization p).isPrimitive_primPart
  rw [htop, PadicInt.ker_toZMod] at hle
  exact
    (IsLocalRing.maximalIdeal.isMaximal Z2).ne_top
      (top_unique hle)

/-- The primitive normalization therefore has a genuine constant unit jet
with zero first logarithm. -/
theorem dlog_primitiveNormalization
    {p : ℚ[X]} (hdeg : p.natDegree ≤ 2) :
    RamifiedDlog.dlog
        (lowDegreeJet
          (primitiveNormalization p)
          (residuePolynomial_primitiveNormalization_ne_zero p)
          (by
            exact Polynomial.natDegree_map_le.trans
              (primitiveNormalization_natDegree_le hdeg))) =
      0 :=
  dlog_lowDegreeJet _ _ _

/-- Evaluation of the primitive integral normalization in the explicit
order differs from evaluation of the original rational polynomial by one
nonzero `ℚ₂` scalar. -/
theorem thetaEval_primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : Q2, c ≠ 0 ∧
      algebraMap N13GaussianOrderTwo.Order
          N13GaussianLocalization.LocalOrder
          (thetaEval (primitiveNormalization p)) =
        q2ToLocalOrder c *
          eval₂ qToLocalOrder localTheta p := by
  obtain ⟨c, hc, hpoly⟩ :=
    primitiveNormalization_spec hp
  refine ⟨c, hc, ?_⟩
  have hz2 :
      q2ToLocalOrder.comp (algebraMap Z2 Q2) =
        z2ToLocalOrder := by
    apply RingHom.ext
    intro z
    exact q2ToLocalOrder_z2 z
  calc
    algebraMap N13GaussianOrderTwo.Order
        N13GaussianLocalization.LocalOrder
        (thetaEval (primitiveNormalization p)) =
      eval₂
        ((algebraMap N13GaussianOrderTwo.Order
            N13GaussianLocalization.LocalOrder).comp
          (algebraMap Z2 N13GaussianOrderTwo.Order))
        localTheta (primitiveNormalization p) := by
      simpa only [thetaEval, localTheta] using
        Polynomial.hom_eval₂
          (primitiveNormalization p)
          (algebraMap Z2 N13GaussianOrderTwo.Order)
          (algebraMap N13GaussianOrderTwo.Order
            N13GaussianLocalization.LocalOrder)
          N13GaussianOrderTwo.theta
    _ =
      eval₂ z2ToLocalOrder localTheta
        (primitiveNormalization p) := by
      rfl
    _ =
      eval₂ q2ToLocalOrder localTheta
        ((primitiveNormalization p).map
          (algebraMap Z2 Q2)) := by
      rw [Polynomial.eval₂_map, hz2]
    _ =
      eval₂ q2ToLocalOrder localTheta
        (C c * toQ2Polynomial p) := by rw [hpoly]
    _ =
      q2ToLocalOrder c *
        eval₂ q2ToLocalOrder localTheta
          (toQ2Polynomial p) := by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
    _ =
      q2ToLocalOrder c *
        eval₂ qToLocalOrder localTheta p := by
      rw [toQ2Polynomial, Polynomial.eval₂_map]
      rfl

/-- The same statement expressed in the global sextic algebra. -/
theorem globalEval_primitiveNormalization_spec
    {p : ℚ[X]} (hp : p ≠ 0) :
    ∃ c : Q2, c ≠ 0 ∧
      algebraMap N13GaussianOrderTwo.Order
          N13GaussianLocalization.LocalOrder
          (thetaEval (primitiveNormalization p)) =
        q2ToLocalOrder c *
          sexticToLocalOrder
            (N13SexticSquareclass.ofPoly p) := by
  simpa only [sexticToLocalOrder_ofPoly] using
    thetaEval_primitiveNormalization_spec hp

/-- Applied to the actual low-degree Mumford section, the raw Kummer
polynomial has a primitive integral local representative whose exact first
jet has zero logarithm. -/
theorem lowRep_has_zero_integralJet
    (D : N13LowDegreeKummerHom.LowRep) :
    let U := primitiveNormalization D.toSemi.u
    let hne := residuePolynomial_primitiveNormalization_ne_zero
      D.toSemi.u
    let hdeg :
        (residuePolynomial U).natDegree ≤ 2 :=
      Polynomial.natDegree_map_le.trans
        (primitiveNormalization_natDegree_le D.degree_le_two)
    (∃ c : Q2, c ≠ 0 ∧
      algebraMap N13GaussianOrderTwo.Order
          N13GaussianLocalization.LocalOrder
          (thetaEval U) =
        q2ToLocalOrder c *
          sexticToLocalOrder
            (N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D))) ∧
      RamifiedDlog.dlog
        (lowDegreeJet U hne hdeg) = 0 := by
  dsimp only
  have hu :
      D.toSemi.u ≠ 0 :=
    D.toSemi.u_monic.ne_zero
  constructor
  · have hspec :=
      globalEval_primitiveNormalization_spec hu
    have huTheta :
        N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D) =
          N13SexticSquareclass.ofPoly D.toSemi.u := by
      rw [N13MumfordKummerValue.uTheta_eq_mk]
      rfl
    rw [huTheta]
    exact hspec
  · exact dlog_primitiveNormalization D.degree_le_two

end

end MazurProof.N13GaussianLowDegreeNormalization
