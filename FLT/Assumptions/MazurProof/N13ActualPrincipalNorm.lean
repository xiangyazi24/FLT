import FLT.Assumptions.MazurProof.N13PrincipalHermiteNormalization
import FLT.Assumptions.MazurProof.SexticMumfordNorm

/-!
Operative source pin: 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

The actual affine principal relation determines the cleared numerator's
norm up to a nonzero scalar. This retains all four graph factors and then
translates that exact identity into the good-model Hermite shape.
-/

namespace MazurProof.N13ActualPrincipalNorm

noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem norm_polynomial_of_principal
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ) (n : R)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ * toPrincipalIdeal R F α =
      mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (D₀.u * D₁.u))) :
    ∃ k : Kˣ,
      (coeff0 M n) ^ 2 - (coeffY M n) ^ 2 * M.f =
        C (k : K) * (D₀.u * D₁.u) * (D₂.u * D₃.u) := by
  obtain ⟨q, hq⟩ := N13PrincipalBranchBalance.exists_scalar_norm_ratio D₀ D₁ D₂ D₃ α h
  let a : F := (N13Infinity.functionConstUnit K q : F)
  let d : F := (N13Infinity.functionConstUnit K q⁻¹ : F)
  let x : F := algebraMap R F (xClass M (D₀.u * D₁.u))
  let y : F := algebraMap R F (xClass M (D₂.u * D₃.u))
  let αbar : F := (conjugateFunctionUnit M α : F)
  have hqf : a * ((α : F) * αbar) * x = y :=
    congrArg (fun u : Fˣ => (u : F)) hq
  have hi : d * a = 1 := by
    change (N13Infinity.functionConstUnit K q⁻¹ : F) *
      (N13Infinity.functionConstUnit K q : F) = 1
    simp [N13Infinity.functionConstUnit, N13Infinity.coordinateConstUnit, ← map_mul]
  have hnbar := congrArg (functionConjugateEquiv M) hn
  simp only [map_mul, functionConjugateEquiv_algebraMap, conjugate_xClass] at hnbar
  have hnorm : algebraMap R F (SexticMumford.norm M n) = (α : F) * αbar * x ^ 2 := by
    rw [SexticMumford.norm, map_mul, hn, hnbar]
    change ((α : F) * x) * (αbar * x) = _
    ring
  have hratio : a * algebraMap R F (SexticMumford.norm M n) = x * y := by
    rw [hnorm]
    calc
      a * ((α : F) * αbar * x ^ 2) = x * (a * ((α : F) * αbar) * x) := by ring
      _ = x * y := by rw [hqf]
  refine ⟨q⁻¹, ?_⟩
  apply xClass_injective M
  rw [← norm_eq_xClass_coeff]
  apply IsFractionRing.injective R F
  calc
    algebraMap R F (SexticMumford.norm M n) = d * (a * algebraMap R F (SexticMumford.norm M n)) := by
      rw [← mul_assoc, hi, one_mul]
    _ = d * (x * y) := by rw [hratio]
    _ = algebraMap R F (xClass M (C (↑(q⁻¹) : K) * (D₀.u * D₁.u) * (D₂.u * D₃.u))) := by
      rw [xClass_mul, xClass_mul, map_mul, map_mul]
      change algebraMap R F (algebraMap K R (↑(q⁻¹) : K)) * (x * y) =
        (algebraMap R F (algebraMap K R (↑(q⁻¹) : K)) * x) * y
      ring

theorem good_norm_eq_sextic_norm (n : R) :
    goodP n ^ 2 - goodP n * goodQ n * N13GeneralizedMumfordIntegral.hPoly -
      goodQ n ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
        (coeff0 M n) ^ 2 - (coeffY M n) ^ 2 * M.f := by
  rw [show M.f = N13Mumford.f K from rfl,
    N13GoodSexticCoordinateEquiv.sextic_eq_h_sq_add_four_rhs (K := K)]
  unfold goodP goodQ
  ring

theorem shape_coefficients (n : R) (A b : K[X])
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy) :
    goodP n = (X ^ 2 + X) * A ∧ goodQ n = b := by
  have he := (toGood_recompose n).symm.trans hshape
  constructor
  · have h := congrArg N13GeneralizedMumfordIntegral.coeff0 he
    simpa only [map_add, N13GeneralizedMumfordIntegral.coeff0_xClass,
      N13GeneralizedMumfordIntegral.coeff0_xClass_mul_yClass, add_zero] using h
  · have h := congrArg N13GeneralizedMumfordIntegral.coeffY he
    simpa only [map_add, N13GeneralizedMumfordIntegral.coeffY_xClass,
      N13GeneralizedMumfordIntegral.coeffY_xClass_mul_yClass, zero_add] using h

theorem norm_of_actual_shape (P Q : DiskPair) (α : Fˣ) (n : R) (A b : K[X])
    (h : mumfordIdealUnit M P.mumford.toSemi * mumfordIdealUnit M P.mumford.toSemi *
      toPrincipalIdeal R F α = mumfordIdealUnit M Q.mumford.toSemi *
        mumfordIdealUnit M B.mumford.toSemi)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)))
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy) :
    ∃ k : Kˣ,
      ((X ^ 2 + X) * A) ^ 2 - ((X ^ 2 + X) * A) * b *
          N13GeneralizedMumfordIntegral.hPoly - b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
        C (k : K) * (N13TwoAdicMumfordTransport.mapPoly P.u) ^ 2 *
          (X ^ 2 + X) * N13TwoAdicMumfordTransport.mapPoly Q.u := by
  obtain ⟨k, hk⟩ := norm_polynomial_of_principal P.mumford.toSemi P.mumford.toSemi
    Q.mumford.toSemi B.mumford.toSemi α n h (by rw [← pow_two]; exact hn)
  obtain ⟨hp, hq⟩ := shape_coefficients n A b hshape
  have hB : B.mumford.u = (X ^ 2 + X : K[X]) := by
    simp [N13TwoAdicAbelChartPic.DiskPair.mumford_u,
      N13TwoAdicMumfordTransport.mapPoly, N13FormalAbelLinearization.uBase]
  refine ⟨k, ?_⟩
  simp only [← hp, ← hq]
  rw [good_norm_eq_sextic_norm, hk]
  change C (k : K) * (P.mumford.u * P.mumford.u) * (Q.mumford.u * B.mumford.u) = _
  simp only [hB, N13TwoAdicAbelChartPic.DiskPair.mumford_u]
  ring

end
end MazurProof.N13ActualPrincipalNorm
