module

public import scratch.PsiSomos

/-! # Division-polynomial separability cert n=3 (SEAM1)

`W.Ψ₃` is separable when `(3:k)` is nonzero, via the resultant/Bezout identity
`A*Ψ₃ + B*(derivative Ψ₃) = C(-81*Δ^2)` (CAS-extracted cofactors, reduced modulo
`b_relation`), the same technique as the keystone nonsingularity certs. -/

open Polynomial
open scoped Polynomial
open FLT.EDS

set_option maxHeartbeats 1000000000
set_option maxRecDepth 16000

namespace WeierstrassCurve
noncomputable section
variable {k : Type*} [Field k]

private lemma bRelC (W : WeierstrassCurve k) :
    C W.b₂ * C W.b₆ - (C W.b₄) ^ 2 - C 4 * C W.b₈ = (0 : k[X]) := by
  have h0 : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by
    have hb := W.b_relation; linear_combination -hb
  have := congrArg (fun z : k => (C z : k[X])) h0
  simpa [map_sub, map_mul, map_pow] using this

/-- Explicit derivative of `Ψ₃`. -/
private lemma dPsi3 (W : WeierstrassCurve k) :
    derivative W.Ψ₃
      = (12 : k[X]) * X ^ 3 + (3 : k[X]) * C W.b₂ * X ^ 2
        + (6 : k[X]) * C W.b₄ * X + (3 : k[X]) * C W.b₆ := by
  rw [WeierstrassCurve.Ψ₃]
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
    derivative_C, derivative_C_mul, derivative_X_pow, Nat.cast_ofNat, map_ofNat, mul_one,
    mul_zero, zero_mul, add_zero, zero_add, Nat.reduceSub, pow_one]
  ring

/-- Bezout cofactor identity for separability. -/
private lemma bezout_Psi3_dPsi3 (W : WeierstrassCurve k) :
    ((648 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆)
          - (648 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (1296 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈)
          - (27216 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (23328 : k[X]) * X ^ 2 * (C W.b₄) ^ 3
          - (31104 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈)
          + (104976 : k[X]) * X ^ 2 * (C W.b₆) ^ 2
          + (162 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆)
          - (162 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (6480 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (5832 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3
          + (2592 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (29160 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2
          - (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆)
          - (46656 : k[X]) * X * (C W.b₆) * (C W.b₈)
          - (81 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈)
          + (405 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          - (324 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          + (3888 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          - (16524 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          - (14256 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (11664 : k[X]) * (C W.b₄) ^ 4
          - (31104 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          + (69984 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          + (20736 : k[X]) * (C W.b₈) ^ 2) * W.Ψ₃
      + (-(162 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆)
          + (162 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (324 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₈)
          + (6804 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (5832 : k[X]) * X ^ 3 * (C W.b₄) ^ 3
          + (7776 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (26244 : k[X]) * X ^ 3 * (C W.b₆) ^ 2
          - (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆)
          + (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (27 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₈)
          + (2187 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          - (1944 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3
          - (9477 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          + (2916 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          + (11664 : k[X]) * X ^ 2 * (C W.b₆) * (C W.b₈)
          + (27 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₈)
          - (189 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          + (162 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          - (1350 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (81 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (7776 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (4536 : k[X]) * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (5832 : k[X]) * X * (C W.b₄) ^ 4
          + (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (30618 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 2
          - (5184 : k[X]) * X * (C W.b₈) ^ 2
          + (27 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈)
          - (108 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 2
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (189 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈)
          - (972 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈)
          + (4374 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2
          - (432 : k[X]) * (C W.b₂) * (C W.b₈) ^ 2
          - (2916 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆)
          + (11664 : k[X]) * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (19683 : k[X]) * (C W.b₆) ^ 3) * derivative W.Ψ₃
      = C (-81 * W.Δ ^ 2) := by
  have hb := bRelC W
  rw [dPsi3 W]
  linear_combination (norm :=
    (simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.Δ,
      map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat, map_one,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]; ring1))
    ((-(972 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (324 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (6480 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (2592 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (5184 : k[X]) * (C W.b₄) ^ 4
          + (9072 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          - (26244 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          - (5184 : k[X]) * (C W.b₈) ^ 2) * hb)

/-- `Ψ₃` is separable when `(3:k)` is nonzero. -/
public theorem Psi3_separable (W : WeierstrassCurve k) [W.IsElliptic] (h3 : (3 : k) ≠ 0) :
    W.Ψ₃.Separable := by
  have hb := bezout_Psi3_dPsi3 W
  have hu : IsUnit (C (-81 * W.Δ ^ 2) : k[X]) := by
    rw [Polynomial.isUnit_C]
    have h81 : (-81 : k) ≠ 0 := by
      have e : (81 : k) = 3 ^ 4 := by norm_num
      rw [show (-81 : k) = -(81) from by ring, e]
      exact neg_ne_zero.mpr (pow_ne_zero 4 h3)
    exact (isUnit_iff_ne_zero.mpr h81).mul (W.isUnit_Δ.pow 2)
  rw [Polynomial.separable_def]
  obtain ⟨w, hw⟩ := hu
  refine ⟨(w⁻¹).val * ((648 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆)
          - (648 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (1296 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈)
          - (27216 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (23328 : k[X]) * X ^ 2 * (C W.b₄) ^ 3
          - (31104 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈)
          + (104976 : k[X]) * X ^ 2 * (C W.b₆) ^ 2
          + (162 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆)
          - (162 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (6480 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (5832 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3
          + (2592 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (29160 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2
          - (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆)
          - (46656 : k[X]) * X * (C W.b₆) * (C W.b₈)
          - (81 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈)
          + (405 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          - (324 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          + (3888 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          - (16524 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          - (14256 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (11664 : k[X]) * (C W.b₄) ^ 4
          - (31104 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          + (69984 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          + (20736 : k[X]) * (C W.b₈) ^ 2), (w⁻¹).val * (-(162 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆)
          + (162 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (324 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₈)
          + (6804 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (5832 : k[X]) * X ^ 3 * (C W.b₄) ^ 3
          + (7776 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (26244 : k[X]) * X ^ 3 * (C W.b₆) ^ 2
          - (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆)
          + (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (27 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₈)
          + (2187 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          - (1944 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3
          - (9477 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          + (2916 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          + (11664 : k[X]) * X ^ 2 * (C W.b₆) * (C W.b₈)
          + (27 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₈)
          - (189 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          + (162 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          - (1350 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (81 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (7776 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (4536 : k[X]) * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (5832 : k[X]) * X * (C W.b₄) ^ 4
          + (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (30618 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 2
          - (5184 : k[X]) * X * (C W.b₈) ^ 2
          + (27 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈)
          - (108 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 2
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (189 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈)
          - (972 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈)
          + (4374 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2
          - (432 : k[X]) * (C W.b₂) * (C W.b₈) ^ 2
          - (2916 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆)
          + (11664 : k[X]) * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (19683 : k[X]) * (C W.b₆) ^ 3), ?_⟩
  have key : ((w⁻¹).val * ((648 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆)
          - (648 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (1296 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈)
          - (27216 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (23328 : k[X]) * X ^ 2 * (C W.b₄) ^ 3
          - (31104 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈)
          + (104976 : k[X]) * X ^ 2 * (C W.b₆) ^ 2
          + (162 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆)
          - (162 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (6480 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (5832 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3
          + (2592 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (29160 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2
          - (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆)
          - (46656 : k[X]) * X * (C W.b₆) * (C W.b₈)
          - (81 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈)
          + (405 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          - (324 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          + (3888 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          - (16524 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          - (14256 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (11664 : k[X]) * (C W.b₄) ^ 4
          - (31104 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          + (69984 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          + (20736 : k[X]) * (C W.b₈) ^ 2)) * W.Ψ₃
      + ((w⁻¹).val * (-(162 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆)
          + (162 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (324 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₈)
          + (6804 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (5832 : k[X]) * X ^ 3 * (C W.b₄) ^ 3
          + (7776 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (26244 : k[X]) * X ^ 3 * (C W.b₆) ^ 2
          - (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆)
          + (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (27 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₈)
          + (2187 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          - (1944 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3
          - (9477 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          + (2916 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          + (11664 : k[X]) * X ^ 2 * (C W.b₆) * (C W.b₈)
          + (27 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₈)
          - (189 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          + (162 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          - (1350 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (81 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (7776 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (4536 : k[X]) * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (5832 : k[X]) * X * (C W.b₄) ^ 4
          + (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (30618 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 2
          - (5184 : k[X]) * X * (C W.b₈) ^ 2
          + (27 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈)
          - (108 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 2
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (189 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈)
          - (972 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈)
          + (4374 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2
          - (432 : k[X]) * (C W.b₂) * (C W.b₈) ^ 2
          - (2916 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆)
          + (11664 : k[X]) * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (19683 : k[X]) * (C W.b₆) ^ 3)) * derivative W.Ψ₃
      = (w⁻¹).val * (((648 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆)
          - (648 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (1296 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₈)
          - (27216 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (23328 : k[X]) * X ^ 2 * (C W.b₄) ^ 3
          - (31104 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₈)
          + (104976 : k[X]) * X ^ 2 * (C W.b₆) ^ 2
          + (162 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₆)
          - (162 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (6480 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (5832 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 3
          + (2592 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₈)
          + (29160 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2
          - (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆)
          - (46656 : k[X]) * X * (C W.b₆) * (C W.b₈)
          - (81 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈)
          + (405 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          - (324 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          + (3888 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          - (16524 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          - (14256 : k[X]) * (C W.b₂) * (C W.b₆) * (C W.b₈)
          + (11664 : k[X]) * (C W.b₄) ^ 4
          - (31104 : k[X]) * (C W.b₄) ^ 2 * (C W.b₈)
          + (69984 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2
          + (20736 : k[X]) * (C W.b₈) ^ 2) * W.Ψ₃ + (-(162 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₆)
          + (162 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (324 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₈)
          + (6804 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (5832 : k[X]) * X ^ 3 * (C W.b₄) ^ 3
          + (7776 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₈)
          - (26244 : k[X]) * X ^ 3 * (C W.b₆) ^ 2
          - (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 4 * (C W.b₆)
          + (54 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (27 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₈)
          + (2187 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          - (1944 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 3
          - (9477 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆) ^ 2
          + (2916 : k[X]) * X ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          + (11664 : k[X]) * X ^ 2 * (C W.b₆) * (C W.b₈)
          + (27 : k[X]) * X * (C W.b₂) ^ 4 * (C W.b₈)
          - (189 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          + (162 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 3
          - (1350 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₈)
          - (81 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          + (7776 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (4536 : k[X]) * X * (C W.b₂) * (C W.b₆) * (C W.b₈)
          - (5832 : k[X]) * X * (C W.b₄) ^ 4
          + (11664 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₈)
          - (30618 : k[X]) * X * (C W.b₄) * (C W.b₆) ^ 2
          - (5184 : k[X]) * X * (C W.b₈) ^ 2
          + (27 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₈)
          - (108 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆) ^ 2
          + (81 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2 * (C W.b₆)
          - (189 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) * (C W.b₈)
          - (972 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₈)
          + (4374 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆) ^ 2
          - (432 : k[X]) * (C W.b₂) * (C W.b₈) ^ 2
          - (2916 : k[X]) * (C W.b₄) ^ 3 * (C W.b₆)
          + (11664 : k[X]) * (C W.b₄) * (C W.b₆) * (C W.b₈)
          - (19683 : k[X]) * (C W.b₆) ^ 3) * derivative W.Ψ₃) := by ring
  rw [key, hb, ← hw]
  exact Units.inv_mul w


/-- Explicit derivative of `preΨ₄`. -/
private lemma dPreΨ₄ (W : WeierstrassCurve k) :
    derivative W.preΨ₄
      = (12 : k[X]) * X ^ 5 + (5 : k[X]) * C W.b₂ * X ^ 4
        + (20 : k[X]) * C W.b₄ * X ^ 3 + (30 : k[X]) * C W.b₆ * X ^ 2
        + (20 : k[X]) * C W.b₈ * X + C (W.b₂ * W.b₈ - W.b₄ * W.b₆) := by
  rw [WeierstrassCurve.preΨ₄]
  simp only [derivative_add, derivative_mul, derivative_pow, derivative_X, derivative_ofNat,
    derivative_C, derivative_C_mul, Nat.cast_ofNat, map_ofNat, mul_one,
    mul_zero, zero_mul, add_zero, zero_add, Nat.reduceSub, pow_one]
  ring

/-- Bezout cofactor identity for `preΨ₄` separability (CAS-verified). -/
private lemma bezout_PreΨ₄_dPreΨ₄ (W : WeierstrassCurve k) :
    ((5760 : k[X]) * X ^ 4 * (C W.b₄)
          - (240 : k[X]) * X ^ 4 * (C W.b₂) ^ 2
          + (2640 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄)
          - (100 : k[X]) * X ^ 3 * (C W.b₂) ^ 3
          - (4320 : k[X]) * X ^ 3 * (C W.b₆)
          + (8640 : k[X]) * X ^ 2 * (C W.b₄) ^ 2
          - (300 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄)
          - (1080 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆)
          + (120 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2
          + (7920 : k[X]) * X * (C W.b₄) * (C W.b₆)
          - (420 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆)
          + (138 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (4548 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (138 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆)
          - (4096 : k[X]) * (C W.b₄) ^ 3
          - (11664 : k[X]) * (C W.b₆) ^ 2) * W.preΨ₄
      + ((40 : k[X]) * X ^ 5 * (C W.b₂) ^ 2
          - (960 : k[X]) * X ^ 5 * (C W.b₄)
          + (20 : k[X]) * X ^ 4 * (C W.b₂) ^ 3
          - (520 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄)
          + (720 : k[X]) * X ^ 4 * (C W.b₆)
          + (80 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄)
          + (240 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (2240 : k[X]) * X ^ 3 * (C W.b₄) ^ 2
          + (160 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₆)
          - (40 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 2
          - (3120 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₆)
          + (58 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₆)
          - (58 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (1768 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (1616 : k[X]) * X * (C W.b₄) ^ 3
          + (3744 : k[X]) * X * (C W.b₆) ^ 2
          + (4 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆)
          - (4 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (134 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (118 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3
          + (312 : k[X]) * (C W.b₂) * (C W.b₆) ^ 2
          + (100 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆)) * derivative W.preΨ₄
      = C (16 * W.Δ ^ 2) := by
  have hb := bRelC W
  rw [dPreΨ₄ W]
  linear_combination (norm :=
    (simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Δ,
      map_neg, map_mul, map_add, map_sub, map_pow, map_ofNat, map_one,
      Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_pow,
      Polynomial.C_neg, Polynomial.C_1]; ring1))
    (((400 : k[X]) * X ^ 6 * (C W.b₂) ^ 2
          - (9600 : k[X]) * X ^ 6 * (C W.b₄)
          + (200 : k[X]) * X ^ 5 * (C W.b₂) ^ 3
          - (5200 : k[X]) * X ^ 5 * (C W.b₂) * (C W.b₄)
          + (7200 : k[X]) * X ^ 5 * (C W.b₆)
          + (20 : k[X]) * X ^ 4 * (C W.b₂) ^ 4
          - (120 : k[X]) * X ^ 4 * (C W.b₂) ^ 2 * (C W.b₄)
          + (2400 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₆)
          - (11840 : k[X]) * X ^ 4 * (C W.b₄) ^ 2
          + (80 : k[X]) * X ^ 3 * (C W.b₂) ^ 3 * (C W.b₄)
          + (460 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₆)
          - (2360 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄) ^ 2
          - (3120 : k[X]) * X ^ 3 * (C W.b₄) * (C W.b₆)
          + (120 : k[X]) * X ^ 2 * (C W.b₂) ^ 3 * (C W.b₆)
          - (3460 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (10440 : k[X]) * X ^ 2 * (C W.b₆) ^ 2
          + (80 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (420 : k[X]) * X * (C W.b₂) * (C W.b₆) ^ 2
          - (2480 : k[X]) * X * (C W.b₄) ^ 2 * (C W.b₆)
          + (4 : k[X]) * (C W.b₂) ^ 4 * (C W.b₈)
          - (4 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) * (C W.b₆)
          + (138 : k[X]) * (C W.b₂) ^ 2 * (C W.b₆) ^ 2
          - (1162 : k[X]) * (C W.b₂) * (C W.b₄) ^ 2 * (C W.b₆)
          + (1024 : k[X]) * (C W.b₄) ^ 4
          + (2916 : k[X]) * (C W.b₄) * (C W.b₆) ^ 2) * hb)

/-- `preΨ₄` is separable when `(4:k)` is nonzero. -/
public theorem Psi4_separable (W : WeierstrassCurve k) [W.IsElliptic] (h4 : (4 : k) ≠ 0) :
    W.preΨ₄.Separable := by
  have hbez := bezout_PreΨ₄_dPreΨ₄ W
  have hu : IsUnit (C (16 * W.Δ ^ 2) : k[X]) := by
    rw [Polynomial.isUnit_C]
    have h16 : (16 : k) ≠ 0 := by
      have e : (16 : k) = 4 * 4 := by norm_num
      rw [e]; exact mul_ne_zero h4 h4
    exact (isUnit_iff_ne_zero.mpr h16).mul (W.isUnit_Δ.pow 2)
  rw [Polynomial.separable_def]
  obtain ⟨w, hw⟩ := hu
  -- Provide the Bezout witnesses: (w⁻¹ * S, w⁻¹ * T)
  -- where S * preΨ₄ + T * derivative preΨ₄ = C(16*Δ²) = ↑w
  -- so (w⁻¹ * S) * preΨ₄ + (w⁻¹ * T) * derivative preΨ₄ = w⁻¹ * ↑w = 1
  set S := ((5760 : k[X]) * X ^ 4 * (C W.b₄)
          - (240 : k[X]) * X ^ 4 * (C W.b₂) ^ 2
          + (2640 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₄)
          - (100 : k[X]) * X ^ 3 * (C W.b₂) ^ 3
          - (4320 : k[X]) * X ^ 3 * (C W.b₆)
          + (8640 : k[X]) * X ^ 2 * (C W.b₄) ^ 2
          - (300 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₄)
          - (1080 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₆)
          + (120 : k[X]) * X * (C W.b₂) * (C W.b₄) ^ 2
          + (7920 : k[X]) * X * (C W.b₄) * (C W.b₆)
          - (420 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₆)
          + (138 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          + (4548 : k[X]) * (C W.b₂) * (C W.b₄) * (C W.b₆)
          - (138 : k[X]) * (C W.b₂) ^ 3 * (C W.b₆)
          - (4096 : k[X]) * (C W.b₄) ^ 3
          - (11664 : k[X]) * (C W.b₆) ^ 2)
  set T := ((40 : k[X]) * X ^ 5 * (C W.b₂) ^ 2
          - (960 : k[X]) * X ^ 5 * (C W.b₄)
          + (20 : k[X]) * X ^ 4 * (C W.b₂) ^ 3
          - (520 : k[X]) * X ^ 4 * (C W.b₂) * (C W.b₄)
          + (720 : k[X]) * X ^ 4 * (C W.b₆)
          + (80 : k[X]) * X ^ 3 * (C W.b₂) ^ 2 * (C W.b₄)
          + (240 : k[X]) * X ^ 3 * (C W.b₂) * (C W.b₆)
          - (2240 : k[X]) * X ^ 3 * (C W.b₄) ^ 2
          + (160 : k[X]) * X ^ 2 * (C W.b₂) ^ 2 * (C W.b₆)
          - (40 : k[X]) * X ^ 2 * (C W.b₂) * (C W.b₄) ^ 2
          - (3120 : k[X]) * X ^ 2 * (C W.b₄) * (C W.b₆)
          + (58 : k[X]) * X * (C W.b₂) ^ 3 * (C W.b₆)
          - (58 : k[X]) * X * (C W.b₂) ^ 2 * (C W.b₄) ^ 2
          - (1768 : k[X]) * X * (C W.b₂) * (C W.b₄) * (C W.b₆)
          + (1616 : k[X]) * X * (C W.b₄) ^ 3
          + (3744 : k[X]) * X * (C W.b₆) ^ 2
          + (4 : k[X]) * (C W.b₂) ^ 4 * (C W.b₆)
          - (4 : k[X]) * (C W.b₂) ^ 3 * (C W.b₄) ^ 2
          - (134 : k[X]) * (C W.b₂) ^ 2 * (C W.b₄) * (C W.b₆)
          + (118 : k[X]) * (C W.b₂) * (C W.b₄) ^ 3
          + (312 : k[X]) * (C W.b₂) * (C W.b₆) ^ 2
          + (100 : k[X]) * (C W.b₄) ^ 2 * (C W.b₆))
  refine ⟨(w⁻¹).val * S, (w⁻¹).val * T, ?_⟩
  have key : (w⁻¹).val * S * W.preΨ₄ + (w⁻¹).val * T * derivative W.preΨ₄
      = (w⁻¹).val * (S * W.preΨ₄ + T * derivative W.preΨ₄) := by ring
  rw [key, hbez, ← hw]
  exact Units.inv_mul w

end
end WeierstrassCurve
