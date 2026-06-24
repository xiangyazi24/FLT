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

end
end WeierstrassCurve

