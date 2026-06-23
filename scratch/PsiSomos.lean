module

public import scratch.WardSomos
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

open Polynomial WeierstrassCurve
open scoped Classical

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The adjacent Somos relation for the division polynomial `ψ`, in `R[X][Y]`.
Immediate from `normEDS_adjacent_somos` since `W.ψ n = normEDS W.ψ₂ (C Ψ₃) (C preΨ₄) n` (defn). -/
public lemma psi_adjacent_somos (W : WeierstrassCurve R) (m : ℤ) :
    W.ψ (m + 2) * W.ψ (m - 2)
      = W.ψ₂ ^ 2 * W.ψ (m + 1) * W.ψ (m - 1) - C W.Ψ₃ * W.ψ m ^ 2 := by
  simpa only [WeierstrassCurve.ψ] using
    normEDS_adjacent_somos W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) m

/-- Coordinate-ring form: under `mk`, `ψ₂² = Ψ₂Sq`, giving the Somos in terms of `Ψ₂Sq`. -/
public lemma mk_psi_adjacent_somos (W : WeierstrassCurve R) (m : ℤ) :
    Affine.CoordinateRing.mk W (W.ψ (m + 2)) * Affine.CoordinateRing.mk W (W.ψ (m - 2))
      = Affine.CoordinateRing.mk W (C W.Ψ₂Sq)
          * Affine.CoordinateRing.mk W (W.ψ (m + 1)) * Affine.CoordinateRing.mk W (W.ψ (m - 1))
        - Affine.CoordinateRing.mk W (C W.Ψ₃) * Affine.CoordinateRing.mk W (W.ψ m) ^ 2 := by
  have h := congrArg (Affine.CoordinateRing.mk W) (psi_adjacent_somos W m)
  simpa only [map_mul, map_sub, map_pow, Affine.CoordinateRing.mk_ψ₂_sq] using h

/-- Descent: `mk ∘ C : R[X] → CoordinateRing` is injective (the rank-1 component of the free
rank-2 basis `{1, mk Y}`).  Lets us check any `R[X]` polynomial identity in the coordinate ring. -/
public lemma mk_C_injective (W : WeierstrassCurve R) :
    Function.Injective (fun p : R[X] => Affine.CoordinateRing.mk W (Polynomial.C p)) := by
  intro p q hpq
  simp only at hpq
  have hsub : Affine.CoordinateRing.mk W (Polynomial.C (p - q)) = 0 := by
    have h : Affine.CoordinateRing.mk W (Polynomial.C (p - q))
        = Affine.CoordinateRing.mk W (Polynomial.C p) - Affine.CoordinateRing.mk W (Polynomial.C q) := by
      rw [map_sub, map_sub]
    rw [h, hpq, sub_self]
  have hsmul : (p - q) • (1 : Affine.CoordinateRing W)
      + (0 : R[X]) • Affine.CoordinateRing.mk W Polynomial.X = 0 := by
    rw [zero_smul, add_zero, Affine.CoordinateRing.smul, mul_one]; exact hsub
  exact sub_eq_zero.mp (Affine.CoordinateRing.smul_basis_eq_zero hsmul).1

/-- ψ ↔ preΨ in the coordinate ring: `mk(ψ n) = mk(C preΨ n) · (ψ₂ if n even else 1)`.
From `mk_ψ` and the definition `Ψ n = C(preΨ n)·(ψ₂ if even else 1)`. -/
public lemma mk_ψ_eq (W : WeierstrassCurve R) (n : ℤ) :
    Affine.CoordinateRing.mk W (W.ψ n)
      = Affine.CoordinateRing.mk W (Polynomial.C (W.preΨ n))
          * (if Even n then Affine.CoordinateRing.mk W W.ψ₂ else 1) := by
  rw [Affine.CoordinateRing.mk_ψ, WeierstrassCurve.Ψ, map_mul, apply_ite (Affine.CoordinateRing.mk W),
    map_one]

/-- preΨ adjacent Somos (the (m,2,1) instance), parity-dependent coefficient: even m → coeff 1,
odd m → coeff Ψ₂Sq². From `mk_psi_adjacent_somos` via `mk_ψ_eq` (ψ₂ factors collapse through
`mk_ψ₂_sq`), descended by `mk_C_injective` + the `Ψ₂Sq ≠ 0` cancellation in the polynomial domain. -/
public lemma preΨ_adjacent_somos [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0) (m : ℤ) :
    W.preΨ (m + 2) * W.preΨ (m - 2)
      = (if Even m then 1 else W.Ψ₂Sq ^ 2) * (W.preΨ (m + 1) * W.preΨ (m - 1))
        - W.Ψ₃ * W.preΨ m ^ 2 := by
  have hS := mk_psi_adjacent_somos W m
  rw [mk_ψ_eq, mk_ψ_eq, mk_ψ_eq, mk_ψ_eq, mk_ψ_eq] at hS
  have h2sq := Affine.CoordinateRing.mk_ψ₂_sq W
  have ep2 : Even (m + 2) ↔ Even m := by simp [Int.even_add]
  have em2 : Even (m - 2) ↔ Even m := by simp [Int.even_sub]
  have ep1 : Even (m + 1) ↔ ¬ Even m := by rw [Int.even_add]; simp [Int.not_even_one]
  have em1 : Even (m - 1) ↔ ¬ Even m := by rw [Int.even_sub]; simp [Int.not_even_one]
  simp only [ep2, em2, ep1, em1] at hS
  by_cases hm : Even m
  · simp only [hm, if_true, not_true, if_false, mul_one] at hS
    rw [if_pos hm, one_mul]
    apply mul_left_cancel₀ (W.Ψ₂Sq_ne_zero h4)
    apply mk_C_injective W
    simp only [map_mul, map_sub, map_pow]
    rw [← h2sq] at hS ⊢
    linear_combination hS
  · simp only [hm, if_false, not_false_iff, if_true, mul_one] at hS
    rw [if_neg hm]
    apply mk_C_injective W
    simp only [map_mul, map_sub, map_pow]
    rw [← h2sq] at hS ⊢
    linear_combination hS

end FLT.EDS
