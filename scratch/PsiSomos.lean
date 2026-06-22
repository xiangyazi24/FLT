import scratch.WardSomos
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

open Polynomial WeierstrassCurve
open scoped Classical

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The adjacent Somos relation for the division polynomial `ψ`, in `R[X][Y]`.
Immediate from `normEDS_adjacent_somos` since `W.ψ n = normEDS W.ψ₂ (C Ψ₃) (C preΨ₄) n` (defn). -/
lemma psi_adjacent_somos (W : WeierstrassCurve R) (m : ℤ) :
    W.ψ (m + 2) * W.ψ (m - 2)
      = W.ψ₂ ^ 2 * W.ψ (m + 1) * W.ψ (m - 1) - C W.Ψ₃ * W.ψ m ^ 2 := by
  simpa only [WeierstrassCurve.ψ] using
    normEDS_adjacent_somos W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) m

/-- Coordinate-ring form: under `mk`, `ψ₂² = Ψ₂Sq`, giving the Somos in terms of `Ψ₂Sq`. -/
lemma mk_psi_adjacent_somos (W : WeierstrassCurve R) (m : ℤ) :
    Affine.CoordinateRing.mk W (W.ψ (m + 2)) * Affine.CoordinateRing.mk W (W.ψ (m - 2))
      = Affine.CoordinateRing.mk W (C W.Ψ₂Sq)
          * Affine.CoordinateRing.mk W (W.ψ (m + 1)) * Affine.CoordinateRing.mk W (W.ψ (m - 1))
        - Affine.CoordinateRing.mk W (C W.Ψ₃) * Affine.CoordinateRing.mk W (W.ψ m) ^ 2 := by
  have h := congrArg (Affine.CoordinateRing.mk W) (psi_adjacent_somos W m)
  simpa only [map_mul, map_sub, map_pow, Affine.CoordinateRing.mk_ψ₂_sq] using h

/-- Descent: `mk ∘ C : R[X] → CoordinateRing` is injective (the rank-1 component of the free
rank-2 basis `{1, mk Y}`).  Lets us check any `R[X]` polynomial identity in the coordinate ring. -/
lemma mk_C_injective (W : WeierstrassCurve R) :
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

end FLT.EDS
