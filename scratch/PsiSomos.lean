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

end FLT.EDS
