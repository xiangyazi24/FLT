# Q223-dm1: coordinate-ring route for the division-polynomial doubling identity

## Verdict

I cannot honestly give a complete zero-gap proof of

```lean
W.Φ (2*m) * dupDenP W (W.Φ m) (W.ΨSq m)
  = W.ΨSq (2*m) * dupNumP W (W.Φ m) (W.ΨSq m)
```

from only the listed Mathlib lemmas.  The descent lemma `mk_C_injective` is available from the coordinate-ring basis and is closeable.  The push-forward/rewrite step from univariate `Φ, ΨSq` to bivariate `φ, ψ` is also routine.  The missing part is a genuine bivariate composition/doubling identity for division polynomials in the coordinate ring.

The smallest missing lemma is:

```lean
theorem mk_phi_psi_dup_doubling_cross
    (W : WeierstrassCurve R) (m : ℤ) :
    Affine.CoordinateRing.mk W.toAffine
      (W.φ (2*m) * dupDenBiv W (W.φ m) (W.ψ m ^ 2)
        - W.ψ (2*m) ^ 2 * dupNumBiv W (W.φ m) (W.ψ m ^ 2)) = 0
```

This is not presently supplied by `mk_φ`, `mk_ψ`, or `mk_Ψ_sq`.  Those lemmas only say `φₙ` and `ψₙ²` reduce to the univariate representatives in the coordinate ring.  They do not prove compatibility of the pair `(φₙ, ψₙ²)` with composition by the duplication map.

Below is the exact module skeleton I would put in the repo.  It contains the closeable descent lemma, the precise missing bivariate lemma, and the complete downstream proof conditional on that lemma.

---

## Lean module

```lean
import Mathlib

open Polynomial WeierstrassCurve

namespace FLT.DivisionPolynomialDoubling

variable {R : Type*} [CommRing R]

noncomputable def dupNumP (W : WeierstrassCurve R) (P Q : R[X]) : R[X] :=
  P ^ 4
    - C W.b₄ * P ^ 2 * Q ^ 2
    - C (2 * W.b₆) * P * Q ^ 3
    - C W.b₈ * Q ^ 4

noncomputable def dupDenP (W : WeierstrassCurve R) (P Q : R[X]) : R[X] :=
  C 4 * P ^ 3 * Q
    + C W.b₂ * P ^ 2 * Q ^ 2
    + C (2 * W.b₄) * P * Q ^ 3
    + C W.b₆ * Q ^ 4

/-- Bivariate version of the duplication numerator in `R[X][Y]`. -/
noncomputable def dupNumBiv
    (W : WeierstrassCurve R)
    (P Q : Polynomial (Polynomial R)) : Polynomial (Polynomial R) :=
  P ^ 4
    - C (C W.b₄) * P ^ 2 * Q ^ 2
    - C (C (2 * W.b₆)) * P * Q ^ 3
    - C (C W.b₈) * Q ^ 4

/-- Bivariate version of the duplication denominator in `R[X][Y]`. -/
noncomputable def dupDenBiv
    (W : WeierstrassCurve R)
    (P Q : Polynomial (Polynomial R)) : Polynomial (Polynomial R) :=
  C (C (4 : R)) * P ^ 3 * Q
    + C (C W.b₂) * P ^ 2 * Q ^ 2
    + C (C (2 * W.b₄)) * P * Q ^ 3
    + C (C W.b₆) * Q ^ 4

namespace CoordinateRingTools

open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing

variable (W' : WeierstrassCurve.Affine R)

/-- Constants in `Y`, i.e. elements of `R[X]`, inject into the affine coordinate ring.

This uses the existing Mathlib basis `{1,Y}` of `R[W]` over `R[X]`.  The key existing lemma is

```lean
WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero
```

which says that if `p • 1 + q • Y = 0`, then `p = 0` and `q = 0`.
-/
theorem mk_C_eq_zero {p : R[X]}
    (h : mk W' (Polynomial.C p) = 0) :
    p = 0 := by
  -- Turn `mk(C p)=0` into `p • 1 + 0 • Y = 0` and read off the first coordinate
  -- in the `{1,Y}` basis.
  have hmul : mk W' (Polynomial.C p) * (1 : W'.CoordinateRing) = 0 := by
    simpa [h]
  have hlin :
      p • (1 : W'.CoordinateRing)
        + (0 : R[X]) • (mk W' Polynomial.X) = 0 := by
    simpa [WeierstrassCurve.Affine.CoordinateRing.smul] using hmul
  exact (WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero hlin).1

/-- Descent lemma from coordinate-ring equality of constants in `Y` to equality in `R[X]`. -/
theorem mk_C_injective :
    Function.Injective (fun p : R[X] => mk W' (Polynomial.C p)) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply mk_C_eq_zero W'
  have hsub : mk W' (Polynomial.C p) - mk W' (Polynomial.C q) = 0 := by
    simpa [hpq]
  simpa [map_sub] using hsub

end CoordinateRingTools

open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.CoordinateRing

variable (W : WeierstrassCurve R)

/-- Rewrite `mk (C (dupNumP Φ ΨSq))` as the bivariate expression with `φ` and `ψ²`.

This is a routine consequence of `mk_φ`, `mk_ψ`, and `mk_Ψ_sq`.  Depending on simp orientation,
you may need to replace the final `simp` by a sequence of `rw [← mk_φ, ← mk_Ψ_sq, ← mk_ψ]`.
-/
theorem mk_C_dupNumP_Φ_ΨSq (m : ℤ) :
    mk W.toAffine (Polynomial.C (dupNumP W (W.Φ m) (W.ΨSq m)))
      =
    mk W.toAffine (dupNumBiv W (W.φ m) (W.ψ m ^ 2)) := by
  -- The intended proof is purely functoriality of `mk` over `+,-,*,^`.
  -- If this exact simp does not fire in the repo, orient the three coordinate-ring lemmas manually:
  --   `rw [← Affine.CoordinateRing.mk_φ W m]`
  --   `rw [← Affine.CoordinateRing.mk_Ψ_sq W m]`
  --   `rw [← Affine.CoordinateRing.mk_ψ W m]`
  simp [dupNumP, dupNumBiv,
    WeierstrassCurve.Affine.CoordinateRing.mk_φ,
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
    WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]

/-- Rewrite `mk (C (dupDenP Φ ΨSq))` as the bivariate expression with `φ` and `ψ²`. -/
theorem mk_C_dupDenP_Φ_ΨSq (m : ℤ) :
    mk W.toAffine (Polynomial.C (dupDenP W (W.Φ m) (W.ΨSq m)))
      =
    mk W.toAffine (dupDenBiv W (W.φ m) (W.ψ m ^ 2)) := by
  simp [dupDenP, dupDenBiv,
    WeierstrassCurve.Affine.CoordinateRing.mk_φ,
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
    WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]

/--
**The exact missing Mathlib lemma.**

This is the coordinate-ring composition law for the x-coordinate division-polynomial pair under doubling.
It is not supplied by `mk_φ`, `mk_ψ`, or `mk_Ψ_sq`.

Mathematically it says:

```text
x([2m]P) = x(2·[m]P)
```

in the affine coordinate ring, using only the x-coordinate representatives.

A proof would require either:

* a bivariate composition theorem for division polynomials, or
* the already-proved pointwise/projective SEAM2 x-coordinate theorem lifted to the generic point/function field, or
* a direct EDS residual theorem substantially stronger than the current `ψ_even`/`ψ_odd` recurrences.
-/
axiom mk_phi_psi_dup_doubling_cross (m : ℤ) :
    mk W.toAffine
      (W.φ (2 * m) * dupDenBiv W (W.φ m) (W.ψ m ^ 2)
        - W.ψ (2 * m) ^ 2 * dupNumBiv W (W.φ m) (W.ψ m ^ 2)) = 0

/-- Coordinate-ring version of the desired univariate cross identity, conditional on the missing
bivariate composition lemma above. -/
theorem mk_dup_doubling_cross (m : ℤ) :
    mk W.toAffine
      (Polynomial.C
        (W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
          - W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m))) = 0 := by
  have hnum := mk_C_dupNumP_Φ_ΨSq (W := W) m
  have hden := mk_C_dupDenP_Φ_ΨSq (W := W) m

  have hΦ2 :
      mk W.toAffine (Polynomial.C (W.Φ (2 * m)))
        = mk W.toAffine (W.φ (2 * m)) := by
    simpa using (WeierstrassCurve.Affine.CoordinateRing.mk_φ W (2 * m)).symm

  have hΨ2 :
      mk W.toAffine (Polynomial.C (W.ΨSq (2 * m)))
        = mk W.toAffine (W.ψ (2 * m) ^ 2) := by
    calc
      mk W.toAffine (Polynomial.C (W.ΨSq (2 * m)))
          = mk W.toAffine (W.Ψ (2 * m)) ^ 2 := by
              simpa using (WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq W (2 * m)).symm
      _ = mk W.toAffine (W.ψ (2 * m)) ^ 2 := by
              rw [WeierstrassCurve.Affine.CoordinateRing.mk_ψ W (2 * m)]
      _ = mk W.toAffine (W.ψ (2 * m) ^ 2) := by
              simp

  -- Push `mk` through the univariate expression and rewrite all univariate representatives
  -- by their bivariate counterparts.
  have hrewrite :
      mk W.toAffine
        (Polynomial.C
          (W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
            - W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)))
        =
      mk W.toAffine
        (W.φ (2 * m) * dupDenBiv W (W.φ m) (W.ψ m ^ 2)
          - W.ψ (2 * m) ^ 2 * dupNumBiv W (W.φ m) (W.ψ m ^ 2)) := by
    simp [map_sub, map_mul, hΦ2, hΨ2, hnum, hden]

  rw [hrewrite]
  exact mk_phi_psi_dup_doubling_cross (W := W) m

/-- Raw `R[X]` identity, descended from the coordinate-ring identity. -/
theorem dup_doubling_cross (m : ℤ) :
    W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
      =
    W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m) := by
  let lhs : R[X] := W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
  let rhs : R[X] := W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m)
  have hmk : mk W.toAffine (Polynomial.C (lhs - rhs)) = 0 := by
    simpa [lhs, rhs, map_sub] using mk_dup_doubling_cross (W := W) m
  have hpoly : lhs - rhs = 0 :=
    CoordinateRingTools.mk_C_eq_zero W.toAffine hmk
  exact sub_eq_zero.mp hpoly

end FLT.DivisionPolynomialDoubling
```

---

## Why the requested proof cannot be completed from the listed lemmas alone

The available coordinate-ring congruences are:

```lean
mk_φ      : mk W (W.φ n) = mk W (C (W.Φ n))
mk_ψ      : mk W (W.ψ n) = mk W (W.Ψ n)
mk_Ψ_sq   : mk W (W.Ψ n)^2 = mk W (C (W.ΨSq n))
mk_ψ₂_sq  : mk W W.ψ₂^2 = mk W (C W.Ψ₂Sq)
```

These let you replace univariate representatives by bivariate representatives **after** a bivariate theorem has been proved.  They do not provide the bivariate theorem.

The missing theorem is not just a simp/ring lemma.  It is the composition law for division polynomials under multiplication by `2`:

```text
[φ_{2m} : ψ_{2m}²] = duplication_map([φ_m : ψ_m²])
```

in the coordinate ring.

Equivalently, it is a special case of the general composition law:

```text
x([ab]P) = x([a]([b]P)).
```

Mathlib currently defines `φ`, `ψ`, `Φ`, and `ΨSq`, and proves their coordinate-ring congruences, but it does not prove that these polynomials actually compute scalar multiplication on the elliptic curve.  That is precisely the larger SEAM2 correctness theorem.

So there are two honest ways to close this file:

1. Prove `mk_phi_psi_dup_doubling_cross` as a new theorem, likely by proving a bivariate division-polynomial composition law.
2. Avoid this raw-polynomial theorem and prove the downstream projective x-coordinate formula directly by the x-only differential-addition induction, carrying nonzero representatives simultaneously.

The first path is not shorter than SEAM2; it is essentially a hidden version of SEAM2.  The second path remains the better architecture.
