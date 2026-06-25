# Q299 (dm2): Relating `mk_invariant_descended` to CAS `Hmiss`

CAS missing identity `Hmiss`:

```text
ψ_{m-1}² ψ_{m+2}
+ ψ_{m-2} ψ_{m+1}²
+ ψ_m³ Ψ₂Sq
- ψ_{m-1} ψ_m ψ_{m+1} · (6X² + b₂X + b₄)
= 0            in the affine coordinate ring
```

Repository lemma shape:

```text
mk(Ψ₃ · (ψ_{m+2}ψ_{m-1}² + ψ_{m+1}²ψ_{m-2} + ψ₂²ψ_m³))
  = mk((preΨ₄ + ψ₂⁴) · (ψ_{m+1}ψ_mψ_{m-1}))
```

## Executive answer

They are **not literally the same identity**.  The repo lemma is the `Ψ₃`-multiple of `Hmiss`.

The bridge is the universal polynomial identity

```text
preΨ₄ + Ψ₂Sq² = Ψ₃ · (6X² + b₂X + b₄)      in R[X].
```

Using `mk(ψ₂²)=mk(C Ψ₂Sq)`, the right-hand side of `mk_invariant_descended` rewrites to

```text
mk(Ψ₃ · (6X² + b₂X + b₄) · ψ_{m+1}ψ_mψ_{m-1}).
```

Thus `mk_invariant_descended` becomes

```text
mk(Ψ₃ · HmissPoly) = 0.
```

So:

```text
Hmiss      ⇒ mk_invariant_descended       -- always, by multiplication by Ψ₃
mk_invariant_descended ⇒ Hmiss            -- only if `mk(C Ψ₃)` can be cancelled
```

Over a domain and away from the `Ψ₃=0` divisor this cancellation is fine.  Over a general `CommRing`, or on the `Ψ₃=0` stratum, it is not valid.  This distinction matters: `mk_invariant_descended` is weaker than `Hmiss` unless you can cancel `Ψ₃`.

## Key polynomial identity

Add this helper first.  It is a univariate identity in `R[X]`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The small universal identity converting the repo invariant to the CAS `Hmiss` coefficient. -/
lemma preΨ₄_add_Ψ₂Sq_sq_eq_Ψ₃_mul_HmissCoeff (W : WeierstrassCurve R) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 =
      W.Ψ₃ * ((6 : R[X]) * X ^ 2 + C W.b₂ * X + C W.b₄) := by
  rw [preΨ₄, Ψ₂Sq, Ψ₃]
  -- If `ring_nf` does not unfold the b-invariants automatically, add:
  --   [b₂, b₄, b₆, b₈]
  ring_nf [b₂, b₄, b₆, b₈]

end WeierstrassCurve
```

This is the algebraic heart.  CAS verified exactly this identity.

## Coordinate-ring version of the same helper

For bivariate coordinate-ring rewriting, use `Affine.CoordinateRing.mk_ψ₂_sq` and the univariate identity above.

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local notation "mkW" p => CoordinateRing.mk W.toAffine p

/-- Coordinate-ring form of
`preΨ₄ + ψ₂⁴ = Ψ₃ * (6X²+b₂X+b₄)`. -/
lemma mk_preΨ₄_add_ψ₂_pow_four_eq_Ψ₃_mul_HmissCoeff :
    mkW (C W.preΨ₄ + W.ψ₂ ^ 4) =
      mkW (C (W.Ψ₃ * ((6 : R[X]) * X ^ 2 + C W.b₂ * X + C W.b₄))) := by
  -- First replace ψ₂² by Ψ₂Sq in the coordinate ring.
  have hψ2sq : mkW (W.ψ₂ ^ 2) = mkW (C W.Ψ₂Sq) := by
    simpa using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))
  calc
    mkW (C W.preΨ₄ + W.ψ₂ ^ 4)
        = mkW (C W.preΨ₄) + mkW (W.ψ₂ ^ 2) ^ 2 := by
            simp [pow_two, pow_succ, mul_assoc, map_add, map_mul]
    _ = mkW (C W.preΨ₄) + mkW (C W.Ψ₂Sq) ^ 2 := by
            rw [hψ2sq]
    _ = mkW (C (W.preΨ₄ + W.Ψ₂Sq ^ 2)) := by
            simp [map_add, map_mul, map_pow]
    _ = mkW (C (W.Ψ₃ * ((6 : R[X]) * X ^ 2 + C W.b₂ * X + C W.b₄))) := by
            rw [W.preΨ₄_add_Ψ₂Sq_sq_eq_Ψ₃_mul_HmissCoeff]

end CoordinateRing
end Affine
end WeierstrassCurve
```

If the exact generated namespace of `mk_ψ₂_sq` in your file is opened, the call may also elaborate as:

```lean
simpa using (WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq (W := W))
```

or, depending on parameter order, simply:

```lean
simpa using W.toAffine.CoordinateRing.mk_ψ₂_sq
```

The lemma is the same one from `DivisionPolynomial.Basic`:

```lean
lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)
```

## Define the CAS `Hmiss` polynomial

Here is a Lean-facing definition using abstract nearby `ψ` terms.  Replace the `ψm...` arguments with the actual objects from `PsiInvariant.lean`.

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The coefficient `6X²+b₂X+b₄` occurring in CAS `Hmiss`. -/
def HmissCoeff : R[X] :=
  (6 : R[X]) * X ^ 2 + C W.b₂ * X + C W.b₄

/-- CAS `Hmiss` polynomial in the bivariate polynomial ring. -/
def HmissPoly
    (ψm2 ψm1 ψm ψp1 ψp2 : R[X][Y]) : R[X][Y] :=
  ψm1 ^ 2 * ψp2
    + ψm2 * ψp1 ^ 2
    + C W.Ψ₂Sq * ψm ^ 3
    - C (HmissCoeff W) * (ψm1 * ψm * ψp1)

end CoordinateRing
end Affine
end WeierstrassCurve
```

## Deriving `Ψ₃ * Hmiss = 0` from `mk_invariant_descended`

This is the exact `have` chain.  The statement of `mk_invariant_descended` below is schematic only in the argument names; the proof body is the important part.

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local notation "mkW" p => CoordinateRing.mk W.toAffine p

/-- What `mk_invariant_descended` actually gives after rewriting: `Ψ₃ * Hmiss = 0`. -/
lemma Ψ₃_mul_Hmiss_of_mk_invariant_descended
    (ψm2 ψm1 ψm ψp1 ψp2 : R[X][Y])
    -- Replace this hypothesis by the actual theorem call:
    (hInv :
      mkW (C W.Ψ₃ * (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3)) =
        mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1))) :
    mkW (C W.Ψ₃ * HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0 := by
  have hψ2sq : mkW (W.ψ₂ ^ 2) = mkW (C W.Ψ₂Sq) := by
    simpa using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))

  have hpre4 :
      mkW (C W.preΨ₄ + W.ψ₂ ^ 4) = mkW (C (W.Ψ₃ * HmissCoeff W)) :=
    mk_preΨ₄_add_ψ₂_pow_four_eq_Ψ₃_mul_HmissCoeff (W := W)

  -- Normalize `hInv` into coordinate-ring algebra.
  have hInv' :
      mkW (C W.Ψ₃) *
          (mkW (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2) + mkW (C W.Ψ₂Sq) * mkW (ψm ^ 3)) =
        mkW (C W.Ψ₃) * mkW (C (HmissCoeff W)) * mkW (ψp1 * ψm * ψm1) := by
    -- This is just `hInv` with `ψ₂² ↦ Ψ₂Sq` and
    -- `preΨ₄ + ψ₂⁴ ↦ Ψ₃*(6X²+b₂X+b₄)`.
    -- `simpa` often closes after the two rewrites; if not, use the calc below.
    calc
      mkW (C W.Ψ₃) *
          (mkW (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2) + mkW (C W.Ψ₂Sq) * mkW (ψm ^ 3))
          = mkW (C W.Ψ₃ * (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3)) := by
              rw [← hψ2sq]
              simp [map_add, map_mul, map_pow]
      _ = mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1)) := hInv
      _ = mkW (C W.Ψ₃) * mkW (C (HmissCoeff W)) * mkW (ψp1 * ψm * ψm1) := by
              rw [hpre4]
              simp [map_mul]

  -- Convert the normalized equality to the zero statement.
  -- This is ring algebra inside the coordinate ring.
  have hzero :
      mkW (C W.Ψ₃) *
        (mkW (ψm1 ^ 2 * ψp2 + ψm2 * ψp1 ^ 2 + C W.Ψ₂Sq * ψm ^ 3
            - C (HmissCoeff W) * (ψm1 * ψm * ψp1))) = 0 := by
    -- The two sums differ only by commutativity/associativity.
    -- `linear_combination` also works, but `ring_nf` is usually enough.
    linear_combination (norm := ring_nf) hInv'

  simpa [HmissPoly, map_add, map_sub, map_mul, map_pow, mul_assoc, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm] using hzero

end CoordinateRing
end Affine
end WeierstrassCurve
```

This is the safe conclusion from the existing invariant lemma.

## Getting `Hmiss` itself: cancellation is an extra hypothesis

If you can cancel `mk(C W.Ψ₃)`, then `mk_invariant_descended` implies `Hmiss`.

Over a field, the coordinate ring is an integral domain by the existing instance, but you still need to know `mk(C W.Ψ₃) ≠ 0`.  A typical statement is:

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

local notation "mkW" p => CoordinateRing.mk W.toAffine p

lemma Hmiss_of_mk_invariant_descended_of_Ψ₃_ne_zero
    (ψm2 ψm1 ψm ψp1 ψp2 : K[X][Y])
    (hΨ₃ : mkW (C W.Ψ₃) ≠ 0)
    (hInv :
      mkW (C W.Ψ₃ * (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3)) =
        mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1))) :
    mkW (HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0 := by
  have hmul := Ψ₃_mul_Hmiss_of_mk_invariant_descended
    (W := W) ψm2 ψm1 ψm ψp1 ψp2 hInv
  -- Coordinate ring is a domain over a field/elliptic curve; use `mul_eq_zero.mp`.
  exact (mul_eq_zero.mp (by simpa [map_mul] using hmul)).resolve_left hΨ₃

end CoordinateRing
end Affine
end WeierstrassCurve
```

A possible proof of `hΨ₃` is by `AdjoinRoot.mk_ne_zero_of_natDegree_lt`, because `C W.Ψ₃` has `Y`-degree `0 < 2`.  You also need `W.Ψ₃ ≠ 0`.  That can fail or become delicate in small characteristics/special strata, so I would **not** bake cancellation into a general theorem unless the target assumptions really provide it.

## Conversely: `Hmiss` implies `mk_invariant_descended` without cancellation

This direction is unconditional and is often the better rewrite direction.

```lean
namespace WeierstrassCurve
namespace Affine
namespace CoordinateRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

local notation "mkW" p => CoordinateRing.mk W.toAffine p

lemma mk_invariant_descended_of_Hmiss
    (ψm2 ψm1 ψm ψp1 ψp2 : R[X][Y])
    (hHmiss : mkW (HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0) :
    mkW (C W.Ψ₃ * (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3)) =
      mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1)) := by
  have hψ2sq : mkW (W.ψ₂ ^ 2) = mkW (C W.Ψ₂Sq) := by
    simpa using (Affine.CoordinateRing.mk_ψ₂_sq (W := W))
  have hpre4 :
      mkW (C W.preΨ₄ + W.ψ₂ ^ 4) = mkW (C (W.Ψ₃ * HmissCoeff W)) :=
    mk_preΨ₄_add_ψ₂_pow_four_eq_Ψ₃_mul_HmissCoeff (W := W)

  -- Multiply `hHmiss` by `mk(C Ψ₃)` and rewrite back.
  have hmul : mkW (C W.Ψ₃) * mkW (HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0 := by
    simpa [hHmiss]

  -- This final step is just coordinate-ring algebra plus the two rewrites.
  calc
    mkW (C W.Ψ₃ * (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2 + W.ψ₂ ^ 2 * ψm ^ 3))
        = mkW (C W.Ψ₃) *
            (mkW (ψp2 * ψm1 ^ 2 + ψp1 ^ 2 * ψm2) + mkW (C W.Ψ₂Sq) * mkW (ψm ^ 3)) := by
              rw [← hψ2sq]
              simp [map_add, map_mul, map_pow]
    _ = mkW (C W.Ψ₃) * mkW (C (HmissCoeff W)) * mkW (ψp1 * ψm * ψm1) := by
              -- Follows from `hmul`; `ring_nf` rearranges `HmissPoly`.
              linear_combination (norm := ring_nf [HmissPoly]) hmul
    _ = mkW ((C W.preΨ₄ + W.ψ₂ ^ 4) * (ψp1 * ψm * ψm1)) := by
              rw [hpre4]
              simp [map_mul]

end CoordinateRing
end Affine
end WeierstrassCurve
```

## Practical recommendation

For the CAS-identified missing identity, add `Hmiss` as the primary theorem if possible:

```lean
mkW (HmissPoly W ψm2 ψm1 ψm ψp1 ψp2) = 0
```

Then derive `mk_invariant_descended` from it.  If you only have `mk_invariant_descended`, you have only the weaker statement

```lean
mkW (C W.Ψ₃ * HmissPoly ...) = 0.
```

Do not cancel `Ψ₃` unless the proof context explicitly has a domain/nonzero hypothesis for `mk(C W.Ψ₃)`.
