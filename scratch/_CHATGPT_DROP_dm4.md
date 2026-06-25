# Q239 (dm4): `AdjoinRoot.mk` quotient-zero API

## Exact lemma names

The quotient-zero lemma is:

```lean
AdjoinRoot.mk_eq_zero
```

Its statement has the shape:

```lean
(AdjoinRoot.mk f) g = 0 ↔ f ∣ g
```

The direct relation for the defining polynomial itself is:

```lean
AdjoinRoot.mk_self
```

with shape:

```lean
(AdjoinRoot.mk f) f = 0
```

For a CAS cofactor goal `mk f (Q * f) = 0` or `mk f (f * Q) = 0`, use `AdjoinRoot.mk_eq_zero`.  `AdjoinRoot.mk_self` is only the special case `g = f`.

## Generic three-line proofs

```lean
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

open Polynomial

variable {R : Type*} [CommRing R]
variable (f Q : R[X])

example : (AdjoinRoot.mk f) (Q * f) = 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩

example : (AdjoinRoot.mk f) (f * Q) = 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

The witness is `Q` in both cases.  Lean’s divisibility convention is `f ∣ g` means `∃ q, g = f * q`; in the `Q * f` case the `ring` step commutes the product.

If you prefer theorem-library proofs of divisibility instead of an explicit witness:

```lean
example : (AdjoinRoot.mk f) (Q * f) = 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  exact dvd_mul_left f Q

example : (AdjoinRoot.mk f) (f * Q) = 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  exact dvd_mul_right f Q
```

The explicit-witness version is usually more robust in polynomial-heavy files.

## Coordinate-ring form

If your goal is literally the affine coordinate-ring wrapper and the curve abbreviation is `W.toAffine`, use `change` to expose the underlying `AdjoinRoot.mk`.

For a left cofactor:

```lean
by
  change (AdjoinRoot.mk W.toAffine.polynomial) (Q * W.toAffine.polynomial) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

For a right cofactor:

```lean
by
  change (AdjoinRoot.mk W.toAffine.polynomial) (W.toAffine.polynomial * Q) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

If the local affine curve object is already named `W` and the goal is

```lean
Affine.CoordinateRing.mk W (Q * W.polynomial) = 0
```

then use:

```lean
by
  change (AdjoinRoot.mk W.polynomial) (Q * W.polynomial) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

and for the other multiplication order:

```lean
by
  change (AdjoinRoot.mk W.polynomial) (W.polynomial * Q) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

## When `bigPoly` is hidden behind a CAS identity

If the goal is

```lean
Affine.CoordinateRing.mk W.toAffine bigPoly = 0
```

and you have

```lean
hbig : bigPoly = Q * W.toAffine.polynomial
```

then:

```lean
by
  rw [hbig]
  change (AdjoinRoot.mk W.toAffine.polynomial) (Q * W.toAffine.polynomial) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

For

```lean
hbig : bigPoly = W.toAffine.polynomial * Q
```

use:

```lean
by
  rw [hbig]
  change (AdjoinRoot.mk W.toAffine.polynomial) (W.toAffine.polynomial * Q) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

## Ultra-short version if the wrapper unfolds by `simp`

Sometimes the coordinate-ring `mk` abbreviation unfolds enough for this to work directly:

```lean
by
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

If not, add the `change` line above.  The `change` line is the reliable version for `Affine.CoordinateRing.mk W.toAffine` goals.
