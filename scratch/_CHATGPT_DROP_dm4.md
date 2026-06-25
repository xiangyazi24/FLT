# Q239 (dm4): `AdjoinRoot.mk` quotient-zero API

## Exact Mathlib names

The lemma you want is:

```lean
AdjoinRoot.mk_eq_zero
```

with statement shape:

```lean
(AdjoinRoot.mk f) g = 0 ↔ f ∣ g
```

There is also the direct root-relation simp lemma:

```lean
AdjoinRoot.mk_self
```

with statement shape:

```lean
(AdjoinRoot.mk f) f = 0
```

So for a CAS cofactor identity `bigPoly = Q * f` or `bigPoly = f * Q`, use `AdjoinRoot.mk_eq_zero`; do not try to use a special `map_mul_self` lemma.

## Generic proof snippets

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

The witness is `Q` in both cases because `f ∣ g` unfolds to `∃ c, g = f * c`; `ring` handles the commuted order in the `Q * f` case.

## Coordinate-ring form

If your goal is already definitionally this:

```lean
Affine.CoordinateRing.mk W.toAffine (Q * W.toAffine.polynomial) = 0
```

then the proof is:

```lean
by
  change (AdjoinRoot.mk W.toAffine.polynomial) (Q * W.toAffine.polynomial) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

For the opposite multiplication order:

```lean
by
  change (AdjoinRoot.mk W.toAffine.polynomial) (W.toAffine.polynomial * Q) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

If the local namespace abbreviates the curve as `W` rather than `W.toAffine`, use exactly the same pattern with `W.polynomial`:

```lean
by
  change (AdjoinRoot.mk W.polynomial) (Q * W.polynomial) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

and

```lean
by
  change (AdjoinRoot.mk W.polynomial) (W.polynomial * Q) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

## If `bigPoly` is hidden behind a hypothesis

If you have a hypothesis from CAS/ring-normalization:

```lean
hbig : bigPoly = Q * W.toAffine.polynomial
```

then use:

```lean
by
  rw [hbig]
  change (AdjoinRoot.mk W.toAffine.polynomial) (Q * W.toAffine.polynomial) = 0
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

For `bigPoly = W.toAffine.polynomial * Q`, replace the `change` line by the corresponding right-multiple version above.

## Shortest version when elaboration already sees `AdjoinRoot.mk`

When the goal is literally

```lean
(AdjoinRoot.mk f) (Q * f) = 0
```

this is enough:

```lean
by
  rw [AdjoinRoot.mk_eq_zero]
  exact ⟨Q, by ring⟩
```

Same for `(AdjoinRoot.mk f) (f * Q) = 0`.
