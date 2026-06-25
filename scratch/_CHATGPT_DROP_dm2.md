# Q226 (dm2): Coordinate-ring machinery for polynomial identities modulo `F_W`

Goal shape:

```lean
Affine.CoordinateRing.mk W.toAffine bigPoly = 0
```

where

```lean
bigPoly : K[X][Y]
```

and `bigPoly ∈ (W.toAffine.polynomial)`.

## Short answer

Use the `AdjoinRoot` quotient API directly.  The affine coordinate ring is literally

```lean
abbrev WeierstrassCurve.Affine.CoordinateRing (W : Affine R) :=
  AdjoinRoot W.polynomial
```

and

```lean
Affine.CoordinateRing.mk W = AdjoinRoot.mk W.polynomial
```

So the exact kernel lemma is:

```lean
AdjoinRoot.mk_eq_zero :
  AdjoinRoot.mk f g = 0 ↔ f ∣ g
```

There is no separate `CoordinateRing.mk_eq_zero` wrapper in the file I checked.  Use `rw [Affine.CoordinateRing.mk, AdjoinRoot.mk_eq_zero]` or `simpa [Affine.CoordinateRing.mk] using ...`.

For monic reduction, the exact lemma is:

```lean
Polynomial.modByMonic_eq_zero_iff_dvd (hq : q.Monic) :
  p %ₘ q = 0 ↔ q ∣ p
```

For the Weierstrass equation as a polynomial in `Y`, the monicity lemma is:

```lean
WeierstrassCurve.Affine.monic_polynomial : W.polynomial.Monic
```

Useful related names:

```lean
AdjoinRoot.mk_self     : AdjoinRoot.mk f f = 0
AdjoinRoot.mk_eq_mk    : AdjoinRoot.mk f g = AdjoinRoot.mk f h ↔ f ∣ g - h
Polynomial.mem_ker_modByMonic
```

## Toy example: `mk W W.polynomial = 0`

This is the minimal proof.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine

variable {R : Type*} [CommRing R] (W : Affine R)

example : CoordinateRing.mk W W.polynomial = 0 := by
  simpa [CoordinateRing.mk] using (AdjoinRoot.mk_self W.polynomial)

end Affine
end WeierstrassCurve
```

If your local goal is phrased with `W : WeierstrassCurve R` rather than `W : Affine R`, use:

```lean
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine W.toAffine.polynomial = 0 := by
  simpa [WeierstrassCurve.Affine.CoordinateRing.mk] using
    (AdjoinRoot.mk_self W.toAffine.polynomial)
```

## Divisibility/cofactor proof pattern

If CAS gives a cofactor

```lean
Q : K[X][Y]
```

with

```lean
bigPoly = W.toAffine.polynomial * Q
```

or `bigPoly = Q * W.toAffine.polynomial`, the most robust Lean proof is:

```lean
example {K : Type*} [Field K] (W : WeierstrassCurve K)
    (bigPoly Q : K[X][Y])
    (hQ : bigPoly = W.toAffine.polynomial * Q) :
    WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine bigPoly = 0 := by
  rw [hQ, map_mul]
  simp [WeierstrassCurve.Affine.CoordinateRing.mk]
```

For a generated proof, I would avoid using a hypothesis `hQ`; instead put the CAS-expanded `Q` in a `def` and close the equality by `ring_nf`/`ring1`:

```lean
noncomputable def addXCertQ (W : WeierstrassCurve K) : K[X][Y] :=
  -- CAS-generated cofactor
  0

lemma addX_bigPoly_eq_mul_polynomial (W : WeierstrassCurve K) :
    bigPoly W = W.toAffine.polynomial * addXCertQ W := by
  -- Usually:
  --   rw [bigPoly, addXCertQ, WeierstrassCurve.Affine.polynomial]
  --   ring_nf
  sorry

lemma addX_bigPoly_mk_eq_zero (W : WeierstrassCurve K) :
    WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (bigPoly W) = 0 := by
  rw [addX_bigPoly_eq_mul_polynomial]
  simp [WeierstrassCurve.Affine.CoordinateRing.mk]
```

This is approach (a), but using `AdjoinRoot.mk_self` through `simp` rather than manually mentioning `Ideal.Quotient`.

## `modByMonic` proof pattern

If you want the remainder route, the proof skeleton is:

```lean
example {K : Type*} [Field K] (W : WeierstrassCurve K)
    (bigPoly : K[X][Y])
    (hrem : bigPoly %ₘ W.toAffine.polynomial = 0) :
    WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine bigPoly = 0 := by
  rw [WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.mk_eq_zero]
  exact (Polynomial.modByMonic_eq_zero_iff_dvd
    (p := bigPoly) (q := W.toAffine.polynomial)
    W.toAffine.monic_polynomial).mp hrem
```

Or as a rewrite:

```lean
example {K : Type*} [Field K] (W : WeierstrassCurve K)
    (bigPoly : K[X][Y])
    (hrem : bigPoly %ₘ W.toAffine.polynomial = 0) :
    WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine bigPoly = 0 := by
  rw [WeierstrassCurve.Affine.CoordinateRing.mk, AdjoinRoot.mk_eq_zero,
    ← Polynomial.modByMonic_eq_zero_iff_dvd W.toAffine.monic_polynomial]
  exact hrem
```

This is approach (c).  It is conceptually clean, but for very large generated polynomials I would not ask Lean to compute `%ₘ` itself unless the expression has been normalized into a small form.

## Which approach is best for the real `addX` identity?

For the real `addX`/`addY` division-polynomial identities, I recommend:

```text
CAS-generate a cofactor Q and prove bigPoly = W.polynomial * Q by `ring_nf`/`ring1`, then use `mk_self`.
```

Reason: `Polynomial.modByMonic` is mathematically perfect, but large Lean goals can become slow if Lean has to perform the quotient/remainder computation internally.  SymPy/Sage/Singular can divide by the monic quadratic in `Y` instantly and return both quotient and remainder.  Then Lean only checks a deterministic polynomial identity with a supplied certificate.

In other words, use this workflow:

1. In Python/SymPy, compute

   ```python
   Q, R = div(bigPoly, F_W, main_variable=Y)
   assert R == 0
   ```

2. Print `Q` as a Lean expression.
3. In Lean, define `Q` and prove

   ```lean
   bigPoly = W.toAffine.polynomial * Q
   ```

   by `ring_nf`/`ring1` after unfolding definitions.
4. Finish by:

   ```lean
   rw [hQ, map_mul]
   simp [Affine.CoordinateRing.mk]
   ```

This keeps all hard division outside Lean but still gives a kernel-checked certificate: Lean verifies the cofactor identity.

## SymPy cofactor extraction

For the short Weierstrass curve:

```python
import sympy as sp

X, Y, A, B = sp.symbols("X Y A B")
FW = Y**2 - X**3 - A*X - B

# bigPoly = ...

Q, R = sp.div(sp.Poly(sp.expand(bigPoly), Y), sp.Poly(FW, Y))
Q = sp.expand(Q.as_expr())
R = sp.expand(R.as_expr())
assert R == 0
print(Q)
```

For the general long Weierstrass curve:

```python
import sympy as sp

X, Y, a1, a2, a3, a4, a6 = sp.symbols("X Y a1 a2 a3 a4 a6")
FW = Y**2 + a1*X*Y + a3*Y - X**3 - a2*X**2 - a4*X - a6

Q, R = sp.div(sp.Poly(sp.expand(bigPoly), Y), sp.Poly(FW, Y))
Q = sp.expand(Q.as_expr())
R = sp.expand(R.as_expr())
assert R == 0
print(Q)
```

Because `F_W` is monic in `Y`, this division is exact over the polynomial coefficient ring; no denominator issue is introduced.

## Practical recommendation

For small identities, this is fine:

```lean
rw [Affine.CoordinateRing.mk, AdjoinRoot.mk_eq_zero]
exact (Polynomial.modByMonic_eq_zero_iff_dvd W.toAffine.monic_polynomial).mp hrem
```

For the large `addX` identity, use a CAS cofactor.  The final Lean proof should look like:

```lean
lemma addX_identity_mk_eq_zero (W : WeierstrassCurve K) :
    Affine.CoordinateRing.mk W.toAffine (addXBigPoly W) = 0 := by
  have hQ : addXBigPoly W = W.toAffine.polynomial * addXIdentityCofactor W := by
    rw [addXBigPoly, addXIdentityCofactor, WeierstrassCurve.Affine.polynomial]
    ring_nf
  rw [hQ, map_mul]
  simp [WeierstrassCurve.Affine.CoordinateRing.mk]
```

If `ring_nf` is too slow on the fully expanded `Q`, split the certificate by `Y`-degree:

```text
bigPoly - F_W * Q = C R0 + C R1 * Y
```

and prove `R0 = 0`, `R1 = 0` as two smaller univariate identities in `K[X]`.  This mirrors the `modByMonic` remainder and is usually faster than one enormous bivariate `ring_nf` goal.
