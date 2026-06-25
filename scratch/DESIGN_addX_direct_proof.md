# Q281 (dm1): general proof strategy for the projective `addX` identity

## Executive answer

Yes, there is a non-circular algebraic proof, but it is **not** the induction you sketched.

Do **not** try to prove

```text
addXYZ(P, addXYZ(P, R_{m-1})) = addXYZ(P, R_m)
```

or use raw `addXYZ` associativity.  Raw `addXYZ` is a coordinate formula for representatives; it is not an associative operation on triples and can return the zero representative in degenerate cases.

The right proof is a **direct general-`m` polynomial identity**.  For the `X` component, you do not need the previous `X`-component identities for `m` or `m-1` at all.  Expand `addX([X,Y,1],R_m)`, use:

```text
φ_m = X ψ_m^2 - ψ_{m+1} ψ_{m-1},
2 ψ_m ω_m = ψ_{2m} - ψ_m^2(a₁φ_m + a₃ψ_m^2),
ψ_{2m} ψ₂ = ψ_{m-1}^2 ψ_m ψ_{m+2} - ψ_{m-2} ψ_m ψ_{m+1}^2,
F_W = 0,
```

and then `ring`.  This gives the theorem for all `m` in one shot.  No associativity, no fraction-field quotient, no root-counting, no separability.

In other words, the `addX` identity is not proved by induction on previously-proved `addX` identities; it is a one-step algebraic consequence of:

* the `φ` definition,
* the `ω` normalization,
* the full bivariate `ψ_even` EDS recurrence,
* the Weierstrass equation.

This is the scalable proof.  It replaces per-`m` cofactors by a symbolic proof parameterized by `m`.

---

## The exact identity to prove

Let

```text
P   = [X, Y, 1]
R_m = [φ_m, ω_m, ψ_m]
ψ₂  = 2Y + a₁X + a₃.
```

For Mathlib’s orientation

```text
addXYZ(P, R_m), not addXYZ(R_m, P),
```

the `Z` component is exact:

```text
addZ(P,R_m) = X ψ_m^2 - φ_m = ψ_{m-1} ψ_{m+1}.
```

The `X` component theorem is:

```text
mk_W (addX(P,R_m) - ψ_{m-1}^2 φ_{m+1}) = 0.
```

Equivalently, in characteristic not `2`, prove the doubled identity:

```text
mk_W (2 * (addX(P,R_m) - ψ_{m-1}^2 φ_{m+1})) = 0.
```

The doubled form is the best Lean target because the `addX` formula contains the term

```text
- ψ₂ * ψ_m * ω_m,
```

whereas your normalization gives `2 * ψ_m * ω_m`.  Multiplying by `2` avoids division during the polynomial proof.  After applying `mk`, cancel the scalar `2` using `h2 : (2 : K) ≠ 0`.

---

## Expanded `addX(P,R_m)` for general Weierstrass

For `P=[X,Y,1]` and `R_m=[φ,ω,ψ]`, Mathlib’s `Jacobian.addX` expands to:

```text
addX(P,R_m)
  = X*φ^2
    - 2*Y*ω*ψ
    + X^2*φ*ψ^2
    - a₁*X*ω*ψ
    - a₁*Y*φ*ψ^2
    + 2*a₂*X*φ*ψ^2
    - a₃*ω*ψ
    - a₃*Y*ψ^4
    + a₄*φ*ψ^2
    + a₄*X*ψ^4
    + 2*a₆*ψ^4.
```

The `ω` terms combine as

```text
-(2Y + a₁X + a₃) * ω * ψ = -ψ₂ * ω * ψ.
```

This is why the normalization identity and the `ψ_even` recurrence are exactly the right inputs.

---

## Direct algebraic proof sketch

Set abbreviations:

```text
a = ψ_{m-1},
b = ψ_m,
c = ψ_{m+1},
d = ψ_{m+2},
e = ψ_{m-2},
φ = X*b^2 - a*c.
```

The inputs are:

```text
Hω    : 2*b*ω = ψ_{2m} - b^2*(a₁*φ + a₃*b^2)
Heven : ψ_{2m}*ψ₂ = a^2*b*d - e*b*c^2
Hφ1   : φ_{m+1} = X*c^2 - d*b
HF    : Y^2 + a₁*X*Y + a₃*Y - X^3 - a₂*X^2 - a₄*X - a₆ = 0.
```

Then:

```text
2*(addX(P,R_m) - a^2*φ_{m+1})
```

is reduced as follows.

1. Combine the `ω` terms into `-2*ψ₂*b*ω`.
2. Use `Hω` to rewrite
   ```text
   -2*ψ₂*b*ω
     = -ψ₂*ψ_{2m} + ψ₂*b^2*(a₁*φ + a₃*b^2).
   ```
3. Use `Heven` to rewrite
   ```text
   -ψ₂*ψ_{2m}
     = -a^2*b*d + e*b*c^2.
   ```
4. Use the definitions of `φ_m` and `φ_{m+1}`.
5. Use `HF` to eliminate the single remaining curve-equation multiple.
6. The rest is commutative ring arithmetic.

This proves the general `m` theorem directly.  It is the generalization of all the per-`m` cofactors, but without ever constructing the cofactor.

---

## Lean target theorem

I would state the doubled theorem first:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

local notation3 "jx" => (0 : Fin 3)
local notation3 "jy" => (1 : Fin 3)
local notation3 "jz" => (2 : Fin 3)

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Projective division-polynomial representative. -/
noncomputable def divPolyRep (m : ℤ) : Fin 3 → K[X][Y] :=
  ![W.φ m, W.ω m, W.ψ m]

/-- Generic affine point in Jacobian coordinates. -/
def genericAffineRep : Fin 3 → K[X][Y] :=
  ![C X, Y, 1]

/-- Doubled `addX` identity.  This avoids dividing by `2` in the polynomial proof. -/
theorem mk_two_mul_addX_generic_divPolyRep_sub
    (m : ℤ) :
    Affine.CoordinateRing.mk W.toAffine
      ((2 : K[X][Y]) *
        ((W.toJacobian.addX genericAffineRep (W.divPolyRep m))
          - W.ψ (m - 1)^2 * W.φ (m + 1))) = 0 := by
  -- Inputs:
  --   hω    : 2 * ψ_m * ω_m = ψ_(2m) - ψ_m^2*(a₁φ_m+a₃ψ_m^2)
  --   heven : ψ_(2m) * ψ₂ = ψ_(m-1)^2 ψ_m ψ_(m+2)
  --                               - ψ_(m-2) ψ_m ψ_(m+1)^2
  --   hF    : mk W.toAffine W.toAffine.polynomial = 0
  -- Then close by `linear_combination` / `ring_nf`.
  have hω := W.two_mul_ψ_mul_ω m
  have heven := W.ψ_even m
  -- `hF` is usually `AdjoinRoot.mk_self` or follows by `simp` on `CoordinateRing.mk`.
  -- Pseudocode proof shape:
  --   linear_combination (norm := ring_nf [divPolyRep, genericAffineRep,
  --     Jacobian.addX, WeierstrassCurve.φ, WeierstrassCurve.ψ_two,
  --     WeierstrassCurve.Affine.polynomial])
  --       (C? polynomial coefficient) * congrArg (Affine.CoordinateRing.mk W.toAffine) hω
  --     + (C? polynomial coefficient) * congrArg (Affine.CoordinateRing.mk W.toAffine) heven
  --     + (C? polynomial coefficient) * (AdjoinRoot.mk_self W.toAffine.polynomial)
  sorry

/-- Undoubled `addX` identity, using `2 ≠ 0`. -/
theorem mk_addX_generic_divPolyRep_sub
    (h2 : (2 : K) ≠ 0) (m : ℤ) :
    Affine.CoordinateRing.mk W.toAffine
      ((W.toJacobian.addX genericAffineRep (W.divPolyRep m))
        - W.ψ (m - 1)^2 * W.φ (m + 1)) = 0 := by
  have h := W.mk_two_mul_addX_generic_divPolyRep_sub m
  -- Since `mk` is a ring hom, `h` is `2 * mk(expr) = 0`.
  -- Cancel `2` in the field/algebra.
  -- Exact API may be `mul_eq_zero.mp`; the scalar coercion is through `algebraMap`/`C`.
  -- This is a small simp/ring step after `map_mul`.
  sorry

end

end WeierstrassCurve
```

In the actual proof, it is usually cleaner to avoid guessing a `linear_combination` coefficient for the curve equation by first proving a plain polynomial identity:

```lean
2 * (addX - ψ_{m-1}^2 φ_{m+1})
  = A_m * W.toAffine.polynomial
    + B_m * (2*ψ_m*ω_m - (ψ_(2m) - ψ_m^2*(a₁φ_m+a₃ψ_m^2)))
    + C_m * (ψ_(2m)*ψ₂ - (ψ_{m-1}^2*ψ_m*ψ_{m+2} - ψ_{m-2}*ψ_m*ψ_{m+1}^2))
```

where `A_m,B_m,C_m` are symbolic expressions in `X,Y,ψ_{m-2},...,ψ_{m+2},φ_m,ω_m`.  `B_m` and `C_m` are simple:

```text
B_m = -ψ₂
C_m = -1
```

up to the orientation convention above.  The curve-equation coefficient `A_m` is whatever remains after ring normalization; it is much smaller in symbolic variables than the fully expanded per-`m` cofactor.

---

## Is this an induction?

Not in the “assume identity for `m` and prove it for `m+1`” sense.

It is better described as a **parametric recurrence proof**:

* `ψ_even m` is the recurrence input for the index `2m`.
* `φ_{m+1}` is unfolded by definition.
* `ω_m` is unfolded by its normalization identity.
* The Weierstrass equation closes the coordinate-ring part.

This is exactly the kind of algebraic proof you want: it uses EDS recurrences and Jacobian formulas, but it does not use point-level associativity or fraction-field quotient arguments.

If you want a true induction theorem for the entire projective formula, use `normEDSRec` / `normEDSRec'` to prove a **suite** of representative identities simultaneously, with the `addX` identity above as one of the local transition lemmas.  Do not make the transition lemma depend on the previous `addX` identity.

---

## What about `dblX` and `dblY`?

The same principle applies.

For `dblZ`, the identity is immediate from `ω` normalization:

```text
dblZ(R_m) = ψ_(2m).
```

For `dblX`, prove the doubled or multiplied symbolic identity directly from:

```text
ω normalization,
φ_{2m} = X ψ_{2m}^2 - ψ_{2m+1}ψ_{2m-1},
ψ_odd m for ψ_{2m+1},
ψ_odd (m-1) for ψ_{2m-1},
F_W = 0.
```

For `dblY`, use the same data plus the `ω_{2m}` normalization.  This is much heavier but still non-circular.

Again: do not prove these by raw `dblXYZ/addXYZ` associativity.  Prove them as direct polynomial identities from recurrences.

---

## Minimal extra infrastructure if direct recurrence proof stalls

The minimal extra theorem is not group associativity.  It is the **full Ward EDS identity** for `ψ`, not only the even/odd recursion:

```lean
theorem ψ_add_mul_sub_mul
    (W : WeierstrassCurve K) (m n r : ℤ) :
    W.ψ (m+n) * W.ψ (m-n) * W.ψ r^2 =
      W.ψ (m+r) * W.ψ (m-r) * W.ψ n^2
        - W.ψ (n+r) * W.ψ (n-r) * W.ψ m^2 := by
  -- This is `IsEllSequence` for the normalized EDS `ψ`.
  sorry
```

Then the `Z` component of the general addition theorem is just the `r=1` case.  Some of the `X/Y` algebra also becomes cleaner with suitable `r=1` and `r=2` specializations.

Mathlib’s EDS file defines `IsEllSequence`, but its module docstring still treats proving the canonical `normEDS` is an EDS as a TODO in the version used by this project.  If your branch does not already have this theorem, adding it would be a high-value infrastructure lemma.

That said, for the specific `addX(P,R_m)` identity, `ψ_even m` plus `ω` normalization should suffice; you do not need the full Ward identity unless you want the fully general `addXYZ(R_n,R_m)` theorem.

---

## Final recommendation

For the `addX` identity you asked about, write the proof as:

```text
1. Prove the doubled statement.
2. Expand `Jacobian.addX`, `φ`, `divPolyRep`, `genericAffineRep`.
3. Use `two_mul_ψ_mul_ω m` to eliminate `2ψ_mω_m`.
4. Use `ψ_even m` to eliminate `ψ₂ψ_{2m}`.
5. Use the affine Weierstrass equation in the coordinate ring.
6. Ring-normalize.
7. Cancel `2` only at the final field-level theorem if needed.
```

This is the scalable general-`m` proof.  It is not per-`m` cofactor extraction, and it does not depend on raw `addXYZ` associativity.
