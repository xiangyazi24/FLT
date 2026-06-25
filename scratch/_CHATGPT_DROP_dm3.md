# Q283 (dm3): Function-field separability route without the projective formula?

## Short verdict

The proposed route is **mathematically standard**, but it is **not currently a
shortcut in Mathlib** for the FLT/Mazur separability brick.

The reason is simple: Mathlib has enough raw ingredients to talk about function
fields and elliptic-curve point groups over fields, and it even has field-theory
separable degree infrastructure.  But it does **not** appear to have the bridge
package that would make this route short:

```text
elliptic curve as a scheme/group scheme
+ multiplication-by-n as a finite morphism/rational map
+ degree([n]) = n²
+ differential d[n] nonzero ⇒ [n] separable
+ separability of [n] ⇒ reduced n-torsion divisor
+ reduced n-torsion divisor ⇒ preΨ'_n squarefree.
```

Moreover, without the projective formula you do not have an explicit function
field pullback

```text
[n]^* X = φ_n / ψ_n²,
[n]^* Y = ω_n / ψ_n³,
```

so there is no direct formal connection between the abstract point-group map
`n • P` and the denominator polynomial `preΨ'_n`.  That denominator connection is
exactly what the projective formula supplies.

Thus the function-field separability route does **not** bypass both the Bezout
certificates and the projective formula in current Mathlib.  It replaces them by a
larger missing algebraic-geometry bridge.

For `n ≤ 16`, the per-`n` Bezout/resultant certificates remain the faster route.

---

## Current Mathlib status by question

### (a) Degree of `[n]` as a rational map: `n²`?

I would plan as if the answer is **no**, at least not in the elliptic-curve API in
a usable form.

Mathlib has:

```lean
#check WeierstrassCurve.Affine.FunctionField
#check WeierstrassCurve.Affine.CoordinateRing
#check WeierstrassCurve.Affine.Point
#check WeierstrassCurve.Jacobian.Point
#check WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
```

It also has `AlgebraicGeometry.RationalMap` and scheme/function-field files.  But
the existing elliptic-curve development is primarily an explicit point/group-law
development over fields, not yet a group-scheme/morphism-degree development for
Weierstrass curves.

The theorem you would want would look like:

```lean
-- Schematic; not an existing small theorem.
theorem degree_mulMap
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    RationalMap.degree (ellipticMulMap W n) = n ^ 2 := by
  sorry
```

But to even state this cleanly, one needs:

```lean
ellipticMulMap W n : RationalMap E E
```

or a function-field embedding

```lean
mulPullback W n : K(E) →+* K(E)
```

as part of the elliptic-curve API.  The point-level map

```lean
fun P : W.Affine.Point => n • P
```

is not automatically a rational map of curves with a degree theorem.

### (b) Separable degree of a rational map?

Mathlib has field-theory infrastructure around separable degree.  In particular,
there is a `Mathlib/FieldTheory/SeparableDegree.lean` file, so the field-extension
side is not empty.

But for this route you need the **geometric wrapper**:

```text
separable degree of a dominant rational map of curves
= separable degree of the corresponding function-field extension.
```

and then the elliptic-specific statement:

```text
sepDegree([n]) = degree([n])  iff  d[n] ≠ 0.
```

I would not expect these to already be connected to
`WeierstrassCurve.Affine.Point` / `Jacobian.Point` in current Mathlib.

A field-theoretic version would have to be built manually:

```lean
-- Schematic only.
noncomputable def mulPullback
    (W : WeierstrassCurve k) (n : ℕ) :
    W.toAffine.FunctionField →+* W.toAffine.FunctionField := by
  -- Need explicit rational functions for [n]^*X and [n]^*Y.
  -- Without projective formula, these are not available.
  sorry

-- Then one would study the extension K(E) / image(mulPullback W n).
```

So Mathlib has some field-theory separability tools, but not the ready-made
rational-map separable-degree theorem for elliptic multiplication.

### (c) Theorem connecting separable degree to `preΨ'_n` squarefree?

I would plan as if the answer is **no**.

The desired theorem is highly nontrivial.  It would say that the denominator of
`[n]^*x`, after removing the universal `ψ₂` factor in even degree, cuts out the
nonzero `n`-torsion divisor modulo `±1`, and that separability of `[n]` implies
this divisor is reduced.  In Lean terms, you would need a bridge like:

```lean
-- Schematic; not existing as a Mathlib theorem.
theorem squarefree_preΨ'_of_sepDegree_mulMap
    (W : WeierstrassCurve k) [W.IsElliptic]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (hsep : separableDegree (ellipticMulMap W n) = n ^ 2) :
    Squarefree (W.preΨ' n) := by
  sorry
```

This bridge is essentially another form of the division-polynomial theorem.  It
requires identifying roots of `preΨ'_n` with x-coordinates of torsion points and
controlling the quotient by `P ↦ -P`.

---

## Why formal-group separability does not by itself prove `preΨ'_n` squarefree

The formal-group statement

```text
[n](T) = n*T + higher terms
```

and hence `d[n] ≠ 0` when `(n : k) ≠ 0` is the correct local reason that
multiplication by `n` is separable/étale.  But there are two missing links if the
goal is squarefreeness of `preΨ'_n`.

### Missing link 1: `[n]` as a morphism/rational map

The formal group gives the differential of the group endomorphism **once the
endomorphism exists as a morphism of the curve**.  Mathlib has the point-level
group law, but not a packaged finite morphism

```text
[n] : E → E
```

with degree and separability theorems.

### Missing link 2: denominator of `[n]^*x`

Even if `[n]` is known to be separable, to conclude that `preΨ'_n` is squarefree
you must know that `preΨ'_n` is the denominator/cutting equation for the nonzero
kernel divisor.  That is the identity

```text
[n]^*x = φ_n / ψ_n²
```

or at least the weaker denominator statement

```text
poles of [n]^*x are exactly zeros of preΨ'_n with the expected multiplicities.
```

This is essentially the X/Z part of the projective formula.  Without it,
separability of the abstract map `[n]` has no formal connection to the specific
polynomial `W.preΨ' n`.

So `formalNsmul_coeff_one` is excellent evidence and may be useful in a local
proof, but it does not remove the need to relate the formal group map to the
univariate division polynomial.

---

## The minimal theorem stack needed for this route

If you wanted to make the function-field route work, I would build it as the
following theorem stack.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Tactic

namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/-- Function field of the affine curve.  This already exists as an abbrev. -/
abbrev K : Type _ :=
  W.toAffine.FunctionField

/-- Missing bridge 1: multiplication-by-`n` as a function-field pullback. -/
noncomputable def mulPullback (n : ℕ) : K W →+* K W := by
  -- Needs rational functions for `[n]^*X` and `[n]^*Y`.
  -- Without projective formula this is not available in computable form.
  sorry

/-- Missing bridge 2: degree of the function-field extension. -/
theorem finrank_mulPullback_eq_sq
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Module.finrank (SubsemiringClass?) (K W) = n ^ 2 := by
  -- Schematic.  Need the correct algebra structure via `mulPullback W n`.
  sorry

/-- Missing bridge 3: formal derivative nonzero implies separability. -/
theorem mulPullback_separable_of_natCast_ne_zero
    (n : ℕ) (hn : (n : k) ≠ 0) :
    -- `K(E)` is separable over `[n]^*K(E)`.
    True := by
  -- Would use `formalNsmul_coeff_one` plus smooth curve/group morphism theory.
  sorry

/-- Missing bridge 4: denominator of `[n]^*X` is `preΨ'_n²` up to units. -/
theorem denom_mulPullback_X_eq_preΨ'
    (n : ℕ) :
    -- Denominator statement for `[n]^*X`.
    True := by
  -- This is essentially the X/Z part of the projective formula.
  sorry

/-- Missing bridge 5: separability of `[n]` implies squarefree denominator. -/
theorem squarefree_preΨ'_of_mulPullback_separable
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Squarefree (W.preΨ' n) := by
  -- Needs divisor/fiber theorem plus the denominator theorem above.
  sorry

end WeierstrassCurve
```

This is a major development.  The most expensive pieces are not field-theoretic
separable degree itself; they are the elliptic-curve/rational-map bridges.

---

## Could one avoid `ω_n` but still use function fields?

Maybe partially, but not enough to be a clean shortcut.

For squarefreeness of `preΨ'_n`, one might hope to prove only the X-coordinate
pullback

```text
[n]^*x = Φ_n / ΨSq_n
```

and avoid the Y-coordinate `ω_n`.  That would be enough to identify the denominator
of the x-map.  However, to prove that the rational function really is `[n]^*x`,
you still need to connect it to the group law.  The usual proof uses the full
projective representative `[φ_n : ω_n : ψ_n]`, because the curve equation alone
does not determine the sign/Y-coordinate of `[n]P`.

There may be a route using only symmetric functions under `P ↦ -P`, because the
x-coordinate descends to the quotient `E/{±1} ≅ P¹`.  But formalizing that in
Mathlib would require quotient-map infrastructure and a proof that the induced
map on `P¹` has denominator `preΨ'_n`.  That is not obviously shorter than adding
`ω_n`.

---

## Comparison with the per-`n` certificate route

For the Mazur `|T| ≤ 16` target, the finite certificate route is still the most
practical.

Per-`n` Bezout/resultant proof needs:

```lean
A_n * W.preΨ' n + B_n * derivative (W.preΨ' n)
  = C_n * W.Δ ^ e_n
```

Then:

```text
[W.IsElliptic] ⇒ W.Δ ≠ 0
(n : k) ≠ 0    ⇒ (C_n : k) ≠ 0
```

and you get `IsCoprime (W.preΨ' n) (derivative (W.preΨ' n))` directly.

The function-field separability route needs, in addition to formal group facts:

```text
construction of [n] as a rational map/function-field embedding;
degree([n]) = n²;
separable degree API connected to this map;
differential nonzero ⇒ separability of the map;
identification of preΨ'_n as the x-denominator/kernel divisor;
separability of the map ⇒ squarefree denominator.
```

That is much larger than 16 generated certificates.

---

## Direct answers

### (a) Does Mathlib have `degree([n]) = n²` as a rational map?

Not in a usable elliptic-curve form that I would rely on.  Mathlib has point group
laws and some scheme/rational-map infrastructure, but no apparent packaged theorem
for degree of the elliptic multiplication map.

### (b) Does Mathlib have separable degree of a rational map?

It has field-theory separable degree infrastructure, but the rational-map/curve
wrapper and its connection to elliptic multiplication maps appear to be missing.

### (c) Does Mathlib connect separable degree to `preΨ'_n` squarefree?

No.  That bridge would itself be a substantial theorem about the n-torsion divisor
and the x-coordinate quotient.  It is essentially another incarnation of the
projective/division-polynomial representability theorem.

## Recommendation

Do not pursue this as the main route for the FLT/Mazur separability brick.

Use `formalNsmul_coeff_one` as conceptual validation and maybe later for a local
formal proof, but for the current project goal the fastest route remains:

```text
per-`n` resultant/Bezout certificates for n ≤ 16.
```

If you later want a reusable general theorem, the most promising non-certificate
route is probably a local/divisor proof that `preΨ'_n` cuts out the reduced
nonzero n-torsion divisor when `(n : k) ≠ 0`.  But that still requires a serious
bridge from division polynomials to the group law; it is not currently supplied by
Mathlib’s function-field API alone.
