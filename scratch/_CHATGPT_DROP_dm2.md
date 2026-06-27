# Q1140 (dm2): shortest honest path for `fullRationalTorsion_order_le_two`

## Problem restatement

You want to prove the Mazur-bound-style B-line lemma:

```lean
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2
```

where

```lean
HasFullRationalTorsion E m
```

means that there is an injective additive homomorphism

```lean
ZMod m × ZMod m →+ (E⁄ℚ).Point.
```

You already have the purely rational-root-of-unity endpoint:

```lean
isPrimitiveRoot_rat_order_le_two
```

morally saying that if `ζ : ℚ` is a primitive `m`th root of unity, then `m ≤ 2`.

The current file proves

```lean
weil_pairing_gives_primitive_root
```

from `fullRationalTorsion_order_le_two` by cases `m = 1`, `m = 2`, and contradiction for `m ≥ 3`.  That is fine as a vacuous consequence, but it cannot also be the route to prove `fullRationalTorsion_order_le_two`: using the bound to prove the primitive-root theorem and then using the primitive-root theorem to prove the bound would be circular.

The dependency should be reversed or split:

```text
minimal Weil-pairing consequence
  -> rational primitive root exists
  -> isPrimitiveRoot_rat_order_le_two
  -> fullRationalTorsion_order_le_two
  -> current vacuous theorem, if still desired
```

The key question is therefore: what is the smallest honest theorem to build that gives the Weil-pairing consequence without formalizing an entire Galois-representation stack?

## Executive answer

The shortest honest path is:

1. Do **not** build mod-`m` Galois representations from scratch.
2. Do **not** try to prove the order bound from cardinality/finite torsion alone.
3. Prove a **minimal base-field Weil pairing consequence**:

   ```lean
   theorem fullRationalTorsion_gives_primitive_root_direct
       (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
       (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
       ∃ ζ : ℚ, IsPrimitiveRoot ζ m
   ```

   where this theorem is proved from a Weil pairing defined over the base field on rational torsion points, not from Galois representations.

4. Then prove the bound by one line:

   ```lean
   obtain ⟨ζ, hζ⟩ := fullRationalTorsion_gives_primitive_root_direct E hm hfull
   exact isPrimitiveRoot_rat_order_le_two ζ hζ
   ```

This avoids the determinant representation, avoids cyclotomic character infrastructure, and avoids Galois equivariance.  It does **not** avoid the Weil pairing itself.  Some form of Weil pairing, or an equivalent theorem, is the essential mathematical input.

The best proof architecture is to isolate that input in one theorem whose statement is exactly what the B-line needs.

---

## Recommended Lean interface

Use a small interface theorem, not a full API for Galois representations.

```lean
import Mathlib

namespace FLT

open scoped BigOperators

/--
Minimal hard theorem.

Mathematical proof: construct the Weil pairing over the base field on rational
`m`-torsion points.  If `ZMod m × ZMod m` injects into `E(ℚ)`, choose the two
standard generators `P` and `Q`; they form a full basis of `E[m]`, so
`e_m(P,Q)` is a primitive `m`th root of unity.  Since the pairing is constructed
over `ℚ` and evaluated on rational points, the value lies in `ℚ`.
-/
theorem fullRationalTorsion_gives_primitive_root_direct
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  -- Hard proof: direct Weil pairing over the base field.
  -- This should NOT depend on `fullRationalTorsion_order_le_two`.
  sorry

/--
The B-line bound follows immediately from the direct Weil-pairing consequence
and the fact that `ℚ` has no primitive roots of unity of order greater than two.
-/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  obtain ⟨ζ, hζ⟩ := fullRationalTorsion_gives_primitive_root_direct E hm hfull
  exact isPrimitiveRoot_rat_order_le_two ζ hζ

end FLT
```

If the actual theorem `isPrimitiveRoot_rat_order_le_two` has the arguments in the other order, the final line becomes one of:

```lean
  exact isPrimitiveRoot_rat_order_le_two hζ
```

or

```lean
  exact isPrimitiveRoot_rat_order_le_two ζ m hζ
```

but the logical shape is the same.

For the existing theorem, keep the vacuous proof if convenient, but make sure it depends on the bound only **after** the bound has been proved from the direct pairing theorem, not the other way around.

---

## What the direct Weil-pairing proof needs

Let

```lean
hfull : HasFullRationalTorsion E m
```

unpack as

```lean
⟨f, hf_inj⟩
```

with

```lean
f : ZMod m × ZMod m →+ (E⁄ℚ).Point.
```

Define the two rational points:

```lean
P := f (1, 0)
Q := f (0, 1)
```

Because the domain has exponent `m`, both `P` and `Q` are killed by `m`.  Because `f` is injective, `P` and `Q` each have exact order `m`, and the map from `ZMod m × ZMod m` identifies the subgroup they generate with a full rank-two `m`-torsion subgroup.

The direct Weil-pairing theorem should then provide:

```text
e_m(P, Q) ∈ ℚ
IsPrimitiveRoot (e_m(P,Q)) m
```

The hard API can be much smaller than a general Galois-representation API.  You only need:

```lean
-- Schematic names only.
noncomputable def weilPairing
    (E : WeierstrassCurve K) [E.IsElliptic] (m : ℕ) :
    E.mTorsion m → E.mTorsion m → Kˣ

-- Pairing value is an m-th root of unity.
theorem weilPairing_pow_eq_one
    (P Q : E.mTorsion m) :
    (weilPairing E m P Q : K) ^ m = 1

-- If P,Q are a basis of E[m], the pairing value is primitive.
theorem weilPairing_isPrimitiveRoot_of_basis
    (hPQ : IsBasisOfTorsion E m P Q) :
    IsPrimitiveRoot (weilPairing E m P Q : K) m
```

You do not need, for this theorem:

```text
- a Galois group,
- a Galois action on E[m],
- a matrix representation rho_m,
- determinant on GL_2(ZMod m),
- a cyclotomic character,
- or the theorem det rho_m = chi_m.
```

The rationality of `e_m(P,Q)` is automatic if the pairing is constructed over `ℚ` and both inputs are points of `E(ℚ)`.  This is the key simplification compared to the usual textbook statement over `Qbar` plus Galois equivariance.

---

## Route 1: direct Weil pairing construction

### Existing Mathlib/FLT ingredients

Mathlib already has useful elliptic-curve and polynomial infrastructure:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
```

Relevant existing pieces include:

```text
WeierstrassCurve
WeierstrassCurve.IsElliptic
WeierstrassCurve.Affine.Point / Projective point APIs
WeierstrassCurve.preΨ'
WeierstrassCurve.Ψ
WeierstrassCurve.ψ
WeierstrassCurve.Φ
map/baseChange lemmas for the division polynomials
IsPrimitiveRoot
cyclotomic-polynomial/root-of-unity API
```

The division-polynomial file gives recurrences and map/base-change lemmas for `preΨ'`, `Ψ`, `ψ`, and `Φ`.  That is useful support code, but it is not itself a Weil pairing.

### Missing pieces

A direct pairing proof still needs real work:

```text
1. A usable rational-function/function-field layer for a Weierstrass curve.
2. Divisors of rational functions on the curve.
3. Miller functions or equivalent functions with prescribed divisors.
4. Definition of e_m(P,Q).
5. Well-definedness independent of auxiliary choices.
6. Bilinearity and alternating/skew-symmetry.
7. Nondegeneracy/perfectness.
8. The theorem that a basis P,Q of E[m] gives a primitive value e_m(P,Q).
```

For the B-line theorem you can aggressively restrict the scope:

```text
- base field K = ℚ, or at most `[Field K] [CharZero K]`;
- only m > 0;
- only inputs that come from an injected `ZMod m × ZMod m`;
- no Galois equivariance;
- no Tate modules;
- no determinant theorem;
- no cyclotomic character.
```

### Feasibility

This is the most honest and shortest mathematical route if you want to avoid building Galois representations.  It is still nontrivial, because the Weil pairing is not just a group-theory construction: it needs rational functions/divisors or an equivalent Miller-function formalization.

The crucial advantage is that the target theorem only needs the **primitive-value consequence**.  You do not need to expose a large public API.  Build the smallest theorem that turns full rational torsion into a primitive root of unity.

### Recommended shape of the hard theorem

Instead of first building a user-facing `weilPairing` object with all its laws, you can state and prove the exact consequence:

```lean
import Mathlib

namespace FLT

/--
Hard geometric theorem: full rational m-torsion forces a rational primitive
m-th root of unity.

This should be proved by a direct base-field Weil pairing, not by the B-line
order bound.
-/
theorem fullRationalTorsion_gives_primitive_root_direct
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  sorry

end FLT
```

Internally, the proof can introduce `weilPairing`, but the exported interface can remain this small.

---

## Route 2: division-polynomial approach

### What exists

Mathlib has substantial division-polynomial infrastructure:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
```

The useful objects are:

```text
W.preΨ' n : K[X]
W.preΨ n  : K[X]
W.Ψ n     : K[X][Y]
W.ψ n     : K[X][Y]
W.Φ n     : K[X]
```

with recurrence lemmas such as:

```text
W.preΨ'_even
W.preΨ'_odd
W.ψ_even
W.ψ_odd
```

and map/base-change lemmas:

```text
map_preΨ'
map_Ψ
map_ψ
baseChange_preΨ'
baseChange_Ψ
baseChange_ψ
```

This API is useful for proving that certain coordinates are `m`-torsion and for building explicit multiplication-by-`m` formulas.

### What would still need to be built

A pure division-polynomial proof of

```lean
HasFullRationalTorsion E m -> m ≤ 2
```

would need a uniform mechanism turning rational full `m`-torsion into a rational primitive `m`th root of unity. Division polynomials alone do not provide that.

They can show facts of the form:

```text
P ∈ E[m]  iff  ψ_m(P) = 0
```

or, after enough work:

```text
x-coordinates of m-torsion points are roots of preΨ'_m / Ψ_m variants.
```

But the implication

```text
all m-torsion points rational -> μ_m ⊆ ℚ
```

is not a formal consequence of the roots of the division polynomial being rational.  It is the Weil pairing theorem in another form.

You might try to extract a root of unity from identities among division polynomials, but those identities are essentially Miller-function/Weil-pairing identities.  That route is likely to recreate the Weil pairing in a more painful coordinate form.

### Feasibility

As a shortcut to the B-line bound: poor.

As support for a direct Weil-pairing implementation: useful.

The division-polynomial route is attractive only if you use it to construct Miller functions and the pairing value.  It is not a standalone replacement for the pairing.

---

## Route 3: pure number theory over `ℚ`

### What exists

You already have the key endpoint:

```lean
isPrimitiveRoot_rat_order_le_two
```

Mathlib also has general root-of-unity and cyclotomic infrastructure around:

```lean
import Mathlib.NumberTheory.Cyclotomic.Basic
```

and generic `IsPrimitiveRoot` API.

### Why this is not enough

The number-theoretic endpoint says:

```text
if ζ ∈ ℚ is primitive of order m, then m ≤ 2.
```

But the missing implication is:

```text
HasFullRationalTorsion E m -> ∃ ζ : ℚ, IsPrimitiveRoot ζ m.
```

That implication is not pure number theory.  It is an elliptic-curve theorem.

Kronecker-Weber does not help by itself.  It says finite abelian extensions of `ℚ` lie in cyclotomic extensions.  The needed statement goes the other way:

```text
ℚ(μ_m) ⊆ ℚ(E[m]).
```

That inclusion is exactly the Weil-pairing/determinant theorem.

Neron-Ogg-Shafarevich also does not help by itself.  If all `m`-torsion is rational, then `ℚ(E[m]) = ℚ`, which is unramified everywhere.  There is no contradiction unless you already know that `ℚ(μ_m)` sits inside `ℚ(E[m])`, again the Weil-pairing input.

Finiteness of rational torsion also does not help.  It allows finite subgroups; it does not exclude a finite subgroup isomorphic to `ZMod m × ZMod m`.

### Mazur's theorem

Mazur's torsion theorem would immediately imply the desired result: over `ℚ`, the rational torsion subgroup is either cyclic of one of the allowed orders or has `2`-primary rank two in the known small cases.  In particular, it cannot contain `ZMod m × ZMod m` for `m ≥ 3`.

But formalizing Mazur's theorem is vastly heavier than formalizing the Weil-pairing consequence.  It is not a shortcut.

### Feasibility

As a route to the missing lemma: not feasible unless you already have Mazur's theorem as an imported theorem.

As the final step after the pairing consequence: ideal.  This is exactly where `isPrimitiveRoot_rat_order_le_two` should be used.

---

## Route 4: determinant of Galois representation

### Mathematical route

The standard determinant proof is:

```text
rho_m : Gal(Qbar/Q) -> GL_2(ZMod m)
det rho_m = cyclotomic character mod m.
```

If `E[m]` is rational, then Galois acts trivially on `E[m]`, so `rho_m` is trivial.  Hence its determinant is trivial, so the cyclotomic character is trivial.  Therefore `μ_m ⊆ ℚ`, and then `isPrimitiveRoot_rat_order_le_two` gives `m ≤ 2`.

### Why this is not actually shorter in Lean

This route requires:

```text
1. algebraic closure and base change of E;
2. E[m] over Qbar as a finite ZMod m-module;
3. the Galois action on E[m];
4. a basis and matrix representation in GL_2(ZMod m);
5. determinant of that representation;
6. cyclotomic character mod m;
7. proof that det rho_m = cyclotomic character;
8. bridge from trivial cyclotomic character to rational primitive roots.
```

The theorem

```text
det rho_m = cyclotomic character
```

is normally proved using the Weil pairing:

```text
e_m(σP, σQ) = σ(e_m(P,Q))
e_m(aP+bQ, cP+dQ) = e_m(P,Q)^(ad-bc)
```

Therefore the determinant theorem is not a real way around the pairing.  It is the pairing packaged as representation theory.

### Feasibility

If FLT already had a proved theorem

```lean
WeierstrassCurve.det_galoisRep_eq_cyclotomic
```

then the determinant route would be short.  But if the Galois representation is absent or defined with unresolved `sorry`s, proving the determinant theorem is a bigger project than the direct base-field pairing consequence.

Do not build this from scratch for the B-line bound.

---

## Route 5: reduction modulo primes or finite-field counts

One might try:

```text
full rational m-torsion over ℚ
  -> for good primes p not dividing m, injects into E(F_p)
  -> m^2 divides #E(F_p)
```

Then hope to find a contradiction.

This is not uniform in `E`.  Bad primes depend on the discriminant.  The first good prime may be large, and the Hasse bound only says

```text
#E(F_p) ≤ p + 1 + 2 sqrt p.
```

For large `p`, this gives no contradiction with fixed `m`.  To make this route work uniformly, one needs deep global input, effectively modular curves or strong torsion classification.

### Feasibility

Poor as a general proof.  It may prove examples, not the theorem for all elliptic curves over `ℚ`.

---

## Route 6: finite-group structure only

From an injection

```lean
ZMod m × ZMod m →+ (E⁄ℚ).Point
```

you get at least `m^2` rational torsion points.  For `m ≥ 3`, that is at least nine points.

This is not contradictory.  Rational elliptic curves can have more than nine torsion points in cyclic cases, and cardinality alone cannot distinguish a cyclic group from a full rank-two subgroup.  The obstruction is specifically the presence of full level `m` structure, not just many torsion points.

A finite-group-only proof would need a theorem classifying rational torsion subgroups.  That is Mazur's theorem again.

### Feasibility

Not useful unless Mazur's theorem is already available.

---

## Practical recommendation for FLT

Replace the current architecture with three layers.

### Layer A: hard geometric input

```lean
import Mathlib

namespace FLT

/--
Hard theorem, proved by direct base-field Weil pairing.
Do not prove this using `fullRationalTorsion_order_le_two`.
-/
theorem fullRationalTorsion_gives_primitive_root_direct
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  sorry

end FLT
```

### Layer B: B-line bound

```lean
import Mathlib

namespace FLT

/--
Full rational `m`-torsion over `ℚ` forces `m ≤ 2`.
-/
theorem fullRationalTorsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    m ≤ 2 := by
  obtain ⟨ζ, hζ⟩ := fullRationalTorsion_gives_primitive_root_direct E hm hfull
  exact isPrimitiveRoot_rat_order_le_two ζ hζ

end FLT
```

### Layer C: existing vacuous primitive-root theorem, if still desired

```lean
import Mathlib

namespace FLT

/--
Once the B-line bound is known, this theorem is trivial in the `m ≥ 3` branch.
The substantive primitive-root construction lives in
`fullRationalTorsion_gives_primitive_root_direct`, not here.
-/
theorem weil_pairing_gives_primitive_root_from_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  have hmle : m ≤ 2 := fullRationalTorsion_order_le_two E hm hfull
  -- Existing proof by cases m = 1 and m = 2.
  -- The `m ≥ 3` branch is closed by `omega` from `hmle`.
  sorry

end FLT
```

The name `weil_pairing_gives_primitive_root_from_bound` is intentionally verbose: it prevents confusion with the actual pairing theorem.  If you keep the existing name `weil_pairing_gives_primitive_root`, make sure the project has a separate theorem whose proof really uses the pairing.

---

## The actual shortest honest route

The shortest honest path is not:

```text
fullRationalTorsion_order_le_two by determinant of rho_m
```

unless the determinant theorem already exists.

It is:

```text
construct only enough Weil pairing over ℚ
  -> full rational m-torsion gives ζ ∈ ℚ primitive of order m
  -> `isPrimitiveRoot_rat_order_le_two`
  -> m ≤ 2.
```

This avoids Galois representations entirely because the pairing is evaluated on rational points and constructed over the base field.

The one remaining `sorry` should therefore be moved from

```lean
fullRationalTorsion_order_le_two
```

to

```lean
fullRationalTorsion_gives_primitive_root_direct
```

or an even smaller internal theorem saying that the Weil pairing of the two injected standard generators is primitive.

That is the cleanest and least misleading architecture:

```text
Hard geometry: Weil pairing primitive-value theorem.
Easy number theory: Q has roots of unity only of orders 1 and 2.
Easy conclusion: full rational torsion has m <= 2.
```

## Bottom line

Route ranking for FLT:

```text
1. Direct base-field Weil pairing consequence: best honest route.
2. Determinant/cyclotomic character: good interface only if already proved; otherwise larger than needed.
3. Division polynomials alone: not enough; useful only as support for Miller/Weil pairing.
4. Pure number theory: only supplies the final `m <= 2` step after a primitive root is produced.
5. Mazur torsion theorem: would solve it, but is far too large and not a shortcut.
6. Reduction mod p / finite cardinality: not uniform and not sufficient.
```

So the answer is: avoid building Galois representations, but do not expect to avoid the Weil pairing or an equivalent theorem.  Build the smallest direct Weil-pairing consequence over `ℚ`, then finish `fullRationalTorsion_order_le_two` with `isPrimitiveRoot_rat_order_le_two`.
