# Q1244 (dm2): B-line replacement by a general Weil-pairing roots-of-unity axiom

## Verdict

Yes.  This is a good B-line replacement if the goal is only to rule out full rational rank-two `m`-torsion.  It avoids the real-topology statement

```lean
Set.ncard {P : (E/R).Point | (m : N) * P = 0} <= 2 * m
```

and replaces the two real-torsion axioms with one algebraic Weil-pairing corollary:

```text
full E[m](k)-rational torsion  ==>  k contains a primitive m-th root of unity.
```

For `k = Q`, the existing rational-root-of-unity lemma

```lean
isPrimitiveRoot_rat_order_le_two
```

then gives `m <= 2`.  This is exactly the obstruction needed for `no_odd_prime_square_in_torsion`.

The new axiom is not a theorem of the current elliptic-curve API unless the Weil pairing itself has already been formalized.  Mathlib has a strong roots-of-unity and cyclotomic API; the missing hard input is the elliptic-curve Weil pairing construction and its nondegeneracy.  So this is a cleaner axiom, not a presently automatic proof from existing elliptic-curve facts.

## Mathlib API status

Mathlib has the relevant field-theoretic language.

### 1. General primitive roots of unity

`IsPrimitiveRoot` is already general.  It is a predicate on elements of any commutative monoid, not just on complex numbers or number fields.

```lean
import Mathlib

#check IsPrimitiveRoot
#check IsPrimitiveRoot.iff_def
#check IsPrimitiveRoot.pow_eq_one_iff_dvd
#check IsPrimitiveRoot.isUnit
#check IsPrimitiveRoot.coe_units_iff
#check IsPrimitiveRoot.zmodEquivZPowers
#check IsPrimitiveRoot.card_rootsOfUnity
#check primitiveRoots
#check mem_primitiveRoots
```

The conceptual definition is:

```text
IsPrimitiveRoot ζ m  :=  ζ^m = 1 and every exponent killing ζ is divisible by m.
```

This is exactly the target conclusion for a Weil-pairing corollary.

### 2. Cyclotomic polynomial API

Mathlib has cyclotomic polynomials and their primitive-root interface.

```lean
import Mathlib

#check Polynomial.cyclotomic
#check Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots
#check Polynomial.prod_cyclotomic_eq_X_pow_sub_one
#check Polynomial.separable_cyclotomic
#check Polynomial.squarefree_cyclotomic
#check Polynomial.orderOf_root_cyclotomic_dvd
```

This API is useful if later we want to reformulate `IsPrimitiveRoot ζ m` as a root of `Polynomial.cyclotomic m k`, or reason about cyclotomic extensions.

### 3. Roots of unity and cyclotomic extensions

Mathlib also has `rootsOfUnity`, implemented as a subgroup of units, plus cyclotomic extensions.

```lean
import Mathlib

#check rootsOfUnity
#check mem_rootsOfUnity
#check mem_rootsOfUnity'
#check rootsOfUnity.mkOfPowEq
#check rootsOfUnityEquivNthRoots
#check IsCyclotomicExtension
#check isCyclotomicExtension_iff
#check IsCyclotomicExtension.exists_isPrimitiveRoot
#check IsPrimitiveRoot.adjoin_isCyclotomicExtension
#check CyclotomicField
```

This is enough language to state the desired field-theoretic corollary cleanly.

## Recommended single axiom

Put this in the same namespace as the current Mazur-proof axioms.  Keep the repository’s aliases `N`, `Q`, `R`, and slash notation if those are already used in the file.

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

namespace FLT.MazurProof

/--
Weil-pairing corollary, B-line axiom.

If an elliptic curve over a characteristic-zero field has full `m`-torsion rational
over the ground field, then the ground field contains a primitive `m`-th root of
unity.

Mathematically, choose a `ZMod m`-basis `P, Q` of `E[m](K)`.  The Weil pairing
`e_m(P,Q)` lies in `Kˣ`, is a primitive `m`-th root of unity by nondegeneracy,
and is fixed by Galois because `P` and `Q` are `K`-rational.
-/
axiom weil_pairing_roots_of_unity
    {K : Type*} [Field K] [CharZero K]
    (m : N) (hm : 0 < m)
    (E : WeierstrassCurve K) [E.IsElliptic]
    (hfull : ∃ f : ZMod m × ZMod m →+ (E/K).Point, Function.Injective f) :
    ∃ ζ : K, IsPrimitiveRoot ζ m

end FLT.MazurProof
```

This is deliberately the raw full-torsion hypothesis rather than a new generic `HasFullKTorsion` definition.  That keeps the change small and avoids introducing another definition parallel to `HasFullRationalTorsion`.

If `(E/K).Point` does not elaborate for a type variable `K` in the local file, use the point spelling already used by Mathlib/repo for points of a `WeierstrassCurve K`.  The intended type is the additive group of `K`-rational points of `E`.

## Replacement theorem over `Q`

This theorem is the direct replacement for the Route 4B real-torsion bound when the downstream proof only needs to bound full rational torsion.

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

namespace FLT.MazurProof

/--
Full rational `m`-torsion over `Q` forces `m <= 2`, by the Weil-pairing
roots-of-unity axiom and the classification of rational primitive roots of unity.
-/
theorem fullRationalTorsion_order_le_two_weil
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (m : N) (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m <= 2 := by
  rcases hfull with ⟨f, hf⟩
  rcases weil_pairing_roots_of_unity (K := Q) m hm E ⟨f, hf⟩ with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ

end FLT.MazurProof
```

If Lean does not unfold `HasFullRationalTorsion` automatically under `rcases`, use this equivalent version:

```lean
theorem fullRationalTorsion_order_le_two_weil
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (m : N) (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m <= 2 := by
  change (∃ f : ZMod m × ZMod m →+ (E/Q).Point, Function.Injective f) at hfull
  rcases hfull with ⟨f, hf⟩
  rcases weil_pairing_roots_of_unity (K := Q) m hm E ⟨f, hf⟩ with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ
```

## Concrete replacement for `no_odd_prime_square_in_torsion`

Use the new Weil route instead of `fullRationalTorsion_order_le_two_route4B`.

```lean
private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    not (exists f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E/Q).Point), Function.Injective f) := by
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p := (incl.comp f, hincl.comp hf)
  have hle : p <= 2 := fullRationalTorsion_order_le_two_weil E p hp.pos hfull
  omega
```

Equivalently, inline the axiom call:

```lean
private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    not (exists f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E/Q).Point), Function.Injective f) := by
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p := (incl.comp f, hincl.comp hf)
  rcases hfull with ⟨g, hg⟩
  rcases weil_pairing_roots_of_unity (K := Q) p hp.pos E ⟨g, hg⟩ with ⟨ζ, hζ⟩
  have hle : p <= 2 := isPrimitiveRoot_rat_order_le_two hζ
  omega
```

The helper-theorem version is cleaner because it isolates the rational-field consequence of the axiom.

## Import restructuring

Under this approach, `Axioms.lean` should not need `RealTorsionBound.lean` for this obstruction.

Recommended import shape:

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs
```

Then add the one new axiom and the helper theorem above.

Remove or stop importing the real-topology B-line axioms:

```lean
-- no longer needed for the rational full-torsion obstruction:
-- axiom real_mTorsion_finite
-- axiom real_mTorsion_card_le
-- theorem fullRationalTorsion_order_le_two_route4B  -- if it only exists to package those axioms
```

If `RealTorsionBound.lean` is still useful elsewhere, it can remain as a separate experimental file, but `Axioms.lean` should not import it for this route.  If the goal is truly “one B-line axiom”, then the old real-torsion axioms should be deleted or removed from the trusted import path.

## Why this is sufficient

The old real-torsion route was:

```text
(Z/m)^2 embeds into E(Q)
  -> (Z/m)^2 embeds into E(R)[m]
  -> m^2 <= #E(R)[m]
  -> m^2 <= 2m
  -> m <= 2.
```

The new field-theoretic route is shorter:

```text
(Z/m)^2 embeds into E(Q)
  -> Q contains a primitive m-th root of unity       -- new axiom
  -> m <= 2.                                        -- existing rational primitive-root lemma
```

For the odd-prime-square obstruction, `p` is prime and `2 < p`, so `p <= 2` contradicts `hpgt` by `omega`.

## Is this axiom weaker?

It is weaker in the local proof-theoretic sense relevant here: it only rules out full rank-two rational torsion.  It does not assert any global cardinality bound for all real `m`-torsion points.

It is not mathematically trivial.  It packages the Weil pairing plus nondegeneracy:

```text
E[m](K) ≅ (Z/m)^2
  -> choose basis P,Q
  -> e_m(P,Q) is a primitive m-th root of unity in K.
```

That is a standard algebraic theorem and is much closer to the actual arithmetic obstruction than the real-topological cardinality bound.

## Acceptance checks for a Codex patch

After implementing this route, run:

```bash
grep -R "axiom real_mTorsion_finite\|axiom real_mTorsion_card_le" -n FLT FermatsLastTheorem scratch || true
grep -R "axiom weil_pairing_roots_of_unity" -n FLT FermatsLastTheorem scratch || true
grep -R "fullRationalTorsion_order_le_two_route4B\|RealTorsionBound" -n FLT FermatsLastTheorem scratch || true
lake env lean path/to/Axioms.lean
```

Expected state:

```text
- exactly one new trusted B-line axiom: weil_pairing_roots_of_unity;
- no imported dependency on real_mTorsion_finite or real_mTorsion_card_le for no_odd_prime_square_in_torsion;
- no call to fullRationalTorsion_order_le_two_route4B in that theorem;
- the target Lean file compiles cleanly.
```

## Bottom line

This approach works well as an axiomatized B-line.  Mathlib already has the root-of-unity, primitive-root, and cyclotomic language needed to state and use the conclusion over general fields.  The only hard missing mathematical object is the elliptic-curve Weil pairing itself, so the clean axiom should be exactly the Weil-pairing corollary above.
