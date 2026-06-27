# Q1256 (dm2): current Mathlib routes for excluding `(Z/pZ)^2 ⊂ E(Q)`

## Short conclusion

For current Mathlib, I do **not** see a sorry-free route proving, for every elliptic curve `E/Q` and odd prime `p`, that no injective homomorphism

```lean
ZMod p × ZMod p →+ (E/Q).Point
```

exists.  The obstruction is not the final field theory: Mathlib has strong roots-of-unity and cyclotomic APIs.  The missing bridge is elliptic-curve-specific: either the Weil pairing, the determinant/cyclotomic character of the torsion Galois representation, or the topology/classification of `E(R)`.

The most concrete feasible route today is a **single algebraic axiom** packaging the Weil-pairing corollary:

```lean
axiom weil_pairing_roots_of_unity_of_zmod_square
    {K : Type*} [Field K] [CharZero K]
    (m : N) (hm : 0 < m)
    (E : WeierstrassCurve K) [E.IsElliptic]
    (h : ∃ f : ZMod m × ZMod m →+ (E/K).Point, Function.Injective f) :
    ∃ ζ : K, IsPrimitiveRoot ζ m
```

Then the target over `Q` is immediate from the existing rational primitive-root lemma `isPrimitiveRoot_rat_order_le_two`.

## What Mathlib has

### Roots of unity / primitive roots / cyclotomic fields

This side is present and is the right language for the conclusion.

```lean
import Mathlib

#check IsPrimitiveRoot
#check IsPrimitiveRoot.iff_def
#check IsPrimitiveRoot.pow_eq_one_iff_dvd
#check IsPrimitiveRoot.isUnit
#check IsPrimitiveRoot.coe_units_iff
#check IsPrimitiveRoot.zmodEquivZPowers
#check primitiveRoots
#check rootsOfUnity
#check Polynomial.cyclotomic
#check IsCyclotomicExtension
#check IsPrimitiveRoot.adjoin_isCyclotomicExtension
#check CyclotomicField
```

So the statement `∃ ζ : K, IsPrimitiveRoot ζ m` is a natural Mathlib statement.

### Additive circle APIs

Mathlib also has useful circle infrastructure:

```lean
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real

#check AddCircle
#check UnitAddCircle
#check ZMod.toAddCircle
#check ZMod.toAddCircle_injective
#check AddCircle.pathConnectedSpace
#check AddCircle.compactSpace
```

`UnitAddCircle` is `AddCircle (1 : R)`, and `ZMod.toAddCircle` is the homomorphism sending `j mod N` to `j / N mod 1`.  This is enough to prove circle torsion facts with some work.

### Division polynomial APIs

Mathlib has division polynomials:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

#check WeierstrassCurve.ψ
#check WeierstrassCurve.Ψ
#check WeierstrassCurve.ΨSq
#check WeierstrassCurve.Φ
#check WeierstrassCurve.map_ψ
#check WeierstrassCurve.baseChange_ψ
```

But this is not enough by itself.  The missing bridge is the theorem relating point multiplication to vanishing of the division polynomial, and even that would mostly give a `p^2`-style algebraic torsion count, not the field-of-definition obstruction needed over `Q`.

## What Mathlib appears not to have

### 1. Completed elliptic-curve torsion Galois representations

The needed theorem would be something like:

```text
det rho_{E,p} = cyclotomic character
```

or equivalently the Galois-equivariant Weil pairing.  Current Mathlib does not appear to expose such a theorem.

The FLT repository has an experimental `FLT.EllipticCurve.Torsion` file, but it contains incomplete placeholders for the finiteness/cardinality of torsion and the continuous Galois representation.  That file is therefore not a present no-axiom solution.

### 2. The real topology/classification of `E(R)`

The real-analytic proof is mathematically excellent:

```text
E(R) ≅ S^1 or S^1 × Z/2Z.
For odd p, all p-torsion lies in the identity component.
Thus E(R)[p] ≅ Z/pZ.
So (Z/pZ)^2 cannot inject into E(R), hence cannot inject into E(Q).
```

But Mathlib does not appear to have the bridge

```lean
(E/R).Point ≃+ UnitAddCircle
```

or

```lean
(E/R).Point ≃+ UnitAddCircle × ZMod 2
```

or the weaker component theorem `#π₀(E(R)) ≤ 2`.  The existing elliptic-curve point file is algebraic: it defines nonsingular affine points and proves the group law using coordinate rings/class groups, not real analytic topology.

### 3. A division-polynomial field-of-definition theorem

A pure root-counting argument with `ψ_p` cannot prove the result.  Over an algebraic closure in characteristic different from `p`, the full `p`-torsion really has `p^2` points, so the division polynomial has enough roots.  The contradiction over `Q` is that full rational torsion forces the appropriate roots of unity into `Q`.

There are algebraic shadows of Weil pairing via discriminants of division polynomials.  For `p = 3`, one might try an explicit quartic-discriminant argument.  For all odd primes, this becomes another form of the cyclotomic/Weil-pairing obstruction, and Mathlib does not appear to have the needed discriminant formulas.

## Concrete recommended patch

Use exactly one trusted B-line axiom, stated over a general characteristic-zero field.

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs

noncomputable section

open scoped Classical

namespace FLT.MazurProof

/--
Weil-pairing corollary.

If `(ZMod m)^2` injects into the group of `K`-rational points of an elliptic curve
over a characteristic-zero field `K`, then `K` contains a primitive `m`-th root of
unity.
-/
axiom weil_pairing_roots_of_unity_of_zmod_square
    {K : Type*} [Field K] [CharZero K]
    (m : N) (hm : 0 < m)
    (E : WeierstrassCurve K) [E.IsElliptic]
    (h : ∃ f : ZMod m × ZMod m →+ (E/K).Point, Function.Injective f) :
    ∃ ζ : K, IsPrimitiveRoot ζ m

/-- Full rational rank-two `m`-torsion over `Q` forces `m <= 2`. -/
theorem zmod_square_rational_torsion_order_le_two
    (m : N) (hm : 0 < m)
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (h : ∃ f : ZMod m × ZMod m →+ (E/Q).Point, Function.Injective f) :
    m <= 2 := by
  rcases weil_pairing_roots_of_unity_of_zmod_square (K := Q) m hm E h with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ

/-- No full rational rank-two odd-prime torsion. -/
theorem no_zmod_square_rational_torsion_of_odd_prime
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    ¬ (∃ f : ZMod p × ZMod p →+ (E/Q).Point, Function.Injective f) := by
  intro h
  have hle : p <= 2 := zmod_square_rational_torsion_order_le_two p hp.pos E h
  omega

end FLT.MazurProof
```

If the downstream theorem is stated for the torsion subtype, use the subtype inclusion:

```lean
private theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve Q) [E.IsElliptic]
    (p : N) (hp : Nat.Prime p) (hpgt : 2 < p) :
    not (exists f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E/Q).Point), Function.Injective f) := by
  rintro (f, hf)
  let incl := (AddCommGroup.torsion (E/Q).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hsq : ∃ g : ZMod p × ZMod p →+ (E/Q).Point, Function.Injective g :=
    ⟨incl.comp f, hincl.comp hf⟩
  have hle : p <= 2 := zmod_square_rational_torsion_order_le_two p hp.pos E hsq
  omega
```

## Why this is the best current route

The real route requires formalizing the topology of real elliptic curves.  The division-polynomial route requires missing multiplication/field-of-definition theorems and still tends back toward Weil pairing.  The Galois-representation route requires the determinant/cyclotomic-character theorem, which is again the Weil pairing in another form.

The single axiom above is exactly the missing mathematical fact, stated in already-supported Mathlib language.  It cleanly replaces the real-torsion cardinality axioms for this proof.
