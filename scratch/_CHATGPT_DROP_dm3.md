# Q2053 (dm3): minimal Weil-pairing axiom seam for Mazur torsion

Date: 2026-06-28.

Question: for the Mazur proof, we only need the consequence

```text
if E/ℚ has full rational m-torsion, then ℚ contains a primitive m-th root of unity.
```

A possible future proof would use:

* A1: over `ℚbar`, `E[m]` is a free `ZMod m`-module of rank `2`;
* A2: the Weil pairing `e_m` exists and is nondegenerate alternating bilinear;
* A3: `e_m(P,Q)` is defined over `ℚ` / fixed by Galois when `P,Q` are `ℚ`-rational.

Should these be three separate axioms, or one packaged axiom?

## Executive answer

Use **one public axiom**, not three separate public axioms.

For the Mazur scaffold, the cleanest Lean API is exactly the theorem-level consequence already consumed downstream:

```lean
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

This is better than exposing A1, A2, and A3 separately.  A1/A2/A3 are the **future proof strategy**, not the right public interface for the Mazur torsion-bound proof.

## Why one axiom is cleaner

### 1. It matches exactly what `TorsionBound.lean` needs

The downstream argument only needs:

```lean
∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

from:

```lean
hm : 0 < m
hfull : HasFullRationalTorsion E m
```

It does not need access to the pairing, to a basis of `E[m]`, to Galois-equivariance, or to any divisor/cardinality theorem.  Keeping those out of the public axiom avoids forcing the rest of the Mazur proof to depend on unfinished elliptic-curve geometry.

### 2. A1 is already a separate hard theorem/sorry elsewhere

The FLT torsion scaffold already has the intended theorem:

```lean
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := ...
```

and the harder cardinality input behind it:

```lean
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry
```

Duplicating A1 as another axiom in `MazurProof/Axioms.lean` would create two theorem seams for the same mathematical fact.

### 3. A2 and A3 are not small Lean statements unless the whole pairing API is fixed

A2 sounds simple mathematically, but in Lean it requires choices such as:

```lean
-- possible target shapes
E.nTorsion m → E.nTorsion m → rootsOfUnity m K
E.nTorsion m → E.nTorsion m → Kˣ
E.nTorsion m → E.nTorsion m → K
```

and then decisions about:

* whether bilinearity is additive in both source variables and multiplicative in the target;
* whether values are in `rootsOfUnity m K` or in units/subtypes;
* how to state alternation: `e P P = 1`, or `e P Q * e Q P = 1`;
* how to state nondegeneracy: trivial left radical, trivial right radical, or an isomorphism to the dual;
* how to encode rationality/Galois equivariance across `ℚ → AlgebraicClosure ℚ`.

Those are all important future design choices, but they are noise for the current Mazur bound.

### 4. Three axioms increase adapter burden

If A1, A2, A3 are separate, then every later refactor has to keep three signatures synchronized with:

* `WeierstrassCurve.nTorsion`;
* the chosen `WeilPairing` definition;
* rational-point/base-change maps;
* Galois actions on points and roots of unity.

A single theorem-level axiom localizes all that churn behind one stable statement.

## Recommended public axiom

Keep the public axiom exactly at the arithmetic consequence:

```lean
namespace MazurProof

/--
Weil-pairing consequence used in the Mazur torsion-bound scaffold.

If `E/ℚ` contains full rational `m`-torsion, then `ℚ` contains a primitive
`m`-th root of unity.  This packages the future proof from:

* the rank-two structure of `E[m]` over `ℚbar`,
* nondegeneracy/alternation/bilinearity of the Weil pairing,
* Galois equivariance/rationality of the pairing value on rational torsion.
-/
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

end MazurProof
```

This is the cleanest Lean 4 axiom statement for the current proof.

## If you want a one-axiom package rather than the final consequence

If the goal is to preserve the outline “A1+A2+A3 imply the result” inside Lean, use a **single internal structure**, not three global axioms.  The structure can live in a future `WeilPairing.lean` or `WeilPairingConsequence.lean` file, and a theorem can convert it to the public consequence.

Sketch:

```lean
structure WeilPairingConsequencePackage
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop where
  primitive_root_of_full_torsion :
    0 < m → HasFullRationalTorsion E m → ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

But this collapses immediately to the same theorem-level statement.  Unless we are actively proving the pure algebra step in the same file, the structure buys very little.

A more proof-oriented future package would be something like:

```lean
structure WeilPairingData
    (K : Type*) [Field K]
    (T : Type*) [AddCommGroup T] [Module (ZMod m) T]
    (m : ℕ) where
  e : T → T → Kˣ
  left_bilin : ...
  right_bilin : ...
  alternating : ...
  nondegenerate_left : ...
  values_mth_roots : ∀ P Q, ((e P Q : K) ^ m = 1)
```

and then separately prove the pure algebra lemma:

```lean
nondegenerate_alternating_pairing_basis_value_primitive :
  ... → IsPrimitiveRoot (e P Q : K) m
```

That is worthwhile for a reusable Weil-pairing library, but it is overkill for the Mazur torsion scaffold.

## How to later replace the axiom

The eventual replacement path should be:

```lean
-- future theorem, after formalizing Weil pairing enough
 theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  -- 1. pass to E over AlgebraicClosure ℚ;
  -- 2. use n_torsion_dimension/cardinality to identify E[m] with (ZMod m)^2;
  -- 3. choose rational basis points from hfull;
  -- 4. use nondegenerate Weil pairing to get primitive e_m(P,Q);
  -- 5. use Galois equivariance/rationality to descend e_m(P,Q) to ℚ.
```

No downstream file should need to change when this proof replaces the axiom.

## Recommendation

For `MazurProof/Axioms.lean`, keep exactly one public axiom:

```lean
axiom weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Do not add separate A1/A2/A3 axioms to the Mazur proof API.  Treat A1/A2/A3 as the implementation plan for proving this one theorem later.
