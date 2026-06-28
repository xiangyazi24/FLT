# Q2031 (dm4): pure-algebra Weil-pairing consequence in Lean

## Executive answer

Yes.  The proof you described can be isolated as a small pure-algebra lemma.  The key is to **not** formalize elliptic curves, divisors, or the Weil pairing itself here.  Instead, package the abstract pairing data as follows:

1. a group `Γ` acting on the torsion module `T` and on an extension field/monoid `L`;
2. a pairing `e : T → T → L`;
3. equivariance: `σ • e P Q = e (σ • P) (σ • Q)`;
4. all torsion points are fixed: `σ • P = P` for every `P : T`;
5. a chosen basis pair `P,Q` such that `e P Q` is a primitive `m`-th root;
6. a descent statement saying that every `Γ`-fixed element of `L` comes from the base field/monoid `K` through an injective monoid map `K →* L`.

Then the proof is exactly:

```text
σ(e(P,Q)) = e(σP, σQ) = e(P,Q),
```

so `e(P,Q)` is fixed; descend it to `ζ : K`; transfer `IsPrimitiveRoot` back across the injective map.

The only root-of-unity API needed is `IsPrimitiveRoot` plus, optionally, `rootsOfUnity` via `IsPrimitiveRoot.toRootsOfUnity`.

## Concrete Lean 4 code

This is deliberately pure algebra.  It does not mention elliptic curves.

```lean
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace MazurProof

/-!
# Pure algebra core of the Weil-pairing argument

This file proves the abstract final step:

* a Galois-equivariant pairing `e : T → T → L`,
* all points of `T` are fixed by the Galois action,
* for some basis pair `P,Q`, `e P Q` is a primitive `m`-th root,
* every fixed element of `L` descends to the base `K`,

imply that the base contains a primitive `m`-th root of unity.

No elliptic curves, no divisors, no Miller functions.
-/

section PrimitiveRootTransport

variable {K L : Type*} [CommMonoid K] [CommMonoid L]

/--
Primitive-root structure descends along an injective monoid hom.

This is the tiny algebra lemma used after the fixed value of the pairing is
identified with an element of the base field.
-/
theorem isPrimitiveRoot_of_injective_monoidHom
    (ι : K →* L) (hι : Function.Injective ι)
    {ζ : K} {m : ℕ}
    (hζ : IsPrimitiveRoot (ι ζ) m) :
    IsPrimitiveRoot ζ m := by
  refine ⟨?pow_eq_one, ?dvd_of_pow_eq_one⟩
  · apply hι
    rw [map_pow, hζ.pow_eq_one, map_one]
  · intro n hn
    apply hζ.dvd_of_pow_eq_one
    rw [← map_pow, hn, map_one]

end PrimitiveRootTransport

section AbstractPairing

variable {K L Γ T : Type*}
variable [CommMonoid K] [CommMonoid L]
variable [Group Γ] [SMul Γ T] [SMul Γ L]

/--
The minimal abstract data needed from the Weil pairing.

`K` is the base multiplicative monoid, typically `ℚ` or `ℚˣ` depending on the
chosen formulation.  `L` is the ambient field/monoid containing the pairing
values.  `Γ` is the Galois group acting on `T` and on `L`.

The field-theoretic fixed-field input is isolated in `fixed_to_base`:
every `Γ`-fixed element of `L` is in the image of `baseMap`.

The mathematical assertion "nondegenerate alternating pairing on a rank-two
free `ZMod m` module" is used here only through the one consequence
`primitive_on_basis`: for a chosen basis `P,Q`, the value `e P Q` is primitive.
-/
structure AbstractWeilPairingData (K L Γ T : Type*)
    [CommMonoid K] [CommMonoid L]
    [Group Γ] [SMul Γ T] [SMul Γ L]
    (m : ℕ) where
  baseMap : K →* L
  baseMap_injective : Function.Injective baseMap
  fixed_to_base : ∀ z : L, (∀ σ : Γ, σ • z = z) → ∃ a : K, baseMap a = z
  P : T
  Q : T
  e : T → T → L
  T_fixed : ∀ σ : Γ, ∀ R : T, σ • R = R
  e_equivariant : ∀ σ : Γ, ∀ R S : T, σ • e R S = e (σ • R) (σ • S)
  primitive_on_basis : IsPrimitiveRoot (e P Q) m

/--
If a Galois-equivariant pairing is primitive on a fixed basis pair, then the
base contains a primitive `m`-th root of unity.
-/
theorem primitive_root_in_base_of_abstract_weil_pairing
    {m : ℕ}
    (D : AbstractWeilPairingData K L Γ T m) :
    ∃ ζ : K, IsPrimitiveRoot ζ m := by
  let μ : L := D.e D.P D.Q
  have hμ_fixed : ∀ σ : Γ, σ • μ = μ := by
    intro σ
    dsimp [μ]
    rw [D.e_equivariant σ D.P D.Q, D.T_fixed σ D.P, D.T_fixed σ D.Q]
  rcases D.fixed_to_base μ hμ_fixed with ⟨ζ, hζ⟩
  refine ⟨ζ, ?_⟩
  apply isPrimitiveRoot_of_injective_monoidHom D.baseMap D.baseMap_injective
  simpa [μ, hζ] using D.primitive_on_basis

/--
Same conclusion, but returning an element of Mathlib's `rootsOfUnity m K`
subgroup.  This is sometimes a more literal spelling of `μ_m ⊂ K`.
-/
theorem primitive_root_in_rootsOfUnity_of_abstract_weil_pairing
    {m : ℕ} (hm : 0 < m)
    (D : AbstractWeilPairingData K L Γ T m) :
    ∃ ζ : rootsOfUnity m K, IsPrimitiveRoot (((ζ : rootsOfUnity m K) : Kˣ) : K) m := by
  rcases primitive_root_in_base_of_abstract_weil_pairing D with ⟨ζ, hζ⟩
  haveI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  refine ⟨hζ.toRootsOfUnity, ?_⟩
  simpa using hζ

end AbstractPairing

end MazurProof
```

## How this corresponds to the mathematical proof

The mathematical proof is exactly the Lean proof of `primitive_root_in_base_of_abstract_weil_pairing`:

```lean
  let μ : L := D.e D.P D.Q
  have hμ_fixed : ∀ σ : Γ, σ • μ = μ := by
    intro σ
    dsimp [μ]
    rw [D.e_equivariant σ D.P D.Q, D.T_fixed σ D.P, D.T_fixed σ D.Q]
```

This is the line-by-line formal version of:

```text
σ(e(P,Q)) = e(σP,σQ) = e(P,Q).
```

Then:

```lean
  rcases D.fixed_to_base μ hμ_fixed with ⟨ζ, hζ⟩
```

is the fixed-field step: the fixed value `μ` is the image of some base element `ζ`.

Finally:

```lean
  apply isPrimitiveRoot_of_injective_monoidHom D.baseMap D.baseMap_injective
  simpa [μ, hζ] using D.primitive_on_basis
```

transports `IsPrimitiveRoot` from the ambient field/monoid back to the base using injectivity of the base map.

## Where the actual Weil-pairing work is hidden

This pure lemma assumes:

```lean
primitive_on_basis : IsPrimitiveRoot (e P Q) m
```

In the real elliptic-curve theorem, that is where the nondegenerate alternating pairing on a free rank-two `ZMod m` module enters.  You can discharge it separately from a statement such as:

```lean
-- schematic
axiom primitive_on_basis_of_nondegenerate_alternating_pairing
    {m : ℕ} (T : Type*) [AddCommGroup T] [Module (ZMod m) T]
    (b : Basis (Fin 2) (ZMod m) T)
    (e : T → T → L)
    -- bilinear, alternating, nondegenerate, values in rootsOfUnity m L
    : IsPrimitiveRoot (e (b 0) (b 1)) m
```

But for the Mazur proof axiom assembly, you probably do **not** need this lower-level theorem.  The minimal useful axiom remains the elliptic-curve input:

```lean
axiom full_rational_torsion_forces_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

The code above is a good intermediate target if you want to split that axiom into:

1. an elliptic-curve Weil-pairing existence/nondegeneracy axiom producing `AbstractWeilPairingData`; and
2. this fully formal pure-algebra theorem.

## Suggested split of the current axiom

Instead of one black-box axiom, use:

```lean
axiom full_rational_torsion_gives_abstract_weil_pairing_data
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    -- returns appropriate `AbstractWeilPairingData ℚ L Γ T m`
    True
```

Then the pure theorem above closes the field-of-definition/root-of-unity part.  In practice, since the concrete `L`, `Γ`, and `T` still require elliptic-curve/Galois infrastructure, the current direct axiom is still the shortest route.  But this Round-3 lemma cleanly separates the genuinely formal algebra from the elliptic-curve content.
