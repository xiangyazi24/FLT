import Mathlib
import FLT.Assumptions.MazurProof.Axioms

/-!
# Abstract Weil Pairing Interface

This file provides the abstract Weil pairing interface for the Mazur torsion
proof.  It is deliberately abstract: no Miller functions, divisors, or
elliptic-curve coordinates appear here.

## Main definitions

* `WeilPairingData`:  bilinear alternating nondegenerate pairing on an abstract
  `m`-torsion module `T` with values in `μ_m ⊆ Kˣ`.
* `AbstractGaloisWeilData`:  Galois-equivariant pairing with descent data,
  packaging the minimal inputs for the pure-algebra argument.

## Main results

* `primitive_root_in_base`:  if a Galois-equivariant pairing is primitive on a
  fully fixed basis, then the base monoid contains a primitive `m`-th root.
  This is the pure-algebra core of the Weil-pairing consequence.
* `weil_interface_bridge`:  connecting the abstract interface to the existing
  axiom `∃ ζ : ℚ, IsPrimitiveRoot ζ m` from `HasFullRationalTorsion E m`.
-/

noncomputable section

namespace MazurProof.WeilPairingInterface

/-! ## Helpers -/

/-- Coerce a root of unity to the underlying field element. -/
abbrev rootVal {m : ℕ} {K : Type*} [CommMonoid K] (ζ : rootsOfUnity m K) : K :=
  ((ζ : Kˣ) : K)

/-! ## Part 1 — Abstract Weil pairing structure -/

/--
Abstract Weil pairing data on an `m`-torsion module `T` with values in `μ_m`.

The module `T` carries `AddCommGroup` and `Module (ZMod m)` instances;
in applications it is instantiated by `E.nTorsion m` or an isomorphic type.
The codomain is `rootsOfUnity m K`, the subgroup of `m`-th roots of unity
in the units of `K`.

The fields record bilinearity (additive in `T`, multiplicative in `μ_m`),
the alternating property, and nondegeneracy witnessed by a pair whose pairing
value is a primitive `m`-th root.
-/
structure WeilPairingData (m : ℕ) (T K : Type*)
    [AddCommGroup T] [Module (ZMod m) T] [Field K] where
  /-- The pairing `e_m : T × T → μ_m`. -/
  pairing : T → T → rootsOfUnity m K
  /-- `e_m(0, Q) = 1`. -/
  pairing_zero_left : ∀ Q : T, pairing 0 Q = 1
  /-- `e_m(P, 0) = 1`. -/
  pairing_zero_right : ∀ P : T, pairing P 0 = 1
  /-- Left-additivity: `e_m(P₁ + P₂, Q) = e_m(P₁, Q) · e_m(P₂, Q)`. -/
  pairing_add_left : ∀ (P₁ P₂ Q : T),
    pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q
  /-- Right-additivity: `e_m(P, Q₁ + Q₂) = e_m(P, Q₁) · e_m(P, Q₂)`. -/
  pairing_add_right : ∀ (P Q₁ Q₂ : T),
    pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂
  /-- Alternating: `e_m(P, P) = 1`. -/
  alternating : ∀ P : T, pairing P P = 1
  /-- Nondegeneracy: there exist `P Q : T` such that `e_m(P,Q)` is a
      primitive `m`-th root of unity. -/
  nondegenerate :
    ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m

namespace WeilPairingData

variable {m : ℕ} {T K : Type*}
variable [AddCommGroup T] [Module (ZMod m) T] [Field K]

@[simp]
theorem pairing_self (w : WeilPairingData m T K) (P : T) :
    w.pairing P P = 1 :=
  w.alternating P

/-- Left nondegeneracy: `(∀ Q, e(P,Q) = 1) → P = 0`. -/
theorem left_nondegenerate (w : WeilPairingData m T K) (P : T)
    (h : ∀ Q : T, w.pairing P Q = 1) : P = 0 := by
  sorry

/-- Right nondegeneracy: `(∀ P, e(P,Q) = 1) → Q = 0`. -/
theorem right_nondegenerate (w : WeilPairingData m T K) (Q : T)
    (h : ∀ P : T, w.pairing P Q = 1) : Q = 0 := by
  sorry

/-- `e(P,Q) · e(Q,P) = 1` (skew-symmetry from alternating + bilinearity). -/
theorem pairing_swap_mul (w : WeilPairingData m T K) (P Q : T) :
    w.pairing P Q * w.pairing Q P = 1 := by
  have h := w.alternating (P + Q)
  rw [w.pairing_add_left P Q (P + Q),
      w.pairing_add_right P P Q,
      w.pairing_add_right Q P Q,
      w.alternating P, w.alternating Q] at h
  simpa [one_mul, mul_one] using h

/-- The pairing produces a primitive root in the field `K`. -/
theorem exists_primitive_root (w : WeilPairingData m T K) :
    ∃ ζ : K, IsPrimitiveRoot ζ m := by
  obtain ⟨P, Q, hprim⟩ := w.nondegenerate
  exact ⟨rootVal (w.pairing P Q), hprim⟩

end WeilPairingData

/-! ## Part 2 — Pure-algebra Galois descent -/

section PrimitiveRootTransport

variable {K₀ L₀ : Type*} [CommMonoid K₀] [CommMonoid L₀]

/--
Primitive-root structure descends along an injective monoid homomorphism.

If `ι(ζ)` is a primitive `m`-th root in `L₀`, then `ζ` is a primitive
`m`-th root in `K₀`, provided `ι` is injective.
-/
theorem isPrimitiveRoot_of_injective
    (ι : K₀ →* L₀) (hι : Function.Injective ι)
    {ζ : K₀} {m : ℕ}
    (hζ : IsPrimitiveRoot (ι ζ) m) :
    IsPrimitiveRoot ζ m where
  pow_eq_one := by
    apply hι
    rw [map_pow, hζ.pow_eq_one, map_one]
  dvd_of_pow_eq_one := by
    intro n hn
    apply hζ.dvd_of_pow_eq_one
    rw [← map_pow, hn, map_one]

end PrimitiveRootTransport

section GaloisDescent

/-!
### Abstract Galois-equivariant Weil pairing data

The structure `AbstractGaloisWeilData` packages the minimal inputs for the
pure-algebra argument that derives a primitive root in the base from:

1. a Galois-equivariant pairing `e : T → T → L`,
2. all torsion points fixed by Galois,
3. a chosen basis pair `(P,Q)` such that `e(P,Q)` is primitive,
4. descent: every Galois-fixed element of `L` lifts to the base `K`.

The proof is the formal version of:
```
  σ(e(P,Q)) = e(σP, σQ) = e(P,Q),
```
so `e(P,Q)` is fixed; descend it to `ζ : K`; transport primitivity.
-/

/--
Minimal abstract data for the Galois descent step of the Weil-pairing argument.

* `K₀` — base multiplicative monoid (e.g., `ℚ` under multiplication).
* `L₀` — ambient monoid containing pairing values (e.g., `ℚ̄`).
* `Γ` — Galois group.
* `T₀` — torsion module.
-/
structure AbstractGaloisWeilData (K₀ L₀ Γ T₀ : Type*)
    [CommMonoid K₀] [CommMonoid L₀]
    [Group Γ] [SMul Γ T₀] [SMul Γ L₀]
    (m : ℕ) where
  /-- Injective monoid map from the base to the ambient monoid. -/
  baseMap : K₀ →* L₀
  /-- The base map is injective. -/
  baseMap_injective : Function.Injective baseMap
  /-- Every Galois-fixed element of the ambient monoid descends to the base. -/
  fixed_to_base : ∀ z : L₀, (∀ σ : Γ, σ • z = z) → ∃ a : K₀, baseMap a = z
  /-- First basis element of the torsion module. -/
  P : T₀
  /-- Second basis element of the torsion module. -/
  Q : T₀
  /-- The pairing (values in the ambient monoid). -/
  e : T₀ → T₀ → L₀
  /-- All torsion points are fixed by Galois (rationality hypothesis). -/
  T_fixed : ∀ (σ : Γ) (R : T₀), σ • R = R
  /-- Galois equivariance: `σ(e(R,S)) = e(σR, σS)`. -/
  e_equivariant : ∀ (σ : Γ) (R S : T₀), σ • e R S = e (σ • R) (σ • S)
  /-- `e(P,Q)` is a primitive `m`-th root in the ambient monoid. -/
  primitive_on_basis : IsPrimitiveRoot (e P Q) m

variable {K₀ L₀ Γ T₀ : Type*}
variable [CommMonoid K₀] [CommMonoid L₀]
variable [Group Γ] [SMul Γ T₀] [SMul Γ L₀]

/--
**Core pure-algebra theorem.**

If a Galois-equivariant pairing is primitive on a fully fixed basis pair, then
the base monoid contains a primitive `m`-th root of unity.

Proof outline:
1. `σ(e(P,Q)) = e(σP, σQ) = e(P,Q)`, so `e(P,Q)` is Galois-fixed.
2. Descend the fixed element to `ζ` in the base via `fixed_to_base`.
3. Transport `IsPrimitiveRoot` from the ambient to the base via injectivity
   of `baseMap`.
-/
theorem primitive_root_in_base {m : ℕ}
    (D : AbstractGaloisWeilData K₀ L₀ Γ T₀ m) :
    ∃ ζ : K₀, IsPrimitiveRoot ζ m := by
  -- Step 1: e(P,Q) is Galois-fixed.
  have hfixed : ∀ σ : Γ, σ • D.e D.P D.Q = D.e D.P D.Q := fun σ => by
    rw [D.e_equivariant σ D.P D.Q, D.T_fixed σ D.P, D.T_fixed σ D.Q]
  -- Step 2: Descend to the base.
  obtain ⟨ζ, hζ⟩ := D.fixed_to_base (D.e D.P D.Q) hfixed
  -- Step 3: Transport primitivity.
  refine ⟨ζ, isPrimitiveRoot_of_injective D.baseMap D.baseMap_injective ?_⟩
  rw [hζ]
  exact D.primitive_on_basis

end GaloisDescent

/-! ## Part 3 — Bridge to the Mazur proof over ℚ -/

section Bridge

open scoped WeierstrassCurve.Affine

/--
Bridge theorem: from `HasFullRationalTorsion E m`, produce a primitive root
in `ℚ`.

This combines:
1. The Weil pairing exists on `E[m]` and is nondegenerate (EC theory).
2. Galois equivariance of the Weil pairing (EC theory).
3. Full rational torsion gives all `E[m]` fixed by `Gal(ℚ̄/ℚ)`.
4. `primitive_root_in_base` (proved above) yields the descent.

The `sorry` encapsulates the elliptic-curve inputs (steps 1--3).
The pure-algebra content (step 4) is fully proved.
-/
theorem weil_interface_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  -- To discharge this sorry, construct:
  --   AbstractGaloisWeilData ℚ ℚ̄ (Gal(ℚ̄/ℚ)) (E[m]) m
  -- from the Weil pairing on E, then apply primitive_root_in_base.
  sorry

end Bridge

end MazurProof.WeilPairingInterface
