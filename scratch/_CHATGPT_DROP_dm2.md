# Q2012 (dm2): abstract Weil-pairing interface for Lean 4

Date searched: 2026-06-28.

Goal: package exactly the Weil-pairing facts needed downstream in the Mazur/FLT proof without committing to a divisor-theoretic, Miller-function, or Picard/Riemann-Roch construction.

## Recommendation

Use an abstract torsion type

```lean
T : Type*
[AddCommGroup T]
[Module (ZMod m) T]
```

for `E[m]` in the interface.

For actual elliptic curves in the FLT project, instantiate `T` with

```lean
E.nTorsion m
```

where `FLT/EllipticCurve/Torsion.lean` defines

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

So: internally `E[m]` is a submodule/subtype of the elliptic-curve point group, but downstream proofs should see it as a type with `AddCommGroup` and `Module (ZMod m)`.  A bare `Subgroup` is too weak for the Mazur proof because the determinant/Galois-representation arguments are naturally `ZMod m`-linear.

For prime-level Mazur arguments, `m = p` is prime, and every nonzero element of `E[p]` has exact additive order `p` once the usual structure theorem is available.  For a general composite `m`, nondegeneracy should be stated using `addOrderOf P = m`, not `P ≠ 0`.

## Concrete Lean 4 proposal

This is designed to use existing Mathlib types:

* `rootsOfUnity m K` for `μ_m`;
* `IsPrimitiveRoot` for primitive pairing values;
* `AddCommGroup T` for the torsion group;
* `Module (ZMod m) T` for the `ZMod m`-module structure;
* `MulSemiringAction Γ K` for a Galois-type action on the target field;
* `DistribMulAction Γ T` for the induced action on torsion points.

```lean
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Abstract Weil pairing data

This file deliberately does not construct the Weil pairing.  It records exactly
the properties needed by downstream Mazur/FLT arguments.

The abstract torsion group is a type `T` with an additive group structure and a
`ZMod m`-module structure.  In the FLT project, instantiate `T` with
`E.nTorsion m` from `FLT.EllipticCurve.Torsion`.
-/

namespace FLT
namespace WeilPairingAbstract

noncomputable section

/-- Coerce a value of `μ_m = rootsOfUnity m K` to its underlying field element. -/
def rootValue {m : ℕ} {K : Type*} [CommMonoid K] (ζ : rootsOfUnity m K) : K :=
  ((ζ : Kˣ) : K)

/-- A root-of-unity subgroup element is primitive when its underlying field element is primitive. -/
def IsPrimitiveRootValue {m : ℕ} {K : Type*} [CommMonoid K]
    (ζ : rootsOfUnity m K) : Prop :=
  IsPrimitiveRoot (rootValue ζ) m

/--
Abstract Weil-pairing data on an abstract `m`-torsion group `T`.

The fields `left_kernel` and `right_kernel` are the clean group-theoretic
nondegeneracy statements.  The primitive-root fields are the stronger form that
is most useful in Mazur-style arguments: an exact-order-`m` torsion point pairs
with something to give a primitive `m`-th root of unity.

For prime `m = p`, exact order can usually be replaced by `P ≠ 0`; see
`WeilPairingPrimeData` below.
-/
structure WeilPairingData (m : ℕ) (T K : Type*)
    [AddCommGroup T] [Module (ZMod m) T] [Field K] where
  /-- Exclude the degenerate `m = 0` interface. -/
  hm_pos : 0 < m

  /-- The abstract Weil pairing `e_m : T × T → μ_m`. -/
  pairing : T → T → rootsOfUnity m K

  /-- Additivity in the first variable, written multiplicatively in the target. -/
  pairing_zero_left : ∀ Q : T, pairing 0 Q = 1
  pairing_add_left : ∀ P P' Q : T,
    pairing (P + P') Q = pairing P Q * pairing P' Q

  /-- Additivity in the second variable, written multiplicatively in the target. -/
  pairing_zero_right : ∀ P : T, pairing P 0 = 1
  pairing_add_right : ∀ P Q Q' : T,
    pairing P (Q + Q') = pairing P Q * pairing P Q'

  /-- Alternating property.  This implies skew-symmetry in many later settings. -/
  alternating : ∀ P : T, pairing P P = 1

  /-- Left-kernel nondegeneracy. -/
  left_kernel : ∀ P : T, (∀ Q : T, pairing P Q = 1) → P = 0

  /-- Right-kernel nondegeneracy. -/
  right_kernel : ∀ Q : T, (∀ P : T, pairing P Q = 1) → Q = 0

  /-- Primitive-root form of left nondegeneracy for exact-order-`m` points. -/
  primitive_of_addOrderOf_eq_left :
    ∀ {P : T}, addOrderOf P = m →
      ∃ Q : T, IsPrimitiveRootValue (pairing P Q)

  /-- Primitive-root form of right nondegeneracy for exact-order-`m` points. -/
  primitive_of_addOrderOf_eq_right :
    ∀ {Q : T}, addOrderOf Q = m →
      ∃ P : T, IsPrimitiveRootValue (pairing P Q)

/--
Prime-level convenience wrapper.

For `p` prime, the Mazur proof usually wants the stronger statement that every
nonzero torsion point pairs with some other torsion point to produce a primitive
`p`-th root of unity.
-/
structure WeilPairingPrimeData (p : ℕ) (T K : Type*)
    [AddCommGroup T] [Module (ZMod p) T] [Field K]
    extends WeilPairingData p T K where
  hp_prime : Nat.Prime p

  primitive_of_ne_zero_left :
    ∀ {P : T}, P ≠ 0 → ∃ Q : T, IsPrimitiveRootValue (pairing P Q)

  primitive_of_ne_zero_right :
    ∀ {Q : T}, Q ≠ 0 → ∃ P : T, IsPrimitiveRootValue (pairing P Q)

/--
Weil-pairing data with Galois equivariance.

The target equality is stated after coercing `rootsOfUnity m K` to `K`.  This
avoids having to set up a separate action on the `rootsOfUnity` subtype: a
`MulSemiringAction Γ K` already expresses that each `σ : Γ` acts on `K` by a
semiring automorphism-like map.
-/
structure WeilPairingGaloisData (m : ℕ) (Γ T K : Type*)
    [Monoid Γ]
    [AddCommGroup T] [Module (ZMod m) T] [DistribMulAction Γ T]
    [Field K] [MulSemiringAction Γ K]
    extends WeilPairingData m T K where
  galois_equivariant : ∀ (σ : Γ) (P Q : T),
    rootValue (pairing (σ • P) (σ • Q)) =
      σ • rootValue (pairing P Q)

section GaloisConsequences

variable {m : ℕ} {Γ T K : Type*}
variable [Monoid Γ]
variable [AddCommGroup T] [Module (ZMod m) T] [DistribMulAction Γ T]
variable [Field K] [MulSemiringAction Γ K]

/-- If both torsion points are fixed by `σ`, then the pairing value is fixed by `σ`. -/
theorem WeilPairingGaloisData.fixed_value_of_fixed_points
    (W : WeilPairingGaloisData m Γ T K)
    {σ : Γ} {P Q : T} (hP : σ • P = P) (hQ : σ • Q = Q) :
    σ • rootValue (W.pairing P Q) = rootValue (W.pairing P Q) := by
  simpa [hP, hQ] using (W.galois_equivariant σ P Q).symm

end GaloisConsequences

/--
Alternative to Galois equivariance: pairing values descend to a base field.

This is useful when the argument only needs the conclusion that all Weil-pairing
values are base-field rational, rather than the full equivariance formula.
-/
structure WeilPairingBaseFieldData (m : ℕ) (T k K : Type*)
    [AddCommGroup T] [Module (ZMod m) T]
    [Field k] [Field K] [Algebra k K]
    extends WeilPairingData m T K where
  /-- A base-field-valued pairing. -/
  pairing_base : T → T → rootsOfUnity m k

  /-- The `K`-valued pairing is obtained from the base-field-valued one. -/
  pairing_eq_algebraMap : ∀ P Q : T,
    rootValue (pairing P Q) = algebraMap k K (rootValue (pairing_base P Q))

/-!
## FLT elliptic-curve specialization

In a file that imports `FLT.EllipticCurve.Torsion`, the intended specialization is:

```lean
import FLT.EllipticCurve.Torsion

namespace FLT
namespace WeilPairingAbstract

abbrev CurveWeilPairingData {K : Type*} [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]
    (m : ℕ) : Type _ :=
  WeilPairingData m (E.nTorsion m) K

abbrev CurveWeilPairingPrimeData {K : Type*} [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic] [DecidableEq K]
    (p : ℕ) : Type _ :=
  WeilPairingPrimeData p (E.nTorsion p) K

end WeilPairingAbstract
end FLT
```

For a base curve over `k` and torsion over an extension `K`, use the torsion of
the base-changed curve, for example schematically:

```lean
WeilPairingData m ((E.map (algebraMap k K)).nTorsion m) K
```

with the exact parameters adjusted to the surrounding FLT file.
-/

end
end WeilPairingAbstract
end FLT
```

## Answer to “what type should `E[m]` be?”

Use this hierarchy:

1. **Concrete elliptic-curve type in FLT:**
   ```lean
   E.nTorsion m
   ```
   This is already defined as `Submodule.torsionBy ℤ (E⁄k).Point m`.

2. **Interface type:**
   ```lean
   T : Type*
   [AddCommGroup T]
   [Module (ZMod m) T]
   ```
   This is the right abstraction boundary.  It hides whether torsion was implemented as a submodule, subgroup, kernel, or subtype.

3. **Avoid a bare `Subgroup`:** it gives additive closure but not the `ZMod m` scalar action needed for linear algebra, determinants, and Galois representations.

4. **Avoid hard-coding `Submodule.torsionBy` in every theorem:** use it at the instantiation boundary only.  Downstream Mazur proofs should be phrased over `T` with the group/module instances.

## Why two nondegeneracy forms?

For general `m`, the statement

```lean
P ≠ 0 → ∃ Q, IsPrimitiveRoot (e_m P Q) m
```

is too strong: a nonzero point of `E[m]` may have exact order a proper divisor of `m`.  The robust general statement is:

```lean
addOrderOf P = m → ∃ Q, IsPrimitiveRoot (e_m P Q) m
```

For prime `p`, nonzero `p`-torsion points have exact order `p`, so `WeilPairingPrimeData` includes the convenient nonzero-point version.

## Why state Galois equivariance in `K` rather than in `rootsOfUnity m K`?

Mathlib defines

```lean
rootsOfUnity m K
```

as a subgroup of `Kˣ`, while

```lean
IsPrimitiveRoot ζ m
```

is a predicate on the underlying ring/field element `ζ : K`.  The helper

```lean
rootValue : rootsOfUnity m K → K
```

keeps coercions explicit.  It also lets equivariance be stated as

```lean
rootValue (e_m (σ • P) (σ • Q)) = σ • rootValue (e_m P Q)
```

using only a `MulSemiringAction Γ K`, with no separate subtype action on `rootsOfUnity` required.
