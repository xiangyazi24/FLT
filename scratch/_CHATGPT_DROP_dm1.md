# Q2026 (dm1): `WeilPairingInterface.lean`

```lean
import Mathlib

/-!
# Abstract Weil pairing interface

This file is intentionally abstract.  It records the API needed for the
Mazur-style full-rational-torsion obstruction, without introducing Miller
functions, divisors, elliptic-curve coordinates, or a concrete Galois action.

In applications, `E` should be instantiated by the `m`-torsion subgroup of an
elliptic curve, or by an abstract additive group known to model that torsion.
The codomain is Mathlib's `rootsOfUnity m K`, implemented as a subgroup of
`Kˣ`.
-/

namespace WeilPairingInterface

universe u v

/-- The group of `m`-th roots of unity in `K`, as implemented by Mathlib. -/
abbrev Mu (m : ℕ) (K : Type v) [Field K] : Type v :=
  rootsOfUnity m K

/-- Coerce a root of unity, represented as a unit, back to the base field. -/
abbrev rootValue {m : ℕ} {K : Type v} [Field K]
    (zeta : rootsOfUnity m K) : K :=
  ((zeta : Kˣ) : K)

/-- The abstract `m`-torsion predicate on an additive group. -/
def MTorsion (m : ℕ) (E : Type u) [AddCommGroup E] : Set E :=
  {P : E | m • P = 0}

/--
Abstract Weil-pairing data on an additive group `E` with values in the
`m`-th roots of unity of a field `K`.

The fields say that `pairing` is multiplicatively bilinear, alternating, and
nondegenerate in both arguments.  This is the interface layer only; no Miller
functions or divisor constructions are included here.
-/
structure WeilPairingData (m : ℕ) (E : Type u) [AddCommGroup E]
    (K : Type v) [Field K] where
  pairing : E → E → rootsOfUnity m K
  map_zero_left : ∀ Q : E, pairing 0 Q = 1
  map_zero_right : ∀ P : E, pairing P 0 = 1
  map_add_left : ∀ P Q R : E,
    pairing (P + Q) R = pairing P R * pairing Q R
  map_add_right : ∀ P Q R : E,
    pairing P (Q + R) = pairing P Q * pairing P R
  alternating : ∀ P : E, pairing P P = 1
  left_nondegenerate : ∀ P : E, (∀ Q : E, pairing P Q = 1) → P = 0
  right_nondegenerate : ∀ Q : E, (∀ P : E, pairing P Q = 1) → Q = 0

namespace WeilPairingData

variable {m : ℕ} {E : Type u} [AddCommGroup E]
variable {K : Type v} [Field K]

@[simp]
theorem pairing_zero_left (w : WeilPairingData m E K) (Q : E) :
    w.pairing 0 Q = 1 :=
  w.map_zero_left Q

@[simp]
theorem pairing_zero_right (w : WeilPairingData m E K) (P : E) :
    w.pairing P 0 = 1 :=
  w.map_zero_right P

@[simp]
theorem pairing_self (w : WeilPairingData m E K) (P : E) :
    w.pairing P P = 1 :=
  w.alternating P

end WeilPairingData

/--
Abstract witness that the `m`-torsion is fully rational over `K`.

The field `galoisFixed` is a placeholder predicate for "fixed by Galois".
A concrete elliptic-curve development should replace or instantiate this with
an actual Galois action and prove `all_mtorsion_fixed` from rationality of all
`m`-torsion points.

The field `primitive_on_mtorsion` is the abstract proof hook supplied by the
standard Weil-pairing theorem: on a fully rational rank-two `m`-torsion module,
a perfect alternating Weil pairing has a value that is a primitive `m`-th root
of unity.  Keeping this as a field avoids committing this interface file to any
particular basis, finite-module, or elliptic-curve implementation.
-/
structure FullyRationalMTorsion (m : ℕ) (E : Type u) [AddCommGroup E]
    (K : Type v) [Field K] where
  galoisFixed : E → Prop
  all_mtorsion_fixed : ∀ P : E, P ∈ MTorsion m E → galoisFixed P
  primitive_on_mtorsion :
    ∀ w : WeilPairingData m E K,
      ∃ P Q : E,
        P ∈ MTorsion m E ∧
        Q ∈ MTorsion m E ∧
        IsPrimitiveRoot (rootValue (w.pairing P Q)) m

variable {m : ℕ} {E : Type u} [AddCommGroup E]
variable {K : Type v} [Field K]

/--
If abstract Weil-pairing data exists and the `m`-torsion is fully rational,
then the base field contains a primitive `m`-th root of unity.

This is the interface-level version of the usual consequence of the Weil
pairing.  The concrete mathematical work is isolated in
`FullyRationalMTorsion.primitive_on_mtorsion`.
-/
theorem weil_pairing_gives_primitive_root
    (hPairing : Nonempty (WeilPairingData m E K))
    (hRat : FullyRationalMTorsion m E K) :
    ∃ zeta : K, IsPrimitiveRoot zeta m := by
  rcases hPairing with ⟨w⟩
  rcases hRat.primitive_on_mtorsion w with ⟨P, Q, _hP, _hQ, hprim⟩
  exact ⟨rootValue (w.pairing P Q), hprim⟩

/-- A convenience variant when the pairing data is already named. -/
theorem WeilPairingData.exists_primitive_root
    (w : WeilPairingData m E K)
    (hRat : FullyRationalMTorsion m E K) :
    ∃ zeta : K, IsPrimitiveRoot zeta m :=
  weil_pairing_gives_primitive_root ⟨w⟩ hRat

end WeilPairingInterface
```
