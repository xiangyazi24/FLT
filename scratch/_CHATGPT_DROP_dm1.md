# Q98-dm1: per-prime module structure for `no_rational_point_of_order_ge_17`

## Executive verdict

There are **no closeable-now primes** for the direct `X_1(p)` route once `p ≥ 17`.

For prime `p ≥ 5`,

```text
g(X_1(p)) = (p - 5) * (p - 7) / 24.
```

Thus

```text
g(X_1(17)) = 5,
```

and the genus only increases from there.  So the A4-style pattern

```text
order point → genus 1 modular curve → rank-zero rational-point enumeration → contradiction
```

has **no prime-order analogue for p ≥ 17** using `X_1(p)`.

The per-prime module structure should therefore have an empty `CloseableNow` group and one deferred genus-≥2 cluster seam.

---

## Important split: direct `X_1(p)` route vs isogeny-reduced finite route

There are two logically different reductions.

### Route A: direct torsion route

A rational point of exact order `p` gives a non-cuspidal rational point on `X_1(p)`.  This applies to **every prime `p ≥ 17`**, so it is an infinite family.  It has no genus≤1 cases.

### Route B: use Mazur's rational-isogeny theorem first

A rational point of exact order `p` also gives a rational cyclic subgroup of order `p`, hence a rational point on `X_0(p)`.  Mazur's isogeny theorem reduces rational prime isogeny degrees to

```text
{2, 3, 5, 7, 11, 13, 17, 19, 37, 43, 67, 163}.
```

Then the prime-order torsion problem for `p ≥ 17` is reduced to the finite list

```text
{17, 19, 37, 43, 67, 163}.
```

But using this finite list imports a theorem essentially as deep as Mazur's method.  It is not a lightweight reduction.  Also, the actual torsion obstruction still lives naturally on `X_1(p)`, not merely on `X_0(p)`: `X_0(17)` and `X_0(19)` are genus 1, but they have non-cuspidal rational points corresponding to rational 17- and 19-isogenies.  That does **not** imply rational 17- or 19-torsion.

---

## Per-prime genus table for the direct `X_1(p)` route

The table below lists the primes most relevant to the discussion.  The verdict column is about the direct `X_1(p)` curve, not `X_0(p)`.

| prime `p` | `g(X_1(p))` | closeable now? | module status |
|---:|---:|---|---|
| 17 | 5 | no | deferred genus≥2/high-genus seam |
| 19 | 7 | no | deferred genus≥2/high-genus seam |
| 23 | 12 | no | deferred genus≥2/high-genus seam |
| 29 | 22 | no | deferred genus≥2/high-genus seam |
| 31 | 26 | no | deferred genus≥2/high-genus seam |
| 37 | 40 | no | deferred genus≥2/high-genus seam |
| 41 | 51 | no | deferred genus≥2/high-genus seam |
| 43 | 57 | no | deferred genus≥2/high-genus seam |
| 47 | 70 | no | deferred genus≥2/high-genus seam |
| 53 | 92 | no | deferred genus≥2/high-genus seam |
| 59 | 117 | no | deferred genus≥2/high-genus seam |
| 61 | 126 | no | deferred genus≥2/high-genus seam |
| 67 | 155 | no | deferred genus≥2/high-genus seam |
| 71 | 176 | no | deferred genus≥2/high-genus seam |
| 73 | 187 | no | deferred genus≥2/high-genus seam |
| 79 | 222 | no | deferred genus≥2/high-genus seam |
| 83 | 247 | no | deferred genus≥2/high-genus seam |
| 89 | 287 | no | deferred genus≥2/high-genus seam |
| 97 | 345 | no | deferred genus≥2/high-genus seam |
| 101 | 376 | no | deferred genus≥2/high-genus seam |
| 103 | 392 | no | deferred genus≥2/high-genus seam |
| 107 | 425 | no | deferred genus≥2/high-genus seam |
| 109 | 442 | no | deferred genus≥2/high-genus seam |
| 113 | 477 | no | deferred genus≥2/high-genus seam |
| 127 | 610 | no | deferred genus≥2/high-genus seam |
| 131 | 651 | no | deferred genus≥2/high-genus seam |
| 137 | 715 | no | deferred genus≥2/high-genus seam |
| 139 | 737 | no | deferred genus≥2/high-genus seam |
| 149 | 852 | no | deferred genus≥2/high-genus seam |
| 151 | 876 | no | deferred genus≥2/high-genus seam |
| 157 | 950 | no | deferred genus≥2/high-genus seam |
| 163 | 1027 | no | deferred genus≥2/high-genus seam |

For all larger primes, the same formula gives even larger genus.  So a literal per-prime `X_1(p)` plan is not a finite Lean plan unless it is preceded by a deep finite-reduction theorem.

---

## Finite exceptional-isogeny list, if that theorem is imported

If the repo is willing to import the rational-isogeny prime list as a seam, then the only prime-order torsion candidates with `p ≥ 17` to exclude are:

| `p` | `g(X_1(p))` | `g(X_0(p))` | closeable via rank-zero elliptic enumeration? | note |
|---:|---:|---:|---|---|
| 17 | 5 | 1 | no | `X_0(17)` has noncuspidal rational points/isogenies |
| 19 | 7 | 1 | no | `X_0(19)` has noncuspidal rational points/isogenies |
| 37 | 40 | 2 | no | genus 2 `X_0`; rational 37-isogenies exist |
| 43 | 57 | 3 | no | exceptional isogeny prime |
| 67 | 155 | 5 | no | exceptional isogeny prime |
| 163 | 1027 | 13 | no | exceptional isogeny prime |

This table is useful for documentation, but it does not produce immediate Lean discharges.  The fact that `X_0(17)` and `X_0(19)` are genus 1 does **not** help the torsion problem in the same way `X_1(14)` helped A4, because `X_0(p)` forgets the generator and only remembers a cyclic subgroup.

---

## Proposed Lean module structure

Recommended layout:

```text
FLT/Mazur/PrimeTorsion/Basic.lean
FLT/Mazur/PrimeTorsion/GenusTable.lean
FLT/Mazur/PrimeTorsion/ModularCurveInterface.lean
FLT/Mazur/PrimeTorsion/DeferredHighGenus.lean
FLT/Mazur/PrimeTorsion/Assembly.lean
```

### `Basic.lean`

This file has only the public seam and convenience wrappers.

```lean
import Mathlib

namespace FLT.Mazur.PrimeTorsion

/--
Final named seam: prime-order part of Mazur's torsion theorem over `ℚ`.

This is intentionally stated directly for elliptic curves because the current repo does not
have a formal modular-curve hierarchy for `X_1(p)`.
-/
axiom no_rational_point_of_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    False

/-- Wrapper matching code that already reasons through `addOrderOf`. -/
theorem no_prime_order_ge_17_of_addOrderOf
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hp : Nat.Prime (addOrderOf P))
    (hp17 : 17 ≤ addOrderOf P) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E hp hp17 P rfl

end FLT.Mazur.PrimeTorsion
```

### `GenusTable.lean`

This file records the arithmetic table used for scoping.  It is not needed by the proof if the high-level seam is kept.

```lean
import Mathlib

namespace FLT.Mazur.PrimeTorsion

/-- Genus of `X_1(p)` for prime `p ≥ 5`, as a natural-number formula. -/
def X1PrimeGenus (p : ℕ) : ℕ :=
  ((p - 5) * (p - 7)) / 24

example : X1PrimeGenus 17 = 5 := by native_decide
example : X1PrimeGenus 19 = 7 := by native_decide
example : X1PrimeGenus 23 = 12 := by native_decide
example : X1PrimeGenus 29 = 22 := by native_decide
example : X1PrimeGenus 31 = 26 := by native_decide
example : X1PrimeGenus 37 = 40 := by native_decide
example : X1PrimeGenus 43 = 57 := by native_decide
example : X1PrimeGenus 67 = 155 := by native_decide
example : X1PrimeGenus 163 = 1027 := by native_decide

/-- There are no genus ≤ 1 direct `X_1(p)` cases for primes `p ≥ 17`. -/
theorem X1PrimeGenus_ge_five_of_ge17
    {p : ℕ} (hp17 : 17 ≤ p) :
    5 ≤ X1PrimeGenus p := by
  unfold X1PrimeGenus
  -- Arithmetic only.  Since `p ≥ 17`, `(p-5) ≥ 12` and `(p-7) ≥ 10`.
  -- The product is at least 120, and `120 / 24 = 5`.
  omega

end FLT.Mazur.PrimeTorsion
```

The `omega` proof may need a small helper about division monotonicity if it does not solve directly.  This file is documentation-oriented; it is not intended to replace the modular-curve theorem.

### `ModularCurveInterface.lean`

Only add this if you want to expose the intended modular-curve theorem without building actual modular curves yet.

```lean
import Mathlib

namespace FLT.Mazur.PrimeTorsion.ModularInterface

/-- Placeholder type for rational points of `X_1(p)`.  Do not use in final code unless a real
modular-curve hierarchy exists. -/
opaque X1Point : ℕ → Type

opaque IsCusp {p : ℕ} : X1Point p → Prop

axiom order_p_point_gives_X1_non_cusp
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    ∃ x : X1Point p, ¬ IsCusp x

end FLT.Mazur.PrimeTorsion.ModularInterface
```

### `DeferredHighGenus.lean`

This is the single modular-curve cluster seam, if you want a modular phrasing.

```lean
import Mathlib
import FLT.Mazur.PrimeTorsion.ModularCurveInterface

namespace FLT.Mazur.PrimeTorsion.ModularInterface

/--
High-genus modular-curve seam: for every prime `p ≥ 17`, every rational point of
`X_1(p)` is cuspidal.

This bundles all genus≥2/high-genus rational-point determinations and Mazur's
uniform method into one named seam.
-/
axiom X1_prime_ge17_rational_points_are_cusps
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (x : X1Point p) :
    IsCusp x

end FLT.Mazur.PrimeTorsion.ModularInterface
```

### `Assembly.lean`

This shows how the modular seam would imply the direct elliptic-curve seam.

```lean
import Mathlib
import FLT.Mazur.PrimeTorsion.ModularCurveInterface
import FLT.Mazur.PrimeTorsion.DeferredHighGenus

namespace FLT.Mazur.PrimeTorsion.ModularInterface

/-- If the modular-curve interface and high-genus cusp seam are available, the prime-order
elliptic-curve obstruction follows immediately. -/
theorem no_rational_point_of_prime_order_ge_17_from_X1
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    False := by
  rcases order_p_point_gives_X1_non_cusp E hp P hP with ⟨x, hnoncusp⟩
  exact hnoncusp (X1_prime_ge17_rational_points_are_cusps hp hp17 x)

end FLT.Mazur.PrimeTorsion.ModularInterface
```

---

## Per-prime theorem signatures

Since there are no genus≤1 direct `X_1(p)` cases for `p ≥ 17`, there are **no closeable-now per-prime theorem signatures** of the A4 rank-zero-elliptic kind.

For documentation only, if you want per-prime wrappers after importing the single high-genus seam, use:

```lean
namespace FLT.Mazur.PrimeTorsion

-- These are wrappers, not independent closeable-now proofs.

theorem no_order17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = 17) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E (by decide : Nat.Prime 17) (by decide : 17 ≤ 17) P hP

theorem no_order19
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = 19) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E (by decide : Nat.Prime 19) (by decide : 17 ≤ 19) P hP

theorem no_order23
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = 23) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E (by decide : Nat.Prime 23) (by decide : 17 ≤ 23) P hP

theorem no_order37
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = 37) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E (by decide : Nat.Prime 37) (by decide : 17 ≤ 37) P hP

theorem no_order43
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = 43) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E (by decide : Nat.Prime 43) (by decide : 17 ≤ 43) P hP

theorem no_order67
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = 67) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E (by decide : Nat.Prime 67) (by decide : 17 ≤ 67) P hP

theorem no_order163
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = 163) :
    False := by
  exact no_rational_point_of_prime_order_ge_17
    E (by decide : Nat.Prime 163) (by decide : 17 ≤ 163) P hP

end FLT.Mazur.PrimeTorsion
```

If the repo has a finite-isogeny reduction theorem, you can use just the wrappers for

```text
17, 19, 37, 43, 67, 163.
```

Without that reduction, the theorem must remain uniform in `p`.

---

## Concrete module recommendation

Use this now:

```text
FLT/Mazur/PrimeTorsion/Basic.lean
```

with exactly one seam:

```lean
axiom no_rational_point_of_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    False
```

Keep the modular-curve files as design notes until there is real support for `X_1(p)`/`X_0(p)`.

The answer to “which primes are closeable now?” is:

```text
none.
```

The answer to “what is the single genus≥2 cluster seam?” is:

```lean
axiom X1_prime_ge17_rational_points_are_cusps
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (x : X1Point p) :
    IsCusp x
```

or, preferably for the current repo:

```lean
axiom no_rational_point_of_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p)
    (P : (E⧸ℚ).Point)
    (hP : addOrderOf P = p) :
    False
```

---

## References / facts used

* Genus formula for prime-level `X_1(p)`: `g = (p - 5)(p - 7)/24` for prime `p ≥ 5`.
* Mazur isogeny theorem prime-degree list: `{2,3,5,7,11,13,17,19,37,43,67,163}`.
* `X_0(17)` and `X_0(19)` are genus 1 but classify rational cyclic subgroups/isogenies, not rational torsion generators; hence they do not supply an A4-style torsion contradiction.
