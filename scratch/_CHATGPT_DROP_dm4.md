# Q1174 (dm4): Alternative B-line via reduction mod primes

## Executive answer

No: the proposed reduction-mod-primes route is **not** shorter than the real torsion bound route for the theorem currently needed in `Axioms.lean`.

It is a valid local obstruction in the following form:

```text
if E has good reduction at ℓ, ℓ ∤ m, and #E(F_ℓ) < m²,
then (Z/mZ)² cannot inject into E(Q).
```

But Hasse plus “there exists some good reduction prime” does **not** imply such an `ℓ` exists.  The first usable good reduction prime can be arbitrarily large for a general rational Weierstrass curve, and Hasse at a large prime only gives

```text
m² ≤ #E(F_ℓ) ≤ (sqrt ℓ + 1)²,
```

which is too weak.

So the B-line would need a new hard theorem of the form:

```text
for every E/Q and every m ≥ 3, there is a good prime ℓ ∤ m
such that #E(F_ℓ) < m².
```

That theorem is essentially another formulation of the same torsion obstruction.  It is not a consequence of elementary good-reduction existence plus Hasse.  In particular, it would not be a smaller axiom than Route 4B.

My recommendation: keep the Route 4B real torsion bound architecture.  Do **not** replace it by the reduction-mod-primes route unless you are willing to add a stronger reduction obstruction axiom, in which case the axiom is not obviously simpler than `real_mTorsion_card_le`.

## Why the simple Hasse argument fails

Assume full rational `m`-torsion:

```text
(Z/mZ)² ↪ E(Q).
```

At a prime `ℓ` of good reduction with `ℓ ∤ m`, the specialization theorem should give an injection

```text
(Z/mZ)² ↪ E(F_ℓ).
```

Thus

```text
m² ≤ #E(F_ℓ).
```

Hasse gives

```text
#E(F_ℓ) ≤ ℓ + 1 + 2 sqrt ℓ = (sqrt ℓ + 1)².
```

Therefore

```text
m ≤ sqrt ℓ + 1.
```

This only bounds `m` in terms of the chosen good prime `ℓ`.  For a general elliptic curve over `Q`, the first good prime not dividing `m` may be much larger than `m²`.  Finite bad reduction says only that some good primes exist; it gives no uniform small good prime.

For small primes:

```text
ℓ = 5:  #E(F_5) ≤ 10, so m² ≤ 10 gives m ≤ 3.
ℓ = 7:  #E(F_7) ≤ 12, so m² ≤ 12 gives m ≤ 3.
```

This still does not rule out `m = 3`.  Also, `E` can have bad reduction at `5` and `7`.  The same issue occurs for `ℓ = 2,3`, and if `ℓ | m`, the prime-to-`ℓ` specialization injection does not apply to the full `m`-torsion.

So the Hasse-bound line proves only this conditional theorem:

```text
small good prime with #E(F_ℓ) < m²
  ⇒ no full rational m-torsion.
```

It does not prove the global theorem:

```text
m ≥ 3 ⇒ no full rational m-torsion.
```

## What Mathlib/FLT currently has

From the FLT repo side, the visible elliptic torsion infrastructure is still centered around `FLT.EllipticCurve.Torsion`.  It defines

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and contains placeholder/sorried geometric torsion facts such as finiteness and cardinality over separably closed fields.  I did not find a ready FLT-local API for:

```text
* good reduction of a rational Weierstrass curve at a prime;
* the reduced curve E/F_ℓ as an elliptic curve with point group;
* the reduction map E(Q) → E(F_ℓ);
* injectivity on prime-to-ℓ torsion;
* Hasse's bound for #E(F_ℓ).
```

As for Mathlib: at the project’s pinned revision, this is not a ready-to-wire stack.  Mathlib has general algebraic geometry, finite fields, and Weierstrass curves, but the complete arithmetic package needed here — integral models/good reduction, specialization of torsion, and Hasse bound for elliptic curves over finite fields — is not available as a small import-and-apply API.

Even if all of those APIs existed, the mathematical obstruction above remains: Hasse plus existence of some good prime is too weak to prove `m ≤ 2`.

## Important correction: Néron-Ogg-Shafarevich is overkill for existence of good primes

For a fixed rational Weierstrass equation, one does not need Néron-Ogg-Shafarevich merely to know that there are good reduction primes.  After clearing denominators, all but finitely many primes avoid the discriminant and give good reduction of that model.

Néron-Ogg-Shafarevich is about characterizing good reduction in terms of the ℓ-adic representation.  It is much stronger than needed for “bad primes are finite”.

But the B-line needs more than finite good reduction.  It needs a prime of good reduction that is small enough, or a theorem producing a cardinality obstruction.  That is the missing hard part.

## The valid local reduction obstruction

The following is the precise mathematical lemma that the B-line can use.

```text
Given:
  * good reduction at ℓ;
  * ℓ ∤ m;
  * reduction injects m-torsion E(Q)[m] ↪ E(F_ℓ);
  * #E(F_ℓ) < m²;
  * full rational m-torsion (Z/mZ)² ↪ E(Q),

contradiction.
```

Here is a Lean-level cardinality skeleton independent of the missing elliptic APIs.

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/--
Pure cardinality core of the reduction-mod-prime obstruction.

This is the only easy part of the B-line.  The hard elliptic-curve input is
hidden in `hred_inj`, namely the existence of an injection from `(ZMod m)^2`
into the finite reduced point group.
-/
theorem contradiction_of_reduction_card_lt_sq
    {G : Type*} [Fintype G]
    {m : ℕ} (hm : 0 < m)
    (hred_card : Fintype.card G < m * m)
    (hred_inj : ∃ g : ZMod m × ZMod m → G, Function.Injective g) :
    False := by
  rcases hred_inj with ⟨g, hg⟩
  have hdom : Fintype.card (ZMod m × ZMod m) = m * m := by
    -- Usually solved by `simp [Fintype.card_prod]` at current Mathlib.
    -- The positivity hypothesis avoids the pathological `ZMod 0` edge case.
    simp [Fintype.card_prod]
  have hle : m * m ≤ Fintype.card G := by
    rw [← hdom]
    exact Fintype.card_le_of_injective g hg
  exact not_lt_of_ge hle hred_card

end ReductionModPrimeRoute

end FLT
```

If the reduced point group is represented by `Nat.card` rather than `Fintype.card`, the same proof becomes:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/-- Same cardinality obstruction, phrased with `Nat.card`. -/
theorem contradiction_of_reduction_natCard_lt_sq
    {G : Type*} [Finite G]
    {m : ℕ} (hm : 0 < m)
    (hred_card : Nat.card G < m * m)
    (hred_inj : ∃ g : ZMod m × ZMod m → G, Function.Injective g) :
    False := by
  rcases hred_inj with ⟨g, hg⟩
  have hdom : Nat.card (ZMod m × ZMod m) = m * m := by
    -- Depending on the local Mathlib simp set, this may need the explicit theorem
    -- for `Nat.card (ZMod m)` plus `Nat.card_prod`.
    simp [Nat.card_prod]
  have hle : m * m ≤ Nat.card G := by
    rw [← hdom]
    exact Nat.card_le_card_of_injective g hg
  exact not_lt_of_ge hle hred_card

end ReductionModPrimeRoute

end FLT
```

The proof is tiny.  The problem is obtaining `hred_inj` and `hred_card` uniformly.

## The missing B-line API, if you want to pursue it anyway

A realistic B-line file would need definitions or axioms like this.

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/-- Placeholder predicate: `E` has good reduction at the rational prime `ℓ`. -/
axiom GoodReductionAt
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) : Prop

/-- Placeholder for the finite point group of the reduced curve over `F_ℓ`. -/
axiom ReducedPointGroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) : Type

axiom reducedPointGroup_fintype
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) :
    Fintype (ReducedPointGroup E ℓ)

/--
Specialization of full rational `m`-torsion into the reduced finite group.
This requires good reduction and `ℓ ∤ m`.
-/
axiom fullTorsion_specializes_injectively
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m ℓ : ℕ}
    (hm : 0 < m) (hℓprime : ℓ.Prime)
    (hgood : GoodReductionAt E ℓ) (hℓ_not_dvd_m : ¬ ℓ ∣ m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ g : ZMod m × ZMod m → ReducedPointGroup E ℓ,
      Function.Injective g

/-- Hasse/cardinality consequence strong enough to contradict full `m`-torsion. -/
axiom reduced_card_lt_sq
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m ℓ : ℕ}
    (hm3 : 3 ≤ m) (hℓprime : ℓ.Prime)
    (hgood : GoodReductionAt E ℓ) :
    Fintype.card (ReducedPointGroup E ℓ) < m * m

end ReductionModPrimeRoute

end FLT
```

But note that `reduced_card_lt_sq` is not a consequence of Hasse for an arbitrary good `ℓ`; it requires `ℓ` to be small relative to `m`, or it must be replaced by an existential theorem producing such an `ℓ`.

The honest global B-line axiom would therefore be this:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/--
The genuinely hard global B-line input.

This says that for any alleged full rational `m`-torsion with `m ≥ 3`, there is
a good prime of reduction whose finite reduced point group is too small to
contain `(ZMod m)^2`.

This is not supplied by Hasse plus finite bad reduction.
-/
axiom exists_small_good_reduction_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm3 : 3 ≤ m) :
    ∃ ℓ : ℕ,
      ℓ.Prime ∧
      GoodReductionAt E ℓ ∧
      ¬ ℓ ∣ m ∧
      Fintype.card (ReducedPointGroup E ℓ) < m * m

end ReductionModPrimeRoute

end FLT
```

With that strong axiom, the route is short:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/--
If the B-line obstruction axiom is available, full rational `m`-torsion is
impossible for `m ≥ 3`.
-/
theorem not_hasFullRationalTorsion_of_three_le_routeB
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_pos : 0 < m := lt_of_lt_of_le (by norm_num : 0 < 3) hm3
  rcases exists_small_good_reduction_obstruction (E := E) (m := m) hm3 with
    ⟨ℓ, hℓprime, hgood, hℓ_not_dvd_m, hcard_lt⟩
  letI : Fintype (ReducedPointGroup E ℓ) :=
    reducedPointGroup_fintype E ℓ
  have hred_inj :
      ∃ g : ZMod m × ZMod m → ReducedPointGroup E ℓ,
        Function.Injective g :=
    fullTorsion_specializes_injectively
      (E := E) (m := m) (ℓ := ℓ)
      hm_pos hℓprime hgood hℓ_not_dvd_m hfull
  exact contradiction_of_reduction_card_lt_sq
    (G := ReducedPointGroup E ℓ) (m := m) hm_pos hcard_lt hred_inj

end ReductionModPrimeRoute

end FLT
```

This is structurally parallel to Route 4B:

```text
Route 4B hard input:
  #E(R)[m] ≤ 2m

B-line hard input:
  ∃ good ℓ ∤ m with #E(F_ℓ) < m²
  + reduction injectivity on m-torsion
```

The B-line hard input is not obviously easier.

## Why the B-line does not replace Route 4B in `Axioms.lean`

For the `Axioms.lean` dependency chain, we need:

```lean
HasFullRationalTorsion E m → m ≤ 2
```

or at least:

```lean
3 ≤ m → ¬ HasFullRationalTorsion E m.
```

Route 4B supplies exactly this from two real-torsion axioms:

```text
real_mTorsion_finite
real_mTorsion_card_le
```

The B-line does not supply it from currently available general facts.  It supplies it only after adding a stronger global reduction obstruction axiom.

Thus, replacing Route 4B by B-line would change the axiom footprint from:

```text
real_mTorsion_finite
real_mTorsion_card_le
```

to something like:

```text
good reduction / reduced curve API
specialization injectivity on prime-to-ℓ torsion
Hasse bound
existence of a good ℓ ∤ m with #E(F_ℓ) < m²
```

The last item is the real blocker.  Without it, the route cannot close.

## What `Axioms.lean` should do

Keep the current Route 4B replacement:

```lean
have hm_le_two : m ≤ 2 :=
  RealTorsionBound.fullRationalTorsion_order_le_two_route4B
    (E := E) (m := m) hm_pos hfull
```

and use it to prove:

```lean
not_hasFullRationalTorsion_of_three_le
no_odd_prime_square_in_torsion
```

Do **not** introduce the B-line into `Axioms.lean` unless a separate file has already provided a theorem of the exact form:

```lean
theorem fullRationalTorsion_order_le_two_routeB
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    m ≤ 2
```

If that theorem exists, the `Axioms.lean` replacement body is identical to the Route 4B body with only the theorem name changed:

```lean
have hm_le_two : m ≤ 2 :=
  ReductionModPrimeRoute.fullRationalTorsion_order_le_two_routeB
    (E := E) (m := m) hm_pos hfull
omega
```

But proving `fullRationalTorsion_order_le_two_routeB` is not shorter than proving the real torsion bound route.

## Final recommendation

Use reduction mod primes only as a diagnostic/local obstruction or as a future optional route.  It is not the right replacement for the current `Axioms.lean` refactor.

For the immediate architecture:

```text
Keep Route 4B:
  real_mTorsion_finite
  real_mTorsion_card_le
    ⇒ fullRationalTorsion_order_le_two_route4B
    ⇒ not_hasFullRationalTorsion_of_three_le
    ⇒ no_odd_prime_square_in_torsion
```

Do not add a B-line unless you are willing to add a new hard axiom that already packages the small-good-prime/cardinality obstruction.  Hasse plus finite bad reduction alone is insufficient.
