# Q1183 (dm4): reduction mod primes for `fullRationalTorsion_order_le_two`

## Executive answer

For the general theorem

```lean
fullRationalTorsion_order_le_two :
  HasFullRationalTorsion E m → m ≤ 2
```

the reduction-mod-primes route is **not concretely shorter** than the real-topology Route 4B.

The reduction idea gives a valid **conditional obstruction**:

```text
if E has good reduction at ℓ,
if ℓ ∤ m,
if reduction is injective on m-torsion,
and if #E(F_ℓ) < m²,
then full rational m-torsion is impossible.
```

But it does not give the global theorem from Hasse alone.  The `m = 3` case is the first visible failure, but the real problem is broader: for a general elliptic curve over `Q`, there is no uniform small good prime available from elementary good-reduction existence.  The bad reduction set is finite, but it can contain any prescribed finite set of small primes, so fixed small primes cannot be used uniformly.

So the honest feasibility comparison is:

```text
Route 4B real topology:
  hard input = #E(R)[m] ≤ 2m.
  After that, the desired theorem is a direct cardinality argument.

Reduction mod primes:
  hard inputs = good reduction API
              + reduction map on points/torsion
              + injectivity on prime-to-ℓ torsion
              + Hasse bound
              + an additional theorem producing a good prime ℓ with a useful
                cardinality/divisibility obstruction.
```

The last item is not supplied by Hasse plus “bad primes are finite”.  Without it, the route cannot close.

## The `m = 3` obstruction

You correctly identified the issue.

For full rational `m`-torsion, reduction at a good prime `ℓ ∤ m` would give

```text
m² | #E(F_ℓ)
```

and hence

```text
m² ≤ #E(F_ℓ) ≤ (sqrt ℓ + 1)².
```

For `m = 3`, Hasse alone would need

```text
(sqrt ℓ + 1)² < 9,
```

so `ℓ < 4`; only `ℓ = 2, 3` are relevant, and these may be bad reduction or divide `m`.

Using small odd primes does not fix this:

```text
ℓ = 5: #E(F_5) can lie between 2 and 10; # = 9 is Hasse-allowed.
ℓ = 7: #E(F_7) can lie between 4 and 12; # = 9 is Hasse-allowed.
```

Thus Hasse does not rule out a subgroup `(Z/3Z)²` at `ℓ = 5` or `ℓ = 7` by cardinality alone.

There is a stronger finite-field fact:

```text
if E(F_q) contains full m-torsion and gcd(m,q)=1,
then m | q - 1.
```

This would immediately rule out full `3`-torsion over `F_5`, since `3 ∤ 4`.  But this fact is essentially the finite-field Weil-pairing/determinant argument.  If the point of Route B is to avoid Weil pairing/cyclotomic arguments, this reintroduces the same mathematics in a finite-field wrapper.

For `ℓ = 7`, even `3 | 7 - 1`, and Hasse still permits `#E(F_7) = 9`.  So one would then need to choose primes in other congruence classes and prove there is a good one.  That needs a Dirichlet/Chebotarev-style existence theorem plus the finite-field torsion structure theorem.  This is not shorter than Route 4B.

## Larger `m` does not solve the global problem

For `m = 5`, a good prime `ℓ < 16` and `ℓ ∤ 5` with Hasse bound would rule out full `5`-torsion by cardinality.  Candidates include `7, 11, 13`.

For `m = 7`, a good prime `ℓ < 36` and `ℓ ∤ 7` would suffice, and there are many candidates.

But for a **general** rational elliptic curve, there is no guarantee that one of those small candidate primes is good.  A rational Weierstrass model can have bad reduction at a prescribed finite set of primes after arranging the discriminant to be divisible by those primes.  Finite bad reduction says there are good primes eventually; it does not say there is one below `(m - 1)^2`.

Therefore, Hasse gives this theorem:

```text
small good prime below (m - 1)^2
  ⇒ no full rational m-torsion.
```

It does not give:

```text
m ≥ 3 ⇒ no full rational m-torsion.
```

That is the gap.

## What exists in the current FLT/Mathlib environment?

I checked the FLT repository through the GitHub connector.  The visible elliptic torsion file is `FLT.EllipticCurve.Torsion`, which defines

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and has placeholder/sorried facts such as:

```lean
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) :
    Finite (E.nTorsion n) := sorry

theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry
```

I did **not** find a ready FLT-local API for:

```text
1. good/bad reduction of rational elliptic curves;
2. reduction maps E(Q) → E(F_ℓ);
3. injectivity of reduction on prime-to-ℓ torsion;
4. Hasse bound for #E(F_ℓ).
```

My honest assessment for Mathlib at the pinned FLT revision is the same: there are many general ingredients in Mathlib — finite fields, Weierstrass curves, algebraic geometry, point groups — but not a ready end-to-end arithmetic-reduction stack that would make this route a short implementation.

So the answers to your three concrete API questions are:

```text
1. Good/bad reduction of elliptic curves?
   Not as a ready-to-use FLT-local API found here.  If Mathlib has fragments, they
   are not wired into this project’s torsion API.

2. Injection E(Q)[m] → E(F_ℓ) for good ℓ ∤ m?
   Not found as a ready theorem.  This would require integral models, reduction
   maps, formal group/kernel analysis, and prime-to-ℓ torsion specialization.

3. Hasse bound #E(F_ℓ) = ℓ + 1 - a_ℓ with |a_ℓ| ≤ 2√ℓ?
   Not found as a ready theorem in the FLT-facing API.  Even if available, it
   would not close the global `m ≤ 2` theorem without a small-good-prime or
   finite-field-structure theorem.
```

## What the reduction route can prove immediately, assuming the missing APIs

The easy part is pure cardinality.  Here is the reusable Lean skeleton.

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/--
Pure cardinality obstruction.

If `(ZMod m)^2` injects into a finite reduced point group `G`, then `G` must
have at least `m^2` elements.  So any bound `#G < m^2` gives a contradiction.
-/
theorem contradiction_of_reduction_card_lt_sq
    {G : Type*} [Fintype G]
    {m : ℕ} (hm : 0 < m)
    (hred_card : Fintype.card G < m * m)
    (hred_inj : ∃ g : ZMod m × ZMod m → G, Function.Injective g) :
    False := by
  rcases hred_inj with ⟨g, hg⟩
  have hdom : Fintype.card (ZMod m × ZMod m) = m * m := by
    simp [Fintype.card_prod]
  have hle : m * m ≤ Fintype.card G := by
    rw [← hdom]
    exact Fintype.card_le_of_injective g hg
  exact not_lt_of_ge hle hred_card

end ReductionModPrimeRoute

end FLT
```

The same proof can be written with `Nat.card` if the reduced point group is packaged as a `Finite` type rather than a `Fintype` type:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/-- `Nat.card` version of the same pure cardinality obstruction. -/
theorem contradiction_of_reduction_natCard_lt_sq
    {G : Type*} [Finite G]
    {m : ℕ} (hm : 0 < m)
    (hred_card : Nat.card G < m * m)
    (hred_inj : ∃ g : ZMod m × ZMod m → G, Function.Injective g) :
    False := by
  rcases hred_inj with ⟨g, hg⟩
  have hdom : Nat.card (ZMod m × ZMod m) = m * m := by
    simp [Nat.card_prod]
  have hle : m * m ≤ Nat.card G := by
    rw [← hdom]
    exact Nat.card_le_card_of_injective g hg
  exact not_lt_of_ge hle hred_card

end ReductionModPrimeRoute

end FLT
```

This is not the hard part.  The hard part is producing `hred_inj` and a useful `hred_card` for some good prime.

## Minimal B-line API if pursued anyway

If you want to package the reduction route as a theorem, the honest interface should look like this.

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/-- Placeholder: `E` has good reduction at the rational prime `ℓ`. -/
axiom GoodReductionAt
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) : Prop

/-- Placeholder for the finite point group of the reduced curve over `F_ℓ`. -/
axiom ReducedPointGroup
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) : Type

axiom reducedPointGroup_fintype
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (ℓ : ℕ) :
    Fintype (ReducedPointGroup E ℓ)

/-- Specialization injectivity on prime-to-`ℓ` torsion. -/
axiom fullTorsion_specializes_injectively
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m ℓ : ℕ}
    (hm : 0 < m) (hℓprime : ℓ.Prime)
    (hgood : GoodReductionAt E ℓ) (hℓ_not_dvd_m : ¬ ℓ ∣ m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ g : ZMod m × ZMod m → ReducedPointGroup E ℓ,
      Function.Injective g

/--
A useful reduction obstruction.  This is stronger than Hasse alone unless `ℓ`
is already known to be small relative to `m`.
-/
axiom exists_good_reduction_card_lt_sq
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm3 : 3 ≤ m) :
    ∃ ℓ : ℕ,
      ℓ.Prime ∧
      GoodReductionAt E ℓ ∧
      ¬ ℓ ∣ m ∧
      Fintype.card (ReducedPointGroup E ℓ) < m * m

/--
If the strong B-line obstruction is available, it gives the desired no-full-torsion theorem.
-/
theorem not_hasFullRationalTorsion_of_three_le_routeB
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m := by
  intro hfull
  have hm_pos : 0 < m := by omega
  rcases exists_good_reduction_card_lt_sq (E := E) (m := m) hm3 with
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

But notice what happened: the route only becomes short after adding the strong axiom

```lean
exists_good_reduction_card_lt_sq
```

which is exactly the missing global content.  Hasse alone does not prove this axiom.

## If one tries to handle `m = 3` separately

There are three possible “special `m = 3`” ideas.

### 1. Hasse only

This fails.  Hasse allows `#E(F_5) = 9` and `#E(F_7) = 9`.

### 2. Finite-field full torsion implies `m | ℓ - 1`

This can rule out full `3`-torsion over `F_5`, and over any `F_ℓ` with `ℓ ≠ 1 mod 3`.

But this theorem is Weil-pairing/determinant content over finite fields.  It is not a Hasse-bound argument anymore.

The interface would be:

```lean
import Mathlib

open scoped Classical

noncomputable section

namespace FLT

namespace ReductionModPrimeRoute

/-- Finite-field structure obstruction, essentially Weil-pairing content. -/
axiom full_torsion_over_finite_field_implies_dvd_card_units
    {q m : ℕ}
    (hm : 0 < m) (hq_coprime : Nat.Coprime m q)
    -- if `(ZMod m)^2` embeds into `E(F_q)`
    : True
    -- intended conclusion: `m ∣ q - 1`

end ReductionModPrimeRoute

end FLT
```

This is not attractive if the purpose is to remove the Weil pairing route.

### 3. Choose a good prime in a useful congruence class

For `m = 3`, one would like a good prime `ℓ ≡ 2 mod 3`.  Since the bad primes are finite, such primes exist by Dirichlet.  But formalizing this requires:

```text
finite bad reduction set
+ Dirichlet primes in arithmetic progressions
+ finite-field full-torsion structure theorem
```

Again, this is not shorter than Route 4B.

## Comparison with Route 4B

### Route 4B

Current Route 4B assumes:

```lean
real_mTorsion_finite
real_mTorsion_card_le
```

and proves, sorry-free after those axioms:

```lean
fullRationalTorsion_order_le_two_route4B :
  HasFullRationalTorsion E m → m ≤ 2
```

The proof is a direct cardinality comparison:

```text
(Z/mZ)² ↪ E(Q) ↪ E(R)[m]
#(Z/mZ)² = m²
#E(R)[m] ≤ 2m
therefore m² ≤ 2m, hence m ≤ 2.
```

### Reduction route

The reduction route requires at least:

```text
1. integral/good-reduction model API;
2. reduced curve over F_ℓ and finite point group;
3. reduction map E(Q) → E(F_ℓ);
4. injectivity on prime-to-ℓ torsion;
5. Hasse bound;
6. additional global theorem finding a good ℓ with #E(F_ℓ) < m²,
   or finite-field full-torsion structure + Dirichlet/Chebotarev.
```

This is strictly more infrastructure than Route 4B for the present target.

## Final recommendation

Do not use reduction mod primes as the main replacement for `fullRationalTorsion_order_le_two`.

The B-line is a good **local obstruction** and may be useful later for explicit curves or finite computations, but for the general theorem needed by `Axioms.lean`, it is not a feasible shorter path.

Keep the Route 4B chain:

```text
real_mTorsion_finite
real_mTorsion_card_le
  ⇒ fullRationalTorsion_order_le_two_route4B
  ⇒ not_hasFullRationalTorsion_of_three_le
  ⇒ no_odd_prime_square_in_torsion
```

If someone wants a reduction-based alternative later, make it a separate theorem:

```lean
ReductionModPrimeRoute.fullRationalTorsion_order_le_two_routeB
```

and require it to package the strong global good-prime obstruction.  Until that theorem exists, `Axioms.lean` should not depend on the reduction route.
