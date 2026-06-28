# Q2076 (dm2): Hasse-only shortcut for full rational torsion?

Date: 2026-06-28.

Question: can we avoid the Weil pairing in Mazur's torsion theorem by arguing as follows?

```text
If E/ℚ has E[m](ℚ) = (ℤ/mℤ)^2, then for every good prime p,
m^2 ∣ #E(𝔽_p).
For p = 2, Hasse gives #E(𝔽_2) ≤ 3 + 2√2 < 6,
so m^2 ≤ 5 and m ≤ 2.
```

## Verdict

This shortcut is **not correct as stated**.

The divisibility step needs a prime-to-`p` injectivity theorem for reduction of torsion.  The correct statement is:

```text
If E has good reduction at p and p ∤ m,
then the reduction map E(ℚ)[m] → E(𝔽_p) is injective.
```

Therefore full rational `m`-torsion gives

```text
m^2 ∣ #E(𝔽_p)
```

only for good primes `p` with `p ∤ m`.

So the proposed `p = 2` argument:

* does **not** apply to even `m`, because then `2 ∣ m`;
* does **not** apply to a curve with bad reduction at `2`;
* for odd `m`, works only under the extra hypothesis that `E` has good reduction at `2`.

Thus it is not a uniform replacement for the Weil-pairing argument.

## (1) Is `E[m](ℚ) = (ℤ/m)^2 ⇒ m^2 ∣ #E(𝔽_p)` correct?

Yes, but only with the missing hypotheses:

```text
p is a good-reduction prime for E,
p ∤ m,
and the reduction map is a group homomorphism that is injective on m-torsion.
```

The formal argument is:

```text
E[m](ℚ) ≅ (ℤ/mℤ)^2
  ⇒ #E[m](ℚ) = m^2.

If reduction is injective on E[m](ℚ), then E(𝔽_p) contains a subgroup
of cardinality m^2.

By Lagrange, m^2 ∣ #E(𝔽_p).
```

The infrastructure required is substantial:

1. A local good-reduction setup at `p`, usually via a DVR/residue field model.
2. A reduction map on points

   ```lean
   red_p : E(ℚ_p) → Ẽ(𝔽_p)
   ```

   or a global-to-local version for rational points.
3. Proof that `red_p` is a group homomorphism.
4. Proof that the kernel has no torsion of order prime to `p`, hence injectivity on `m`-torsion when `p ∤ m`.
5. A finite-subgroup/Lagrange step giving `m^2 ∣ Nat.card Ẽ(𝔽_p)`.

The false part of the proposed statement is the phrase **for every good prime `p`**.  It should be **for every good prime `p` not dividing `m`**.

## Why `p = 2` is not enough

Hasse at `p = 2` says:

```text
#E(𝔽_2) ≤ 2 + 1 + 2√2 < 6,
```

hence, since the point count is an integer,

```text
#E(𝔽_2) ≤ 5.
```

If `E` has good reduction at `2` and `m` is odd, injectivity gives

```text
m^2 ∣ #E(𝔽_2),
```

so `m^2 ≤ 5`, hence `m ≤ 2`.

But this cannot rule out the even cases

```text
m = 4, 6, 8, 10, 12,
```

because the required prime-to-`p` condition fails at `p = 2`.  It also cannot rule out an odd `m` curve whose reduction at `2` is bad.

The correct Hasse-only conditional lemma is:

```text
If full rational m-torsion holds and there exists a good prime p with
p ∤ m and p < (m - 1)^2, then contradiction.
```

Proof:

```text
m^2 ∣ #E(𝔽_p) ⇒ m^2 ≤ #E(𝔽_p).
Hasse: #E(𝔽_p) ≤ p + 1 + 2√p = (√p + 1)^2.
If p < (m - 1)^2, then (√p + 1)^2 < m^2.
Contradiction.
```

This is useful for a **specific curve** if a suitable small good prime is available.  It is not a uniform theorem over all elliptic curves over `ℚ` from Hasse alone, because a curve can have bad reduction at whichever small primes the argument wants to use.

## (2) Does Mathlib have the Hasse bound?

I did not find a packaged elliptic-curve Hasse bound in current Mathlib under the expected searches:

```text
Hasse
Hasse bound elliptic curve
HasseWeil elliptic finite field
WeierstrassCurve Hasse
```

What Mathlib **does** have is an L-function file defining the local polynomial.  In good reduction it uses the expected local coefficient

```lean
letI q : ℤ := Nat.card (IsLocalRing.ResidueField R)
letI a : ℤ := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2 else ...
```

So Mathlib has the point-count expression used to define `a_p` in the local Euler factor, but I did not find a theorem of the form

```lean
|a_p| ≤ 2 * Real.sqrt q
```

or an integer-square-root version of it.

For this shortcut, the Hasse bound would likely need to be added as a new theorem or carried as a hypothesis/axiom.

## (3) Does Mathlib have good reduction / reduction maps for EC?

Mathlib has **curve-level reduction infrastructure**, but I did not find the point-reduction map or prime-to-`p` torsion injectivity theorem needed for this shortcut.

The relevant file is:

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
```

It defines:

```lean
class IsIntegral (W : WeierstrassCurve K) : Prop
class IsMinimal (W : WeierstrassCurve K) : Prop
noncomputable def reduction (W : WeierstrassCurve K) [IsMinimal R W] :
  WeierstrassCurve (ResidueField R)
class HasGoodReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W
```

It also has the deprecated alias:

```lean
IsGoodReduction := HasGoodReduction
```

and the good-reduction/smooth-special-fiber bridge:

```lean
hasGoodReduction_iff_isElliptic_reduction :
  HasGoodReduction R W ↔ (W.reduction R).IsElliptic
```

What I did **not** find in Mathlib is a ready-made API like:

```lean
reductionMapPoint : W.PointOverLocalField → (W.reduction R).toAffine.Point
reductionMapPoint.map_add
reductionMapPoint.injective_on_prime_to_p_torsion
```

Searches for combinations of `reduction`, `Point`, `injective`, and torsion did not turn up this package.

So the infrastructure status is:

```text
available:      minimal/integral/good-reduction predicates and reduced curve;
available:      local Euler factor using #reduction points;
not found:      Hasse bound theorem;
not found:      point reduction map with group-hom API;
not found:      prime-to-p torsion injectivity of reduction.
```

## Lean-oriented theorem shape if pursuing this shortcut

The clean abstraction is to separate the missing arithmetic geometry from the finite-cardinality argument.

```lean
/-- Placeholder for the reduction-injectivity theorem at a good prime. -/
class PrimeToReductionInjectivity
    (E : Type*) [AddCommGroup E]
    (Ered : Type*) [AddCommGroup Ered]
    (m p : ℕ) : Prop where
  red : E →+ Ered
  injective_on_mtorsion :
    ∀ {P Q : E}, m • P = 0 → m • Q = 0 → red P = red Q → P = Q
```

Then the finite group step should be stated independently:

```lean
/-- If full m-torsion injects into a finite reduction group, then m^2 divides its order. -/
theorem m_square_dvd_card_reduction_of_full_torsion_injective
    {E Ered : Type*} [AddCommGroup E] [AddCommGroup Ered] [Fintype Ered]
    {m : ℕ}
    -- abstract full-torsion hypothesis, e.g. E[m] ≃ ZMod m × ZMod m
    (hfull : FullRationalMTorsion E m)
    (hinj : InjectiveOnMTorsion E Ered m) :
    m ^ 2 ∣ Fintype.card Ered := by
  -- group-theoretic/Lagrange proof
  sorry
```

And the Hasse contradiction should be conditional:

```lean
theorem no_full_mtorsion_of_good_prime_hasse
    {m p N : ℕ}
    (hdiv : m ^ 2 ∣ N)
    (hhasse : (N : ℝ) ≤ p + 1 + 2 * Real.sqrt p)
    (hsmall : p < (m - 1)^2) :
    False := by
  -- arithmetic inequality proof
  sorry
```

For a real Mazur formalization, however, this shortcut still needs exactly the kind of serious EC reduction infrastructure that Mathlib does not seem to expose yet.

## Recommendation

Do **not** replace the Weil-pairing step with the `p = 2` Hasse shortcut.

For the Mazur proof, the Weil-pairing obstruction remains the clean theorem:

```text
E[m](ℚ) ≅ (ℤ/mℤ)^2
  ⇒ μ_m ⊂ ℚ
  ⇒ m ≤ 2.
```

The Hasse route is valuable as a conditional/local lemma:

```text
full rational m-torsion + suitable good prime p ∤ m + Hasse bound
  ⇒ contradiction.
```

But it does not provide a uniform proof by taking `p = 2`, and Mathlib currently appears to lack the two main ingredients needed to formalize it directly: Hasse's bound and prime-to-`p` injectivity of the point-reduction map.
