# Q2902 dm-codex2: audit of `N12FourSquaresAP.lean`

Repo target: `xiangyazi24/FLT`, local file under audit: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.

I could not fetch `N12FourSquaresAP.lean` or the named declarations from the canonical GitHub branch through the connector, so this is a design/math audit based on the route and declaration names in the prompt rather than a line-by-line local read.

## Executive audit result

Assuming the local single-file check really has no `axiom`, `sorry`, or imported theorem equivalent to the final AP theorem, the route is mathematically plausible and is the right architecture for the N=12 residual:

```text
integer 4-square AP
  -> primitive centered 4-square AP
  -> EulerSquarePair
  -> smaller EulerSquarePair
  -> primitive centered 4-square AP
  -> infinite descent
  -> no nonconstant integer/rational 4-square AP
```

The highest-risk points are not Lean syntax; they are normalization and descent-measure correctness:

1. arbitrary integer AP -> centered primitive AP may secretly require parity/divisibility facts;
2. `PrimitiveCenteredFourSqAP` may be too strong or accidentally vacuous;
3. `EulerSquarePair` may encode an orientation/sign convention that is not preserved by the two bridge maps;
4. the descent metric may fail to be strictly smaller after `natAbs`/sign normalization;
5. the final infinite-descent theorem may only rule out primitive centered AP, while the rational/integer theorem needs nonconstant preservation through denominator clearing and primitive normalization.

I do not see a mathematical reason the route must fail, but these are the exact places where a checked-looking development can accidentally prove a vacuous intermediate or a weaker final theorem.

## Prioritized checklist

### P0. Import/circularity audit

Inspect the imports and namespace around the final theorem first.

Must verify:

```text
fourRatSquaresAPConst_checked
  does not import/use
    fourRatSquaresAPConst_checked
    fourIntSquaresAPConst_checked
    primitiveCenteredFourSqAPDescent_checked
    or any assumption theorem equivalent to no four-square AP
  except through the intended local descent chain.
```

Concrete checks:

```bash
rg "axiom|constant|opaque|unsafe|sorry|admit" FLT/Assumptions/MazurProof/N12FourSquaresAP.lean
rg "fourRatSquaresAPConst_checked|fourIntSquaresAPConst_checked|PrimitiveCenteredFourSqAP" FLT/Assumptions/MazurProof -n
lake env lean FLT/Assumptions/MazurProof/N12FourSquaresAP.lean
```

Counter-risk: a helper with a harmless name like `EulerSquarePair.noInfiniteDescent` or `fourSquaresAP_classical` may already contain the final result. If that helper is imported, the local descent proof is not an independent residual closure.

### P1. `PrimitiveCenteredFourSqAP` is non-vacuous and has the right nonconstant field

Inspect the definition directly.

Checklist:

* It must encode four integer squares in AP, not four arbitrary AP terms.
* It should include the nonconstant datum in a form equivalent to nonzero common difference or unequal square values.
* Its primitive condition should be on the square roots, not on the square values in a way that is too strong or too weak.
* It must not require impossible parity/sign conditions unless those are proved in the normalization theorem.
* It should permit the expected local shape after centering, up to reversal/sign changes.

Concrete theorem to inspect:

```lean
primitiveCenteredFourSqAPDescent_checked
```

Make sure its input is not already impossible because of an over-strong field in `PrimitiveCenteredFourSqAP`.

Counter-risk: if `PrimitiveCenteredFourSqAP` requires, for example, a positive root ordering incompatible with sign choices after centering, then `primitiveCenteredFourSqAPDescent_checked` is vacuous even though it compiles.

### P2. Arbitrary integer AP -> primitive centered AP preserves nonconstancy

Inspect the theorem that starts the chain from arbitrary integer four-square AP.

It should prove something like:

```lean
integerFourSqAP_nonconstant_to_primitiveCentered :
  FourIntSquaresAP a b c d -> Nonconstant ->
    ∃ P : PrimitiveCenteredFourSqAP, metric P > 0
```

Critical details:

* common denominator/primitive division must not divide by zero;
* if all four square values are equal, the theorem should not produce a nonconstant centered object;
* if the original AP has integer square values, any centering requiring halves or quarters must be justified by modular arithmetic of squares.

The dangerous parity point is that the center of four terms in AP is usually a half-integer:

```text
s0, s0+r, s0+2r, s0+3r
center = s0 + 3r/2
```

A centered integer model normally needs either a doubled-center formulation or a proof that the relevant doubled quantities are integral. If the file uses an undoubled center, inspect the mod-2/mod-4 lemma that justifies it.

Counter-risk: a proof may silently use integer division `/ 2` or `/ 4` and then prove identities only after truncation-specific simplification. The theorem still compiles but may represent a different object than the intended centered AP.

### P3. `primitiveCenteredToEulerSquarePair_constructive`

Inspect algebraic identities and sign/orientation.

Must verify:

* the constructed `EulerSquarePair` fields are not all zero;
* primitivity of the Euler pair follows from primitivity of the centered AP, not from a hidden stronger condition;
* every division by `2`, `gcd`, or a parity factor is justified by a divisibility lemma;
* the Euler equations match exactly the descent theorem’s expected orientation.

Recommended local strengthening:

```lean
theorem primitiveCenteredToEulerSquarePair_metric_pos
    (P : PrimitiveCenteredFourSqAP) :
    0 < eulerMetric (primitiveCenteredToEulerSquarePair_constructive P)
```

and, if the constructor returns an existential:

```lean
theorem primitiveCenteredToEulerSquarePair_constructive_nontrivial
    (P : PrimitiveCenteredFourSqAP) :
    ∃ E : EulerSquarePair,
      E = primitiveCenteredToEulerSquarePair_constructive P ∧
      0 < eulerMetric E
```

Counter-risk: sign reversal can turn the intended descent metric negative before `natAbs`; then a later theorem may compare the wrong natural measure.

### P4. `eulerSquarePairDescent_constructive`

This is the most important theorem to audit.

The theorem must expose, not merely imply internally:

```lean
∃ E' : EulerSquarePair,
  eulerMetric E' < eulerMetric E
```

where `eulerMetric : EulerSquarePair -> ℕ` is a well-founded natural-valued measure and `0 < eulerMetric E` is known for every nontrivial pair.

Inspect for these mistakes:

* strict `<` accidentally proved for an integer expression before `natAbs`, but the recursive/noetherian argument uses `natAbs` later;
* metric can become `0` for a valid nontrivial pair;
* descent map returns a pair equivalent to the original under sign or swap, so the strict inequality only holds because the metric was not invariant under that normalization;
* primitivity of the descended pair is lost or reproved using a false gcd claim;
* descent requires a hidden positivity/order condition not included in `EulerSquarePair`.

Recommended strengthening theorem:

```lean
theorem eulerSquarePairDescent_constructive_strict_metric
    (E : EulerSquarePair) :
    let E' := eulerSquarePairDescent_constructive E
    eulerMetric E' < eulerMetric E
```

If descent returns an existential:

```lean
theorem eulerSquarePairDescent_constructive_spec
    (E : EulerSquarePair) :
    ∃ E' : EulerSquarePair,
      eulerMetric E' < eulerMetric E ∧
      0 < eulerMetric E'
```

Counter-risk: many Euler descents prove a smaller positive integer such as a smaller hypotenuse or smaller sum. If the formal metric is instead one coordinate’s `natAbs`, a sign/swap convention can break the strict-decrease proof.

### P5. `eulerSquarePairToPrimitiveCentered`

This inverse bridge should not be used to hide any descent algebra. It should explicitly build a valid primitive centered AP from the descended Euler pair.

Inspect:

* it preserves nonconstancy;
* it produces a primitive centered object satisfying the same definition consumed by `primitiveCenteredToEulerSquarePair_constructive`;
* it does not require a choice of square root not justified by the Euler equations;
* signs of generated roots are irrelevant or explicitly normalized.

Recommended round-trip sanity theorem:

```lean
theorem euler_to_centered_to_euler_metric_control
    (E : EulerSquarePair) :
    eulerMetric (primitiveCenteredToEulerSquarePair_constructive
      (eulerSquarePairToPrimitiveCentered E)) <= eulerMetric E
```

If exact round-trip is too strong, metric control plus validity is enough.

Counter-risk: the inverse construction may produce a centered AP that corresponds to a sign-reversed or swapped Euler pair. That is fine only if the next descent metric is invariant or controlled under that symmetry.

### P6. `primitiveCenteredFourSqAPDescent_checked`

This theorem should combine P3-P5 into a genuine descent on primitive centered AP.

Expected shape:

```lean
theorem primitiveCenteredFourSqAPDescent_checked
    (P : PrimitiveCenteredFourSqAP) :
    ∃ P' : PrimitiveCenteredFourSqAP,
      centeredMetric P' < centeredMetric P
```

or a contradiction by well-founded descent.

Inspect exactly which metric it uses. If it uses an Euler metric of the associated pair, then the statement should expose that metric and prove it is positive for every primitive centered AP.

Counter-risk: if `primitiveCenteredFourSqAPDescent_checked` returns a smaller Euler pair but not a smaller centered AP, the later infinite-descent theorem may be applying well-foundedness to the wrong sequence.

### P7. Final rational theorem `fourRatSquaresAPConst_checked`

Inspect clearing denominators:

For rationals `x0 x1 x2 x3`, if `x0^2, x1^2, x2^2, x3^2` are AP, choose a common nonzero denominator `D` and set integer roots

```text
A_i = D * x_i
```

Then `A_i^2` are integer squares in AP. The proof must show:

* `D ≠ 0`;
* each `A_i` is integer by construction;
* if the rational square AP is nonconstant, the integer square AP is nonconstant;
* if the integer result gives equal square values, division by `D^2` gives equal rational square values.

Counter-risk: nonconstancy of roots is not the same as nonconstancy of square values. For example `1` and `-1` have equal squares. The final theorem should state constancy of the four square values, not equality of the four rational roots, unless extra sign normalization is present.

## 2-3 small sanity theorems to add

These are deliberately small and should not require new mathematics. They increase confidence that the formal chain is not vacuous or metric-misaligned.

### Sanity theorem 1: primitive centered objects have positive metric

```lean
/-- A primitive centered nonconstant AP has positive descent measure. -/
theorem primitiveCenteredFourSqAP_metric_pos
    (P : PrimitiveCenteredFourSqAP) :
    0 < centeredMetric P := by
  -- Should unfold `centeredMetric` and use the nonconstant/common-difference field.
  -- If this is not provable, the metric is probably not the right descent measure.
  ...
```

If the file does not have `centeredMetric`, define one explicitly and use it in the descent theorem.

### Sanity theorem 2: Euler descent is strictly decreasing in the exported metric

```lean
/-- The constructive Euler descent strictly decreases the metric consumed by well-foundedness. -/
theorem eulerSquarePairDescent_metric_strict
    (E : EulerSquarePair) :
    eulerMetric (eulerSquarePairDescent_constructive E) < eulerMetric E := by
  -- This should be a direct projection from the descent theorem.
  -- If it requires substantial reproving, the descent theorem is underspecified.
  ...
```

If `eulerSquarePairDescent_constructive` returns an existential, use:

```lean
theorem eulerSquarePairDescent_exists_metric_strict
    (E : EulerSquarePair) :
    ∃ E' : EulerSquarePair,
      eulerMetric E' < eulerMetric E := by
  ...
```

### Sanity theorem 3: rational clearing preserves and reflects constant square values

```lean
/-- Denominator clearing does not change whether the four square values are constant. -/
theorem fourRatSquaresAP_clear_den_const_iff
    (x0 x1 x2 x3 : ℚ) :
    -- Replace `D`/integer roots by the local denominator-clearing construction.
    -- The intended statement is:
    -- integer cleared squares are constant ↔ rational square values are constant.
    True := by
  trivial
```

In real local terms, the theorem should say: after constructing integer roots `A_i = D*x_i`,

```lean
A0 ^ 2 = A1 ^ 2 ∧ A1 ^ 2 = A2 ^ 2 ∧ A2 ^ 2 = A3 ^ 2
  ↔
x0 ^ 2 = x1 ^ 2 ∧ x1 ^ 2 = x2 ^ 2 ∧ x2 ^ 2 = x3 ^ 2
```

using `D ≠ 0`. This catches the common final-step error of proving equality of roots rather than equality of square values.

## Concrete likely flaw to look for first

The most likely real bug class is **descent metric mismatch**:

```text
primitiveCenteredToEulerSquarePair_constructive P = E
Euler descent gives E' with eulerMetric E' < eulerMetric E
EulerSquarePairToPrimitiveCentered E' = P'
```

This does not automatically imply

```text
centeredMetric P' < centeredMetric P
```

unless the file proves that `centeredMetric` is exactly the Euler metric after conversion, or that the conversions preserve/control the chosen metric.

If `primitiveCenteredFourSqAPDescent_checked` is stated only as a contradiction and hides the metric comparison, strengthen it to expose the metric. The audit question I would answer from the file is:

```text
Which natural number does well-founded induction descend on, and where is strict decrease for that exact natural number proved after all conversions and normalizations?
```

If that exact theorem is absent, add it before trusting the final rational AP theorem.

## Minimal confidence checklist before using this residual downstream

Before treating `fourRatSquaresAPConst_checked` as a stable residual closure for N=12, confirm these facts by direct `#check`/inspection:

```lean
#check PrimitiveCenteredFourSqAP
#check EulerSquarePair
#check primitiveCenteredToEulerSquarePair_constructive
#check eulerSquarePairDescent_constructive
#check eulerSquarePairToPrimitiveCentered
#check primitiveCenteredFourSqAPDescent_checked
#check fourRatSquaresAPConst_checked
```

Then verify the exported theorem statements include, or are backed by, these exact ingredients:

```text
1. nonconstant integer AP -> exists primitive centered AP with positive metric;
2. primitive centered AP -> EulerSquarePair with positive metric;
3. EulerSquarePair -> smaller EulerSquarePair for the same metric used in induction;
4. smaller EulerSquarePair -> primitive centered AP without losing validity/nonconstancy;
5. rational denominator clearing preserves nonconstant square-value AP.
```

If all five are present as checked theorems, I would rate the formalization design as sound. If any of (1), (3), or (5) is only implicit inside a large proof, those are the first places to factor out small sanity theorems.
