# DOCTRINE — N13DirectEndpoint: Close 2 remaining sorry

## Main Goal

Prove `classify_injective` and `classify_abel` in N13DirectEndpoint.lean,
eliminating the last 2 sorry in the N13 endpoint and making the
rational-point theorem `n13_affine_x_is_cuspidal` unconditional.

## The 2 Sorry

### classify_injective (line 54)
```lean
theorem classify_injective : Function.Injective classify
```
Where `classify g = specialClass (exactSpreadLine g)`.

**Mathematical content:** The specialization map G → SpecialSet is injective.
G has 19 elements (rational Picard classes of J₁(13)).
SpecialSet has 19 elements (PicTwoSetModel = special Abel classes).
Both have cardinality 19, so injectivity = surjectivity = bijectivity.

**Route:** Since both sets have the same finite cardinality 19, injective ↔ surjective.
We need a surjectivity or injectivity argument. Options:
(a) Finite.injective_iff_surjective: show classify is surjective (every special class
    is hit by some rational class via exactSpreadLine).
(b) Direct: show if classify g₁ = classify g₂ then g₁ = g₂.
    Two spread lines with same specialClass → same Mumford data after normalization
    (normalize_eq_of_class) → same rationalClass.
(c) Use the existing trivialKernel_separated / NSeparated infrastructure: the kernel
    of the reduction map is trivial, hence the map is injective.

### classify_abel (line 61)
```lean
theorem classify_abel (P : RationalCurvePoint) :
    classify (rationalAbel P) = specialPointClass (reduceCurve P)
```

**Mathematical content:** The specialization of a rational curve point's
Abel class (via exactSpreadLine) agrees with the special Abel class of its
proper reduction.

**Route:** We know `pointSpreadLine P` satisfies this — its `special_eq`
says `toSpecialPic = specialPointClass (reduceCurve P)`. We also know
`exactSpreadLine (rationalAbel P)` has `rationalClass = rationalAbel P`.
Both spread lines have the same rationalClass. Need to show they have the
same specialClass. This requires showing that specialClass depends only
on the rationalClass, which is exactly what class_eq_iff says — but
class_eq_iff was declared unprovable for arbitrary SpreadLines.

However, for the EXACT spread lines used here (exactSpreadLine and
pointSpreadLine), both are constructed from the SAME normalized Mumford
representative (normalize_eq_of_class), so their realizations share the
same Mumford data, hence the same specialDivisor and specialClass.

## Avenues

### (a) classify_injective via Finite cardinality argument

Both G and SpecialSet have exactly 19 elements.
`classify : G → SpecialSet` between two Fin-19-equivalent types.
Prove surjectivity (every special class is in the image) or use
`Finite.injective_iff_surjective` to reduce injectivity to surjectivity.

Surjectivity route: For every s : SpecialSet, there exists a SpreadLine L
with specialClass L = s. The existing `exists_exactSpreadLine` gives a
spread for every G element. If classify is the composition
G →(exactSpreadLine) SpreadLine →(specialClass) SpecialSet,
and G has 19 elements and SpecialSet has 19 elements, then classify is
injective iff bijective.

Actually, the cardinality argument is: any injective function from a finite
set to a set of the same cardinality is bijective, and conversely any
surjective function from a finite set to a set of the same cardinality is
injective. So we could:
- Show classify is surjective → done (Finite.injective_iff_surjective)
- OR show |image classify| = 19

**Terminal:** Either prove surjectivity or find a counterexample showing
classify is not surjective (contradicting the mathematical content).

### (b) classify_injective via existing separation infrastructure

The existing `trivialKernel_separated` + `NSeparated` infrastructure
shows that the kernel of the reduction map is trivial. The reduction map
goes G → G/ker → SpecialSet. If ker = ⊥ (trivial), then G ≅ G/ker → SpecialSet
is injective.

Need to connect `classify` to the existing reduction framework. The
`reductionData` constructor builds a `CompatibleReduction` from spread data
+ class_eq_iff. But we're trying to avoid class_eq_iff.

Can we build a different path that uses NSeparated directly?

**Terminal:** Either connect or show the existing framework requires class_eq_iff.

### (c) classify_abel via Mumford normalization

Key insight from handoff: both exactSpreadLine and pointSpreadLine
for the same rationalClass use the same normalized Mumford representative.
normalize_eq_of_class ensures identical affine ideals and specialDivisors.

Chain: same rationalClass → same normalizedMumford → same mapMumford →
same genericRaw → same affine ideal → (saturation) → same integral model →
same specialDivisor → same toSpecialPic → same specialClass.

Need to verify each step in the existing infrastructure.

**Terminal:** Complete chain or identify a gap where two different integral
models with the same generic Mumford can have different special classes.

### (d) classify_abel via direct ReducesTo

The existing `abel_reduces` in `rationalPointReductionData` proves exactly
`ReducesTo (rationalAbel P) (specialPointClass (reduceCurve P))` using
`pointSpreadLine P`. If we can show that `classify` agrees with the
`classify` of ANY SpreadData that has the same specialClass function,
we might be able to transfer the result.

But this requires class_eq_iff for the SpreadData construction.

**Terminal:** Either find a class_eq_iff-free path or identify the dependency.

## Execution Order

1. START with (c) — classify_abel via Mumford normalization
2. IN PARALLEL: dispatch ChatGPT to analyze (a) — finite cardinality route for classify_injective
3. THEN: attempt (a) or (b) for classify_injective based on what (c) reveals
