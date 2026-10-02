Final provenance update: after this source review, the canonical overlay baseline was normalized to exact Git blob 20c6208962f3163e4eabda838efc5c73afdc0b6c and all four tiny module checks plus the axiom audit were rerun successfully. See CANONICAL_COMPILE_RECEIPT.json. Production proof bytes are unchanged.

# Independent source review: N25 affine principal-divisor degree

Review date: 2026-10-02 UTC.

## Verdict

**Source review passes for the four preferred production candidates.** I found no mathematical weakening, replacement data carrier, circular use of the desired identity, multiplicity mismatch, lost support, or incorrect residue weight. The final W-chart proposition is the exact target from `N25_PLAN.md`.

This review did not run Lean, invoke a build, or change any Lean file. The first three production modules have successful canonical-import checks in the supplied log; I independently checked that the production bytes equal the checked overlay bytes. The fourth, `N25F_WChartPrincipalDegree.lean`, still needs elaboration and a fresh axiom emission in the actual FLT import closure. Source approval is not a claim that this final check has happened.

One minor documentation issue at the initial inspection is recorded below: the copied original `CurveDedekindDivisor` was identical to the reported upstream blob except for one additional final newline, so its initial “byte-for-byte” upstream claim was too strong. This does not alter any declaration or proof. The parent subsequently confirmed that the author is normalizing the original-source overlay and rerunning the bounded canonical checks with a command/hash receipt; this source-mathematics review does not wait for that correction.

## Scope and pins

Only these production candidates were reviewed for integration:

1. `N25F_DedekindFactorDegree.lean`
2. `N25F_PrincipalDivisorCoefficient.lean`
3. `N25F_PrincipalDivisorQuotientDegree.lean`
4. `N25F_WChartPrincipalDegree.lean`

The Infinite-only, prime-power-wrapper, finite-type-wrapper, and duplicate standalone coefficient alternatives were not assessed as production dependencies and are not required by this chain.

FLT source pin supplied for this task: `40efa26fea43fb0ed7d70db804f0d0dcdd71342b`. Local Mathlib HEAD was independently read as `96fd0fff3b8837985ae21dd02e712cb5df72ec05`. Source/API inspection used that Mathlib checkout, the supplied existing geometry sources, the accepted quotient-finiteness helper, and the canonical-module check log. No independent remote commit fetch was performed in this review.

## Exact target and assumptions

The final theorem, at `N25F_WChartPrincipalDegree.lean:16–22`, is:

```lean
theorem wChart_principal_degree_eq_quotient_finrank
    (a : W) (ha : a ≠ 0)
    (f : Additive ((FractionRing W)ˣ))
    (hf : (f.toMul : FractionRing W) = algebraMap W (FractionRing W) a) :
    wChartDivisorDegree
        (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) =
      (Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) : ℤ)
```

There is no additional finiteness, infinitude, nonunit, support, chosen multiplicity, norm-degree, product-formula, or geometric premise. The `W` in the current namespace is the existing `WChartQuotient`. `hf` identifies the same fraction-field unit with the given regular function; no other function or generator is substituted.

The generic arithmetic theorem explicitly assumes finite-dimensionality of the ideal quotient. In the concrete W theorem that assumption is discharged locally by `wChart_quotient_finite a ha` at lines 24–25. The accepted helper proves it from the actual ring's finite-type and Dedekind facts via zero-dimensionality of the nonzero principal-ideal quotient. Its source does not depend on the weighted-degree formula.

## Factorization and cardinality proof

`N25F_DedekindFactorDegree.lean:18–61` uses the existing Dedekind CRT equivalence for exactly `S/I`, indexed by the distinct ideals in `(factors I).toFinset`, and the exact factor counts as prime-power exponents.

- A factor `P` is proved prime and nonzero, not merely assumed to index a component
- `I ≤ P` follows from actual factor divisibility, giving a surjective quotient map `S/I → S/P`
- Finiteness of each residue quotient is derived from the finite quotient `S/I`
- Pinned Mathlib's `cardQuot_pow_of_prime` requires the supplied Dedekind, prime, and nonzero facts; it introduces no characteristic-zero or `Infinite S` premise
- Cardinality of the CRT product, the finite-field vector-space cardinality formula, and injectivity of exponentiation by `Nat.card k ≥ 2` give the dimension identity
- The finite-subtype product/sum is explicitly converted back to the original factor finset

Lines 65–70 replace `factors` by `normalizedFactors` using the genuine trivial-unit ideal-monoid normalization theorem. This retains multiplicities rather than only preserving the underlying set of prime factors.

The proof includes the unit ideal: its factor finset is empty and its quotient is the zero vector space. It does not introduce a nonunit assumption that would silently omit constant/unit regular functions.

## Principal-divisor coefficient and finite support

`N25F_PrincipalDivisorCoefficient.lean:15–25` uses the exact sequence:

1. `FractionalIdeal.coeIdeal_span_singleton`
2. `FractionalIdeal.count_coe`
3. `Ideal.count_associates_factors_eq`

Thus the fractional-ideal count at `v` is the integer cast of the normalized multiplicity of `v.asIdeal` in the same principal ideal `(a)`. Nonzeroness of `(a)` is proved from `ha`.

`N25F_PrincipalDivisorQuotientDegree.lean:17–26` unfolds the existing `CurveDedekindDivisor.principalDivisor` coefficient and rewrites by `hf`. The source definition of that existing principal divisor is the finitely supported vector of fractional-ideal counts of `spanSingleton` of the actual input unit. The candidate does not define another divisor with convenient coefficients.

The `Finset.sum_bij` at lines 50–68 accounts for the full support in both directions:

- A supported height-one prime maps to an ideal with nonzero normalized factor count, hence to the factor finset
- Injectivity of `v ↦ v.asIdeal` is supplied by `HeightOneSpectrum.ext`
- Every normalized prime factor is proved prime and nonzero, supplies a genuine `HeightOneSpectrum`, and has nonzero coefficient, so it lies in the actual principal-divisor support
- The summand equality uses the previously proved coefficient identity and the same quotient `R/v.asIdeal`

Finally, the natural-number weighted formula is cast into the integer-valued divisor degree. There is no unsigned/signed mismatch: the existing divisor is integer-valued, and this regular-function case proves its coefficients are the nonnegative factor counts.

## Actual W weights and the two transports

The existing definitions fix the orientations:

- `nonBoundaryPrincipalDivisor` transports the height-one principal divisor through `Finsupp.domCongr fullNonBoundaryAtomEquivHeightOne.symm`
- `nonBoundaryDivisorEquivWChart` then transports through `Finsupp.domCongr fullNonBoundaryAtomEquivMaximalIdeal`

Pinned Mathlib defines `domCongr` with `equivMapDomain` as its forward function. Hence the candidate's `change` at lines 35–38 exactly unfolds those two existing maps in the correct order. Applying `Finsupp.sum_equivMapDomain` twice reindexes the original finite support; it neither drops coefficients nor creates an independent vector.

The transported weight at height-one prime `v` is the degree of

```lean
fullNonBoundaryAtomEquivMaximalIdeal
  (fullNonBoundaryAtomEquivHeightOne.symm v)
```

The existing `wChartMaximalIdealDegree` is `residueDegree` of that maximal ideal, and `residueDegree` is the actual `Module.finrank (ZMod 2)` of its quotient. The existing height-one equivalence's `asIdeal` is definitionally that same maximal ideal. Thus lines 26–33 reduce the weight to the quotient by `(e (e.symm v)).asIdeal` and use `Equiv.apply_symm_apply` to obtain exactly `W/v.asIdeal`.

This is a direct check of the absolute binary residue weight. It does not substitute relative inertia degree, cardinality, an unproved tower identity, or a chosen atom weight. The existing degree module separately relates this residue degree to the genuine full closed-point atom degree.

## Verification evidence and remaining gate

`CanonicalModuleChecks.log` records successful separate compilation of the original `CurveDedekindDivisor` and the first three new modules under their real `FLT.Assumptions.MazurProof.*` import names. It records only `propext`, `Classical.choice`, and `Quot.sound` for both public principal-divisor theorems. Earlier isolated core logs report those same standard axioms for the factor and coefficient lemmas.

I found no `axiom`, `sorry`, `admit`, `unsafe`, replacement opaque declaration, or trust/check disabling option in the four candidates. This lexical finding supplements the supplied core axiom emissions; it does not replace a final concrete-W emission.

Remaining integration gate:

1. Elaborate the fourth module against the current actual W geometry import closure
2. Emit `#print axioms MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_principal_degree_eq_quotient_finrank`
3. Verify the expected dependency set before describing the actual-W theorem as accepted

No mathematical premise remains to be supplied to the candidate, but a successful full-import elaboration remains unverified here. Boundary valuations, a projective principal-divisor map, the global product formula, and N25 closure are outside this result and remain unproved by it.

## Provenance precision

At the initial inspection, the production files and their canonical overlays were byte-identical for all three checked new modules. The original source/overlay `CurveDedekindDivisor.lean` was also byte-identical between those two local copies, but their raw Git blob was `1ad8e8b2b9d3e3a367e0a9a2f1de24f34b5a96bc`. Removing exactly one extra final newline yielded the reported upstream Git blob `20c6208962f3163e4eabda838efc5c73afdc0b6c`.

Likewise, the supplied degree/split/evaluation source copies reproduce their recorded upstream blobs after removal of one additional final newline. The nonboundary source used for inspection agrees with the source pinned in the norm-delivery records up to that same newline; the accepted quotient-finiteness helper matches blob `1ac81106e1f048fb669e8fddfc5b666b5a54bd11` exactly.

The parent confirmed the author is already applying the normalize-and-recheck option with a fresh machine-readable command/hash receipt. Use that corrected receipt for final delivery rather than the initial serialization. This is a low-severity audit-wording issue, not a proof-content blocker; the four production proof bytes are unchanged.

## Reviewed production SHA-256

```text
b536b08c43bbfe3d60121419ddb3d526971ea2eb8db91f02aa92ba43ca79d2f3  N25F_DedekindFactorDegree.lean
ffab496854fae1b92c28c844f0ed99cc585a219741a6dac26535580285db3f50  N25F_PrincipalDivisorCoefficient.lean
86f564f819b3bb11afc55903518afd579450457fb16ab051a555054d85174d68  N25F_PrincipalDivisorQuotientDegree.lean
3c5eace10e22247b0141b8f6b918e4634efc4e36b5006a4ea3f39f78a43e62aa  N25F_WChartPrincipalDegree.lean
```
