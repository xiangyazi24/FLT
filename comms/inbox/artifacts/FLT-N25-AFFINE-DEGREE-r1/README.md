# N25 actual affine principal-divisor degree

## Exact result

Four production files provide the dependency-ordered proof:
1. N25F_DedekindFactorDegree.lean
2. N25F_PrincipalDivisorCoefficient.lean
3. N25F_PrincipalDivisorQuotientDegree.lean
4. N25F_WChartPrincipalDegree.lean

The exact original actual-W target is now proved in source:

```lean
theorem wChart_principal_degree_eq_quotient_finrank
    (a : W) (ha : a ≠ 0)
    (f : Additive ((FractionRing W)ˣ))
    (hf : (f.toMul : FractionRing W) = algebraMap W (FractionRing W) a) :
    wChartDivisorDegree
        (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) =
      (Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) : ℤ)
```

Final FQN:
`MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_principal_degree_eq_quotient_finrank`.

No hypothesis is added, the same f/a identification is retained, and no existing definition is replaced. In particular, no independent multiplicity vector, alternate principal divisor, arbitrary boundary coefficients or subgroup named Principal is introduced.

## Dependency-ordered proof

### 1. Actual ideal factor multiplicities

The generic Dedekind/finite-field theorem establishes:

```lean
Module.finrank k (S ⧸ I) =
  ∑ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
    (UniqueFactorizationMonoid.normalizedFactors I).count P *
      Module.finrank k (S ⧸ P)
```

It uses Mathlib's exact prime-power CRT equivalence, transfers finiteness along quotient-surjective maps, computes prime-power quotient cardinalities, and equates powers of the finite field cardinality. It needs neither Infinite S nor Module.Free ℤ S. The latter would be inappropriate for characteristic two.

The actual-W theorem discharges the required quotient finiteness with the already accepted `wChart_quotient_finite a ha`; it is not an extra premise of the final result.

### 2. Actual fractional-ideal coefficient

For the same nonzero regular a, the existing fractional-ideal order equals its actual normalized ideal-factor count. The proof uses:
- `FractionalIdeal.coeIdeal_span_singleton`
- `FractionalIdeal.count_coe`
- `Ideal.count_associates_factors_eq`

This is the order used by the existing `CurveDedekindDivisor.principalDivisor`, not a replacement valuation.

### 3. Existing principal-divisor weighted degree

The generic theorem on that exact existing principalDivisor identifies its weighted finite-support sum with the quotient finrank. Its `Finset.sum_bij` uses height-one primes' actual `asIdeal` map:
- nonzero source coefficient iff that ideal occurs as a normalized factor
- the height-one map is injective
- every normalized factor is a genuine nonzero prime and therefore supplies a height-one point

Thus no support-completeness premise is added.

### 4. Existing W-chart transports

The final W wrapper:
- installs the already accepted finite-quotient instance
- unfolds the existing nonboundary/maximal-ideal maps, both `Finsupp.domCongr`
- applies two `Finsupp.sum_equivMapDomain` rewrites
- identifies the actual weight with `Module.finrank (ZMod 2) (W ⧸ v.asIdeal)`
- invokes the checked real principalDivisor theorem

All carriers, maps and weights are those already in the repository.

## Pins and acceptance synchronization

Current accepted FLT source: `9ecac38589bd3b45abc144ffda01e2f711213c52`.
The only source change from previous pin 40efa26fea43fb0ed7d70db804f0d0dcdd71342b is the accepted norm-dimension module. All dependencies used here are unchanged.

[Lead r8](https://github.com/xiangyazi24/FLT/blob/12c72c1e508e72bd7a665ef803af2c21d774d2ce/comms/outbox/lead-FLT-N13-ENDPOINT-receipt-r8.md) accepts the actual-W norm/dimension theorem byte-equal, with build 8644 jobs, unchanged ActualWCheck, and standard-three axioms. That proof and the earlier quotient-finiteness proof are preserved unchanged.

Lean: 4.31.0-rc2.
Mathlib: 96fd0fff3b8837985ae21dd02e712cb5df72ec05.

## Precisely checked locally

Bounded checks use one CPU, one Lean thread, 3072 MiB Lean cap, and 60-second timeout per invocation. No broad FLT or Mathlib build was run.

- CRT factor/normalized-factor identities: kernel check and standard-three axiom audit PASS
- finite-type specialization without a quotient-finiteness premise: PASS
- principal fractional-ideal coefficient: PASS
- degree theorem using the real existing CurveDedekindDivisor definition: PASS
- proper canonical FLT module imports for the unchanged small CurveDedekindDivisor module and the three new generic helpers: PASS
- actual W geometry wrapper: **not compiled locally**, pending the lead's project check

Canonical-module commands, exit statuses and file hashes are in CANONICAL_COMPILE_RECEIPT.json. The baseline CurveDedekindDivisor source is verified against Git blob 20c6208962f3163e4eabda838efc5c73afdc0b6c. Earlier scratch serialization had one extra final newline; the final canonical-module check uses the exact baseline bytes. No mathematical source change was made.

The generic harnesses and their logs are included for reproducibility. The canonical import check strengthens these tests, but none is mislabeled as full actual-W project acceptance.

## Lead integration

Copy the four files from comms/candidates to FLT/Assumptions/MazurProof with the same basenames. Compile in listed dependency order or build N25F_WChartPrincipalDegree. Use LEAD_VALIDATION.lean for the exact original statement and final axiom emission.

Do not integrate superseded Infinite-only, prime-power-wrapper or duplicate regular-coefficient alternatives from earlier local exploration. Only the four manifest-listed production files are delivered.

## Remaining scope

This closes the selected affine weighted-degree statement at source level. The actual-W compiler/axiom receipt is still pending. It does **not** construct projective principal divisors, the three genuine boundary valuations, the global product formula, Picard/Riemann–Roch/rational arithmetic, or the final N25 obstruction exclusion. No root custom axiom is claimed discharged.

