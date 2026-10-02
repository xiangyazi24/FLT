# N25 affine principal-degree formula: checked core and actual-W candidate

## Outcome

The nontrivial generic arithmetic and finite-support comparison are fully checked against the pinned Mathlib, using the actual existing `CurveDedekindDivisor.principalDivisor` definition.

The exact originally requested actual-W theorem now has a complete proof candidate in `N25F_WChartPrincipalDegree.lean`:

```lean
theorem wChart_principal_degree_eq_quotient_finrank
    (a : W) (ha : a ≠ 0)
    (f : Additive ((FractionRing W)ˣ))
    (hf : (f.toMul : FractionRing W) = algebraMap W (FractionRing W) a) :
    wChartDivisorDegree
        (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) =
      (Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) : ℤ)
```

Only this actual-W wrapper needs the lead's current-project elaboration. Its proof derives quotient finiteness from accepted `wChart_quotient_finite`, unfolds the two existing domain equivalences, checks their actual weights by the `e(e.symm v)` law, and invokes the checked arithmetic theorem. It does not introduce an alternate divisor, principal subgroup, or assumption about product formulas.

## Integrate these four new module files

Under `FLT/Assumptions/MazurProof/`:

1. `N25F_DedekindFactorDegree.lean`
2. `N25F_PrincipalDivisorCoefficient.lean`
3. `N25F_PrincipalDivisorQuotientDegree.lean`
4. `N25F_WChartPrincipalDegree.lean`

All four are present at the delivery root and copied into `production/`, which contains exactly these four files. The first three compiled under their actual module names and emitted only `propext`, `Classical.choice`, and `Quot.sound`. The fourth is not locally project-compiled because doing that requires the actual W geometry import closure; the task explicitly excludes a broad build here.

The other files in this directory are verification harnesses, source-only superseded alternatives, or optional stronger variants. Do not include the unused Infinite-only/cardinality scaffolding or the duplicate standalone regular-coefficient wrapper in the minimal integration.

## Checked chain

- CRT splits a nonzero ideal quotient into its actual factor prime powers.
- `cardQuot_pow_of_prime` computes their cardinalities.
- Finite-field cardinality gives quotient finrank as the normalized-factor sum weighted by actual residue finranks.
- `FractionalIdeal.count_coe` and `Ideal.count_associates_factors_eq` identify the coefficients of the existing principal divisor of a regular element with those same normalized counts.
- `Finset.sum_bij` along `HeightOneSpectrum.asIdeal` compares the exact principal-divisor support with that normalized factor support. Prime/nonzero and support membership are proved in both directions.
- Integer casting yields `CurveDedekindDivisor.principalDivisor_degree_eq_quotient_finrank`.

## Canonical import validation

`check_project/` is an isolated Lean search-path overlay, not a replacement FLT checkout.

- The parent-supplied original `CurveDedekindDivisor.lean` had exactly one extra connector-materialization terminal newline. Removing only that extra newline yields the exact accepted Git blob `20c6208962f3163e4eabda838efc5c73afdc0b6c` (4199 bytes). The overlay uses those exact accepted bytes. Current accepted baseline is `9ecac38589bd3b45abc144ffda01e2f711213c52`; the parent verified these dependencies unchanged from `40efa26fea43fb0ed7d70db804f0d0dcdd71342b`.
- That original module was compiled unchanged.
- The three new core modules were then compiled separately under proper `FLT.Assumptions.MazurProof.*` import names.
- A separate import-only file emitted axioms for both public principal-divisor theorems.
- All checks passed; see `CANONICAL_COMPILE_RECEIPT.json` for exact commands, environment/search paths, source and olean paths/hashes, per-command exit statuses and durations, and the independent source-body harness identity checks. `CanonicalModuleChecks.log` contains the readable output.
- Exact Mathlib commit: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.
- Lean version: `4.31.0-rc2`.
- Every invocation used the authorized bounded runner, one CPU/thread, 3072 MB Lean cap, and 60-second timeout.
- No broader FLT build was run and no compiler is left running.

## Next validation

Lead should compile all four new modules in the actual current FLT checkout and emit:

```lean
#print axioms MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_principal_degree_eq_quotient_finrank
```

That is the remaining validation step, not a remaining mathematical premise. Even a successful check proves only the affine degree/dimension identity. It does not produce boundary valuations, prove the projective product formula, or discharge N25.
