# Independent source review: W-chart quotient finiteness

**Verdict: source-level PASS; no blocking mathematical or pinned-API issue found.** The actual-W specialization has not been compiled in this review. No Lean/lake/build/cache command was run by this reviewer, and no external write was made.

## Scope and provenance

- FLT: `22f88d43187caf0e57affcc6ded92cdf9b49714a`
- Mathlib: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`
- Reviewed `N25F_WChartQuotientFinite.lean`, SHA-256 `b93b4090ed99594fe85811c37aaec0f751dec5389fec9bd0cb4274d0c3dd6cd9`
- Reviewed `GenericFiniteQuotient.lean`, SHA-256 `461235f570f0abec1b7cdf0795b3a91e530aa87c5c6152a79b49eb66028bf16f`

The local Mathlib checkout reports the exact pinned HEAD and a clean worktree. All 13 supplied Mathlib source copies match that checkout after ignoring only final whitespace. Four relevant FLT copies (principal divisor, W normalization, affine charts, smooth charts) were independently checked against GitHub at the exact FLT pin: their Git blob hashes match after removing the copies' one extra trailing newline. The W alias and binary-field alias were additionally read directly at that pin.

## Exact statement and available instances

The final declaration as currently written is:

`MazurProof.N25F_NonBoundaryPrincipalDivisor.wChart_quotient_finite (a : W) (ha : a ≠ 0) : Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W))`

There are no section variables, new typeclass assumptions, replacement carriers, or hidden finiteness hypotheses in this concrete theorem. Its `W` is the existing abbreviation for `WOpenEvaluation.WChartQuotient`, definitionally `AffineChartsSmooth.ChartQuotient (3 : Fin 4)` (WOpenEvaluation:51). This is the genuine chart quotient, not an abstract substitute.

- `ChartQuotient` is `AffineChart pivot ⧸ chartAffineEquationIdeal pivot` (AffineChartsSmooth:36–37).
- `AffineChart` is `MvPolynomial (OtherCoordinate pivot) k` (AffineCharts:37), with finite coordinate subtype and `k := ZMod 2` (GradedKoszul:21).
- Thus the existing multivariate-polynomial finite-type instance and `Algebra.FiniteType.quotient` supply finite type for W and then W/(a) (FiniteType:98–112). No `Module.Finite (ZMod 2) W` premise is used or needed.
- The already-imported `canonicalWChart_isDedekindDomain` applies to the definitionally identical `ChartQuotient 3` (WChartNormalization:573–574). `IsDedekindDomain → IsDedekindRing → Ring.DimensionLEOne` is the pinned class hierarchy (DedekindDomain/Basic:118–119,145–146).
- The field `ZMod 2` supplies the Artinian base-ring instance. The quotient need not be nontrivial; units are correctly allowed as inputs.

## Proof/API check

1. `Module.finite_iff_krullDimLE_zero R A` requires commutative rings, `Algebra R A`, `Algebra.FiniteType R A`, and `IsArtinianRing R`, and concludes `Module.Finite R A ↔ Ring.KrullDimLE 0 A` (Jacobson/Artinian:22,49–54). The selected `.2` direction is correct.
2. `Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal` has exactly the quotient/minimal-prime equivalence used, with no extra dimension assumption on the source (KrullDimension/Zero:62–65).
3. `P ∈ I.minimalPrimes` unfolds to `Minimal (fun q ↦ q.IsPrime ∧ I ≤ q) P`. Therefore `hP.1.1 : P.IsPrime` and `hP.1.2 : I ≤ P` are the correct projections (Ideal/MinimalPrime/Basic:42–62).
4. `Ideal.span_singleton_eq_bot.not.mpr ha` proves `(a) ≠ ⊥`. `ne_bot_of_le_ne_bot` correctly propagates this through `(a) ≤ P`. It is the generated dual of `ne_top_of_le_ne_top` (Order/BoundedOrder/Basic:205–207).
5. `Ideal.IsPrime.isMaximal` takes the prime proof followed by `P ≠ ⊥`, under `Ring.DimensionLEOne W` (DedekindDomain/Basic:62–64). This is exactly the final term.

The generic theorem uses the same valid proof. Its formal `Ring.DimensionLEOne A` hypothesis says every nonzero prime is maximal. Optional documentation refinement: say that explicitly, rather than merely “dimension at most one,” because the latter wording can suggest the weaker ordinary Krull-dimension bound for rings with zero divisors.

## Dependency boundary and naming

No `sorry`, `admit`, new axiom, circular use of this lemma, or assumed quotient-finiteness result occurs in either candidate. The concrete proof uses only existing chart structure and Mathlib's finiteness/dimension argument; it does not invoke the N25 obstruction axiom, a degree-zero/product-formula claim, or the principal-divisor theorem to prove finiteness. This source inspection is not an emitted transitive axiom audit of the concrete specialization.

Keeping the existing `MazurProof.N25F_NonBoundaryPrincipalDivisor` namespace is clean and minimizes alias/import churn, since it already owns `W` and the intended downstream divisor API. The provisional new namespace is not mathematically necessary. Report the actual FQN above in delivery.

## Validation boundary

Parent reports a separate, successful exact-pin microcompile of the generic theorem and principal-ideal corollary, with only the standard three axioms and no `sorryAx`; that tested file has SHA-256 `0d2f30725331edc3649feb35597e567bd6e944e1cdbb6398798eefa965f82aca`. This reviewer did not run or independently reproduce that check. Actual-W elaboration, emitted axiom audit, integration, and aggregate acceptance remain to be established by the lead. This helper proves quotient finiteness only; it does not close N25 or the projective degree-zero bridge.
