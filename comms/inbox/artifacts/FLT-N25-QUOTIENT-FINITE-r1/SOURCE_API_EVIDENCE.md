# Source/API evidence

All sources below were read through the GitHub connector at their exact pinned commit. Search results were discovery aids only. The proof uses these pinned declarations.

## Mathlib: 96fd0fff3b8837985ae21dd02e712cb5df72ec05

- [Jacobson/Artinian.lean:21,47–53](https://github.com/leanprover-community/mathlib4/blob/96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/RingTheory/Jacobson/Artinian.lean#L21-L53), blob `40907827396a5f5a8e0025519350d80077001197`
  - Variables: `(R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]`
  - `Module.finite_iff_krullDimLE_zero [IsArtinianRing R] : Module.Finite R A ↔ Ring.KrullDimLE 0 A`
  - Applied with R = ZMod 2, A = W/(a). A field is Artinian; finite type follows from the quotient/MvPolynomial instances below.

- [KrullDimension/Zero.lean:60–70](https://github.com/leanprover-community/mathlib4/blob/96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/RingTheory/KrullDimension/Zero.lean#L60-L70), blob `1971d6da9a135e24b90df035509764d51dd4e81b`
  - `Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal {R : Type*} [CommRing R] {I : Ideal R} : Ring.KrullDimLE 0 (R ⧸ I) ↔ ∀ J ∈ I.minimalPrimes, J.IsMaximal`
  - No nontrivial quotient or proper-ideal assumption.

- [DedekindDomain/Basic.lean:55–65,119–147](https://github.com/leanprover-community/mathlib4/blob/96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/RingTheory/DedekindDomain/Basic.lean#L55-L147), blob `836e591313a5c62b87339ad86fba2f929fae9c6f`
  - `Ideal.IsPrime.isMaximal {R : Type*} [CommRing R] [Ring.DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p ≠ ⊥) : p.IsMaximal`
  - `IsDedekindDomain` extends `IsDedekindRing`, which extends `Ring.DimensionLEOne`.
  - The same file uses the exact `ne_bot_of_le_ne_bot hp hr2` argument pattern in `Ideal.mem_minimalPrimes_of_ne_bot`.

- [Ideal/MinimalPrime/Basic.lean:42–58](https://github.com/leanprover-community/mathlib4/blob/96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean#L42-L58), blob `23e037a198388abf710e9641cc10b856cdcb09c6`
  - Minimal-prime membership has `hP.1.1 : P.IsPrime` and `hP.1.2 : I ≤ P`.
  - These are precisely the two projections used by the candidate.

- [Ideal/Span.lean:109–110](https://github.com/leanprover-community/mathlib4/blob/96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/RingTheory/Ideal/Span.lean#L109-L110), blob `b3e8c4bdf6b91c34240536aee7e657fcaf45e80e`
  - `Ideal.span_singleton_eq_bot {x} : Ideal.span ({x} : Set α) = ⊥ ↔ x = 0`
  - Its `.not.mpr ha` proves exactly `(a) ≠ ⊥`.

- [FiniteType.lean:98–112](https://github.com/leanprover-community/mathlib4/blob/96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/RingTheory/FiniteType.lean#L98-L112), blob `3748e2ff54e2fb9ea77e56c2ccc99bd0803fef43`
  - `Algebra.FiniteType.quotient` supplies finite type for quotients of finite-type algebras.
  - The finite-variable MvPolynomial instance supplies finite type for the polynomial presentation of W.
  - A second use supplies finite type for W/(a).

## FLT: 22f88d43187caf0e57affcc6ded92cdf9b49714a

- [N25F_NonBoundaryPrincipalDivisor.lean:19](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/N25F_NonBoundaryPrincipalDivisor.lean#L19), blob `4cb645a429c94c736267ff2ec7f7e77463eb493d`
  - Existing `abbrev W := WChartQuotient`.

- [WOpenEvaluation.lean:50–52](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoWOpenEvaluation.lean#L50-L52), blob `8523290a73ebcd6ec25550578ca8b41c991d01c8`
  - Existing `abbrev WChartQuotient := ChartQuotient (3 : Fin 4)`.

- [AffineChartsSmooth.lean:36–37](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoAffineChartsSmooth.lean#L36-L37), blob `5848a044ec5838a89774c164292c99d9b10eec2c`
  - `ChartQuotient pivot := AffineChart pivot ⧸ chartAffineEquationIdeal pivot`.

- [AffineCharts.lean:24–37](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoAffineCharts.lean#L24-L37), blob `01d535accd5441b43f3a0135ee1404b3d66ab87a`
  - `OtherCoordinate i := {j : Fin 4 // j ≠ i}`.
  - `AffineChart i := MvPolynomial (OtherCoordinate i) k`.
  - The coefficient alias k is the existing binary field.

- [WChartNormalization.lean:354–358,572–574](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoWChartNormalization.lean#L354-L574), blob `13312dbe3c5cec7fdef9576da6ead94843ae5c3e`
  - `canonicalWChart_isDedekindDomain : IsDedekindDomain (ChartQuotient 3)`.
  - The existing `residueFiniteType` proof already uses inferred `Algebra.FiniteType (ZMod 2) (ChartQuotient 3)`, independently confirming that this presentation's standard algebra structure supports the required synthesis.

## Review boundary

The generic proof and exact specialization have been source-reviewed. The generic theorem and principal-ideal corollary additionally passed the bounded pinned Mathlib microcompile; see `GENERIC_CHECK.log`. The actual W specialization has not been compiled, so this file is not its kernel acceptance certificate. No source read from the default-branch discovery queries is relied on without its pinned counterpart.

