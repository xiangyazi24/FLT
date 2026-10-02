# N25 next exact cut after accepted N13 wiring

## Status, provenance, and selected scope

Accepted-root pin supplied by lead r5: `22f88d43187caf0e57affcc6ded92cdf9b49714a`. Lead reports N13 wiring and aggregate acceptance complete, with exactly N25, N49, and prime ≥23 custom axioms and no `sorryAx`. This document does not independently emit or verify that result.

Read-only connector checks at 22f88d4 confirmed the following blobs equal the previously inspected 6aef baseline:

| File | Git blob |
| --- | --- |
| N25F_ProjectiveDivisorDegree.lean | 30b90a32ee153c3c7eedb0b4746a882d25be34b4 |
| N25F_ProjectiveDivisorSplit.lean | c3ab045b8c87ebf90b5af37e3ebc6369cbb00c34 |
| N25F_NonBoundaryPrincipalDivisor.lean | 4cb645a429c94c736267ff2ec7f7e77463eb493d |
| N25F_ChartLocalOrder.lean | a808c0fb1c4aa6d5410f8d5abbdc8c27a4366f92 |
| N25F_ChartLocalUnitCriterion.lean | f780d30cb9ab83947001d55b23b3e7005f740daa |
| RationalPointsN25QuotientTwoWBoundaryXLocal.lean | 8fcf421cd1d897766c2126af96c9c11f6a25135a |
| RationalPointsN25QuotientTwoWBoundaryYZLocal.lean | d1dfc2e8b07b252e908a5b32af444df70fa238e9 |
| RationalPointsN25QuotientTwoWBoundaryZLocal.lean | bd4ca9299d029906af1c8b6c6f758733be2528d9 |
| RationalPointsN25QuotientTwoWBoundaryLocalDivisor.lean | 40bd61664a4dc51e685be0978687b62eca530aad |
| RationalPointsN25QuotientTwoWChartNormalization.lean | 13312dbe3c5cec7fdef9576da6ead94843ae5c3e |
| RationalPointsN25QuotientTwoPlaneFunctionField.lean | 0d711ee0eb8a62d6300f81a3b4dd05a76b0fa0ee |
| RationalPointsN25QuotientTwoWOpenEvaluation.lean | 8523290a73ebcd6ec25550578ca8b41c991d01c8 |
| RationalPointsN25QuotientTwoWBoundaryChartArtin.lean | 7dd2a3b0dcaf84ac8afa1ea9b5151327c9cb0539 |

The next bounded mathematical target recommended below is the **actual affine principal-divisor degree/quotient-dimension identity**, followed by the genuine boundary comparison needed for a full projective product formula. This is an intermediate theorem, not a replacement of the N25 axiom. No Lean build, cache operation, or axiom emission was run; proposed signatures/proof sketches below have not been elaborated.

## 1. Exact existing objects; do not substitute proxies

In the existing namespaces:

```lean
MazurProof.N25F_NonBoundaryPrincipalDivisor.W :=
  MazurProof.RationalPointsN25QuotientTwoWOpenEvaluation.WChartQuotient

MazurProof.N25F_NonBoundaryPrincipalDivisor.nonBoundaryPrincipalDivisor :
  Additive ((FractionRing W)ˣ) →+
    (FullNonBoundaryAtom25Two →₀ ℤ)

MazurProof.N25F_ProjectiveDivisorSplit.ProjectiveDivisor25Two :=
  fullClosedPointGrading25Two.Divisor

MazurProof.N25F_ProjectiveDivisorSplit.BoundaryCoefficients25Two :=
  ℤ × (ℤ × ℤ)

MazurProof.N25F_ProjectiveDivisorSplit.nonBoundaryDivisorEquivWChart :
  NonBoundaryDivisor25Two ≃+ WChartDivisor25Two

MazurProof.N25F_ProjectiveDivisorSplit.fullDivisorEquivBoundaryCoefficientsChart :
  ProjectiveDivisor25Two ≃+
    (BoundaryCoefficients25Two × WChartDivisor25Two)

MazurProof.N25F_ProjectiveDivisorDegree.wChartDivisorDegree :
  WChartDivisor25Two →+ ℤ
```

These displays expose existing aliases, not instructions to introduce duplicate definitions. Boundary coefficient order is exactly X, YZ, Z. The chart degree is the signed sum of each coefficient times the actual binary residue degree. See [principal divisor:19–108](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/N25F_NonBoundaryPrincipalDivisor.lean#L19-L108), [split carrier](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/N25F_ProjectiveDivisorSplit.lean), [degree:88–152,293–381](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/N25F_ProjectiveDivisorDegree.lean#L88-L381).

**Missing object:** there is no already constructed full-projective principal-divisor homomorphism in these files. The existing map records only the W-chart/nonboundary valuations. Its degree is not generally zero. The three boundary coefficients must be the valuations of the **same rational function** at the actual boundary local rings.

Choosing arbitrary boundary coefficients summing to the negative affine degree would trivially produce a degree-zero divisor but would not construct a principal divisor. Do not take that shortcut, nor use an arbitrary subgroup named `Principal` as the geometric producer.

## 2. Recommended next nontrivial exact lemma

Use the following existing-name open context, not new abstract carrier structures:

```lean
open MazurProof.N25F_NonBoundaryPrincipalDivisor
open MazurProof.N25F_ProjectiveDivisorSplit
open MazurProof.N25F_ProjectiveDivisorDegree
```

The proposed new theorem type is:

```lean
theorem wChart_principal_degree_eq_quotient_finrank
    (a : W) (ha : a ≠ 0)
    (f : Additive ((FractionRing W)ˣ))
    (hf : (f.toMul : FractionRing W) =
      algebraMap W (FractionRing W) a) :
    wChartDivisorDegree
        (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) =
      (Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) : ℤ)
```

Here `hf` identifies the unit with the same regular chart function `a`; it is not an extra arithmetic assumption about the N25 curve. The theorem is the weighted zero-divisor degree formula for a nonzero element of the actual affine Dedekind ring. It does not assert that its affine degree vanishes.

First prove, rather than add as a premise, the necessary finiteness lemma:

```lean
theorem wChart_quotient_finite
    (a : W) (ha : a ≠ 0) :
    Module.Finite (ZMod 2) (W ⧸ Ideal.span ({a} : Set W))
```

These types use already constructed ring, divisor, residue-degree, and coefficient maps. They do not presuppose a newly named projective principal-divisor map. They have not been compiled here.

### Dependency-ordered proof plan

1. Use the actual W-chart Dedekind-domain instance and the nonzero principal ideal `(a)`. The ring is already finite over the fixed binary polynomial ring. Prove its nonzero-ideal quotient is finite over `ZMod 2`; use integral closure/finite algebra or ideal factorization, not a fake `Fintype` parameter.
2. Factor `(a)` into the finitely many maximal/height-one prime powers. Preserve the exact exponents used by `CurveDedekindDivisor.principalDivisor`.
3. Prove the local quotient-length identity at each prime: exponent times actual residue-field degree. Sum through the finite-support decomposition/Chinese remainder theorem to obtain the binary vector-space dimension of `W/(a)`.
4. Transport those exact coefficients through `fullNonBoundaryAtomEquivHeightOne` and `nonBoundaryDivisorEquivWChart`. The residue-degree comparison is already supplied by `residueDegree_fullNonBoundaryAtomEquivHeightOne` / `wChartMaximalIdealDegree_fullNonBoundary`.
5. Apply the definition of `wChartDivisorDegree`; do not introduce an independent valuation vector or choose different principal generators in the geometric identification.

Existing useful source inputs include [W finite over the polynomial base:184–198](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoWChartNormalization.lean#L184-L198), [Dedekind/relative norm:573–612](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoWChartNormalization.lean#L573-L612), and [local coefficient/order bridge:505–526](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/N25F_ChartLocalOrder.lean#L505-L526).

An alternative norm proof must keep two degrees distinct: the relative inertia degree in `canonicalWChart_relNorm_eq_basePrime_pow` and the absolute binary residue degree in `wChartDivisorDegree`. Their tower-degree relation is a proof obligation, not definitional equality.

### Honest candidate assessment

No existing tracked theorem located in the inspected modules directly proves this degree/dimension identity, and no substantive proof body has been constructed or checked in this source-only pass. This is a concrete proposed theorem target with a bounded factorization/length proof plan, not a delivered Lean proof candidate. Further source/API inspection and genuine proof construction are needed; compilation and fresh emitted checks remain lead-owned.

There is an immediately derivable transport-only statement converting the full projective degree to boundary sum plus affine degree, but that is already the substance of `splitDegree_apply_components` and `splitDegree_apply`. Duplicating it and calling it product-formula progress would be misleading.

## 3. Genuine boundary producer required next

The existing boundary rings are:

- `RationalPointsN25QuotientTwoWBoundaryXLocal.XLocalRing`, at `[1:0:0:0]`
- `RationalPointsN25QuotientTwoWBoundaryYZLocal.YZLocalRing`, at `[0:1:1:0]`
- `RationalPointsN25QuotientTwoWBoundaryZLocal.ZLocalRing`, at `[0:0:1:0]`

They already compute the order of the restricted hyperplane section W as 3, 1, 2 respectively. That is not yet an order function for arbitrary members of `FractionRing W`.

A precise first producer target uses the actual X-chart coordinates and existing common field. With the existing namespaces opened:

```lean
open MazurProof.RationalPointsN25QuotientTwoWBoundaryChartArtin
open MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal
open MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
```

Prove the following existence statement (using fully qualified `W` from the principal-divisor namespace if open-name ambiguity arises):

```lean
theorem exists_xBoundaryEmbedding_into_wFunctionField :
    ∃ j : XLocalRing →+* FractionRing W,
      Function.Injective j ∧
      (∀ r : ZMod 2,
        j (algebraMap (ZMod 2) XLocalRing r) =
          algebraMap (ZMod 2) (FractionRing W) r) ∧
      j (algebraMap XChartRing XLocalRing xY) =
        algebraMap W (FractionRing W) qy /
          algebraMap W (FractionRing W) qx ∧
      j (algebraMap XChartRing XLocalRing xZ) =
        algebraMap W (FractionRing W) qz /
          algebraMap W (FractionRing W) qx ∧
      j (algebraMap XChartRing XLocalRing xW) =
        (algebraMap W (FractionRing W) qx)⁻¹
```

This is a construction obligation, not an assumption to introduce. The coordinate requirements prevent an arbitrary field embedding from replacing the actual chart transition. `qx,qy,qz` are the existing X/W, Y/W, Z/W elements, and `xY,xZ,xW` the existing Y/X, Z/X, W/X elements. [X-chart coordinates:29–37](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoWBoundaryChartArtin.lean#L29-L37), [W-chart coordinates:45–59](https://github.com/xiangyazi24/FLT/blob/22f88d43187caf0e57affcc6ded92cdf9b49714a/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoWOpenPrimeSurjective.lean#L45-L59)

Required proof order:

1. Use the actual chart-overlap maps to embed the X chart into the W-chart function field; prove denominator nonvanishing on the generic point.
2. Prove injectivity and that every denominator outside the boundary maximal ideal maps to a unit of the field; extend to the actual localization.
3. Establish the compatible `IsFractionRing` structure on the same common field, and the DVR/local-domain facts for the actual boundary local ring.
4. Repeat for YZ and Z with their actual coordinate transitions. Do not identify the boundary local ring with its Artinian W-section quotient.
5. Define their integer fraction orders on the same `Additive ((FractionRing W)ˣ)`, retaining the coordinate-checked common-field maps. Prove additivity and compatibility with the existing 3/1/2 W-germ calculations.

No ready proof of the displayed boundary embedding was found in the inspected modules. Existing nonboundary fraction-ring and unit-criterion code is reusable guidance, not an already instantiated boundary theorem.

## 4. Exact projective end condition once genuine boundary orders exist

The existing split equivalence fixes how the principal divisor must be assembled. For any **genuine** boundary coefficient triple `c` and the same function `f`, the projective divisor is the existing expression

```lean
fullDivisorEquivBoundaryCoefficientsChart.symm
  (c, nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f))
```

Its degree zero is exactly equivalent, by existing `splitDegree_apply_components` and `boundaryCoefficientDegree_apply`, to

```lean
c.1 + c.2.1 + c.2.2 +
  wChartDivisorDegree
    (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) = 0
```

This is the nontrivial global product formula **only after c has been constructed as the three actual boundary valuations of f**. Until those functions exist, there is no honest current fully qualified name for a complete projective principal-divisor homomorphism; this plan deliberately does not invent one and treat it as implemented.

Use the degree/dimension identity for chart numerators and denominators, then prove the actual boundary contribution cancels that difference. A finite-function-field norm proof is possible in principle, but must establish all places/ramification/residue-degree compatibilities, including boundary places, rather than rely only on the affine relative-norm theorem.

After the product formula, the range of the resulting genuine homomorphism supplies the actual subgroup `Principal ≤ fullClosedPointGrading25Two.divisorDegree.ker`. Only then is it legitimate to instantiate the concrete Picard quotient geometry. Finiteness, complete linear systems/Riemann–Roch, characteristic-three comparison, rational rank zero, reduction maps, pullback/norm and Abel–Jacobi classification remain later work; this bounded target does not claim to discharge them.

## Acceptance gate

- New exact target statements: proposed, not compiled
- Existing source identities and blob continuity: checked at 22f88d4
- New genuine mathematical proof candidate: not yet available
- New Lean placeholder file, axiom, `sorry`, or abstract replacement structure: none created
- Stop this next proof task after the actual degree/dimension theorem and its finite-quotient prerequisite are proved and freshly checked with their emitted dependencies; continue boundary-map construction only if separately included in the assigned proof scope
- Do not report N25 closure until the unchanged `no_explicit_order25_obstruction` proposition is proved and wired into the fresh root
