# N25 and N49 source-boundary review

## Current-pin continuity

All 152 inspected N25/N49 Lean-family blobs are unchanged at accepted source 22f88d43187caf0e57affcc6ded92cdf9b49714a, verified against the full current tree. Thus the mathematical boundary findings below continue to apply. Lead r5 now confirms that N25, N49, and the prime-at-least-23 tail are exactly the three custom axioms in the fresh Mazur root audit; N13 has been discharged.

## Result and scope

At pin `6aef0f8bdea96652f4879d0f74acd6bf189f306c`, both requested names are still literal axioms. No unconditional, noncircular replacement was found in the complete tracked N25/N49 module families inspected. N25 is substantially more developed in current source; N49 still lacks its global arithmetic bridge. Neither is a wiring-only finish.

This is **source inspection only**, not a new kernel audit. Read-only GitHub retrieval covered the full recursive tree, all 152 tracked Lean files whose MazurProof paths contain `25` or `49`, relevant common divisor/Riemann–Roch modules, assembly, and frontier documents. No builds, cache downloads, or external writes were performed. This report concerns the exact pin above; it makes no claim about the separate later `62968808` checkout.

## 1. Exact boundary statements

### N25

The declaration is:

```lean
axiom MazurProof.CyclicExclusion25.no_explicit_order25_obstruction :
  ¬ ExplicitOrder25Obstruction
```

Expanding both obstruction aliases and `F5` gives:

```lean
¬ ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic
      (MazurProof.TateOriginDivision.W b c),
      b ≠ 0 ∧
      b - c ≠ 0 ∧
      MazurProof.TateOrder25Factor.F25 b c = 0
```

Sources:
- [CyclicExclusion25:30–54](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicExclusion25.lean#L30-L54)
- [ExplicitOrder25Obstruction:352–354](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateOrder25Factor.lean#L352-L354)
- [F5 definition:55](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateNFDivision.lean#L55)

`W b c` abbreviates the Tate curve with coefficients `(a₁,a₂,a₃,a₄,a₆) = (1-c,-b,-b,0,0)`, hence equation

`y² + (1-c)xy - by = x³ - bx²`.

[W:28–29](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateOriginDivision.lean#L28-L29), [coefficient record:80–85](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/scratch/TateZ2xZ10Reduction.lean#L80-L85)

`F25` is a literal 234-term polynomial at [TateOrder25Factor:309–310](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateOrder25Factor.lean#L309-L310). For a readable exact description, the source proves

```lean
G11 b c * G13 b c ^ 3 - b * G14 b c * G12 b c ^ 3 =
  (b - c) * F25 b c
```

with compact factors explicitly defined at [236–254](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateOrder25Factor.lean#L236-L254) and factorization at [318–333](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateOrder25Factor.lean#L318-L333). In particular,

`preΨ′₂₅(0) = b²⁰⁸(b-c)F25(b,c)`.

The axiom excludes rational points on the primitive order-25 Tate locus, with both ellipticity and proper-order-five exclusion retained. It is not merely a nonvanishing assertion on every rational zero of the displayed polynomial.

### N49

Expanding its obstruction definition gives exactly:

```lean
¬ ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic
      (MazurProof.TateOriginDivision.W b c),
      b ≠ 0 ∧
      ((MazurProof.TateOriginDivision.W b c).preΨ' 49).eval 0 = 0 ∧
      ((MazurProof.TateOriginDivision.W b c).preΨ' 7).eval 0 ≠ 0
```

[Raw definition and axiom:20–43](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicExclusion49.lean#L20-L43)

The source algebraic reformulation is:

```lean
∃ b c : ℚ, ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
  b ≠ 0 ∧
  (c ^ 3 - b ^ 2 + b * c) ≠ 0 ∧
  bracket49 b c = 0
```

`TateOrder49Bridge.raw_order49_obstruction_iff` proves equivalence, and `TateOrder49Factor.prePsi_fortynine_eval_compact` proves

`preΨ′₄₉(0) = b⁸⁰⁰ · bracket49(b,c)`.

[Bridge:29–59](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateOrder49Bridge.lean#L29-L59), [compact identity:330–342](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/TateOrder49Factor.lean#L330-L342)

Despite the definition's comment saying “primitive,” `ExplicitOrder49Obstruction` uses the unfactored bracket with `F7 ≠ 0`, not a stored primitive `F49` polynomial.

## 2. Active-route callers and circularity

For both boundaries:

1. Axiom
2. `CyclicExclusion25.no_rational_point_of_order_25` / `CyclicExclusion49.no_rational_point_of_order_49`
3. `CyclicOrderAssembly.no_order_25` / `no_order_49`
4. private `no_order_bad_composite`
5. `mazur_cyclic_order_bound_assembled`

[CyclicExclusion25:49–54](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicExclusion25.lean#L49-L54), [CyclicExclusion49:45–50](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicExclusion49.lean#L45-L50), [assembly:170–225](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/CyclicOrderAssembly.lean#L170-L225)

Using these public exclusions or the assembled cyclic bound to discharge their inputs would be circular.

`TateOrder49Bridge` imports `CyclicExclusion49` to obtain the predicate/front-end theorem, but its displayed algebraic proof does not call the axiom. Importing that module alone does not establish axiom dependence. It supplies only an equivalence and forward reduction, never the needed negation.

## 3. N25: actual current frontier

Several roadmap statements are stale. Current source goes significantly beyond the map's “identify the overlap unit” task:

- Tate parameters already map to a nonzero, noncuspidal point on the genus-four canonical model. [CanonicalSourceBridge:816–855](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25CanonicalSourceBridge.lean#L816-L855)
- Binary projective smoothness and relative dimension one are present. [TwoSmooth:146–164](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoSmooth.lean#L146-L164)
- Properness is present. [TwoProper:64–76](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoProper.lean#L64-L76)
- The inverse-coordinate-ratio overlap transition is present. [CanonicalDifferentialOverlaps:1133–1210](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps.lean#L1133-L1210)
- The actual scheme-relative differential sheaf is identified with the hyperplane twist. [RelativeDifferentials:2291–2320](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoRelativeDifferentials.lean#L2291-L2320)

Newest concrete divisor work:

- Nonboundary principal-divisor homomorphism exists. [N25F_NonBoundaryPrincipalDivisor:25–30,88–110](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/N25F_NonBoundaryPrincipalDivisor.lean#L25-L110)
- Its coefficients equal genuine local orders. [N25F_ChartLocalOrder:505–526](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/N25F_ChartLocalOrder.lean#L505-L526)
- Order zero is equivalent to representation by a local-ring unit. [N25F_ChartLocalUnitCriterion:277–293](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/N25F_ChartLocalUnitCriterion.lean#L277-L293)
- Full projective degree splits into boundary and affine contributions. This file explicitly disclaims proving the product formula. [N25F_ProjectiveDivisorDegree:5–16,293–381](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/N25F_ProjectiveDivisorDegree.lean#L5-L381)

Thus the concrete next cut is full projective principal divisors, boundary compatibility, and degree zero/product formula, followed by actual Picard finiteness, complete linear systems and Riemann–Roch. Current class-number consumers explicitly require those inputs:

- [Binary hyperplane/section consumer:248–326](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoMiddleRiemannRoch.lean#L248-L326)
- [Characteristic-three divisor-Picard consumer:205–243](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25QuotientMiddleRiemannRoch.lean#L205-L243)

The characteristic-two consumer still takes `Principal ≤ divisorDegree.ker`, a `Fintype` instance for `PicDegree ... 0`, degree-two/four section spaces, equivalences of effective-divisor fibres with their projectivizations, and the residual Riemann–Roch finrank identity as arguments. These are visible hypotheses, not completed concrete geometry hidden behind the conclusion `= 71`.

After that remain actual rational rank-zero/good-reduction maps and primary-kernel results, geometric norm/pullback with composition `[2]`, and Abel–Jacobi rational-point classification. Existing reduction/pullback files explicitly say they are abstract finite-group bookkeeping, not constructions of Jacobians or geometric maps. [ReductionCardinality:5–14](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25ReductionCardinality.lean#L5-L14), [DegreeTwoPullback:5–14](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN25DegreeTwoPullback.lean#L5-L14)

Important F3 limitation: denominator-open maximal-ideal equivalence is not full W-chart coverage. Current source explicitly disproves unconditional denominator avoidance using `[0:0:0:1]`. [ThreeWOpenClosedPoints:568–619](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/N25F_ThreeWOpenClosedPoints.lean#L568-L619)

## 4. N49: actual current frontier

- Structural recurrence/bracket reduction is present.
- The alternate composition theorem still ends in literal `sorry`. [RationalPointsN49Composition:91–96](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/RationalPointsN49Composition.lean#L91-L96)
- Proving that identity would not prove rational-point exclusion.
- `X049DescentObstruction` supplies archimedean and finite-modulus local obstruction lemmas; it does not construct descent exact sequences or prove rank zero/exhaustion. Its header's conclusion is prose, not an exported theorem. The finite certificates use `native_decide`. [X049DescentObstruction:66–188](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/FLT/Assumptions/MazurProof/X049DescentObstruction.lean#L66-L188)

The newer root-level Newton analysis retracts the all-local plan: it reports Hensel-liftable faces and says p-adic refinement cannot close the remaining chart. This is research-document evidence, not an independently verified Lean theorem. [N49_NEWTON_ANALYSIS:89–113](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/N49_NEWTON_ANALYSIS.md#L89-L113)

The revised global route requires:

1. Explicit Tate/order-49 → X₀(49) map
2. Assembled rational-point/rank-zero proof for the elliptic target
3. Identification of its two rational points as cusps and source cusp avoidance

[Updated root N49_PROOF_PLAN:58–76](https://github.com/xiangyazi24/FLT/blob/6aef0f8bdea96652f4879d0f74acd6bf189f306c/N49_PROOF_PLAN.md#L58-L76)

Do not repeat DOCTRINE's “birational map” wording: the plan describes a degree-21 quotient, and genus 69 to genus 1 cannot be birational.

## 5. Bounded ranking recommendation

For **current-source maturity**, rank **N25 ahead of N49**.

- N25 has the exact source-to-target map, cusp avoidance, extensive actual curve/sheaf/local-divisor infrastructure, and explicit downstream consumer hypotheses.
- N49 has the Tate front end and useful algebra/local certificates, but still lacks the global quotient map and assembled arithmetic exhaustion.

This is an evidence-based judgment about the inspected source, **not a reliable calendar-effort estimate**. N25's remaining Riemann–Roch/Picard/rank-zero infrastructure is substantial, while N49's proposed target is only genus one. Neither boundary has an existing theorem ready to substitute for its axiom at the inspected pin.
