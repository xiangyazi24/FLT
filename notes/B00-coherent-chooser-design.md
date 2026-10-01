# B00 source audit and coherent chooser design

SOURCE: xiangyazi24/FLT, a6290bc36c3549d89239da82b13b1f59ebd0388e. No other source revision used. All proposed Lean elaboration/build/axiom checks: NOT RUN. No builds, clones, caches or existing-file edits performed.

## Result

The three degree-zero witnesses can be glued into a genuine **class-level** degree-zero realization. The existing global existence declarations do not imply a globally specialization-compatible chooser. Degree-one reorientation also needs correction; degree-two generic/special marking must be checked rather than assumed coherent. The missing step is geometric and is stronger than arithmetic recentering.

### Exact source declarations

All names below are in `MazurProof` unless fully qualified, and all files under `FLT/Assumptions/MazurProof/` at the pin above.

* `N13TwoChartPicardRealization.Data` in `N13TwoChartPicardRealization.lean` has `charts`, an independent `infinityOrder`, `specialDivisor`, and literal `special_affine`/`special_infinity` equations. It has **no equation tying infinityOrder to the generic infinity chart**. `Data.toGenericPic` reads the affine fractional ideal and independent order; `Data.toSpecialPic` reads the special divisor.
* `N13RationalPicardSpreadExistence.reorientData` changes only infinityOrder. `reorientData_genericRaw` and `reorientData_affineVerticallySaturated` prove genuine statements but cannot repair this missing tie. Our first candidate `reorientData_toSpecialPic` is definitional equality and makes the limitation explicit.
* `N13CoherentPointReduction.exactRaw_saturated_does_not_determine_specialClass` is an actual formal counterexample. Do not infer special uniqueness from exact raw equality plus affine saturation, and do not use `exactSpreadLine` as coherent.
* Degree-zero nInf=0 uses `N13InfinityPointPicardRealization.infinityMinusData`, `infinityMinusData_toGenericPic`, `infinityMinusLine_affineVerticallySaturated`, and special divisor minus+plus.
* Degree-zero nInf=1 uses that namespace's `infinityPlusData`, `infinityPlusData_toGenericPic`, `infinityPlusLine_affineVerticallySaturated`, and divisor plus+plus.
* Degree-zero nInf=2 uses `N13InverseInfinityWitness.inverseInfinityData` from `N13InverseInfinityWitness.lean`; its `infinityOrder` is -2 and its special divisor is C+A. `inverseInfinityData_toGenericPic_eq_opposite` and `inverseInfinityData_affineVerticallySaturated` from `N13InverseInfinityWitnessClass.lean` are the class-level and saturation certificates. The former proof uses `genericIdealUnit_caLine`, `N13Arithmetic.AJ13_C_add_A_eq_classOf_opposite`, and base change. It does not prove raw equality with (1,0,2), nor should it: the raw affine ideals and integers differ.
* `N13Arithmetic.oppositeInfinityMumford`, `classOf_opposite_add_infinityMinus`, `classOf_opposite_eq_neg_AJ13_T`, and `AJ13_C_add_A_eq_classOf_opposite` are in `N13OppositeInfinityClass.lean`.
* Existing degree-one producers are `N13RationalCurvePointPicardRealization.integralAffineData`, `escapingAffineData`, their `*_map_affineIdeal` and `*_affineVerticallySaturated` lemmas, and `data P : Data P`, whose fields are `realization`, `generic_eq`, `special_eq`. `pointSpreadLine` packages these. These point witnesses are meaningful coherent anchors.
* The global `N13RationalPicardSpreadExistence.exists_saturated_data_of_natDegree_eq_one` first resets `nInf` via `degreeOnePointForm`, extracts a point with `SexticMumford.exists_affinePoint_of_natDegree_eq_one`, then reorients without changing the special divisor. It therefore does not certify the nInf=1 branch's special geometry. Increasing the generic order by one adds the **opposite**, not the negative-infinity, class: see `N13InverseInfinityWitness.genericClass_sub_one` for the exact opposite-direction formula.
* `N13RationalPicardSpreadExistence.exists_saturated_data_of_natDegree_eq_two` calls `N13QuadraticPicardRealization.exists_saturated_data (mapMumford D) hdeg₂`. This gives exact generic raw and class equalities and affine saturation. It does not add the missing relation between integer marking and infinity chart.

### Degree-two sign caution supported by actual lemmas

Let O = classOf(oppositeInfinityMumford Q₂). Two proved declarations give

  inverseInfinityData.toGenericPic = genericClass caLine (-1) - O
  inverseInfinityData.toGenericPic = O.

Thus genericClass caLine (-1) = O+O. Our `caLine_minus_one_class` candidate proves this by `eq_sub_iff_add_eq`, using exactly the two declarations above, not a comment. By contrast the coherent C+A witness uses order -2 and class O. This is enough to reject the inference “the same chart line with standard quadratic mark -1 is automatically coherent.” A full formal identification with every quadratic branch, or a nonzero-class proof making inequality explicit, is **not claimed** here. Actual class identities, not header claims, support the caution.

## Precise interfaces and open existence theorem

`comms/candidates/N13CoherentChooserSpecification.lean` supplies Lean definitions, not an axiom or a theorem asserted without proof:

* `Chooser.choose : G → Data`
* `Chooser.generic_eq : ∀ P, (choose P).toGenericPic = picMapRatToQ₂ P`
* `Chooser.saturated : ∀ P, AffineVerticallySaturated (choose P).charts`
* `Chooser.point_compatible : ∀ P, Nonempty (IntegralComparison (choose (rationalAbel P)).charts (data P).realization.charts)`

`HasIntegralTensorComparisons c` is the geometrical statement

  ∀ P Q, Nonempty (IntegralComparison
    (tensor (c.choose P).charts (c.choose Q).charts)
    (tensor (c.choose (P+Q)).charts (c.choose 0).charts)).

`GlobalExistenceTarget` is the precise proposition whose future theorem should be

  theorem exists_coherent_global_chooser : GlobalExistenceTarget

The proposition also requires calibration at 0, AJ13 T, and -AJ13 T to the three witnesses. The theorem is **missing** and is deliberately not entered as an unproved declaration. This is not a completed B00 proof conditional on renamed B03: tensor comparison is separately displayed as a major open geometric theorem. It mentions actual regular functions, both integral chart ideals, nonzero reductions, and a common overlap fraction; it contains no finite code or desired additive equation. Point compatibility alone does not establish full coherence for arbitrary non-Abel classes. A proof must additionally tie generic infinity data to full chart geometry before attempting tensor comparisons.

## Concrete principal comparison without inventing a function-field API

`N13CoherentChartComparison.IntegralComparison L M` stores four regular functions: affine aNum/aDen and infinity iNum/iDen. Principal ideal equalities are

  (aNum) * L.affineIdeal = (aDen) * M.affineIdeal
  (iNum) * L.infinityIdeal = (iDen) * M.infinityIdeal.

The overlap cross-product equation identifies the two fractions. All four reductions are required nonzero. Thus this is an actual common principal relation, with denominators accounted for, and excludes silent loss of a vertical power of 2. It does not assert a generic fraction has such a presentation: proving existence after vertical normalization is precisely part of the missing geometry.

`SpecialComparison` is the analogous reduced-ring structure. `IntegralComparison.reduce` follows by applying the reduction maps to the ideal equations and the overlap equation. This candidate requires only already-known ring maps and reduction squares, not a new special function-field identification.

Additional source reads at the same pin:

* `N13IntegralInfinityPointSpread.lean`, Git blob b30e578241a1f4c9a0b32877c44343994564e39f. Its `TwoChartLine` has two invertible ideals and equality on `N13OrdinaryCurveOverlap.InfinityOverlap`.
* `N13TwoChartSpecialRestriction.lean`, Git blob 259f23b7a28c9a94881076f68f814665ffc9be94. Exact APIs: `SpecialAffine`, `SpecialInfinity`, `ChartPair`, `restrict`, `reduceInfinityOverlap_comp_affineToInfinityOverlap`, and the tensor restriction lemmas. Its proof also uses `N13OverlapReductionCompatibility.reduceInfinityOverlap_comp_algebraMap`.

URLs: https://github.com/xiangyazi24/FLT/blob/a6290bc36c3549d89239da82b13b1f59ebd0388e/FLT/Assumptions/MazurProof/N13IntegralInfinityPointSpread.lean and https://github.com/xiangyazi24/FLT/blob/a6290bc36c3549d89239da82b13b1f59ebd0388e/FLT/Assumptions/MazurProof/N13TwoChartSpecialRestriction.lean

## Dependency-ordered work

1. `N13CoherentDegreeZeroChooser.reorientData_toSpecialPic`: definitional limitation lemma, existing reorientData.
2. `mumford_ext`: proof-irrelevant field extensionality; candidate.
3. `exists_degreeZero_class_data`: degree zero forces u=1,v=0; infinity_bound yields nInf≤2; split 0/1/2 and use the three exact class/saturation declarations. Candidate contains actual proof and no raw-equality requirement.
4. `caLine_minus_one_class`: derived sign audit above; candidate.
5. `N13CoherentChartComparison.map_cleared_ideal_eq`: Ideal.map preserves products and principal ideals; candidate.
6. `IntegralComparison.reduce`: reduction squares plus preceding map lemma; candidate.
7. Generic infinity-mark coherence for point, quadratic, and changed-representative constructions: **missing**. Correct degree-one nInf=1 without bare reorientation; audit/correct quadratic order conventions; allow principal-equivalent representatives rather than insist on exact normalized raw.
8. Representative-independent integral extension on both charts: **missing**. Need equality of generic line bundles to extend to a common principal comparison with controllable vertical factor; affine saturation alone does not do this.
9. `exists_coherent_global_chooser : GlobalExistenceTarget`: **missing**, assembled only after 7–8 and branch gluing. Classical choice cannot invent the absent compatibility.
10. Degree-four principal-equivalence invariance of sum of divisor codes: **missing**, B03 lane. A bijection of nineteen-element sets and the degree-two AbelRel classification do not imply this statement.

## Candidate and peer-review status

Three B00 candidate files are UTF-8 and new-file-only. Install candidate comparison at `FLT/Assumptions/MazurProof/N13CoherentChartComparison.lean` when testing the specification import; no such existing source file is changed here. Original pinned dependency closure and Mathlib are needed; input-only folder is not a buildable checkout. No Lean checks were run.

Source-level peer review of B03's `N13TwoChartTensorCompatibility.lean` and `N13SpecialCodeRecenter.lean`: PASS for stated mathematical meaning. `genericClass_tensor_balance` assumes only generic agreement with an existing additive map (instantiate picMapRatToQ₂), not special additivity. Its equality cannot be lifted to whole-chart equivalence from bare Data. `specialCode_add_iff` correctly isolates an arithmetic equivalence of obligations; it proves neither geometric obligation. Lean elaboration and axiom review: NOT RUN.
