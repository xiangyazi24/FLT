# B03 specialization-additivity lane

Task FLT-C13-B03-PLAN, revision 1. Source pin `a6290bc36c3549d89239da82b13b1f59ebd0388e`, repository `xiangyazi24/FLT`. This report is a source audit and uncompiled proof design. Every Lean check: **NOT RUN**. No build, cache fetch, or project compilation was attempted.

## Result first

There are genuine ring-level tensor identities available now, and the candidate files extend them to generic oriented classes and complete special chart pairs. They do **not** establish B03. The two missing mathematical results are:

1. A geometrically marked global family has whole-chart, integral principal comparisons between the degree-four lines `c(P) ⊗ c(Q)` and `c(P+Q) ⊗ c(0)`, with nonzero reduction of their numerator/denominator presentations. Generic oriented-Picard equality by itself does not establish this.
2. The explicit finite code kills actual principal relations among degree-four divisors on the good special curve. Its present separation theorem only identifies the degree-two equivalence relation `AbelRel`; it does not identify a Picard group law.

The conditional mathematical proof of B03 once those two results are genuinely established is short and exact, as shown below. Neither missing result is silently assumed in a purported construction or in a candidate claiming B03.

## Source audit: facts actually present

At the source pin, with paths relative to `FLT/Assumptions/MazurProof/`:

- `N13SpecialAbelCode.lean`: `MazurProof.N13SpecialAbelCode.pointCode`, `baseAmplitude`, `divisorCode`, `divisorCode_mk`, and `divisorCode_eq_of_abelRel` assign amplitudes 1, 7, 8 and prove invariance for the explicitly defined degree-two relation.
- `N13SpecialAbelCodeQuotient.lean`: `divisorCode_eq_iff_abelRel`, `picCode`, `picCode_abel`, `picEquiv`, `picEquiv_apply`, `picCode_specialTranslateCode`, and `specialTranslateCode_add` prove a set bijection and transport translations along it. They do not establish compatibility with tensor of geometric lines.
- `N13AbelFiberTwoModel.lean`: `MazurProof.N13AbelFiberTwoModel.AbelRel` is literally `D = E ∨ IsCanonical D ∧ IsCanonical E`. `PicTwoSetModel` is its set quotient. The finite cardinal is not an additive-law theorem.
- `N13TwoChartLineTensor.lean`: `MazurProof.N13TwoChartLineTensor.tensor` multiplies both chart ideals; `tensor_affineIdeal`, `tensor_infinityIdeal`, and `map_tensor_affineIdeal` establish the corresponding identities.
- `N13TwoChartSpecialRestriction.lean` (additional exact-pin fetch): `MazurProof.N13TwoChartSpecialRestriction.restrict_tensor_affineIdeal` and `restrict_tensor_infinityIdeal` already prove reduction multiplicativity on both charts. `ChartPair.ext` upgrades two ideal equalities to an equality of whole chart pairs. `reduceInfinityOverlap_comp_affineToInfinityOverlap` supplies the overlap reduction square.
- `N13SpecialDivisorCharts.lean` (additional exact-pin fetch): `MazurProof.N13SpecialDivisorCharts.tensor`, `tensor_comm`, `ofDivisor`, `ofDivisor_mk` identify degree-two divisors with products of point chart pairs.
- `N13TwoChartPicardRealization.lean`: `genericIdealUnit`, `coe_genericIdealUnit`, `genericRaw`, `genericClass`, and `Data` supply the exact objects used by the tensor candidates. `Data.infinityOrder` is a separately supplied integer; its type contains no equation relating it to the infinity chart. `Data.toSpecialPic` is `abel specialDivisor`.
- `N13SpecializationGroupHom.lean`: the source defines `G`, `J₂`, an inferred additive-group instance, `specialNormalize`, and `genericNormalize`. Despite the header's intended future API, it does not define `specialize : G →+ J₂` or prove a reduction homomorphism into the explicit special code. Moreover its `G` is over Q₂, whereas the endgame's `G` is rational.

## Exact route from the two-chart data

Let `c : G → Data`, put `d(P) := (c P).specialDivisor`, and let

`u(P) := picCode ((c P).toSpecialPic) = divisorCode (d P)`.

Use `specialCode(P) := u(P) - u(0)`. Because `picEquiv_apply` identifies `picEquiv` with `picCode`, this is exactly the requested recentered equivalence.

For `P,Q`, the required geometric comparison is

`c(P).charts ⊗ c(Q).charts ~ c(P+Q).charts ⊗ c(0).charts`.

Both sides represent degree-four effective divisors. Using `c(P+Q)` alone would compare degrees four and two and omit the basepoint correction. A tensor of two `Data` objects is **not** another `Data`: its reduced divisor has degree four, while `Data.specialDivisor` has type `Sym2 CurvePoint`.

The B00 lane's actual principal-comparison structures are in candidate `N13CoherentChartComparison.lean`, namespace `MazurProof.N13CoherentChartComparison`:

- `IntegralComparison L M` supplies numerator/denominator elements in each integral chart, principal-ideal equality on each chart, cross multiplication asserting the same rational function on the overlap, and nonzero reductions of all four elements.
- `IntegralComparison.reduce` yields `SpecialComparison (restrict L) (restrict M)`. It applies `Ideal.map_mul`, `Ideal.map_span`, and the commutative reduction square. This reduction is a real ring proof, rather than an assertion about the code.

Candidate `restrict_tensor_data` identifies these two restricted pairs with

`tensor (ofDivisor (d P)) (ofDivisor (d Q))` and
`tensor (ofDivisor (d (P+Q))) (ofDivisor (d 0))`.

The missing special-fibre bridge must therefore have this exact Lean statement, after importing `N13CoherentChartComparison`:

```lean
-- SPECIFICATION ONLY: no proof is supplied, and this is not a candidate declaration.
theorem degreeFourCode_eq_of_comparison
    (D E F H : MazurProof.N13SymmetricSquareTwo.EffectiveDivisorTwo)
    (h : MazurProof.N13CoherentChartComparison.SpecialComparison
      (MazurProof.N13SpecialDivisorCharts.tensor
        (MazurProof.N13SpecialDivisorCharts.ofDivisor D)
        (MazurProof.N13SpecialDivisorCharts.ofDivisor E))
      (MazurProof.N13SpecialDivisorCharts.tensor
        (MazurProof.N13SpecialDivisorCharts.ofDivisor F)
        (MazurProof.N13SpecialDivisorCharts.ofDivisor H))) :
    MazurProof.N13SpecialAbelCode.divisorCode D +
        MazurProof.N13SpecialAbelCode.divisorCode E =
      MazurProof.N13SpecialAbelCode.divisorCode F +
        MazurProof.N13SpecialAbelCode.divisorCode H
```

Apply this to `D=d P`, `E=d Q`, `F=d(P+Q)`, `H=d 0`. It gives

`u(P)+u(Q)=u(P+Q)+u(0)`.

Subtract `2*u(0)` and obtain exactly

`specialCode(P+Q)=specialCode(P)+specialCode(Q)`.

The candidate `specialCode_abel_add_iff` proves the arithmetic equivalence precisely. It is explicitly only an equivalence of obligations; it is not presented as solving the geometric side.

## What proving the missing bridge actually requires

The input `SpecialComparison` is expressed in concrete special coordinate rings, so this is a substantive algebraic theorem. A valid route is to construct the actual Picard/divisor quotient of the good characteristic-two model and prove the code is a homomorphism on its rational-point-supported divisor classes. An alternative is a bounded, certified Riemann–Roch calculation for degree-four differences, proving that existence of the stated principal comparison forces the code equation. A finite enumeration of point/divisor codes alone does not establish that implication: the principal-comparison witnesses are arbitrary coordinate-ring elements.

In particular, the sextic equation obtained by completing the square is not automatically a valid substitute for the smooth good characteristic-two model. Any bridge through `N13SpecializationGroupHom.J₂` must justify the characteristic-two coordinate model and its principal relation, not simply instantiate a set-cardinality theorem.

The integral comparison additionally needs a genuine marking/whole-chart extension theorem. Candidate `genericClass_tensor_balance` proves the generic Picard-class equality available from a homomorphism and a family with correct generic classes. The source counterexample `N13CoherentPointReduction.exactRaw_saturated_does_not_determine_specialClass` rules out inferring whole-chart special coherence from exact generic raw data and affine saturation. It is therefore invalid to feed that generic equality directly into specialization without the missing geometric comparison.

## Dependency-ordered candidate lemmas

All exact Lean statements and proof bodies are in the new files. For assembly, copy each file to the identically named `FLT/Assumptions/MazurProof/` path; no existing file or statement is edited.

1. `N13TwoChartTensorCompatibility.lean`, namespace `MazurProof.N13.TwoChartTensorCompatibility`:
   - `genericIdealUnit_tensor`, using `coe_genericIdealUnit`, `Units.ext`, `Ideal.map_mul`, and `FractionalIdeal.coeIdeal_mul`.
   - `genericRaw_tensor`, using the preceding identity and addition in `Multiplicative ℤ`.
   - `genericClass_tensor`, using the preceding raw identity and `map_mul` for the principal quotient.
   - `genericClass_tensor_balance`, using the generic tensor theorem, `hc : ∀ P, (c P).toGenericPic = f P`, and `map_add`/`map_zero` for `f : G →+ GenericPic`.
   - `restrict_tensor`, using both existing special restriction tensor lemmas and `ChartPair.ext`.
   - `restrict_data`, using `Data.special_affine`, `Data.special_infinity`, and `ChartPair.ext`.
   - `restrict_tensor_data`, using the preceding two equalities.
   Exact direct import: `FLT.Assumptions.MazurProof.N13TwoChartPicardRealization`.
2. B00 lane's `N13CoherentChartComparison.lean`: the concrete integral/special principal-comparison interface and its reduction theorem.
3. **Missing geometric existence** for the global family's tensor comparisons. No candidate claims this exists.
4. **Missing degree-four special-code soundness**, exact statement above. No candidate claims it is proved.
5. `N13SpecialCodeRecenter.lean`, namespace `MazurProof.N13.SpecialCodeRecenter`:
   - `specialCode` and `specialCode_zero`.
   - `specialCode_translate`, showing a uniform transported translation cancels under recentering.
   - `specialCode_add_iff` and `specialCode_abel_add_iff`, exposing precisely the degree-four code equation.
   Exact direct import: `FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient`.
6. `N13SpecialCuspCodeChecks.lean`, namespace `MazurProof.N13.SpecialCuspCodeChecks`, independent finite regression checks:
   - `pointCode_cusp` computes all six cusp values, respecting the sheet reversal at x=1.
   - `divisorCode_double_anchor`, `divisorCode_negative_anchor`, `divisorCode_inverse_pair`, and `inverse_pair_recentered` verify the degree-zero witnesses' necessary code relation.
   Exact imports: `FLT.Assumptions.MazurProof.N13SpecialAbelCodeQuotient`, `FLT.Assumptions.MazurProof.N13SpecialCuspReduction`.

The cusp checks have raw divisor codes 16 for 2∞+, 0 for ∞−+∞+, and 13 for C+A. Recentered by 16 they give 0, 3, and 16, so the latter two are additive inverses. The value 13 uses `cuspCoordinate .negOnePlus = (Sum.inl 1,1)`; taking it as sheet zero would create a false apparent contradiction. These checks are necessary consistency tests, not a proof for arbitrary rational classes.

## Check status

- Exact-pin source audit of the listed declarations: PASS (source inspection)
- No use of `N13ClassEqIff.n13_class_eq_iff`: PASS (static inspection)
- No appeal to `exactSpreadLine` special coherence: PASS (static inspection)
- No new axioms, admitted proofs, `native_decide`, `True` stand-ins, or edits to existing files in this lane's candidates: PASS (static inspection)
- Lean parsing/elaboration/build: NOT RUN
- `#print axioms`: NOT RUN
- B00 geometric-family existence: NOT PROVED
- B03 additivity: NOT PROVED; two exact missing bridges identified above

The release criterion remains the lead's build and `#print axioms`, not this source audit.
