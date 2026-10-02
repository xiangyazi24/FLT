# Independent source and mathematical review

## Verdict and frozen artifact

No mathematical counterexample, statement weakening, missing finite case, incorrect polynomial certificate, or concrete source/API mismatch was found in this review. This is a source-only review, not a claim of Lean acceptance.

- Candidate: `FLT/Assumptions/MazurProof/N13SpecialSmallFunctionCertificate.lean`
- Final SHA-256: `5ca2de32cec1df09a869dfbc5f3bcc216ece07af20d44d6796ae0f384404de26`
- Final size: 255643 bytes
- Declared accepted base: `b07243d72093bec5686e15b1208cb50d000f3e8d`
- Original certificate source: `INPUT_N13SpecialSmallFunctionCertificate.lean`, supplied from branch commit `4109ba77745784c1a9f8c4c7b304df4124bf5ac4`
- This final hash differs from reviewed predecessor `a9f1f49e…` only by parenthesizing `K[X]` as `(K[X])` in `CharP.cast_eq_zero`; all independent source-literal checks were rerun against the final hash.

## Public API and scope

All 18 public declaration signatures are unchanged: 16 definition/abbreviation declarations and the two public theorems. Full source bodies of all 16 definitions/abbreviations are byte-for-byte unchanged. Both theorem statements, including every divisibility hypothesis, order bound, nonzero coefficient requirement, earlier-coefficient vanishing requirement, and the weighted-code conclusion, are unchanged.

The only added import is `Mathlib.RingTheory.Coprime.Lemmas`. Added proof helpers and all 128 certificate rows are private. The file introduces no `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, excluded `RationalPicardSpreadExistence`, or excluded `CoherentDegreeZeroChooser` reference. The original scalar coefficient predicate in `jetOrder` is retained unchanged.

This certificate remains finite polynomial algebra in the good F2 model. The separate identification with actual geometric local orders is neither assumed away nor claimed proved by this file.

## Independent arithmetic

The reviewer independently implemented coefficient-list convolution and Euclidean division over F2. This uses a different representation from the author's bit-polynomial calculation. It checks all 128 coefficient pairs and agrees with every norm, six-jet polynomial, six-order vector, support flag, and weighted code in the author's table.

Results:

- 69 supported pairs
- 58 unsupported pairs with nonzero norm
- 1 zero-norm pair, precisely both coefficient vectors zero
- Every supported jet has order at most 7, hence strictly below 9
- Every supported jet has coefficient 1 at its claimed first nonzero index and zero at every earlier index
- Weighted integer sums belong to `{-57, -38, -19, 0, 19, 38, 57}`, so all codes are zero in `ZMod 19`
- Both zero-chart residual cofactors are `X + X^5`
- The remaining four residual cofactors are `1 + X^2 + X^3 + X^7`

The mathematical content of both original finite statements is therefore supported independently; no false statement was found.

## Audit of emitted Lean literals

A separate independent parser reads the actual frozen Lean text and evaluates its displayed polynomial expressions over the integers. It checks all 512 emitted normalization identities, rather than trusting the generation script:

- 6 residual identities
- 414 jet-normal-form identities, six for each supported pair
- 58 norm-factor identities
- 34 Bezout identities for 17 obstruction factors

For a `linear_combination q * two_poly` line, the audit checks the exact integer equality `lhs - rhs = 2*q`; for a `ring` line it checks `lhs - rhs = 0`. This is additional source-mathematical validation, not a replacement for running the Lean tactics.

The parser also checks every row's input coefficient vectors, displayed six-polynomial normal form, order vector, cited obstruction factor, and the final 128-leaf case-dispatch order. The case order is the expected seven nested binary splits, with the last coefficient varying fastest. No finite pair is missing or duplicated.

## Proof and API review

### First-nonzero bridge

The local Lean 4.31.0-rc2 source `Init/Data/List/Find.lean`, lines 670–671, states exactly the needed `List.findIdx_eq` equivalence for an index below list length. The candidate now supplies explicit `xs := List.range 9` and `i := n`.

The same toolchain's `Init/Data/List/Range.lean` has simp-tagged `getElem_range` (line 152) and `length_range` (line 162). Thus the supplied bound `hn`, the Bool-valued coefficient predicate, and the earlier-index false conditions reduce to the hypotheses `hne` and `hzero`. The constructed `Fin 9` index uses `hj.trans hn`, with the correct bound and orientation.

`goodJets_of_coefficients` replaces each original `jetOrder` with the proved index, preserving all finite coefficient clauses and the weighted code. `PairCertificate` is definitionally the original implication with its conclusion unfolded; it adds no hypothesis.

### Obstruction factors

`IsCoprime` is the existence of coefficients whose linear combination is one. Witnesses `(1,u)` and `(1,v)` therefore have the correct order for `f + u*X = 1` and `f + v*(X-1) = 1`.

Exact fetched `Mathlib/RingTheory/Coprime/Basic.lean` at Mathlib pin `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, blob `4aed62561adf6505213ad2d9504a57aab531c461`, confirms:

- line 114: `IsCoprime.mul_right` combines the two right factors
- line 160: `IsCoprime.isUnit_of_dvd` takes `x ∣ y` and returns `IsUnit x`

The inspected `Coprime/Lemmas.lean` line 199 has `IsCoprime.pow_right` with an implicit exponent, matching the candidate's use. `Polynomial.Monic.eq_one_of_isUnit` in the inspected `Polynomial/Monic.lean` lines 209–214 takes monicity followed by unitness and returns equality to one. The contradiction orientation is correct.

Every obstruction polynomial is monic of positive degree; its displayed highest-degree coefficient is one. Therefore the coefficient comparison against the constant polynomial one establishes the required nonidentity. The explicit factors need not be irreducible, and the file does not require irreducibility.

### Polynomial and finite tactics

The characteristic-two statement `CharP.cast_eq_zero (K[X]) 2` occurs verbatim in the already supplied `N13GoodCoordinateRingTwo.lean` source, including line 114. All polynomial identities were independently checked as above. The coefficient proof structure splits finite indices and applies ordinary coefficient formulas and numerical simplification. The zero-norm case derives that a nonzero product is zero, using the correct direction of `zero_dvd_iff`.

The 138 explicit row-level `decide` calls cover 69 concrete six-index bound checks and 69 concrete `ZMod 19` code equalities. The remaining proof-level `decide` is after the two-element scalar case split. No polynomial divisibility proposition is passed to `decide`. The original scalar `decide` within `jetOrder` is unchanged.

## Verification boundary

No Lean executable, build, project runner, cache executable, kernel check, or axiom audit was run. Only source reads and standalone independent arithmetic/text checks were performed; no remote write was made. Elaboration, tactic execution, resource sufficiency, and kernel/axiom acceptance remain for the lead. In particular, static algebraic correctness does not prove that all `norm_num`/`linear_combination` and coercion elaboration steps execute successfully.

## Reproducible review artifacts

Review artifact paths below are relative to this artifact directory:

- `independent_certificate_audit.py`
- `independent_certificate_math.json`
- `independent_source_literal_audit.py`
- `independent_source_literal_audit.json`
- `Mathlib_Coprime_Basic.lean`
- `Mathlib_Coprime_Basic.receipt.json`
