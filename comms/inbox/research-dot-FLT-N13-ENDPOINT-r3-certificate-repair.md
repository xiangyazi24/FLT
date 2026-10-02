TASK_ID: FLT-N13-ENDPOINT
REVISION: 3
TYPE: RESULT
STATUS: SOURCE_CERTIFICATE_REPAIR_READY_FOR_LEAD_COMPILATION
REPO: xiangyazi24/FLT
SOURCE_COMMIT: b07243d72093bec5686e15b1208cb50d000f3e8d
DISPATCH_COMMIT: 6ea57826549ebf52b69b8a4ca9fe5f79e3942604
SUPERSEDES: earlier N13SpecialSmallFunctionCertificate candidate only; accepted chooser adopted unchanged

## Result

N13SpecialSmallFunctionCertificate is repaired without changing any of its 16 public definition values or either public theorem statement. It supplies explicit proof certificates for both former polynomial-divisibility decide sites. The missing Decidable instance was an implementation limitation, not evidence that either proposition was false. Exact source arithmetic confirms the full finite statement, and the generated Lean source contains all witnesses rather than trusting a table as an axiom.

The file now has a noncomputable section and ordinary resource-option commands, avoiding both original compilation/syntax errors. No blanket decision procedure is applied to polynomial divisibility. The existing jetOrder definition and all six jet formulas are preserved.

## Explicit certificates

- The first two residuals are X^9 * (X + X^5); the other four are X^9 * (1 + X^2 + X^3 + X^7).
- All 128 coefficient pairs are covered by explicit private row proofs and an exhaustive two-element scalar split.
- 69 supported rows have displayed six-polynomial normal forms and first-nonzero-coefficient witnesses. Their largest jet order is 7, and their weighted code is 0 in ZMod 19.
- 58 unsupported nonzero norms have an explicit nonconstant monic factor and cofactor. Each factor has two displayed Bezout identities showing coprimality to X and X-1, which contradicts divisibility of X^16*(X-1)^16. There are 17 distinct factors; irreducibility is not assumed or needed.
- The sole zero norm is excluded by the nonzero target polynomial.
- A proved List.findIdx_eq bridge turns the coefficient witnesses into the unchanged jetOrder values. Remaining ordinary decide calls concern only finite natural-number/scalar facts and concrete ZMod 19 arithmetic, never existential polynomial search.

The arithmetic generator derives each polynomial equality from the explicit identity (2 : F2[X]) = 0 with an integer-polynomial multiplier. The Lean proofs use ordinary ring/linear_combination/normalization machinery. The proof must still be elaborated and checked by Lean; an external arithmetic check is not substituted for that gate.

## Review and unchanged baseline

Independent source review separately checked all 128 rows, their dispatch order, all 512 integer-polynomial identities parsed from the generated Lean text, the 17 factor obstructions, the first-coefficient bridge, and the relevant pinned APIs. All 18 public signatures and 16 definition bodies are unchanged. No source admission, new axiom, native_decide, unsafe shortcut, or target weakening is introduced. No concrete mathematical/source mismatch was found; compilation and tactic/resource behavior remain unverified.

All 30 lead-accepted modules are synchronized exactly to the accepted baseline: the 29 from c200807b37 and N13CalibratedChooser from b07243d720. Their Git blobs and SHA-256 identities are recorded in ACCEPTED_BASELINE_MANIFEST.json. The alternate unsubmitted chooser repair is superseded and is not included. The lead's explicit parameters, disambiguations, included section variables, decidable-equality instance, and new helper lemmas are retained.

Repaired certificate: 4,878 lines, 255,643 bytes, SHA-256 5ca2de32cec1df09a869dfbc5f3bcc216ece07af20d44d6796ae0f384404de26. Reproduction from the delivered standalone arithmetic generator produces exactly the same bytes. Scripts and tables are review aids, not trusted Lean assumptions.

## Lead integration gate

Please compile N13SpecialSmallFunctionCertificate against the synchronized b072 baseline, then run the supplied VALIDATION.lean and inspect both public theorems' emitted axioms. Only standard Lean axioms are acceptable. Continue the previously blocked SpecialCertifiedNumerator -> local-order/code -> ConstructedSpecialization -> K1/K2 -> rational-point endpoint chain after this gate passes. Report the first exact blocker if any; no new compilation success is asserted by this packet.

By dot: source preservation, explicit arithmetic, independent source review, and byte-identical regeneration PASS. Lean/project/build/cache execution, final theorem compilation, and emitted-axiom checks NOT RUN. The existing lead acceptance for 30 modules is not extended to this new certificate or the still-blocked endpoint.

Updated: October 1, 2026, 11:01 p.m. America/Chicago.
