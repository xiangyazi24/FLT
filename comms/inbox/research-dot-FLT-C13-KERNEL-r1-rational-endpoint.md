TASK_ID: FLT-C13-KERNEL
REVISION: 1
TYPE: RESULT
STATUS: SOURCE_ENDPOINT_CANDIDATE
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 29e80dbc17c5fdf3a194618d65dc0676199e19f5
SUPERSEDES: none (extends the K1/K2 endpoint delivery; two explicit helper-isolation replacements)

The new N13ConstructedRationalPointTheorem.affine_x_is_cuspidal has exactly the proposition still declared as the N13 arithmetic axiom:

    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1

It supplies the constructed compatible reduction and its actual separated kernel to the existing finite-classifier/two-surjectivity endgame. It adds no mathematical hypothesis and does not import or call the old target declaration. The lead-owned CyclicExclusion13 file is unchanged. Compilation and theorem-level emitted-axiom checks are still required before replacing its old axiom.

## Exact delta

1. N13ConstructedRationalPointTheorem: 40 new lines. The four theorems identify the quotient reduction kernel with actual specialization.ker, transport the constructed separation, and invoke the existing curve/affine endpoints.
2. N13EffectiveDataCompatibility: replace its sole use of RationalPicardSpreadExistence.mapMumford by the identical explicit mapCoeffs expression; import the defining base-change and surjectivity modules directly.
3. N13CalibratedChooser: replace its sole CoherentDegreeZeroChooser.mumford_ext use by the same elementary structure-extensionality proof locally. Every existing public declaration statement is unchanged. The classical chooser fix is retained.

The two replacements remove the helper-only import routes into the flagged exactSpreadLine file. Historical source snapshots remain at commit 2561ea7c66fb30c15416934a7ae513127cb387e1, including chooser SHA256 514c47dedbefede319d8fd87d536d68d50b14790f053c3a34314629231c446c7. This packet includes exact two-file patches and current hashes, so it must be applied as an explicit delta after the earlier packet, not confused with its frozen receipt.

## Preceding reviewed construction

K1 was delivered at c8753dd7e6e7a17557e0fe2ca4dcc9d4a472e483. The translated special divisor is C+B, code 8. The effective raw mark −2 and balanced raw mark −1 are related by the retained +1 twist.

The complete K2 candidate was delivered at fd65ed8d059ad3a195d2162ed87136d0a6e8fd6b (58/58 immutable readbacks). It retains one principal multiplier, its ideal equation, and the same regular numerator through both −4 pole orders, good-model degree bounds, actual opposite-point jets, Hermite scalar normalization, exact norm descent, and centered first-order cancellation. This supplies the unchanged FirstJetDoublingCompatibility and literal actual specialization.ker separatedness.

The lead accepted the four initial K2 support modules at 940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5. The exact accepted dependencies were synchronized, followed by the lead-compiled N13InvertibleReductionSaturation from 45e67c257b399eb8b3a429a2284e60db5c043f2a. This is distinct from acceptance of the uncompiled new K1/K2 geometry or this thin endpoint.

## Independent bounded source audit

The final overlay has 335 fully resolved project imports at 29e80. The independent audit checked the actual twoSurjective → constructedHalfData → Gaussian/Kummer identity-fibre → finite-half route, and found no visible circular use of the new kernel construction. The isolated graph excludes both RationalPicardSpreadExistence and CoherentDegreeZeroChooser. Its source scan found no exactSpreadLine, target-axiom, axiom/sorry/admit token, or directed import cycle. This is a bounded source trace, not a fresh line-by-line audit of all imported arithmetic and not an emitted-axiom report.

The two changed modules retain all 27 existing public declaration statement prefixes byte-equivalently up to whitespace. Their full old/new source patches are included. The endpoint's proposition is textually identical up to whitespace to the existing N13 arithmetic axiom.

## Source restoration and limits

The old 940dc5 missing-source request was resolved by 29e80dbc17, which committed 55 previously untracked files. The exact N18RouteC_Separated source and its generic filtration proof are now available. A direct check confirms an actual sorry remains in N18Block5Instantiation.AddCongr.add_congr, N18AddCongr.lean line 303; the other reported word matches are comments. That N18 addition theorem is outside the constructed N13 endpoint's import graph.

All source scans and audits are text-level checks. They do not replace Lean elaboration, whole-proof mathematical review, or emitted-axiom verification. The supplied validation harness is NOT RUN. No main file, old arithmetic axiom, PR, release, or site is changed by this packet.

## Lead integration gate

After compiling the exact dependency overlay and this packet, run the supplied KERNEL_RATIONAL_ENDPOINT_VALIDATION.lean and inspect the final theorem's axioms. Only after those gates pass should the lead import N13ConstructedRationalPointTheorem in CyclicExclusion13 and replace the existing axiom declaration by a theorem with the identical proposition and body:

    N13ConstructedRationalPointTheorem.affine_x_is_cuspidal

That replacement is not performed here. Existing CyclicExclusion13 downstream declarations then retain their statement and call-site names. Final acceptance and integration remain with the lead.

Updated: 2026-10-01 18:32 America/Chicago.

Independent audit report SHA256: 169341530e27a2cde84572128e7e529d3c3afb769cd327eb882cfe4fa3b390e7. Exact receipt SHA256: 869792c64550d29c21689f88dfc093746d515b93bb3ceb5dce8fec5c31d69bc6. All 13 receipt artifacts were independently rehashed before transfer.
