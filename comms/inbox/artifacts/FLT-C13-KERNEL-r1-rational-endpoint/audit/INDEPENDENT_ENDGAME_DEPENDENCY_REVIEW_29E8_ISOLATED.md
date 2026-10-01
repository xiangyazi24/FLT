# Final bounded source audit: N13 endgame at 29e80 with import isolation

## Current result and limits

The final 40-line rational-point adapter and two-file helper-isolation delta have no concrete local statement or proof-wiring defect found. The updated project import closure is fully resolved at **335 modules**. After stripping nested comments and strings, the source scan found no axiom/sorry/admit token, target-axiom reference, exactSpreadLine reference, or directed import cycle in that closure.

The graph excludes CyclicExclusion13, N13RationalPicardSpreadExistence, N13CoherentDegreeZeroChooser, N18AddCongr, N18ReductionHom, and TateOrder16Cyclic. The earlier missing-source and flagged-file-import issues are resolved for the exact isolated overlay reviewed here.

This is a source/import audit, not a Lean or emitted-axiom result. No Lean, build, project execution, axiom check, or remote write was performed. The new geometry, endpoint and isolation code still need lead compilation and theorem-level axiom checks. The old target axiom remains declared in CyclicExclusion13 until deliberately replaced/rewired by the lead.

Operative pin: `29e80dbc17c5fdf3a194618d65dc0676199e19f5`, plus explicit reviewed construction/isolation overlays. Mathlib remains `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, Lean v4.31.0-rc2. The independently fetched 940dc5→29e80 comparison has exactly 56 additions and no modified/deleted existing file: 55 restored sources and the accepted saturation module.

The 940dc5 audit is retained under `historical-940dc5/`. Its no-admission result was not carried forward without checking the newly available imports. The complete 29e80 graph was recomputed before isolation (337 modules) and after isolation (335 modules).

## Exact frozen delivery overlay

* `N13ConstructedRationalPointTheorem.lean`: 40 lines, 1,628 bytes, SHA-256 `4ba28bc185751f81edf7f8ef1761473d2abdce49b6bdbe5f00ccafc10606a72f`. The only change from the earlier 23ffa48f snapshot is its operative-pin header, verified by reconstructing the original hash.
* Isolated `N13CalibratedChooser.lean`: 177 lines, SHA-256 `8ca422db7b5258e3a60de1379fe0577f2250c862ddc2cecee95c0e159a53ef3f`.
* Isolated `N13EffectiveDataCompatibility.lean`: 124 lines, SHA-256 `ba152c560cc07db0b0a30ab0fe925b7cfadf4a08cdbc354bcd415dabbfdbd751`.

The isolation files are in the separate `flt-c13-endgame-isolation` packet. This closure result requires those exact overlays. Reverting to the historical chooser/effective files restores the flagged imports.

## Local endpoint and exact target

The wrapper's four theorem declarations perform the expected wiring. quotient_kernel_eq applies the existing classifier red_ker theorem and unfolds the constructed classifier to the actual specialization.ker. quotient_kernel_separated transports the reviewed actual-kernel candidate across that equality. The two point-classification theorems invoke the existing CompatibleReduction endgame with the constructed compatibleReduction and precisely that quotient kernel.

Its affine proposition and the old axiom's proposition are identical after whitespace normalization:

`∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X=0 ∨ X=-1`.

There is no additional premise, alternate curve equation, or direct use/import of the target axiom. CyclicExclusion13 was fetched separately for comparison and is not a root of the audited graph. Its old axiom and its optimized-model caller remain unchanged at 29e80. Adding this candidate does not itself replace that declaration or eliminate the old callers' dependency.

## Reduction-injectivity dependency chain

CompatibleReduction.curvePoint_eq_cusp uses proper reduction and cusp compatibility to find a cusp with the same actual classifier value. The quotient embedding gives equality under the actual quotient map. N13ReductionClassifier.n13_reduction_injective supplies actual twoSurjective and the separated quotient kernel to the general finite-target theorem.

The target is finite because the actual image quotient embeds into the finite special classifier set. The proof needs no new special-fiber group law and does not use the optional exponent-nineteen detour. Source two-divisibility makes doubling surjective on the finite target, hence injective there. Iterated halves of a kernel element consequently remain in the kernel. Separatedness kills that infinitely 2-divisible kernel element, proving reduction injectivity. The existing Abel-Jacobi injection then identifies the rational point with its cusp, and the affine wrapper reads the x-coordinate after excluding the infinity cases.

TwoSurjective and separatedness are explicit assumptions of the abstract theorem. The concrete wrapper supplies both from their constructions rather than inserting the final rational-point conclusion as a premise.

## Actual two-surjectivity and finite halves

The actual twoSurjective theorem has no input parameter. For P it uses constructedHalfData P, which retains the chosen low-degree representative D. The constructor obtains full Kummer value 1 from N13GaussianGlobalZeroCarrierDlog.actualKummer_trivial P through the structural/full-Kummer equivalence. The full-gauge coordinate theorem supplies β and a rational unit q for that same representative. finiteIdealGraphRootData_of_full_gauge constructs an actual graph-presented finite ideal root and principal correction; finiteIdealHalfData takes those exact fields. The final equality is P=lowClass(D)=2•finite.half.

The actualKummer_trivial capstone constructs CandidateLocalization. The Gaussian global factorization, named unit squareclasses, and actual normalized-squareclass seam yield aligned zero-carrier coordinates; the dlog calculation proves them trivial locally before the scalar squareclass is erased. Candidate collapse then kills the genuine structural Mumford Kummer map. CandidateLocalization is a filled structure/Prop, not a postulate. “Fake” in fake-squareclass namespace names the mathematical quotient target, not an unproved stub.

The identity-fiber construction normalizes the full gauge with a Gaussian unit, produces Padé data, and treats the genuine zero-scalar and polynomial-rank cases. Every branch returns a finite graph-root witness with a principal correction and literal ideal-square equality. Passing that equality to the oriented quotient leaves an integer infinity component. The explicit N13InfinityHalf Mumford/function calculation supplies the required half of the fixed infinity class and absorbs that component.

This gives a generic half; it does not claim that its generic ideal root extends to an integral normalized lattice. It does not invoke new K1/K2 data for that extension.

The complete twoSurjective subclosure has **106 resolved project modules**, with no missing import and no Constructed-kernel, CoherentChooser, RationalPicardSpreadExistence, or CyclicExclusion13 module. It has no visible cycle back through the new separatedness or spread/coherence construction. It imports abstract two-adic endgame definitions but does not use an assumed separatedness theorem to produce a half.

This is a bounded source-call and premise trace, not a fresh line-by-line mathematical audit of every pre-existing Gaussian arithmetic or roughly 3,000-line Padé/identity-fiber proof. Their global kernel and emitted-axiom checks remain lead-owned.

## Restored separation source and flagged unrelated files

The restored N18RouteC_Separated source has Git blob `9d49862027469b7829bdb31766822574cb5b2d2f` and SHA-256 `157570192a637d365023c493e58d4cf9161a9e281371fefa126f1a58a58f5b6f` at 29e80. It defines InfinitelyNSmulDivisible n x as existence of an n^k-preimage for every k, and NSeparated G n as the assertion that every such x is zero. Its nsmul commutation and strict-filtration separatedness arguments are generic group/Nat proofs, without a target-classification or N13-kernel premise.

Its only import is N18RouteC_PushPull, whose only import is Mathlib. PushPull contains generic additive-group algebra. The restored path therefore does not pull in the rest of the N18 geometric modules.

The three lead-flagged files were fetched independently and checked with comments removed:

* N18AddCongr has an actual sorry at line 303.
* Both raw sorry matches in N18ReductionHom are comments.
* The raw sorry match in TateOrder16Cyclic is a comment.

None is imported by this N13 endpoint. The real admission is not dismissed globally; it is outside the audited graph. OUTSIDE_CLOSURE_FLAG_CHECK.json records their exact identities and line classifications.

The accepted N13InvertibleReductionSaturation addition was also checked at 29e80. Its three edits are proof-only coercion, unfolding and case-splitting repairs; no public statement or premise change was found.

## Import-isolation delta review

The original complete 29e80 graph still imported RationalPicardSpreadExistence and CoherentDegreeZeroChooser. Active construction did not visibly call exactSpreadLine, but strict import exclusion was not satisfied. The two reviewed changes remove both entry edges:

1. EffectiveDataCompatibility replaces mapMumford with its exact defining expression `D.mapCoeffs ratToQ₂ ratToQ₂_injective (map_n13_f ratToQ₂)`, including the same proof arguments. It directly imports InfinityBaseChange and MumfordInfinityBalance. Its necessary RationalPointEndgame declarations remain in its actual transitive import closure.
2. CalibratedChooser removes CoherentDegreeZeroChooser and copies the one elementary mumford_ext helper privately. The copied proof cases on both Mumford structures and simplifies equality of their three non-proof fields.

The exact patches change no public theorem proposition and add no hypothesis. They insert no spread-existence, comparison, additivity, or classification assumption. The same certified effective repair and marked comparison machinery still constructs the chooser and its compatibility data.

With the isolated overlay, both flagged files are absent and no exactSpreadLine reference remains. CoherentChooserSpecification and CoherentChartComparison remain as the required data/specification interfaces. The new certified/marked construction supplies their fields; their names are not an assumed coherence theorem. No source admission or axiom was found in them.

These isolation patches are uncompiled. Their interfaces are unchanged and the source substitutions are exact, but the lead must validate import availability and elaboration on the integrated files.

## Reproducible closure and provenance

The final 335 project modules comprise 274 MazurProof sources matching the 29e80 directory's Git blobs, 4 further FLT library sources fetched at that commit, 37 previously reviewed 2561ea7c overlay modules, 18 current K1/K2/target overlay modules, and the 2 isolated overlays.

All project imports are resolved. Mathlib/standard-library imports are recorded but are not recursively re-audited in this bounded project-source pass. The static parser strips nested comments and strings, follows project imports, matches tracked sources by Git blob, records overlays, and checks cycles. It reads source text only and never executes project code.

The resulting absence of source admissions and specified flagged routes is not a substitute for #print axioms on the integrated final theorem. It establishes availability and visible dependency exclusion under the exact recorded pins/overlays, not validation of every proof term or tactic execution.

## Remaining acceptance work

Integrate the exact isolated overlay and current source additions; compile K1, the new K2 geometry/assembly modules and the 40-line wrapper; run theorem-level emitted-axiom checks, especially the final affine theorem. Only after acceptance should the lead replace/rewire the old CyclicExclusion13 boundary. Its original axiom and callers remain unchanged in the audited tree.

Current status: **source-only wrapper and project-import audit complete for the exact isolated overlay; compiler, theorem-axiom and old-boundary replacement gates remain open**. No unconditional broader theorem or completed axiom elimination is claimed.

## Evidence

IMPORT_CLOSURE.json fixes every source, hash, Git blob, import edge and flag. BOUNDED_TRACE_RESULT.json records the final exclusions and zero missing/cyclic imports. TWO_SURJECTIVE_AND_TARGET_CHECK.json records the 106-module subclosure and exact proposition comparison. ISOLATION_REVIEW_IDENTITIES.json fixes the two patches. REPIn_COMPARE_29E8.json records the add-only comparison. OUTSIDE_CLOSURE_FLAG_CHECK.json distinguishes the unrelated admission from comment matches. REVIEW_RECEIPT.json records final artifact hashes. Earlier results are historical only.
