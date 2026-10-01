# Independent source review: exact K2 endpoint assembly

## Result, scope, and remaining gates

No concrete local mathematical, same-witness, coefficient-sign, interface, or target-substitution defect found in the two frozen endpoint files:

* `N13IntegralHermiteCoefficientBounds.lean`: 51 lines, 2,057 bytes, SHA-256 `b602bf2369bed4b4370702e81d5b1fee89f3b53e06be305e731e10d1bfc64ad8`
* `N13ConstructedKernelDoubling.lean`: 89 lines, 4,690 bytes, SHA-256 `b8f047e2602aaf639045d4b2de83c8f58c7a89c3f08d78f74a594c722130069c`

The local candidate chain now supplies the exact pre-existing FirstJetDoublingCompatibility interface and ends at the literal actual specialization-kernel separatedness type. These endpoint declarations and the new geometry modules remain uncompiled. A complete import/axiom-closure audit is also not yet established: the defining source of the pre-existing `N18RouteC.Separated.NSeparated` predicate is missing from the tracked operative tree, as detailed below. This receipt must not be described as full kernel acceptance, an unconditional endgame theorem, or a completed dependency-closure audit.

No Lean, build, axiom check, project execution, or remote write was performed by this reviewer. The supplied lead receipt reports builds and standard-three-axiom results for the first four arithmetic modules only. It does not cover this endpoint chain or K1, which that receipt lists as queued.

Operative dependency baseline `940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5`; original framework `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`; Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Lean v4.31.0-rc2.

## Integral coefficient packaging

The private linear-polynomial helper proves coefficientwise ideal membership by handling degree zero, degree one, and every higher coefficient. It does not check only two coefficients while leaving an unbounded tail. quad_monic proves the explicit X²+d₁X+d₀ polynomial monic. lin_coefficients_mem packages the two retained e₀/e₁ memberships directly.

The centered polynomial identity is exact:

`quad(d₀,d₁)-centeredSquareU(P)`

equals the linear polynomial with constant coefficient `d₀-2*x₀*x₁` and linear coefficient `d₁+2*(x₀+x₁)+1`. This matches the pinned definition centeredSquareU=2*u(P)-Ubase and the actual u(P)=(X-x₀)(X-x₁). The two retained centered I² bounds therefore give every coefficient hypothesis of the accepted cross-norm theorem, with the correct signs and offset +1.

## Same-witness selected cross coefficients

The principal/norm integration concern identified during the earlier review is resolved explicitly in this assembly:

1. P is the actual L.pair(z), and Q is the actual L.pair(2•z).
2. `multiplier_of_centered_double` is called once, producing α, its principal ideal relation hα, and both zero infinity orders.
3. `tensor_numerator_mem_product` is called with that exact α,hα to produce n, its full product membership, and the clearing equation. Neither a second multiplier nor an independent numerator is selected.
4. The clearing equation proves n≠0 using α's nonvanishing, the monic u(P), xClass nonvanishing and fraction-ring injection.
5. Both pole lemmas use the same α,n and their matching order/image facts. The resulting coefficient bounds are used on that same n.
6. Base-ideal membership and the good shape are obtained from the retained full membership. The corrected good-shape inclusion lemma is used.
7. `normalize_actual_numerator` receives that same n,A,b and full product membership, obtaining t≠0 and one integral d₀,d₁,e₀,e₁ witness with exact matching and all four I² bounds.
8. Crucially, `norm_of_actual_shape` receives the original hα together with the same α,n and good shape. The earlier existential endpoint that dropped hα is not used here.
9. `descend_actual_norm` uses the matching equalities, t≠0, actual rational norm and the same integral e₁ bound. It returns the exact integral norm with actual P and Q, scalar 1-e₁, and all base factors retained.
10. The accepted `cross_coefficients_of_norm` is instantiated with the explicit integral quad/lin, their proved monicity/coefficient bounds, and this exact integral norm. It proves all cross coefficients lie in I(P)².
11. The final simplification only unfolds I(P), NearBaseFamily.coord, and the fixed P/Q lets. It converts the ideal to the actual `coordIdeal L.coord z`; it does not replace it by the maximal ideal, use Q's coordinate ideal, or change the doubled argument.

There is no compatibility, cross-coefficient, small-numerator, integral-lattice, nonzero-scale, or separatedness assumption added to selected_cross_coefficients. Its generic input is only the existing NearBaseFamily L and z. Each substantive intermediate property is supplied by the reviewed producer chain.

## Exact existing compatibility interface

The existing FirstJetDoublingCompatibility structure is unchanged. Its field is

`∀ z i, L.coord(2•z)(i)-L.squareJet(z)(i) ∈ coordIdeal(L.coord,z)²`.

The endpoint uses the existing `ofCenteredCrossCoefficients` adapter with coefficients **1 and 3** of exactly `u(P)²-Ubase*u(Q)`. The adapter's signs and order match the produced cross polynomial. Its established coordinate reducer and weighted-square estimate give the exact compare field, not a newly defined surrogate property.

The `forFamily` definition has no additional arithmetic parameter. It constructs that exact compatibility for any existing L from selected_cross_coefficients. The concrete `firstJetCompatibility` then instantiates it with the same `N13ConstructedMappedSpecialFamily.nearBaseFamily` constructed by K1. That definition is literally `mappedSpecialFamily.toNearBaseFamily`, so the family required by `.separated` is definitionally the same one; no equality of independently chosen families is presumed.

## Actual kernel target

The K1 alias Kernel is literally `N13ConstructedSpecialization.specialization.ker`. The specialization is the previously constructed additive homomorphism from the rational Picard group to ZMod 19, not an arbitrary map argument introduced by this endpoint.

`actual_kernel_separated` has no explicit hypotheses or target-classification input. Its declared result is exactly

`N18RouteC.Separated.NSeparated N13ConstructedSpecialization.specialization.ker 2`.

It invokes the existing mapped-special-family separatedness adapter on the constructed K1 family and the new concrete compatibility. No K1 or K2 premise is fed back into its own construction. The previous source-reviewed K1 producer supplies the family; its compiler acceptance remains a separate gate.

## Current consumer verification

Fetched the following complete consumer files at the operative 940dc5 commit, verified their Git blobs locally, and compared them byte-for-byte to the prior pinned copies:

* N13RationalKernelDoublingAdapter: blob `c0e58c34b50fda8757398e5b392cdd79af747153`
* N13MumfordCenteredDoublingAdapter: blob `184b11d1a5b4f7d7f3397d3e2865febeeb684c88`
* N13TwoAdicAbelChartSection: blob `5958734242c83788ea2feea99ec28adda3e7e3f9`

Their relevant interfaces are unchanged. The rational-kernel data supply actual Picard realization and its inherited injectivity, and the compatibility adapter supplies the unary doubling law used by their existing separatedness theorem. This is a check of their accessible source signatures and implementations, not a replacement for a complete axiom/import audit.

All sixteen current K2 modules, totaling **1,870 lines**, were frozen in the chain identity receipt. Four are the lead-reported accepted arithmetic versions; the remaining twelve are source-reviewed geometry/normalization/assembly candidates. The five K1 candidate identities were also rechecked. The corrected good-shape hash 094cc2f… is used; its original 671cc695… version and initial superseded review are not part of this freeze.

## Precise source-closure gap

The pinned `N13TwoAdicKernelChart.lean` imports `FLT.Assumptions.MazurProof.N18RouteC_Separated`. An exact fetch of `FLT/Assumptions/MazurProof/N18RouteC_Separated.lean` at 940dc5 returned 404. A successful listing of the same repository directory at that commit contained 660 entries and no such source file; under the N18RouteC prefix it listed only N18RouteC_VariableChangePoints. The author independently confirmed that the original dispatch/operative tracked tree and shared captures contain no copy.

The unchanged adapters do fix the literal endpoint type above. However, the definition/proof source behind NSeparated cannot yet be audited from the tracked sources available here. This is a provenance/import-closure gap, not evidence that separatedness is false or axiomatic, and not a claim that the lead's compiled environment lacks the module. The missing defining source or its pinned provenance must be supplied to finish that part of the source audit.

The broader final reduction-injectivity/endgame closure, including possible use of the target axiom or spread/coherence routes, is a separate follow-on review. No unconditional broader endgame claim is included in this receipt.

## Verification boundary

The two endpoint files contain no admissions or unsafe/native evaluation outside comments. Their local proof wiring and the previously reviewed mathematical chain match the exact frozen interfaces. Full elaboration, theorem axiom reports, import closure and kernel acceptance remain open for the twelve new K2 geometry modules and the K1 chain. The overall status is **source-reviewed endpoint candidate, with compiler and dependency-closure gates still open**.

Evidence is in `SOURCE_IDENTITIES.json`, `K2_CHAIN_FROZEN_IDENTITIES.json`, and `MISSING_SEPARATED_SOURCE.json`; final artifact hashes are in `REVIEW_RECEIPT.json`.
