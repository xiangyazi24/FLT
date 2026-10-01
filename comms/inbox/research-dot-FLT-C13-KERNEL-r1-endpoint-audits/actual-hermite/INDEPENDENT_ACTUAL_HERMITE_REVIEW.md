# Independent source review: actual Hermite equations

No concrete mathematical, transport-sign, premise, or pinned-API defect found in the current frozen `N13ActualHermiteEquations.lean`: 108 lines, 5,108 bytes, SHA-256 `7825b13ddc6a5ce4a623996089eb8684c88e0df991f42345a2f4783335789f02`. Six declarations remain uncompiled. No Lean, build, project execution, axiom check, or remote write was performed.

This review uses `k2-actual-hermite-current-review-manifest.json`; the earlier similarly named manifest has a superseded pre-sign-fix hash and is not the reviewed version. The good-shape dependency is the corrected `094cc2f034f0832132b31754960e81e76d6058a37246c1ecd4e396485d3c397f` version, not its original inclusion-orientation error.

Base framework pin `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`, with operative accepted dependency overlay `940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5`; Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, Lean v4.31.0-rc2.

## Actual point and tangent transport

The module defines x,y,s by applying the actual coefficient inclusion ℤ_[2]→ℚ_[2] to the already constructed disk x-coordinate, opposite ordinate, and integral opposite-sheet slope. Its curve and tangent lemmas are the images of the exact prior opposite-curve and slope equations. The curve's rhs `(x²+x)*x³` is correctly rearranged to x⁵+x⁴; the tangent's coefficients 2,3,4,5 are transported by map_ofNat. No arbitrary generic tangent or unrelated point is substituted.

The actual mapped u polynomial vanishes at both mapped disk points by `eval_map_apply` and the pinned disk-root lemmas. The good opposite graph is `V=-h-map(v)`, so it evaluates to the same mapped opposite ordinate by the disk interpolation-value lemmas and coefficient-map compatibility. These are the exact u,v point hypotheses required by the reviewed dual-number detector.

## Conjugate graph and quotient/remainder sign

Let p=map(P.v), U=map(P.u), and W=completedGraph(p)=2*p+h. The actual sextic graph of the disk pair is W modulo U, and its conjugate has graph `-(W % U)` with unchanged U.

The good opposite graph V=-h-p completes to `2*V+h=-W`. To compare its sextic ideal with the actual conjugate, the proof uses the congruence

`(-W)-(-(W % U)) = U*(-(W/U))`.

The pinned `EuclideanDomain.mod_add_div` reads `W%U + U*(W/U)=W`. The current candidate's positive `linear_combination h` proves exactly the displayed negative-quotient identity. The sign and quotient witness are correct. No evaluation denominator or coprimality assumption is needed.

The actual `sextic_mumfordIdeal_eq_of_dvd_sub` takes divisibility of the difference of graph polynomials, with precisely this orientation. Mapping the resulting ideal equality back through toGood uses toGood∘toSextic=id on GoodRing, matching the coordinate equivalence's declared direction. The final `change` is justified by the exact definitions of conjugateSemiMumford, the mapped u, and the reduced completed graph. Thus the source theorem transports the actual conjugate graph, not an unreduced surrogate.

## Squared ideal to four actual equations

The input hmem is the retained single product membership `(I(Q)*I(B))*J(P)²`. The current code correctly uses `Ideal.mul_le_left hmem` to select its right factor J(P)². Exact pinned Mathlib `Ideal.mul_le_left : I*J≤J` confirms the orientation; this version incorporates the naming correction detected in the prior good-shape review.

Mapping that same element through toGood, `Ideal.map_pow` and the proved conjugate-graph identity give membership in the square of the actual good graph ideal `(U,y-V)`. Substituting the supplied same-numerator shape `gx((X²+X)*A)+gx(b)*gy` makes it directly eligible for the dual-number theorem.

For each j:Fin 2, the code supplies the actual x,y,s, their proved curve/tangent relations, and the proved U/V evaluation facts. The detector gives:

* value: `(x²+x)*A(x)+b(x)*y=0`
* derivative: `(2*x+1)*A(x)+(x²+x)*A'(x)+b'(x)*y+b(x)*s=0`

The product differentiation is correct, including the derivative of X²+X and the ordinate slope term. These yield exactly two value and two derivative equations. The proof does not require A to be monic or impose coefficient degree bounds; those are separate properties of the selected numerator supplied by other modules. It likewise does not replace the numerator or its witnesses when applying the point detector.

## Source/API checks

Inspected pinned sources:

* `N13TwoAdicAbelChartData`: exact u root and v interpolation-value equations at both disk points
* `N13TwoAdicMumfordTransport`: coefficient inclusion, polynomial mapping, actual sexticSemi fields
* `N13GoodSexticMumfordTransport`: completedGraph=2*v+h; generalized-to-sextic ideal image; graph congruence via divisibility; reduced graph=W%U
* `N13GoodSexticCoordinateEquiv`: inverse map and its composition orientation
* Prior reviewed actual opposite-curve/slope lemmas, corrected good-shape aliases, and dual-number graph-square detector
* Mathlib `Ideal/Operations.lean:287`: correct right-factor inclusion
* Mathlib `Ideal/Maps.lean:652`: map of an ideal power is the power of the mapped ideal

Two additional complete Mathlib sources were fetched at the stated pin and their Git blobs checked:

* `Polynomial/Eval/Defs.lean:575`: evaluation of a mapped polynomial at a mapped scalar
* `EuclideanDomain/Defs.lean:133`: mod_add_div with the exact remainder/dividend orientation used above

Current candidate, all three new direct dependencies, and the relevant original transport captures were independently rehashed. The machine-readable receipt records the corrected good-shape hash and current actual-Hermite manifest, preventing accidental substitution of either older draft.

Lean still must check definition unfolding through the conjugate/reduced graph, scalar-map simplification, the linear_combination proof, and the final derivative simplifier. No elaboration or kernel-acceptance result is claimed.

## Remaining interface

This module derives the actual four Hermite equations from the actual principal-derived numerator's retained product membership and good shape. It does not yet prove its A leading coefficient nonzero, perform scalar normalization, identify its coefficients with the uniquely solved integral Hermite coefficients, or identify its residual polynomial with the actual selected double. Those remaining links are substantive; K2 is still open.

Final artifact hashes are in `REVIEW_RECEIPT.json`.

## Accepted dependency update during review

The author synchronized five active dependencies to the lead-accepted 940dc5 commit while this review was being finalized. Their bytes/Git blobs were reverified, and the full supplied proof-only diff plus the PrimitiveChartTransport diff were inspected. No statement or premise change was found. The direct HermiteResidualDivisibility dependency now has SHA-256 `7ac7d80ce7e37d0b850c9c874d2b90fd99810421e95674246d321f22b3566712`; the current 108-line candidate and other geometry drafts are unchanged.

The supplied lead receipt reports that the first four K2 arithmetic modules build and eleven checked theorem axioms are the standard three; K1 remains queued. That is an external compiler receipt for those accepted versions, not a reviewer-run build and not acceptance of this 108-line geometry adapter. It does not close the actual K2 endpoint. Earlier uncompiled source-review snapshots remain historical records of their original bytes.
