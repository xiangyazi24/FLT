# Independent source review: exact actual principal norm

No concrete mathematical, multiplier-scalar, norm-sign, or pinned-API defect found in `N13ActualPrincipalNorm.lean`: 109 lines, 5,322 bytes, SHA-256 `2f7d3b5ccbd6c3bfd852cf8fa0df236494cafb8026da0dcc81565f6d84dd47e1`. Four declarations remain uncompiled. No Lean, build, project execution, axiom check, or remote write was performed.

Operative dependency baseline `940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5`; original framework `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`; Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Lean v4.31.0-rc2.

## Exact generic norm and reciprocal scalar

The input principal relation is explicitly the four-factor equality

`I₀*I₁*principal(α)=I₂*I₃`,

and the numerator equation is explicitly `map(n)=α*map(xClass(u₀*u₁))`. The proof uses the same α in both premises.

The previously reviewed scalar norm-ratio theorem gives a unit q in the coefficient field with

`q*(α*conjugate(α))*x=y`,

where x is the function-field image of xClass(u₀*u₁), and y is the image of xClass(u₂*u₃). The candidate keeps both polynomial products intact.

Conjugating the actual numerator equation fixes xClass(x-polynomials) and conjugates α. Since the coordinate-ring norm is n*conjugate(n), its image is `(α*conjugate(α))*x²`. Multiplying by q and using the ratio identity gives q*norm(n)=x*y. The inverse constant d corresponding to q⁻¹ satisfies d*q=1, so norm(n)=q⁻¹*x*y.

The output scalar is correctly **k=q⁻¹**, not q. It remains a unit of ℚ_[2], not an unproved integral unit or the number 1. The proof cancels only this known coefficient-field unit; it never divides by u₀,u₁ or any moving coordinate. Injectivity of the coordinate-ring algebra map into its fraction field, followed by xClass injectivity, lifts the field equality to the claimed polynomial norm identity.

The coercions used for functionConstUnit and conjugateFunctionUnit agree definitionally with their pinned Units.map constructions. In particular, conjugateFunctionUnit's value is functionConjugateEquiv applied to the original field unit value.

## Good-model norm identity

For the sextic decomposition n=p+qY, the good-model coefficients are goodP=p+q*h and goodQ=2*q. The good norm expands as

`(p+q*h)²-(p+q*h)*(2*q)*h-(2*q)²*rhs`

which is `p²-q²*(h²+4*rhs)`. The exact good/sextic polynomial relation is f=h²+4*rhs, so this is precisely the sextic norm polynomial `p²-q²*f`. The two minus signs, factor 2 in the graph coordinate, and factor 4 in the completed-square equation are all retained correctly.

`shape_coefficients` compares the two reconstructions of the same toGood(n). The actual good-coordinate coeff0/coeffY projections recover goodP=Ubase*A and goodQ=b, without assuming a normal-form equality or a different numerator. The free rank-two coordinate-ring projection lemmas justify both components.

## Actual four-factor specialization

`norm_of_actual_shape` substitutes D₀=D₁=P, D₂=Q, D₃=B. The numerator clearing polynomial is therefore u(P)², while the right-hand norm retains u(Q)*u(B). The actual base polynomial is X²+X. After applying the same-shape coefficient equalities and the good/sextic norm identity, the result is exactly

`Norm(Ubase*A+b*y)=C(k)*map(u(P))²*Ubase*map(u(Q))`.

Only commutativity reorders the final base and Q factors. No base factor, square, or scalar is discarded. The theorem is over the generic coefficient field; descending a normalized version to ℤ_[2] is a separate task.

## Same-multiplier integration requirement

The norm theorem correctly requires the principal ideal relation for the same α appearing in the clearing equation. Earlier selected-numerator/good-shape existential endpoints retain α,n, product membership and the clearing equation but do not output that principal relation. Therefore the final assembly must retain it from the original `multiplier_of_centered_double` witness, or reconstruct the entire same-witness chain while keeping it. Independently choosing another multiplier is insufficient. This was flagged to the author during review.

This is an interface obligation for assembling the current lemmas, not a defect in the norm theorem's explicit statement. No principal relation or norm conclusion is hidden as a renamed K2 assumption.

## Exact source/API checks

Inspected exact sources:

* `N13PrincipalBranchBalance.exists_scalar_norm_ratio`, including the order of q, α, conjugate α, and both polynomial products
* `SexticMumfordNorm.norm_eq_xClass_coeff`, norm multiplication, and xClass injectivity
* `SexticFunctionConjugation.conjugateFunctionUnit` and its value theorem, and function-conjugation compatibility with the coordinate algebra map
* `N13InfinityAPI.coordinateConstUnit` and `functionConstUnit` as successive unit maps
* `N13GoodSexticCoordinateEquiv.sextic_eq_h_sq_add_four_rhs`
* Good-model coeff0/coeffY projection lemmas, the actual DiskPair Mumford u map, and actual basePair u
* Pinned fraction-ring algebra-map injectivity and ring-homomorphism/unit multiplication APIs already checked in the preceding reviews

The candidate, direct normalization dependency, relevant original source captures, and branch-balance dependency match their recorded identities. No admissions or unsafe/native evaluation occur outside comments. The machine-readable record is `SOURCE_IDENTITIES.json`.

Lean still needs to validate the unit/coercion simplifier in d*q=1, the change steps through the conjugation maps, and the final polynomial reconstruction. This is not an elaboration, resource, axiom, or kernel-acceptance result.

## Remaining endpoint

The exact norm is established conditionally on the explicit same-multiplier data, with k a nonzero generic scalar. The already matched integral normalized numerator still needs scalar cancellation/descent and comparison with the actual Q polynomial. The final selected-family assembly must also retain the principal relation noted above. Actual K2 remains open until those links and the endpoint chain are proved and reviewed.

Final artifact hashes are recorded in `REVIEW_RECEIPT.json`.
