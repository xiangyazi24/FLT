# Independent source review: actual good-model numerator shape

No concrete mathematical, premise, coordinate-direction, or pinned-API defect found in `N13GoodCenteredNumerator.lean`: 132 lines, 6,173 bytes, SHA-256 `671cc6955a9627182618c4e6759c8411cc67cce01cdfc219da79f3a9f2f5f4ec`. Seven theorem declarations remain uncompiled. No Lean, build, project execution, axiom check, or remote write was performed.

Framework pin `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`, Mathlib pin `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, Lean v4.31.0-rc2. The previously reviewed 96-line pole-bound dependency remains unchanged. Earlier completed review reports were not edited.

## Completion-of-square direction and coefficients

The exact coordinate equivalence is GoodRing ≃ SexticRing: toSextic is its forward map and toGood its inverse. The actual sextic variable maps to `2*y+h(x)` in the good ring. Therefore the same sextic element `p(x)+q(x)*Y` maps to

`(p+q*h)(x) + (2*q)(x)*y`.

The candidate defines goodP=p+q*h and goodQ=2*q, with the correct plus sign and factor 2. Its reconstruction uses the actual sextic coefficient decomposition, the exact xClass/yClass transport lemmas, and ring algebra. No inverse-2 factor is misplaced into this direction of the map.

## Exact graph-ideal transport

The pinned `map_mumfordIdeal_sexticSemi` maps a base-changed good-model graph ideal through toSextic to the actual sextic graph ideal of the disk pair. The candidate applies toGood to this equality and uses `Ideal.map_map` with composition toGood∘toSextic. The equality with the identity on GoodRing follows from `coordinateRingEquiv.symm_apply_apply`, whose direction is correct for the declared equivalence.

The resulting target is the generalized ideal with the actual mapped P.u and P.v. The proof does not replace the completed/reduced sextic v by an unrelated ordinate. Its `change` is justified by the exact definitions of DiskPair.mumford, DiskPair.smoothMumford, baseChange, and sexticSemi.

## Base membership forces the polynomial factor

The actual base pair has good-model polynomial U=X²+X and graph v=0. The candidate uses the actual baseChange of B.smoothMumford and the pinned simp equations for these two fields.

Starting with membership of n in the actual sextic base ideal, it transports the same element through toGood. The generalized membership theorem is exactly

`z∈(u,y-v) ↔ u ∣ coeff0(z)+coeffY(z)*v`.

For the actual base v=0, this becomes U∣coeff0(toGood(n)). Substituting the proved good reconstruction and applying the actual coefficient projection lemmas identifies that coefficient as goodP(n). Thus U divides goodP(n). This is derived from retained base-ideal membership, not supplied as a new divisibility premise.

## Degree bounds and zero cases

The previously derived sextic bounds are deg(p)≤4 and deg(q)≤1. Since h=X³+X+1 has degree at most three, goodP=p+q*h has degree at most four. The constant scalar 2 does not increase degree, so goodQ has degree at most one. This argument takes place over the generic coefficient field ℚ_[2]; it does not assert integrality of arbitrary principal-derived coefficients.

Extracting the exact divisibility witness goodP=U*A gives the desired shape. If A=0, its natDegree is zero and the bound holds directly. If A≠0, U is monic and degree two; the nonzero-factor product-degree theorem gives deg(goodP)=2+deg(A), hence deg(A)≤2. The theorem therefore does not exclude the zero polynomial or assume A monic/nonzero.

The exact resulting element is `gx(U*A)+gx(b)*gy`, with b=goodQ and b of degree at most one. The same n is used throughout.

## Selected family witness preservation

From membership in `(I(Q)*I(B))*J(P)²`, `Ideal.mul_le_left` first gives membership in I(Q)*I(B), and `Ideal.mul_le_right` gives membership in I(B). The nesting is correct. There is no inference of product membership from separate factor membership.

`exists_selected_good_shape` obtains the prior selected α,n once, derives the base membership only to construct the shape, and retains the original full double/base times conjugate-square membership in its output. It also retains n≠0 and the exact field equation `map(n)=α*map(xClass(u(P)²))`. A,b are new polynomial decomposition witnesses of that same n; no separate numerator is substituted.

## Exact sources and API scope

Inspected pinned definitions and signatures:

* `N13GoodSexticCoordinateEquiv`: good/sextic rings; sexticYInGood; toGood and toSextic; xClass/yClass maps; GoodRing-to-SexticRing coordinateRingEquiv
* `N13TwoAdicMumfordTransport`: baseChange returns a generalized SemiMumford over ℚ_[2]; u/v maps; sexticSemi and its graph-ideal image theorem
* `N13TwoAdicAbelChartData`: basePair u/v, smoothMumford u/v projections
* `N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff` at lines 475–490 and its coefficient projection lemmas at lines 157–193
* Mathlib `Ideal.map_map` and `Ideal.map_id`, with the actual composition orientation, plus membership mapping and product-ideal inclusions
* Previously checked polynomial sum/product degree bounds, product-degree equality under explicit nonzero factors, and compute_degree/monicity tactics

The candidate, direct prior dependency, and materialized geometry/direct source captures were rehashed against their exact recorded SHA-256 and Git blob identities. These records are in `SOURCE_IDENTITIES.json`.

Lean still needs to validate definitional coercions through the two coordinate models, simplifier rewrites, coefficient linear-map operations, the degree proof scripts, and resource usage. The source review is not elaboration or kernel acceptance.

## Remaining K2 interface

This module derives the exact degree-bounded good-model Hermite shape for the actual generic principal numerator. It does not prove A is monic, normalize its scalar, show its coefficients integral, derive its four Hermite vanishing equations from the squared conjugate ideal, or identify it with the independently constructed integral Hermite numerator/residual. Those links remain separate. Actual K2 remains open.

Final audit artifact hashes are in `REVIEW_RECEIPT.json`.
