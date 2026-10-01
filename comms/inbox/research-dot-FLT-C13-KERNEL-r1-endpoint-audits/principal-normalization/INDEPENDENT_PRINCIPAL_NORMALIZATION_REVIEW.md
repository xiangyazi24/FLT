# Independent source review: actual principal/Hermite normalization

No concrete mathematical, premise, scalar, or pinned-API defect found in `N13PrincipalHermiteNormalization.lean`: 139 lines, 6,763 bytes, SHA-256 `fd8d5f776c829a9bbd802eb61388c1456554cc478839c8f5348ddb4de72f7165`. Four declarations remain uncompiled. No Lean, build, project execution, axiom check, or remote write was performed.

Operative dependency baseline `940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5`; original framework `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`; Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Lean v4.31.0-rc2. The current rational matrix and actual-Hermite adapters are unchanged from their reviewed hashes, and the corrected good-shape version is retained.

## Polynomial coefficient reconstruction

`quadratic_eq` proves that every polynomial of natDegree≤2 is its coefficient-2, coefficient-1, and coefficient-0 expression. `linear_eq` similarly reconstructs a polynomial of natDegree≤1. Both proofs check the small coefficient indices and use coefficient vanishing above the degree bound elsewhere. They do not presume the top coefficient is nonzero and therefore correctly include lower-degree and zero polynomials.

The following evaluation and derivative identities have the correct order and constants:

* A(x)=t*x²+a₁*x+a₀, where t=A.coeff 2
* A'(x)=2*t*x+a₁
* b(x)=b₀+b₁*x
* b'(x)=b₁

These are derived from the polynomial equalities, then substituted into the same actual Hermite equations. The coefficients enter the rational matrix theorem in its exact `(a₀,a₁,b₀,b₁)` order, with leading scale t=A.coeff 2. The supplied derivative coefficient is 2*t*x, matching the previous system.

## Matching and retaining the integral witness

The reviewed rational comparison yields one integral normalized solution d₀,d₁,e₀,e₁ satisfying

`a₀=t*c(d₀), a₁=t*c(d₁), b₀=t*c(e₀), b₁=t*c(e₁)`.

Using the explicit coefficient reconstructions and polynomial-map identities, the candidate obtains exact polynomial equalities

`A=C(t)*map(quad(d₀,d₁))` and `b=C(t)*map(lin(e₀,e₁))`.

The normalized quad is monic by its explicit definition X²+d₁X+d₀; its leading term maps to X². No extra leading coefficient is introduced or omitted by coefficient base change. All four original I(P)² bounds remain attached to this same d₀,d₁,e₀,e₁ witness.

At this stage no inverse of t has been used. If t=0, the two proved polynomial identities force A=0 and b=0. The explicit hypothesis `A≠0 ∨ b≠0` in `normalize_shape` therefore proves t≠0. This is valid even though the initial degree bounds allowed lower degree: the equations plus nonzero pair now force a genuinely quadratic A.

## Actual numerator discharges the nonzero-pair premise

`normalize_actual_numerator` takes the same actual nonzero generic coordinate-ring numerator n, its degree-bounded good shape, and its full double/base times conjugate-square product membership. The actual-Hermite adapter derives the two value and two derivative equations from these exact hypotheses.

The only extra premise needed by the general normalization lemma is the nonzero pair A,b. If both were zero, the supplied shape would give toGood(n)=0. The inverse of the actual GoodRing-to-SexticRing equivalence is toGood, and its injectivity gives n=0, contradicting the caller's actual nonvanishing. The equivalence direction is correct: n belongs to the sextic generic ring, and its image belongs to the good generic ring.

Thus the final actual-numerator theorem proves t≠0 rather than assuming it, while retaining exact polynomial matching and all integral I² data. It neither chooses another divisor/class nor swaps to a separately selected numerator. It does not yet invert t; a later field-unit construction may now do so legitimately.

## Exact source/API checks

The coefficient/degree and polynomial map/evaluation APIs were checked against the previously retrieved Mathlib-pin sources. The inspected APIs include coefficient vanishing above natDegree, coefficient projection of C-multiples and powers of X, polynomial map on sums/products/powers/C/X, and the product/power derivative formulas. The interval_cases/simp/ring/omega methods are available through the actual Mathlib import closure.

The direct `N13RationalHermiteMatrix.coefficients_are_scaled_integral` statement was checked for coefficient order and all four ideal facts. The actual-Hermite statement matches the same x,y,s and polynomial shapes. The explicit quad/lin definitions come from the accepted residual module. The good/sextic equivalence's inverse function and injectivity agree with the final cancellation argument.

The current source manifest, direct adapters, corrected good-shape module, and accepted five-file 940dc5 overlay were rehashed. Identities are recorded in `SOURCE_IDENTITIES.json`. No admissions or unsafe/native evaluation occur outside comments.

Lean still must validate the coefficient simplifier cases, rewriting through local equalities, scalar map normalization, duplicate local-name shadowing, and final equivalence coercion. This source review is not an elaboration, resource, axiom, or kernel-acceptance result for the new module.

## Remaining norm interface

The actual degree-bounded principal numerator is now matched up to a proved nonzero generic scalar to one integral normalized Hermite shape. This is not yet the exact integral norm factorization with the actual selected doubled polynomial. The scalar in that norm, its descent, and the resulting actual residual identification remain to be supplied. Actual K2 remains open until that norm/endpoint chain is established and reviewed.

Final artifact hashes are recorded in `REVIEW_RECEIPT.json`.
