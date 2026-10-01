# Independent source review: rational Hermite matrix comparison

No concrete mathematical, premise, scalar, or pinned-API defect found in the frozen `N13RationalHermiteMatrix.lean`: 113 lines, 5,439 bytes, SHA-256 `b6be44e4fadd5e511928134e13946684e41e5d42d1f799a7f8eab105c2c241b9`. Five declarations remain uncompiled. No Lean, build, project execution, axiom check, or remote write was performed.

Operative source/dependency overlay `940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5`; original framework pin `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`; Mathlib pin `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Lean v4.31.0-rc2. The accepted integral matrix and slope dependencies are the synchronized versions recorded in the prior actual-Hermite audit, rather than their historical uncompiled drafts.

## Matrix and base change

matrixQ is exactly the coefficient map of the accepted four-by-four integral Hermite matrix, evaluated at the actual integral opposite-sheet slopes. rhsQ is exactly the componentwise coefficient map of its right side. No matrix or tangent system is substituted.

The accepted integral determinant is a unit. A ring homomorphism maps units to units, and the pinned determinant-map identity identifies that image with det(matrixQ). The explicit `change` handles mapMatrix versus Matrix.map, matching the correction in the accepted integral module. The determinant-unit equivalence gives matrixQ a unit matrix.

The pinned `Matrix.mulVec_injective_iff_isUnit` requires a field, supplied by the actual K=ℚ_[2], and finite/decidable matrix indices, supplied by Fin 4. Thus matrixQ multiplication is injective. This step does not assume that a merely nonzero determinant over an arbitrary ring is invertible.

## Four equations with arbitrary leading scalar

The input rational quadratic is `t*x²+a₁*x+a₀` and the linear term is `b₀+b₁*x`. The value rows move the leading contribution t*U*x² to the right. The derivative rows move t*(U'*x²+U*2*x) to the right. These are exactly t times the four accepted right-side entries, in the order `(value₀,value₁,derivative₀,derivative₁)`.

The candidate's coefficient vector order `(a₀,a₁,b₀,b₁)` matches the accepted matrix columns. Its scalar action on the four-vector is coordinatewise field multiplication. The point/ordinate/slope definitions are the actual coefficient-mapped values, so expansion by Fin cases and ring algebra yields `matrixQ*coeff=t*rhsQ` with the stated sign. No assumption about t being nonzero is needed.

## Integral solution and coefficient comparison

`exists_integral_solution` invokes the accepted `exists_normalized_coefficients` at the same P and the actual integral slope. Applying the coefficient homomorphism to its value/derivative equations gives the rational system with t=1. The map lemmas cover powers, additions, products, the derivative constants, and the fixed scalar one. The resulting rational matrix equation has rhsQ with no remaining scale.

All four original I(P)² membership facts remain attached to those integral coefficients: the two b coefficients and the two centered deviations of the monic quadratic. This lemma does not weaken I² to the maximal ideal or discard its dependence on the actual original P.

For an arbitrary rational solution with leading coefficient t, the accepted integral coefficient vector d satisfies matrixQ*d=rhsQ. Linearity gives matrixQ*(t*d)=t*rhsQ. Injectivity identifies the caller's coefficient vector with t*d. Extracting the four Fin 4 entries gives the displayed equalities with exactly the same integral d₀,d₁,e₀,e₁ and all four retained ideal bounds.

No inverse of t is introduced. The t=0 case correctly forces all four rational coefficients to zero. Proving t≠0 for the actual nonzero numerator belongs to the subsequent polynomial-shape matching step, not this theorem. No denominator involving a moving coordinate or point difference is introduced in this comparison.

## Exact APIs

Inspected pinned matrix declarations:

* `Matrix/Determinant/Basic.lean:317`: ring-homomorphism determinant map
* `Matrix/NonsingularInverse.lean:127`: matrix unit iff determinant unit
* `Matrix/NonsingularInverse.lean:360`: mulVec injectivity iff matrix unit over a field
* Newly fetched `Data/Matrix/Mul.lean:794`: `M*(t • v)=t • (M*v)` under the commuting scalar action, satisfied for the commutative field ℚ_[2]

The new matrix-multiplication source was fetched at the exact Mathlib pin and its Git blob `5cdb2a47f5e0a528c16cac3d2469f3516595807c` verified locally. The matrix/determinant source captures, accepted integral matrix and residual slope files, current actual-Hermite dependency, and all five accepted-overlay file identities were rechecked.

The Fin-vector simplifier goals, scalar/coefficient-map reduction, and proof scripts still require Lean. This is not an elaboration, resource, axiom, or kernel-acceptance result for this 113-line module. The supplied lead receipt's earlier four-module acceptance does not include it.

## Remaining interface

The result compares arbitrary rational Hermite coefficient data to an integral normalized solution while retaining the scale t. It does not yet package the actual degree-bounded polynomials into these coefficients, prove their leading scalar nonzero, or identify the actual residual with the selected doubled polynomial. Actual K2 remains open.

`SOURCE_IDENTITIES.json` and `REVIEW_RECEIPT.json` record exact identities and final artifact hashes.
