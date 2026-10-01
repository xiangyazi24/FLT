# Independent FLT K2 review: integral numerator and residual divisibility

## Result and status

No concrete mathematical, source-premise, sign, or pinned-API defect found in the frozen 281-line delta. The integral Hermite system is genuinely solved, and its residual has the claimed exact squared factor. These statements do not identify the residual with the actual doubled-family divisor, establish the principal comparison, or close K2. All Lean proofs remain uncompiled; no Lean, build, axiom report, project code, or remote write was run.

Scope:

* `N13IntegralHermiteNumerator.lean`: 131 lines, 5,762 bytes, SHA-256 `b65eef165d6de788ff2b8e1d49910d7c55752be46c772004c853f0a2e28f37d6`
* `N13HermiteResidualDivisibility.lean`: 150 lines, 7,147 bytes, SHA-256 `3b761745e4d65a0064bbbf13882c127b0b6a2658a224448377a0d64498e2a658`

Twelve theorem declarations, including three private helpers, with no admissions or unsafe/native evaluation outside comments. The prior 270-line arithmetic audit and its candidate hashes are unchanged. The separate 105-line `N13NormalizedHermiteResidual.lean` is excluded from this review.

Exact pins: FLT `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`, Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, Lean `v4.31.0-rc2`.

## Four-variable integral system

The unknown vector is `(a₀,a₁,b₀,b₁)`, for A=X²+a₁X+a₀ and b=b₀+b₁X. Write U=x²+x, d=2x+1, and y for the actual opposite ordinate. The value row is `(U,U*x,y,y*x)` and has right side `-U*x²`. The derivative row is `(d,d*x+U,s,y+x*s)` and has right side `-d*x²-U*(2*x)`. Expanding these rows gives exactly the four prior Hermite equations, with no omitted coefficient or sign.

On the special fiber, the actual chart facts are x₀=0, x₁=1, y₀=y₁=0 for the selected sheet. The opposite sheet has ordinate 1 at both points. U is 0 and d is 1 at both reductions. Thus the candidate's residue matrix is precisely

`[[0,0,1,0], [0,0,1,1], [1,0,s₀,1], [1,1,s₁,1+s₁]]`.

Its displayed inverse multiplies on the right to the identity. I independently expanded the matrix product with symbolic s₀,s₁; the identity even holds over the integer polynomial ring, so no special slope values or finite search are needed. The Lean proof's sixteen index cases inspect a literal 4×4 matrix rather than enumerating disk pairs.

`reduce_matrix` uses the actual reduction map and the previously proved reduction facts for the disk coordinates/ordinates. `matrix_det_unit` maps the determinant, obtains a right inverse on the residue matrix, and hence a unit determinant over ZMod 2. The Frobenius-fixed zero-or-one theorem and `ZMod.pow_card` force that determinant residue to 1. The difference det-1 lies in the exact kernel of PadicInt.toZMod, namely the maximal ideal; the actual local-ring unit-lifting lemma then proves det is an integral unit.

The subsequent determinant-unit to matrix-unit to mulVec-surjectivity API chain is exact and applies over the commutative ring of two-adic integers. Solving for the displayed right side supplies integral coefficients. There is no division by 2, by U(x), or by either disk coordinate. No solvability hypothesis is assumed. The last theorem invokes the already reviewed Hermite coefficient lemma on the very same solved coefficients, retaining both value and derivative equations together with their normalization.

## Actual opposite-sheet slopes

For h=x³+x+1 and rhs=x⁵+x⁴, the opposite ordinate is `y=-h-y_selected`. `opposite_curve` proves `y²+h*y-U*x³=0` directly from the actual selected point's curve equation. It uses the correct negative involution for the generalized model.

The vertical derivative is `2*y+h`, which equals `-(2*y_selected+h)`. The selected ordinate lies in the maximal ideal, while h is a unit on each disk. Therefore this vertical derivative is an integral unit, proved by the actual disk lemmas and negation.

The constructed slope is

`(5*x⁴+4*x³-(3*x²+1)*y) * (2*y+h)⁻¹`,

where the inverse is explicitly the inverse of the proved unit in the integral ring. `slope_relation` verifies

`(2*y+h)*s + (3*x²+1)*y - (5*x⁴+4*x³)=0`.

This is the differentiated equation on the actual opposite sheet, with the correct signs and no assumption that a generic-field reciprocal happens to be integral. The use of `IsUnit.unit_spec` and `Units.mul_inv` agrees with the existing chart's analogous delta-inverse construction.

## Residual factor and double zeros

Let A be the constructed monic quadratic, b the constructed linear polynomial, U=X²+X, T=X³, and H=X³+X+1. The candidate defines

`F = U*A² - A*b*H - b²*T`.

Its unconditional `norm_factor` is the exact identity

`Norm(U*A+b*y) = U*F`,

using rhs=U*T. The sign of both subtracted terms agrees with conjugation y ↦ -H-y.

The key root argument does not cancel U(x). At one actual opposite point, put N=U*A+b*y, C=y²+H*y-U*T, and G=A*y-b*T. The exact polynomial identity is

`F*y = G*N - A*b*C`.

Both N and C vanish. The candidate concludes F=0 by multiplying by y and using y≠0, supplied by the proved unit opposite ordinate. The written proof uses `mul_eq_zero` in the two-adic integral domain and resolves its y=0 alternative. It is not a general-ring cancellation theorem, but the concrete coefficient ring has the required no-zero-divisors instance. In particular, it does not infer that U(x) is nonzero.

For the derivative, let D be differentiation in x along the actual integral slope. Differentiating the same identity gives

`F'*y = G*N' + G'*N - s*F - (A'*b+A*b')*C - A*b*C'`.

The candidate's long `linear_combination` has exactly these five terms. Its G' is `A'*y+A*s-b'*x³-3*b*x²`; C' is the proved slope relation. The value and derivative Hermite equations kill N and N', the curve and slope equations kill C and C', and the established residual value kills F. Hence F'*y=0; the same nonzero unit y gives F'=0. I independently expanded this exact identity, the value identity, the norm factor, and the implicit derivative equation symbolically; all residual polynomial differences are zero.

`double_root_dvd` uses the remainder/root theorem twice. Factoring p=(X-Ca)*q and evaluating its derivative at a gives q(a)=0 because the derivative of X-Ca is 1. This introduces no characteristic-zero division or factorial cancellation. It yields `(X-Ca)² ∣ p`.

The actual x₁-x₀ is a unit. The pinned coprimality theorem therefore gives coprime linear factors, and its power lemma gives coprime squares. Combining the two divisibilities in the correct order yields `u(P)² ∣ F`; commutativity and `mul_pow` convert the product to the exact actual P.u. The final witness is `F=P.u²*q` with integral q and the prior coefficient normalization.

This covers x₀=0, x₁=-1, and coincidence with either base x-coordinate. The two moving points remain distinct from each other by the chart's unit-separation fact; the proof does not assume they avoid the base divisor.

## Exact API and source checks

The already materialized API files were independently rehashed against their recorded Mathlib-pin Git blobs. Four additional complete Mathlib source files were fetched at that same pin and their Git blobs verified locally. Key APIs inspected:

* `Matrix/Determinant/Basic.lean:317`: `RingHom.map_det` maps a determinant to that of the mapped matrix.
* `Matrix/NonsingularInverse.lean:127`, `145`, `349`: determinant unit iff matrix unit; right inverse implies determinant unit; mulVec surjective iff matrix unit. The surjectivity equivalence uses a commutative ring, not a field.
* `FieldTheory/Finite/Basic.lean:594`: `ZMod.pow_card` gives x^p=x under Fact p.Prime, supplied for p=2.
* `NumberTheory/Padics/RingHoms.lean:325`: the toZMod kernel is the p-adic maximal ideal.
* `Polynomial/Div.lean:607`: `dvd_iff_isRoot` for X-Ca.
* `Polynomial/Derivative.lean:227`, `479`: product and power differentiation used by the double-root and residual derivative proofs.
* `Polynomial/RingDivision.lean:278`: a unit a-b gives coprimality of X-Ca and X-Cb, with the orientation used in the candidate.
* `RingTheory/Coprime/Lemmas.lean:193–204`: both exponents of `IsCoprime.pow` are implicit and inferred as 2, so the un-applied `.pow` term is appropriate.

The prior arithmetic source identities were rechecked, including the actual disk coordinate definitions and reduction facts, fixedTwo theorem, opposite-sheet unit lemma, formal coefficients, and all 126 prior recorded source entries. The new source identity receipt also records the nine author-captured API files, four newly retrieved exact-pin files, and the unchanged prior audit receipt/report.

No complete Lean import elaboration or tactic execution was performed. The finite matrix norm_num proofs and the long derivative linear_combination remain compiler/resource gates even though their underlying identities were checked independently.

## Remaining mathematical interface

These two modules now construct integral Hermite coefficients and a genuine integral residual factor for every actual disk pair. The endpoint leaves q as an arbitrary residual polynomial witness. It does not prove q monic, its degree, its graph ordinate, its effective divisor, or equality with u(F.pair(2•z)) up to a unit. It also does not prove the principal comparison needed to identify that divisor with the actual double. The later normalization file addresses a separate part of this gap and was not reviewed here.

Accordingly, the prior norm arithmetic cannot yet be applied to the actual doubled family solely from this delta. There is no new kernel-separatedness or K2 premise hiding that gap. The supported result is the exact integral numerator/residual-divisibility construction, source-reviewed and uncompiled.

Evidence: `SOURCE_IDENTITIES.json`, `SYMBOLIC_IDENTITY_RESULT.json`, and the reviewer-owned `symbolic_identity_check.py`. The symbolic script checks only formal polynomial identities, imports no project code, and is not a Lean acceptance test. `REVIEW_RECEIPT.json` records final hashes.
