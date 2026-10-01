# Independent source review: FLT K2 Hermite and norm arithmetic

## Result and frozen scope

No concrete mathematical, premise, sign, or pinned-API defect found in the two frozen candidates. This review supports the stated conditional arithmetic lemmas. It does not establish the actual K2 first-jet comparison, a principal-numerator producer, residual-divisor identification, or kernel separatedness. Lean elaboration, tactic execution, compilation, and axiom checks were not run. No remote writes or project executions were performed.

Reviewed exactly:

* `N13CenteredHermiteFirstOrder.lean`: 148 lines, 7,043 bytes, SHA-256 `a8f7366c0574f3d068e8360187f3b0c9bb3eeca25d089e4086326d57665a63e3`
* `N13CenteredNormFirstOrder.lean`: 122 lines, 5,757 bytes, SHA-256 `b1340eb7b4415573f1985e6675d4777186964dc255871a00261aaa7742740907`

Together: 270 lines, ten theorem declarations including three private helpers. No sorry/admit/axiom/unsafe/native_decide token occurs outside comments. These files contain no executed axiom report. Neither file was edited by the reviewer.

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`. Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`. Lean toolchain: `v4.31.0-rc2`.

The newly added `N13IntegralHermiteNumerator.lean` and `N13HermiteResidualDivisibility.lean` are separate, unreviewed follow-on work and are excluded from this receipt.

## Actual objects and normalizations

`DiskPair` is the actual two-adic Abel chart pair, with x₀ in the maximal ideal and x₁+1 in the maximal ideal. The Hensel-selected ordinates y₀,y₁ are also in the maximal ideal. Its polynomial is `(X-C x₀)*(X-C x₁)`, and the actual coordinate ideal I is the span of `{x₀,x₁+1}`.

The fixed base polynomial is `U=X²+X`. The pinned centered square is `2*u(P)-U`, hence

* constant coefficient `2*x₀*x₁`
* linear coefficient `-2*(x₀+x₁)-1`
* quadratic coefficient 1

Consequently the signs and constant offset in the Hermite conclusion, `a₀-2*x₀*x₁` and `a₁+2*(x₀+x₁)+1`, exactly match the pinned normalization. The centering is at x₁=-1, not at x₁=0.

The curve is `y²+h(x)*y=rhs(x)`, with `h=x³+x+1` and `rhs=x⁵+x⁴`. The opposite ordinate is `-h-y`. Thus for `g=U*A`, the norm of `g+b*y` is `g²-g*b*h-b²*rhs`, exactly the norm premise's two minus signs.

## Hermite module, theorem-by-theorem

1. `cancel_unit_mem` uses ideal closure and the exact pinned `Ideal.unit_mul_mem_iff_mem`. It cancels a unit only; no cancellation of arbitrary nonzero elements in a quotient is hidden.
2. `linear_coeff_mem` subtracts the two evaluations, obtaining `c₁*(x₁-x₀)` in the ideal. The actual chart proves x₁-x₀ is a unit. Unit cancellation gives c₁ in the ideal, then subtracting c₁*x₀ gives c₀. The general lemma explicitly retains its unit-separation premise and works over any commutative ring and ideal.
3. `uBase_eval_mem` factors x₀²+x₀ as x₀*(x₀+1) and x₁²+x₁ as x₁*(x₁+1). This uses the actual two coordinate generators, including x₁+1.
4. `uBase_derivative_unit` compares 2*x₀+1 with the unit 1, and 2*x₁+1 with the unit -1. The two differences are 2*x₀ and 2*(x₁+1), respectively. Neither step divides by 2.
5. `oppositeY_unit` first shows y+h is a unit because h is a unit on each disk and y is in the maximal ideal, then negates it. This covers the actual opposite sheet. The cited local-ring theorem's subtraction orientation is correct.
6. `hermite_coefficients_mod_square` assumes exactly two value equations and two derivative equations, indexed by Fin 2. The polynomial A is built into the equations as `x²+a₁*x+a₀`, and b as `b₀+b₁*x`, so their degree bounds/monicity are explicit in that statement. The slope values are arbitrary elements of the integral coefficient ring; no assertion that they are the actual implicit slopes is proved or assumed by type alone.

The last proof's sequence is valid:

* U(xⱼ) is in I. The value equation and unit opposite ordinate put b(xⱼ) in I, hence both b coefficients in I.
* The derivative equation and unit U'(xⱼ) put A(xⱼ) in I. Subtracting U(xⱼ) gives a linear expression, hence a₀ and a₁-1 lie in I.
* Returning to the value equation, U(xⱼ)*A(xⱼ) lies in I², so b(xⱼ), b₀, and b₁ lie in I².
* The exact derivative rearrangement is `(A+U)*U' = -(b₁*ybar + b*slope + U*(a₁-1))`. Every right-hand term is in I², so A(xⱼ)+U(xⱼ) lies in I² after unit cancellation.
* Evaluating the linear expression with coefficients `a₀-2*x₀*x₁` and `a₁+2*(x₀+x₁)+1` at x₀ or x₁ gives exactly A(xⱼ)+U(xⱼ). Unit-separated interpolation therefore yields the stated two centered coefficient congruences.

All products multiplied into ideal membership are integral. The proof uses no estimate for the slopes beyond their integral type, and no square-ideal membership is presumed for A or b.

## Norm module and nonreduced quotient audit

The two private coefficient helpers are direct consequences of polynomial coefficient extensionality and `Ideal.Quotient.eq_zero_iff_mem`: coefficientwise membership in J is equivalent to zero after the quotient map, and coefficientwise membership of p-q gives equality of the mapped polynomials.

`mapped_u_square` proves the unconditional identity modulo I²:

`u(P)² = U*centeredSquareU(P)`.

It uses the pinned exact identity whose error is `(u(P)-U)²`. The deviation polynomial has linear coefficient `-(x₀+(x₁+1))` and constant coefficient x₀*x₁, both in I. Hence the deviation lies in the coefficient-extended ideal `map C I`; its square lies in `map C (I*I)` by exact ideal-map multiplicativity. `Polynomial.ker_mapRingHom` and the quotient kernel identity turn that into zero after mapping. The code never assumes the quotient is reduced or a domain.

`cross_coefficients_of_norm` has these substantive premises:

* A is monic
* every coefficient of A-centeredSquareU(P) lies in I(P)²
* every coefficient of b lies in I(P)²
* the exact displayed norm factorization holds with its scalar k and the specified P and Q

It does not assume the target cross congruence. Its A congruence is an auxiliary-numerator normalization, not a renamed Q conclusion. The prior Hermite result supplies the two nontrivial A congruences and b congruences when A and b are packaged from its coefficients; that polynomial packaging and the actual norm's production are not themselves supplied by these two modules.

In the quotient ring R/I², put U=map(base), V=map(u(P)), W=map(u(Q)), and Abar=map(A). All four are monic by the exact pinned monic-map theorem. The coefficient premises give bbar=0 and V²=U*Abar. Mapping the norm yields

`U²*Abar² = C(q(k))*(V²*U*W)`.

Leading coefficients on both sides give `1=q(k)`: the left product is monic, and `Monic.leadingCoeff_C_mul` states the right leading coefficient is exactly q(k), including when q(k)=0. The proof does not discard k before proving this fact, and does not assume k is a unit or literally 1 in R.

After substituting q(k)=1 and V²=U*Abar, multiplication by the monic polynomial U²*Abar is canceled to give Abar=W. The cited `Monic.isRegular` requires only a ring, not a domain, reduced ring, or nontrivial ring. Its `.left` field is precisely injectivity of left multiplication. This is safe over the potentially nonreduced quotient R/I². The target mapped cross polynomial is zero, and coefficient extraction gives membership for every coefficient, including the actual consumer's coefficients 1 and 3.

## Pinned API checks

Fetched complete source files at the Mathlib pin and checked their provider Git blobs against locally calculated blob hashes. Important declarations and conditions:

* `RingTheory/Ideal/Defs.lean:75`: `unit_mul_mem_iff_mem I hu`, with the factor order used by the helper after commutativity.
* `RingTheory/Ideal/Operations.lean:275`: `mul_mem_mul` for two ideal-membership facts.
* `RingTheory/Ideal/Maps.lean:68` and `631–641`: `mem_map_of_mem` and `Ideal.map_mul`.
* `RingTheory/Ideal/Quotient/Defs.lean:111`: quotient equality to zero iff membership.
* `RingTheory/Polynomial/Basic.lean:437–442`: polynomial map kernel equals the constant-coefficient extension of the scalar kernel.
* `Algebra/Polynomial/Eval/Coeff.lean:78–81`: `[simp] coeff_map`, supporting quotient coefficient extraction.
* `Algebra/Polynomial/Monic.lean:56–58`: monicity survives a ring homomorphism, including a possibly trivial target.
* `Algebra/Polynomial/Degree/Operations.lean:336–337`: monic leading coefficient after multiplication by C(r), with no nonzero or no-zero-divisors premise. This declaration is in the general semiring section, before the later NontrivialSemiring section.
* `Algebra/Polynomial/Monic.lean:509–516`: monic polynomial regularity under `[Ring R]`, with left/right cancellation fields.

The exact FLT local-ring unit lemma, disk-unit h lemmas, coordinate-ideal definition, actual disk coordinates, base polynomial, opposite-sheet sign, formal deviation identity, and centered-square error identity were inspected at the stated source pin. Source identity records include 126 pre-materialized source entries rehashed across the four validation manifests and twelve newly retrieved exact-pin files, including eight Mathlib modules and four FLT modules.

## Relation to actual K2 and remaining gate

The pinned `N13MumfordCenteredDoublingAdapter.FirstJetDoublingCompatibility.ofCenteredCrossCoefficients` requires the two cross memberships for the actual family P=F.pair(z), Q=F.pair(2•z). The new norm theorem can provide those memberships only after its hypotheses are proved for precisely those representatives. These two modules do not identify any Q as the actual double and do not construct the exact norm factorization from a principal Picard comparison. They therefore do not close that consumer.

No K1 input or kernel-separatedness assumption is smuggled into these arithmetic lemmas. The stronger geometric numerator/norm hypotheses are visible, substantive, and still require actual construction. The separate new numerator/residual modules need their own review; this receipt does not inherit their claims.

Final machine-readable identities are in `SOURCE_IDENTITIES.json`; final artifact hashes are in `REVIEW_RECEIPT.json`. The two candidates remain source-reviewed and uncompiled. No parser, elaborator, tactic-resource, or kernel-acceptance result is claimed.
