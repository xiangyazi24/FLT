# Independent source review: actual numerator pole bounds

No concrete mathematical, premise, sign, or pinned-API defect found in the frozen 96-line `N13CenteredNumeratorPoleBounds.lean`, 5,172 bytes, SHA-256 `a29f0961026d3a44e868aefb15307de75f7462707c295eb137c772634cdacffc`. Four theorem declarations remain uncompiled. No Lean, build, axiom check, project execution, or remote write was performed.

Exact framework pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`; Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Lean v4.31.0-rc2. The previously reviewed 154-line principal numerator module is the direct new dependency, unchanged at hash `d67575a8ee276901e15ac41937cb2a916059421d007b1b21da46c5cd40e5af7f`.

## Same-witness Laurent orders

Both order lemmas start from the exact equation `map(n)=α*map(xClass(u(P)²))` and the appropriate zero infinity order of the same multiplier α. They apply the corresponding actual function-field Laurent embedding. Compatibility with the coordinate-ring embedding and the xClass evaluation formulas gives

`Laurent(n)=Laurent(α)*evalPoly(u(P)²)`.

The field embedding is injective, so the image of the unit α is nonzero. The actual u(P) is monic, so u(P)² is nonzero; the pinned polynomial-evaluation theorem proves its Laurent image nonzero. Thus `HahnSeries.order_mul` is applied with both required nonzero hypotheses.

The actual infinity-order definitions use `Multiplicative.ofAdd` of the Laurent order, so the `change` steps converting their toAdd values to order equalities are definitionally correct. At either infinity, polynomial evaluation uses the same X=t⁻¹, and its order is minus the polynomial's degree. The square of the actual degree-two u(P) has degree four. Hence the numerator order is exactly 0-4=-4 at each infinity. There is no swapped sign, omitted square, or use of a different numerator.

The lemmas do not need a separate n≠0 hypothesis because their image equation and nonzero factors already preclude n=0. The selected endpoint nevertheless retains the earlier explicit nonvanishing proof for applying the next theorem.

## Deriving coefficient bounds

`polynomial_bounds` decomposes the actual coordinate-ring element as `xClass(p)+xClass(q)*Y` using p=coeff0(n), q=coeffY(n), and the pinned `recompose` theorem. Nonvanishing is transferred through that exact equality into `N13BranchLeading.branch_min_order`.

That theorem states that the minimum of the two infinity orders is minus

`max (natDegree p) (if q=0 then 0 else natDegree q+3)`.

Its assumptions are a field of characteristic zero and a nonzero coordinate-ring element. They hold here over ℚ_[2]. In particular, its proof that cancellation cannot raise both branch orders uses invertibility of 2 in this generic field, not reduction to characteristic two.

Since both orders are -4, the pole degree is 4, and the candidate only needs its upper bound by 4. It separately handles q=0, avoiding the false contribution natDegree(0)+3. For q≠0, max≤4 gives natDegree p≤4 and natDegree q+3≤4, hence natDegree q≤1. Both coefficient conclusions therefore follow without a caller-supplied small-numerator hypothesis.

`exists_selected_small_numerator` destructures the prior selected-numerator theorem once, applies both order lemmas to the same α,n,image equation, and applies the degree reducer. Its output preserves the original nonvanishing, actual double/base times conjugate-square product membership, and exact clearing equation, while adding the two degree bounds. It does not replace or independently choose any of these witnesses.

## Source and API checks

Inspected exact source definitions/signatures:

* `N13Infinity.laurentOrder`, `infinityOrderHom`, and `positiveInfinityOrder`
* `N13InfinityMinus.infinityOrderHomMinus` and `negativeInfinityOrder`
* Both API modules' fraction-field/algebra-map compatibility and xClass evaluation theorems
* `N13BranchNorm.evalPoly`, `evalPoly_ne_zero`, `evalPoly_order`, and `linearFunction`
* `SexticMumfordBasis.recompose`
* `N13BranchLeading.poleDegree` and the full statement/proof of `branch_min_order`
* Actual `DiskPair.sexticSemi_u_natDegree` and the definitionally identical Mumford u field
* Pinned polynomial power-degree API, already checked in the normalization review

Fetched and Git-blob-verified the complete pinned HahnSeries multiplication source. `HahnSeries.order_mul` at line 1022 takes explicit nonzero factors, exactly as used. Its coefficient no-zero-divisors and ordered-exponent assumptions are supplied by Laurent series over the field ℚ_[2] with exponent group ℤ.

The older exact-pin calibration source captures for BranchLeading, negative infinity, Laurent polynomial order, and the coordinate basis were rehashed against their recorded Git blobs, alongside the corresponding current materialized dependency sources. The new candidate and its principal-numerator dependency match their frozen manifests. Machine-readable identities are in `SOURCE_IDENTITIES.json`.

The proof scripts' coercion reduction, casts, simplification of the zero-q branch, omega goals, and resource use remain compiler gates. This review does not claim Lean acceptance.

## Remaining interface

The result gives actual generic-sextic coefficient bounds 4 and 1 on the principal-derived numerator. It does not yet convert that numerator into the integral good-model Hermite shape, normalize its leading coefficient, or identify it with the previously constructed integral numerator and monic residual. Actual K2 remains open. The next good-model shape module is a separate delta, excluded from this receipt.

Final hashes are recorded in `REVIEW_RECEIPT.json`.
