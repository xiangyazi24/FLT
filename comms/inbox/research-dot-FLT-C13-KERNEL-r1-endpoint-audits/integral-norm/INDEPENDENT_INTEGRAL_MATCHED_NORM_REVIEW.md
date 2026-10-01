# Independent source review: integral matched norm descent

No concrete mathematical, scalar, cancellation, or pinned-API defect found in `N13IntegralMatchedNorm.lean`: 100 lines, 4,958 bytes, SHA-256 `793b58a8f73de5c97a95ffc732c35eb50676d1c30f296a4490b675e908b31d0a`. Three declarations remain uncompiled. No Lean, build, project execution, axiom check, or remote write was performed.

Operative dependency baseline `940dc5a6b4062e8f591ddd744e4f3b8c2b562ea5`; original framework `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`; Mathlib `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Lean v4.31.0-rc2.

## Norm and its leading coefficient

normPoly is the exact integral good-model norm `(U*A)²-(U*A)*b*h-b²*rhs`, with U the actual baseSmoothMumford.u=X²+X. Its coefficient map is the stated generic norm, since the actual h and rhs polynomials have the same coefficients under the inclusion ℤ_[2]→ℚ_[2]. No scalar is inserted by this map.

For integral quad(d₀,d₁) and lin(e₀,e₁), the prior residual identity gives normPoly=U*residual. The residual degree-six coefficient is 1-e₁. The hypothesis e₁∈I(P)² gives the already proved unit property of 1-e₁, hence nonvanishing. The upper degree bound and this top coefficient force residual degree exactly six. Since U is monic, the norm's leading coefficient is the same residual leading coefficient, exactly 1-e₁.

This step does not pretend the normalized norm is monic: the unit correction 1-e₁ is preserved. Its image under the coefficient inclusion is the leading coefficient of the mapped norm because that inclusion is injective.

## Recovering the exact scalar

The hypotheses are the exact actual generic norm with scalar k, the same polynomial matching A=C(t)*map(quad), b=C(t)*map(lin), t≠0, and the retained integral e₁ bound. The target T is the actual integral product `u(P)²*U*u(Q)`. All its factors are monic, so T and its coefficient image are monic. The Q here remains the given actual disk pair; it is not replaced by the independently constructed residual witness.

Every term in the norm is quadratic in A and b. Substituting their matching equalities therefore yields

`C(t²)*map(N)=C(k)*map(T)`.

The code derives this by the exact norm_map identity and ring algebra. Taking leading coefficients gives

`t²*c(1-e₁)=k`.

The left side uses the domain leading-coefficient product theorem over ℚ_[2], and the right side uses monicity of map(T). The field scalar k is not silently set to 1-e₁ before accounting for t².

## Safe cancellation and integral reflection

The constant polynomial C(t²) is nonzero because t≠0 and the coefficient field is a domain. `mul_left_cancel₀` cancels that polynomial only in ℚ_[2][X], giving

`map(N)=C(c(1-e₁))*map(T)`.

The scalar multiplication rewrite uses the exact derived k=t²*c(1-e₁); its direction and associativity match the left cancellation. No cancellation by T, any moving u factor, or an element of ℤ_[2] with an unproved integral inverse occurs.

Finally, the map on polynomial rings is injective because the coefficient inclusion ℤ_[2]→ℚ_[2] is the injective fraction-ring algebra map. Reflecting the equality gives literally

`N=C(1-e₁)*u(P)²*U*u(Q)`

over ℤ_[2]. This is an equality of integral polynomials, not merely equality in a quotient or equality modulo I². It is the norm premise needed by the accepted centered-norm arithmetic theorem, with its integral scalar explicitly retained.

## Exact API checks

Inspected prior pinned sources for the integral unit/degree/coefficient facts, monic product and map lemmas, polynomial map injectivity, and fraction-ring injectivity. In particular:

* `Polynomial/Degree/Operations.lean:693`: leadingCoeff of a product over a no-zero-divisors coefficient ring, as used over the field ℚ_[2]
* `Polynomial/Eval/Coeff.lean:103`: coefficient injection implies polynomial-map injection
* Actual accepted residual norm_factor and the separately reviewed normalization module's one_sub_unit/residual degree-six coefficient

Newly fetched complete exact-pin sources were Git-blob-verified:

* `Polynomial/Degree/Lemmas.lean`: leadingCoeff_map_of_injective, with injectivity supplied explicitly and the polynomial argument inferred by rewriting
* `GroupWithZero/Defs.lean`: mul_left_cancel₀ cancels the left factor under its explicit nonzero hypothesis, matching the proof's factor C(t²)

The candidate, actual-principal-norm dependency, 105-line normalization dependency, accepted centered-norm module, and all five accepted-overlay files were rehashed against their recorded identities. No admissions or unsafe/native evaluation occur outside comments. Records are in `SOURCE_IDENTITIES.json`.

Lean still must validate the norm-map simplification, rewriting through local N/T definitions, leading-coefficient rewrites, and final coefficient-map reflection. This source review does not constitute elaboration, resource, axiom, or kernel acceptance for the new module.

## Remaining assembly

The literal integral norm is available once the explicit same-witness matching and actual norm premises are supplied. The selected-family assembly still must retain one multiplier/numerator and its principal relation, carry the four integral I² bounds, invoke the accepted cross-coefficient theorem for the actual Q, and feed the actual first-jet interface. This file itself does not assert K2 or separatedness. K2 remains open until that endpoint chain is proved and reviewed.

Final hashes are in `REVIEW_RECEIPT.json`.
