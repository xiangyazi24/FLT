# Independent source review: normalized Hermite residual

No concrete mathematical, premise, coefficient, or pinned-API defect found in `N13NormalizedHermiteResidual.lean`: 105 lines, 4,646 bytes, SHA-256 `dba1627201b7df1e9073b7d28b4be237dddde3216c2e0432d1da94a396ed51f2`. Its six declarations remain uncompiled. No Lean, build, project execution, axiom check, or remote write was performed.

This is a separate delta review. The prior 270-line arithmetic and 281-line numerator/divisibility reviews remain unchanged. Source pin `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`; Mathlib pin `96fd0fff3b8837985ae21dd02e712cb5df72ec05`; Lean v4.31.0-rc2.

## Checked argument

1. The actual coordinate ideal is the span of x₀ and x₁+1. Both are in the two-adic maximal ideal by `DiskPair.coord_mem_maximal`, so the span is contained there. This uses the actual chart ideal, not a newly assumed smallness predicate.
2. If b₁ belongs to I², it belongs to I and hence the maximal ideal. The difference `(1-b₁)-1=-b₁` belongs to the maximal ideal. The existing local-ring lemma therefore proves 1-b₁ is a unit. No claim that it is literally 1 is made.
3. The displayed expansion of the residual has degree at most six, with degree-six coefficient exactly 1-b₁. I independently expanded all seven displayed coefficients using symbolic polynomial algebra; their difference from the residual is identically zero. In particular, the correction to the leading coefficient comes from the degree-six term `-A*b*h`, while `-b²*X³` has degree at most five.
4. The unit leading coefficient is nonzero in the concrete two-adic integral domain. Together with the degree bound, this proves residual natDegree=6. The factorization residual=u(P)²*q then forces q≠0.
5. The actual u(P) is monic of degree two. The degree product and power identities, with both factors nonzero where needed, give 6=4+natDegree(q), hence natDegree(q)=2.
6. Taking leading coefficients in that exact factorization and canceling the monic factor gives leadingCoeff(q)=1-b₁. This is monic-leading-coefficient computation, not an assumption of scalar normalization.
7. Let v be the actual unit with value 1-b₁. The candidate chooses Q=C(v⁻¹)*q. Its leading coefficient is 1 by `Units.inv_mul`; multiplication by a unit constant preserves degree two. Reassembling the factors using `C(1-b₁)*C(v⁻¹)=1` yields exactly `residual=C(1-b₁)*u(P)²*Q`.
8. `exists_monic_residual` uses the previously constructed integral coefficients and q, preserving the same b₀,b₁,a₀,a₁ normalization facts. It adds monicity, degree two, and the actual unit factor without asserting a Picard-class or selected-family identification.

All ring/domain requirements are satisfied by the actual coefficient ring ℤ_[2]. No quotient-ring domain assumption, division by 2, coordinate denominator, or base-polynomial evaluation is introduced.

## Exact APIs

Existing pinned source declarations checked:

* `N13TwoAdicAbelChartData.DiskPair.coord_mem_maximal`, lines 447–453
* `N13TwoAdicAbelChartPic.DiskPair.u_natDegree`, lines 45–51
* `Ideal.mul_le_left` and the previously reviewed local-ring `isUnit_of_sub_mem_maximal`
* `Polynomial/Degree/Operations.lean:69`: natDegree equality from a degree bound and nonzero top coefficient
* `Polynomial/Degree/Operations.lean:365`: `leadingCoeff_monic_mul`
* `Polynomial/Degree/Operations.lean:398`: unit constant multiplication preserves natDegree
* `Polynomial/Monic.lean:60`: monicity from scalar times leading coefficient equal to one

Newly fetched complete Mathlib source files were verified against their exact-pin Git blobs:

* `Polynomial/Degree/Domain.lean`: `natDegree_mul` at line 37 and `natDegree_pow` at line 54, with the no-zero-divisors/nonzero premises used by the candidate
* `Tactic/ComputeDegree.lean`: `compute_degree!` at lines 454–472, supporting a natDegree upper-bound goal and normalizing its arithmetic side goals

The `compute_degree!`, polynomial coefficient simplification, rewriting through `leadingCoeff`, and final `omega` still require Lean execution. This source audit is not parser, elaborator, tactic-resource, or kernel acceptance.

## Boundary of the result

The output Q is an integral monic quadratic residual obtained from Hermite interpolation. This file does not identify Q with the actual recovered polynomial of the selected double, construct its graph ordinate, or match its numerator to the actual principal multiplier. Those geometric interfaces remain open. No K2 closure or separatedness claim follows from this file alone.

`SOURCE_IDENTITIES.json` and `REVIEW_RECEIPT.json` record the frozen candidate, its unchanged prior candidates/audit reports, exact source pins, and final artifact hashes.
