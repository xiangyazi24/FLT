# Exact-count reindexing and the remaining FLT degree assembly

Local only. No external publication or GitHub writes.

## New checked adapter

`N25F_ExactCountWeightedSum.weighted_sum_eq_of_exact_counts` is valid for a
commutative Dedekind domain R, fraction field K, a nonzero integral ideal I,
a finitely supported integer vector d, and arbitrary integer ideal weights w.
Its sole vector hypothesis is exact equality with every fractional-ideal count.
No nonnegativity, residue finiteness, or quotient dimension assumption is added.
The counts are derived with `FractionalIdeal.count_coe` and
`Ideal.count_associates_factors_eq`; the support bijection is the existing
principal-divisor argument generalized from a principal ideal to I.

`N25F_ExactCountQuotientDegree` reuses the existing
`DedekindQuotientDegree.finrank_quotient_eq_sum_normalizedFactors`, without a
new quotient-dimension proof. It provides finite-field and F2 specializations.
They explicitly require Module.Finite for R/I. The existing actual-W proof
`N25F_WAffineConditionCost.wIdealQuotient_finite` is private; either use the
public weighted-cost inequality directly or the existing public
`N25F_NonBoundaryPrincipalDivisor.wChart_ideal_quotient_finrank_eq_sum`.
Do not claim access to the private finiteness declaration from another module.

## Exact geometric bookkeeping still to assemble

Let E = affineNonpositiveRepresentative25Two D. The existing shifted ideal
packet supplies I with count(I,v) = -E(A(v)). Set d(v) = -E(A(v)), using the
finite-support comap in `N25F_ShiftedAffineIdeal.UNCOMPILED.lean`.
Instantiate the new reindexing theorem with
w(P) = (Module.finrank (ZMod 2) (W / P) : Z).
This identifies the cast of the already checked affineCost sum with
sum_v -E(A(v)) * residueDegree(v). It does not itself identify that sum with
the full divisor's affine contribution: transport through the genuine
nonboundary-atom/height-one-prime equivalence remains to be written and checked.
The existing residueDegree is definitionally the F2 quotient finrank;
`N25F_ProjectiveDivisorDegree.wChartMaximalIdealDegree_fullNonBoundary`
provides its equality with the full atom's degree. The maximal-ideal and
height-one-prime indexing must be aligned explicitly, not silently assumed.

Choose n with E <= nH by the existing domination theorem. H is exactly
[X] + [YZ] + 2[Z], not three equal coefficients. Thus the natural deficits are
  a = (n - E(X)).toNat,
  b = (n - E(YZ)).toNat,
  c = (2*n - E(Z)).toNat.
Domination proves all three differences nonnegative, so their integer casts
are the original differences. The three boundary residue degrees are one.
The split-degree formula must then give
  deg E = E(X) + E(YZ) + E(Z) - affineCost.
Consequently, in integer arithmetic,
  affineCost + a + b + c
    = affineCost + (n-E(X)) + (n-E(YZ)) + (2*n-E(Z))
    = 4*n - deg E
    = 4*n - deg D.
The last equality is the existing principal-shift degree preservation theorem.
Equivalently, use `affineRepresentative_complement_degree` together with
`divisorDegree_eq_boundary_add_chart` for nH-E. This avoids proving a new
product formula or quotient-dimension theorem.

## Remaining section-space bridge

With B = a[X]+b[YZ]+c[Z] and F = E+B, an identity-on-functions linear injection
ker(wSectionIdealQuotient25Two n I) -> L(F) is enough. The established kernel
order inequalities handle affine atoms; membership in L(nH) handles boundary
atoms because F and nH agree there. Zero must be handled separately.
Full equality or surjectivity of these spaces is unnecessary.

Reuse the existing inequalities:
  dim L(nH) <= dim ker(q) + affineCost,
  dim ker(q) <= dim L(F),
  dim L(F) <= dim L(E) + a+b+c.
Then apply the degree bookkeeping above, the existing polynomial-window lower
bound, and principal-shift finrank equality. This assembly is not claimed
proved by the present packet. General RR lower bounds, high-degree
effectiveness, Picard finiteness, and root-axiom elimination remain open.

## Source reuse

- Published affine cost: commit 20f43b99f3a906637e369439c0eab2e78ed1d1b0,
  comms/candidates/N25F_WAffineConditionCost.lean.
- Local boundary-condition packet: flt-n25-boundary-condition-cost.
- Local exact ideal and total-boundary-cost packet: flt-n25-total-boundary-cost.
- Existing reindexing template: flt-n25-divisor-length/
  N25F_PrincipalDivisorQuotientDegree.lean, lines 44-68.
- Existing degree, shift, and H sources inspected under flt-n25-divisor-length,
  flt-n25-principal-shift, and flt-n25-w-basis-pole-bound.

## Import limitations

Both new modules are checked at their intended FLT.Assumptions.MazurProof
module names in a small overlay using pinned cached Mathlib and the unchanged,
previously compiled N25F_DedekindFactorDegree dependency. This is stronger than
an import-stripped family harness, but it is not a full FLT checkout build.
No actual-W geometry module, shifted-ideal adapter, boundary packet import
closure, or final Riemann-Roch assembly was newly compiled here.
