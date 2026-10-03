# Coarse lower-bound assembly (local, unpublished)

## Result and limit

`N25F_CoarseLowerBound.UNCOMPILED.lean` is a production-shaped, unconditional
candidate for

    deg D ≤ (finrank F₂ L(D) : ℤ) + 4 * (wPolynomialBasisPoleBound25Two : ℤ).

It uses the actual full projective divisor carrier, W-chart ideals, genuine
section submodule, and existing principal shift. There is no new geometric
hypothesis, degree identity premise, `sorry`, or `axiom` declaration.

The actual-geometry import closure is NOT compiled. No such result is claimed
kernel-checked. Source-level assembly is complete; verification is still open.
No GitHub writes, publication, full build, or downloads were performed.

## Degree bookkeeping is derived, not assumed

1. `heightOneEquivMaximal` composes the existing full-atom/height-one inverse
   with the existing full-atom/maximal-ideal equivalence.
2. `heightOneEquivMaximal_val` proves that this composite preserves the
   underlying ideal, using `fullNonBoundaryAtomEquivHeightOne_asIdeal`.
   Thus the quotient fields and F₂ finranks are exactly the same objects.
3. The existing `wChartMaximalIdealDegree` is definitionally that quotient
   finrank. No new residue-degree theorem is required. Alternatively the
   source already exports `residueDegree_fullNonBoundaryAtomEquivHeightOne`,
   which directly aligns the height-one and full-atom weights.
4. `split_boundary_coefficients` and `split_chart_coefficient` unfold the
   existing additive split; they do not substitute a different divisor model.
5. Let C be the actual chart component of E. Reindex −C to height-one primes.
   The exact ideal-count producer supplies its coefficients. The previously
   checked `weighted_sum_eq_of_exact_counts` identifies its weighted sum with
   the existing natural normalized-factor cost.
6. The newly checked `DegreeReindex.sum_neg_reindex` identifies the same sum
   with −chartDegree(C). Together with the existing
   `divisorDegree_eq_boundary_add_chart`, this gives

       deg E = E(X) + E(YZ) + E(Z) − affineCost(I).

7. Domination E ≤ nH makes each natural deficit exact, with H=X+YZ+2Z.
   The three boundary degrees are one. The candidate explicitly defines the
   boundary deficit divisor B and proves its degree, then derives

       affineCost(I) + deg B = 4n − deg D

   for E = affineNonpositiveRepresentative25Two D, using the existing shift
   degree invariance. This is `shifted_affineCost_add_boundary_degree`.

## Dimension chain

The final theorem chooses the actual shift E, a dominating n, and its exact
nonzero integral ideal I. It uses the predecessor's injection inequality

    dim L(nH) ≤ dim L(E) + affineCost(I) + a + b + c,

which already composes the affine quotient cost, identity-on-functions kernel
injection into L(E+B), and three-boundary cost. It combines this with
`four_mul_le_finrank_basePole_add_constant`, the derived degree identity,
and `affineNonpositiveRepresentative25Two_finrank`. Integer cancellation is
`omega`. No kernel surjectivity, Riemann–Roch theorem, or replacement section
space is assumed.

## Dependency/status table

| Dependency | Exact source / declaration | Status for this packet |
|---|---|---|
| Generic negative finite-support reindexing | DegreeReindex.lean / sum_neg_reindex | Newly kernel checked |
| Generic final cancellation | DegreeReindex.lean / coarse_bound | Newly kernel checked |
| Exact count → normalized-factor weighted sum | flt-n25-weighted-reindexing/N25F_ExactCountWeightedSum.lean / weighted_sum_eq_of_exact_counts | Prior checked pinned overlay; reused unchanged |
| Exact ideal construction | flt-n25-total-boundary-cost/N25F_EffectiveAffineIdeal.lean | Prior generic kernel check; unchanged |
| Actual shifted ideal | flt-n25-total-boundary-cost/N25F_ShiftedAffineIdeal.UNCOMPILED.lean / exists_shifted_affine_ideal | Production source only |
| Actual affine quotient cost | flt-n25-affine-regular-lift/N25F_WAffineConditionCost.lean / finrank_basePole_le_kernel_add_weighted_affine_cost | Existing source and prior family evidence; full imports not rechecked |
| Actual kernel injection and combined costs | flt-n25-kernel-section-injection/N25F_KernelSectionInjection.UNCOMPILED.lean / finrank_basePole_le_section_add_cost | Production source only; generic predecessor check is separate |
| Three-boundary cost | flt-n25-total-boundary-cost/N25F_TotalBoundaryCost.lean / finrank_le_sub_three_boundaries | Prior family check; full imports uncompiled |
| Projective degree split | flt-n25-quotient-finite/sources/N25F_ProjectiveDivisorDegree.lean / divisorDegree_eq_boundary_add_chart | Exact source inspected; not rechecked |
| Prime ideal alignment | flt-n25-quotient-finite/sources/N25F_NonBoundaryPrincipalDivisor.lean / fullNonBoundaryAtomEquivHeightOne_asIdeal | Exact source inspected; not rechecked |
| Principal shift, domination, rank and degree | flt-n25-principal-shift/N25F_AffineNonpositiveRepresentative.lean | Existing production candidate; not rechecked |
| Polynomial-window lower bound | flt-n25-polynomial-window/N25F_WPolynomialWindow.lean / four_mul_le_finrank_basePole_add_constant | Existing production candidate; not rechecked |
| New actual index/degree/cost/lower-bound assembly | N25F_CoarseLowerBound.UNCOMPILED.lean | UNCOMPILED production-shaped candidate |

## Checked scope and receipt

PASS generic-final: exit 0, 4.303 seconds including shared-gate wait;
peak child RSS 1,719,196 KiB. Both axiom audits contain only `propext` and
`Quot.sound`, with no `sorryAx`. See generic-final.json and generic-final.log.
Pinned Lean 4.31.0-rc2, Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05;
one CPU/thread, 3072 MiB, 60 active seconds, shared compiler gate.
The first local generic check also succeeded; it is not the formal receipt.

The generic file has no curve, valuation, section-space, or geometric model.
Its checked assumptions are explicit mathematical equalities for arbitrary
finitely supported functions. The production candidate discharges those
assumptions from actual source definitions, but that discharge is UNCOMPILED.
To stage production imports, map DegreeReindex.lean to
FLT/Assumptions/MazurProof/DegreeReindex.lean and remove the .UNCOMPILED marker
from candidate basenames only in a validation overlay. No import stripping
would count as validation of the actual-geometry theorem.

## Remaining frontier

No additional mathematical geometric statement was found missing from the
source producers for this coarse bound. The outstanding gap is elaboration
and kernel verification of the actual import chain (including predecessor
production candidates), not an assumed affine degree certificate. Local
search found no cached .olean for ProjectiveDivisorDegree, KernelSectionInjection,
AffineNonpositiveRepresentative, or WPolynomialWindow, so a resource-bounded
full-geometry check was not attempted. High-degree effectiveness, Picard
finiteness, and root axiom elimination are not established by this packet.
