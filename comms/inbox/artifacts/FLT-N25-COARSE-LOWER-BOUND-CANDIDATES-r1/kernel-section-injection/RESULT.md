# Local identity-on-functions kernel-to-section bridge

UNPUBLISHED. No GitHub write. Earlier canceled publication remains blocked.

## Production-shaped source (UNCOMPILED)

N25F_KernelSectionInjection.UNCOMPILED.lean uses the actual W field and full
atom carrier, not a substituted section model. The key theorem
kernel_mem_section consumes the exact existing ideal counts and the published
wSectionIdealQuotient25Two_eq_zero_iff_orders. Its zero branch is explicit.
For boundary atoms it reuses the source section's L(nH) membership. For
nonboundary atoms it rewrites the genuine projective principal coefficient
through nonBoundaryPrincipalDivisor_apply to the real fractional-ideal count.
No additional order hypothesis is assumed.

boundaryFilledDivisor fills the signed deficits n-E(X), n-E(YZ), 2n-E(Z).
Its boundary coefficients equal nH, and its affine coefficients equal E.
The production map kernelSectionMap is the identity on the common-field
function, with injectivity and finrank_kernel_le_filled_section. Domination
identifies the fill with the natural deficits a,b,c. The final source theorem
finrank_basePole_le_section_add_cost composes the existing weighted affine
cost, injection, and three-boundary cost, using only dimension inequality.

No full import check was attempted: the required actual geometry .olean
closure is absent in the cached workspaces. These are production-shaped
proof candidates, not claimed kernel-checked actual-curve results.

## Checked independent mathematics

KernelSectionLinearAlgebra.lean introduces NO curve/valuation/section model.
It proves restriction of any kernel's ambient subtype map into any submodule,
its injectivity, the resulting finite-dimensional inequality, exact integer
casts of natural deficits, and the arithmetic cancellation given the explicit
geometric degree identity. The membership premise is plainly part of this
generic lemma; the production candidate discharges that premise separately
using actual order interfaces. This generic check does not establish that
production discharge.

PASS generic-03: exit 0; 12.227 seconds including gate wait; peak child RSS
2,137,860 KiB. All five axiom audits contain only propext, Classical.choice,
and/or Quot.sound. No sorryAx. Receipt source SHA-256:
09cff9525bbe410872ac500997a46e628a277d01ba36aae151e9c1883a64083f.
The two failed iterations are isolated under failed/ and are not validation.
Exact pinned Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05;
shared gate, one CPU/thread, 3072 MiB, 60 active seconds. No downloads/full build.

## Degree assembly still open

The checked reindex packet proves ideal-count sum = normalized-factor weighted
sum. It does not yet supply the exact affine geometric transport needed to
rewrite the full divisor degree as E(X)+E(YZ)+E(Z)-affineCost. The height-one
prime indexing, maximal ideal indexing, and full atom indexing must be aligned
with the existing residue-degree transport theorem. No unverified equality
is passed off as an assembled result here. Once that identity is checked,
deficit_cost_identity proves the arithmetic affineCost+a+b+c=4n-degD, using
the existing shift degree invariance. General lower bound, high-degree
effectiveness, Picard finiteness, and root axiom elimination remain open.
