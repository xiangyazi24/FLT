TASK_ID: FLT-C13-KERNEL
REVISION: 1
TYPE: RESULT
STATUS: K1_SOURCE_COMPLETE_K2_IN_PROGRESS
NONCE: FLT-DOT-20261001
SOURCE_COMMIT: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5
DISPATCH_COMMIT: 05ced4c57c83858c84032b8452b8c47f30ded392
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDENCY_DELIVERY: 2561ea7c66fb30c15416934a7ae513127cb387e1
DATE: October 1, 2026, 4:52 p.m. CDT (America/Chicago)

## K1 result

Five new modules (513 lines) construct the exact endpoint
`N13ConstructedMappedSpecialFamily.mappedSpecialFamily :
N13RationalKernelDoublingAdapter.MappedSpecialFamily
N13ConstructedSpecialization.specialization.ker`.
The endpoint has no mapped-special, near-base, separatedness, or K2 input.

1. Additive specialization and noncanonical code8 force the SAME translated
   chosen witness to have literal special divisor C+B.
2. The reduced infinity ideal contains t-1. Integral-to-special branch
   constant-coefficient compatibility then forces both actual generic
   infinity multiplicities to vanish. The effective graph has degree2 and
   nInf=-1, hence raw mark-2.
3. Vertical saturation identifies the same affine lattice with the canonical
   contraction of its generic graph. Its reduction is exactly the adapter's
   specialIdeal=(X²+X,Y).
4. Balancing the graph changes the raw mark from-2 to-1. The explicit C+B
   base pair acquires the SAME +1 raw twist, establishing the precise
   c+basePic class required by MappedSpecialRepresentative.
5. Existing Hensel graph recovery gives the centered NearBaseFamily.

## Validation and scope

Independent mathematical/source/API-shape review passed after correcting
`sub_right_injective` to `sub_left_injective` in chosen_translated_code.
The original review snapshot is preserved as historical metadata; current
manifest hashes record the corrected source. All five dispatch inputs and
additional source/API captures were verified at exact pins.

Lean compilation, ordinary-decide evaluation, kernel checking, and #print
axioms: NOT RUN. The lead owns all such checks and integration. Earlier
B00/B03 source dependencies remain uncompiled from dot's perspective.
No existing lead source declaration was edited. No main/PR/release/site
action is part of this delivery.

## K2 remains active

FirstJetDoublingCompatibility and actual-kernel separatedness are NOT
claimed. The exact existing N13MumfordCenteredDoublingAdapter reduces K2
to coefficients1 and3 of u(P)^2-uBase*u(Q) lying in I(P)^2. The pinned
GaugeFreedom module proves weightedGaugeJet is surjective; arbitrary
Cech/Picard equality cannot justify applying firstJet.

Current arithmetic work uses a regular numerator N=uBase*A+b*y, A monic
quadratic and b linear. Four actual Hermite equations on the conjugate
disk pair force b=0 and A=2u(P)-uBase modulo I(P)^2. An exact norm identity
then supplies the centered cross coefficients by monic cancellation over
the possibly nonreduced quotient R/I(P)^2. The two arithmetic candidates
are separate from this reviewed K1 batch. Producing that normalized
numerator, its Hermite equations, and exact norm from the actual principal
comparison remains the substantive K2 obligation.

## Files

The five new Lean modules are listed in
`comms/inbox/research-dot-FLT-C13-KERNEL-r1-K1-manifest.json`.
The audit and source identity receipts are under
`comms/inbox/research-dot-FLT-C13-KERNEL-r1-K1-audit/`.
A separate subsequent commit records the immutable result commit and
exact remote readback outcome.
