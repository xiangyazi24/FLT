# r22 ACK and actual reciprocal rational-base degree four

TASK_ID: FLT-N25-RATIONAL-BASE-INVERSION
REVISION: 22
TYPE: ACK_AND_RESULT
STATUS: INVERSION-ACCEPTANCE-VERIFIED; RECIPROCAL-FINITE-FIELD-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 0b59e35689c95d2a5823e2a40f9a148353d2538b
DISPATCH_COMMIT: bb66dbe5c32ae6225ac178cd496f5306eb2f242c
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continued actual infinity normalization comparison

## Acceptance synchronized

R22 accepts N25F_RationalBaseInversion byte-equal:1608-job build and seven
public definition/theorem audits exactly standard-three. Our earlier
local audit also checked both carrier abbreviations, for nine entries.
I resolved the full accepted SHA and independently verified the bytes.
The actual inversion automorphism is now lead-integrated.

## New actual field action and theorem

Candidate: comms/candidates/N25F_InfinityFunctionField.lean
Namespace: MazurProof.N25F_InfinityFunctionField

The original polynomial base maps its variable to qz in the same actual
CurveField=FractionRing W. Its injective map is extended to BaseField,
the concrete FractionRing(Polynomial F2). The reciprocal rational-base map
is explicitly the old map composed with the accepted baseInversion.
Its polynomial restriction is proved equal to infinityBaseToField,
the already-constructed actual evaluation map t↦1/qz.

The key public theorem is:

    infinityRationalBaseToField_finite_finrank :
      letI : Algebra BaseField CurveField :=
        infinityRationalBaseToField.toRingHom.toAlgebra
      Module.Finite BaseField CurveField ∧
        Module.finrank BaseField CurveField = 4

No finite-extension, coordinate-change or rank hypothesis is added to the
production theorem. The old degree four is derived from the accepted
wChart_finrank_polynomial_eq_four and the actual fraction-ring tower.
A concrete finite basis is then transported along the proved automorphism.
Both scalar actions are kept explicit; no competing global algebra
instance changes the existing qz coefficient action.

This is the finite degree-four common field over the inverted rational
base. It does not yet assert separability for the new action, the integral
normalization, the three-prime classification, or the general product
formula.

## Checks actually run

PASS: generic finite-basis/finrank transport between the original action
and its precomposition with a field automorphism, twist-05:29.222s wrapper
elapsed,2,202,948KiB peak child RSS, standard-three audit.

PASS: actual-curve common-field action comparison, original rank four,
reciprocal polynomial compatibility, and reciprocal finite/rank result,
actual-02:16.316s,2,499,260KiB peak child RSS. All ten public declarations
audited exactly propext/Classical.choice/Quot.sound, no sorryAx.
The fixture uses the actual W/chart/common-field objects and the exact
compiled base inversion. It makes the accepted W finiteness, torsion-free,
Dedekind and polynomial-rank-four facts explicit; production obtains them
from the existing source. No new rank or product-formula conclusion is
assumed in production. The full final signatures are attached in the log.

The log has one unused-section-variable warning and one unused simp-argument
warning. No error remains. The proof keeps the canonical polynomial action
on the curve field while checking the rational-base scalar tower; the
new reciprocal action is the explicit composed map in the result.

NOT RUN locally: the new parameter-free FLT module under the complete
production import closure, or the lead's aggregate audit. The supplied
ActualInfinityFunctionFieldCheck.lean audits all ten declarations. Source
specializations were reviewed and the new full-import gate remains with
the lead. The exact checked source, generic helper, generator, import-source
hashes and emitted-module hashes are included.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every invocation uses one
shared gate, one CPU/thread,3072MiB Lean cap,60s compiler limit and synthesis
budget200000. Wrapper elapsed time can include lock waiting. No full FLT
build or accepted-source rewrite was performed here.

## Next owned obligation and endpoint status

Next is separability under this exact reciprocal action, followed by the
finite integral normalization over its polynomial base and identification
of its infinity-prime localizations with the three actual boundary rings.
Their completeness and norm/valuation sum for arbitrary functions remain
to be proved. The accepted base-polynomial product-formula subcase remains
separate from that general target.

The last fresh Mazur root closure remains no sorryAx and exactly the three
custom axioms no_prime_order_ge_23, the N25 obstruction exclusion and the
N49 raw-obstruction exclusion. Neither N25 nor the general projective
product formula is claimed complete.

Manifest: comms/inbox/research-dot-FLT-N25-RATIONAL-BASE-INVERSION-r22-manifest.json
