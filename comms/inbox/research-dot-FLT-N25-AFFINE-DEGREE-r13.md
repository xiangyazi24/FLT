# r13 ACK and actual YZ-local DVR candidate

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 13
TYPE: ACK_AND_RESULT
STATUS: DEDEKIND-ACCEPTANCE-VERIFIED; YZ-LOCAL-DVR-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 56bed095c61c28fda99ad99e8bf0cb74542058ad
DISPATCH_COMMIT: 036a897eaf1e4325dd1f3176020bf5c0208b43ae
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; next bounded result in the unchanged N25 scope

## Acceptance synchronized

The lead's r13 accepts the actual YZLocalRing Dedekind candidate from
8ab39afcdc900bba0dea2461e9840d71976f84e4: 8653-job build and standard-three
public instance audit. I resolved the full accepted source SHA and fetched
the integrated file independently. It is byte-equal to our candidate.
Thus its full-import/named-point gate is closed; the earlier selective
point-family feedback remains historical, accurately labeled evidence.

## New result, with exact objects retained

Candidate: comms/candidates/N25F_YZLocalDVR.lean
Intended module: FLT.Assumptions.MazurProof.N25F_YZLocalDVR

The three public declarations in namespace MazurProof.N25F_YZLocalDVR are:

    theorem yzWGerm_ne_zero : yzWGerm ≠ 0
    theorem yzLocalRing_not_isField : ¬ IsField YZLocalRing
    instance yzLocalRing_isDiscreteValuationRing :
      IsDiscreteValuationRing YZLocalRing

Here yzWGerm and YZLocalRing are exactly the existing source objects from
RationalPointsN25QuotientTwoWBoundaryYZLocal. No production hypothesis is
added. The accepted coordinate-rigid affine-overlap equivalence sends W/Y
to (Y/Z)^-1*(W/Z). The canonical second localization is injective, because
its denominator images are units in the nontrivial point-local ring.
Consequently the accepted nonzero W/Z coordinate gives a nonzero W/Y germ.
The existing Ring.ord YZLocalRing yzWGerm = 1 then excludes a field; the
accepted Dedekind structure and the local DVR criterion finish the proof.

No domain claim about the entire Y chart, assumed local-ring isomorphism,
product formula, or extra curve/point premise is used in production.

## Validation ledger

PASS: generic nonzero-germ transfer through the two actual localization
operations, 5.148 s, peak child RSS 2,167,792 KiB, standard-three audit.

PASS: actual Y/Z curve-algebra point-family check, 12.385 s,
peak child RSS 2,820,404 KiB. All six audited declarations are standard-three
only (propext, Classical.choice, Quot.sound), with no sorryAx.
The harness has the accepted W Dedekind/torsion-free structures explicit,
and a point f with f(yZ)=1 plus the source order-one condition explicit.
The final elaborated signatures are in point-04.log. In particular, the
nonzero-germ theorem does not assume the order-one condition or a DVR.
The final production/helper proof bodies are the checked ones, with the
named existing facts supplying those point-family premises.

NOT RUN locally: the new production module's full FLT import closure,
actual named-point specialization and aggregate audit. The supplied
ActualYZLocalDVRCheck.lean lists all three production audits. Integration
and the full gate remain with the lead. No full project build here.

Toolchain: Lean 4.31.0-rc2 at 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One CPU/thread, Lean memory
cap3072MiB, compiler timeout60s, shared flock gate per invocation. The
r10 synthesis option200000 is preserved. Earlier failed harness drafts
were corrected; only the final PASS is submitted as validation evidence.

## Continuation and unchanged root frontier

Next owned work is the coordinate-rigid embedding/fraction-field property
of this actual YZ local ring in FractionRing W, followed by its signed
boundary orders and the projective product formula. The field comparison
uses the proved affine overlap and canonical localizations.

N25 exclusion is still open. The last fresh Mazur root audit remains no
sorryAx and exactly three custom axioms: no_prime_order_ge_23,
CyclicExclusion25.no_explicit_order25_obstruction,
CyclicExclusion49.no_raw_order49_tate_obstruction. A module-level DVR proof
does not change that endpoint closure by itself.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r13-manifest.json
