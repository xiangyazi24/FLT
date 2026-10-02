# r19 ACK and actual reciprocal-qz germ at X

TASK_ID: FLT-N25-PROJECTIVE-PRINCIPAL-DIVISOR
REVISION: 19
TYPE: ACK_AND_RESULT
STATUS: BASE-POLYNOMIAL-PRODUCT-ACCEPTED; X-INFINITY-GERM-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 8a8daa4e41c0d852b4b4a8a34aaed9c530012ea3
DISPATCH_COMMIT: 370ffa3465e81eef2d6967f5d0053d084f8d7c88
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; next bounded infinity-comparison prerequisite

## R19 accepted version adopted

The lead accepted the actual projective-principal-divisor module with a
name-resolution fix. Full imports expose two W abbreviations; the original
candidate did not build there. The accepted version fully qualifies W by
N25F_NonBoundaryPrincipalDivisor.W. I resolved the full source SHA, fetched
and Git-blob-verified it, and confirmed that the entire diff is exactly
this identifier replacement (16 token matches in the delivered bytes).
No other source text changed. This delivery synchronizes the candidate
copy to that accepted version and preserves the historical originals.

The actual principal-divisor construction, component/degree formulas,
coefficient-map bridge and base-polynomial degree-zero theorem now have
lead-run acceptance: 8680-job build and all six public audits exactly
propext/Classical.choice/Quot.sound. This closes that full-import gate;
the general arbitrary-function product formula is still open.

## New actual local result

Candidate: comms/candidates/N25F_XInfinityGerm.lean
Namespace: MazurProof.N25F_XInfinityGerm

The actual DVR orders prove xZGerm ∣ xWGerm, because2≤3. The source
constructs xInverseZGerm : XLocalRing from that divisibility and proves:

    xZGerm * xInverseZGerm = xWGerm
    xLocalToFraction xInverseZGerm = 1 / algebraMap W K qz
    xInverseZGerm ≠ 0
    Ring.ord XLocalRing xInverseZGerm = 1

All symbols are the existing actual X-boundary ring, germs, common field
and coordinate-rigid map. No local division operation, abstract rational
function germ or new production hypothesis is assumed. Classical.choose
selects a factor from a proved divisibility, and the field identity fixes
its mathematical meaning. The order-one proof uses actual multiplicative
order and finite ENat cancellation.

This supplies the previously missing X-local representative of the
reciprocal polynomial-base parameter, needed to map the infinity base into
the actual boundary ring. YZ and Z reciprocal representatives are simpler
expressions using the existing unit/germ. No claim about the full infinity
normalization or all primes over infinity is made yet.

## Validation ledger

PASS: XInfinityGermCheck.lean, actual-02,22.616s elapsed,
2,921,820KiB peak child RSS, all six public declarations exactly the
standard three axioms, no sorryAx and no warnings in this final check.
The selective harness uses the actual X-point evaluator and local ring.
Its explicit parameters are the already accepted W Dedekind structure,
W/X order3 and qz≠0. The actual orders of Z/X and its field image are
proved inside the reused emitted harness; the new quotient is not a
supplied premise.

The reused XBoundaryZOrderCheck source was re-emitted unchanged under the
same bounds in41.885s; it passed and its source/olean hashes are recorded.
This is a reusable local check artifact, not the lead's production olean.
NOT RUN locally: the new parameter-free module with full FLT imports and
its aggregate actual-binding audit. ActualXInfinityGermCheck.lean audits
all six declarations for the lead.

Lean4.31.0-rc2/5e44d5f905127c78a2da7a015fe7a47840c95eb1,
Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05. Each call uses one shared
gate, one CPU/thread,3072MiB Lean cap,60s compiler limit and synthesis budget
200000. Elapsed wrapper times can include lock waiting. No broad build.

## Remaining mathematics and ownership

I continue the concrete infinity-base maps and their compatibility with
the same common field, then the finite normalization/norm comparison for
arbitrary functions. Completeness and identification of the three
boundary places must be proved, not packaged as a product-formula premise.
The accepted degree-zero base-polynomial result is a subcase only.
The last fresh Mazur root audit still has no sorryAx and exactly the three
custom axioms no_prime_order_ge_23, the N25 obstruction exclusion, and the
N49 raw-obstruction exclusion. N25 and the general product formula remain
open; lead retains integration and aggregate verification ownership.

Manifest: comms/inbox/research-dot-FLT-N25-PROJECTIVE-PRINCIPAL-DIVISOR-r19-manifest.json
