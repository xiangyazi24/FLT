# r10 ACK, accepted-source configuration sync, and actual affine overlap equivalence

TASK_ID: FLT-N25-AFFINE-DEGREE
REVISION: 10
TYPE: ACK_AND_RESULT
STATUS: R10-ACCEPTANCE-ACKNOWLEDGED; TWO-PENDING-OVERLAP-MODULES-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 0b2cfe016226552b61f3ef4074a05e48cec50560
EARLIER_ACCEPTED_SOURCE: 1eab90d583a58211846c1b69e24e5ed73a59ce4d
DISPATCH_COMMIT: 5f5d4776181bf744e8d6ce28b97736e7b2ab0459
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; ACK of the acceptance receipt, continuing its explicitly unchanged N25 scope

## 1. Acceptance and exact delta verified

I read the formal r10 receipt and resolved both abbreviated source commits.
The lead reports:
- XChartFractionMap: byte-equal, 8645-job build, eight standard-three audits
- Thirteen subsequent candidates: 8662-job build, 107 public audits, 103 using
  propext/Classical.choice/Quot.sound and four with no axioms

The actual point/local-ring specializations in those accepted modules now
have lead-run full-import acceptance; their earlier local generic-check
caveats remain historical evidence, not the current integration status.
This closes those individual import gates, not N25 or the Mazur endpoint.

I independently fetched all thirteen integrated candidates and all three
changed legacy local modules at the full source pin, and rehashed all sixteen
materialized files against their Git blob SHAs. I compared each with its
original candidate/source. Removing ONLY the documented synthesis-option
lines, the exact explanatory comment, and blank lines makes every remaining
source line identical. Thus the declaration and proof source text is
unchanged; this is not a blanket byte-equality claim or an independent
comparison of emitted proof-term binaries.

The observed configuration changes are eight file-level candidate options,
three per-declaration candidate options, and five per-declaration options
across the legacy XLocal/YZLocal/ZLocal files. The option is exactly:
`set_option synthInstance.maxHeartbeats 200000`.

The candidate copies in this packet are synchronized to the accepted source
bytes. Immutable earlier deliveries and their receipts remain available.
Legacy source snapshots are provided as accepted-input artifacts only;
I do not edit or reintegrate the lead's source branch. The accepted-source
comparison table is `verified-delta.json`.

## 2. New genuine unconditional affine-overlap equivalence

`N25F_YZAffineOverlapEquiv.lean` proves:

```lean
MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv :
  Localization.Away yZ ≃ₐ[ZMod 2] Localization.Away zY
```

Both rings are the actual Y/Z affine-chart localizations. The proof constructs
both quotient maps by homogeneous rescaling, extends them through localization,
proves all six coordinate formulas and inverse-coordinate identities, and
establishes mutual inverses by localization and generator extensionality.
There is no domain, field, point, unit, or abstract-isomorphism premise added
to the production statement or its successful exact-chart harness.

PASS: all seventeen public audits use only standard three axioms. The
original unconditional check took 24.656 s. Following r10, both headers were
updated with the synthesis option; namespace proof bodies were verified
byte-identical and a fresh bounded check/.olean emission passed. Its total
wall time was 167.821 s INCLUDING shared-lock waiting; the actual Lean
process retained its 60-second timeout, one CPU/thread and 3072 MiB cap.
Peak child RSS was 2463576 KiB. This is not a 167-second compiler allowance.

Current candidate SHA-256:
`41b01e4e7689bc23c919115212035b24d3964cb423a4c2c36d547d7b38a53455`.
Current checked source SHA-256:
`055dbb9c8673c87641ef16f00ed3cbbe1601590e040978ba09503b097b0a4e49`.
Full FLT imports of this NEW module are NOT RUN locally and await the lead.

## 3. Previously pending one-sided localization module

N25F_YZOverlapLocalization from
[16ef7352ebdad572c90f13e1b09fb343201c4022](https://github.com/xiangyazi24/FLT/commit/16ef7352ebdad572c90f13e1b09fb343201c4022)
was after r10's accepted cutoff. I have added the same file-level synthesis
option, preserved its proof source, and rerun its generic-algebra check.
The current candidate and fresh receipt are included. Its verification
scope remains generic algebra feedback; the actual local specialization
and full imports remain pending. It is a one-sided map, not a claimed
local-ring equivalence.

All checks use Lean 4.31.0-rc2 and Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
No full-project build, new axiom, sorry/admit/native_decide, logical target
weakening, main/PR/merge/release action, or duplicate source integration was
performed. The provided ActualYZAffineOverlapCheck requests the two pending
full-import gates.

Manifest: comms/inbox/research-dot-FLT-N25-AFFINE-DEGREE-r10-manifest.json.

## Next owned proof

I continue the requested overlap-localization comparison for the actual
YZLocalRing. The concrete next transfer is Dedekind structure through the
proved affine overlap and localization tower, followed by the YZ field order.
A generic algebraic transfer lemma has already passed bounded feedback;
its actual specialization is separate work, not included as a completed
result here. The full boundary coefficient triple and projective product
formula remain open, as does the N25 root exclusion. Integration and fresh
kernel acceptance remain with the lead.
