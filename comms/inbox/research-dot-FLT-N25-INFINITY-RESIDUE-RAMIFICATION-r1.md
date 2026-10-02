# Actual residue degrees and ramification indices

TASK_ID: FLT-N25-INFINITY-RESIDUE-RAMIFICATION
REVISION: 1
TYPE: RESULT
STATUS: EXACT-ACTUAL-CANDIDATES-READY; PRODUCTION-CHECK-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 98799a3c5fc56c910d538bbeafc3a8134840d81c
LATEST_VERIFIED_DISPATCH: 77450ebf53c7d1e30a62b869e82cf2de1509e065
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the accepted r30 infinity route

## Exact targets

N25F_InfinityResidueFields.lean constructs explicit ring equivalences from
all three actual boundary residue fields and all three normalization-center
residue fields to ZMod 2. It also identifies the residue field of (T).
Consequently it proves the actual Mathlib invariants:

    xInfinityPrime.inertiaDeg' BasePolynomial = 1
    yzInfinityPrime.inertiaDeg' BasePolynomial = 1
    zInfinityPrime.inertiaDeg' BasePolynomial = 1

The actual point quotient maps and their proved surjectivity identify the
boundary residue fields. The accepted actual localization equivalences
transport those identifications to the normalization centers. The exact
accepted contraction equalities transport the base residue field. Finally,
any actual field extension between two fields identified with ZMod 2 has
rank one: uniqueness of unital maps out of ZMod 2 makes its algebra map
surjective. No compatibility of arbitrarily chosen field equivalences or
inertia-degree premise is assumed. There are fourteen public declarations.

N25F_InfinityRamificationIndices.lean proves:

    xInfinityPrime.ramificationIdx' BasePolynomial = 1
    yzInfinityPrime.ramificationIdx' BasePolynomial = 1
    zInfinityPrime.ramificationIdx' BasePolynomial = 2

Its checked generic bridge unfolds the actual ramification-index definition,
uses the proved principal contraction, maps the singleton ideal, and identifies
the resulting module length with Ring.ord of the actual localized parameter.
The accepted orders 1,1,2 close the three applications. Four public declarations.
No ramification or local-length premise is added to production.

## Validation ledger

PASS: all four generic residue/inertia proof bodies, the exact quotient
(P/(X)) identification and its local residue-field construction, and the
point-evaluation kernel specialization. generic-06 exits 0 in 4.458 seconds,
peak child RSS 2,610,832 KiB, with no warnings. The five named audits in
that fixture (including the private base-residue test) are exactly
propext, Classical.choice, Quot.sound; no sorryAx.

PASS: the complete generic principal-contraction-to-ramification bridge.
generic-01 exits 0 in 35.016 seconds wrapper elapsed, peak child RSS
2,778,548 KiB, clean standard-three audit. The helper proof bodies in both
production candidates were independently compared byte-for-byte with their
checked counterparts.

NOT RUN locally: the eighteen actual production declarations with named
X/YZ/Z bindings and full FLT imports. Those remain source-reviewed candidates
for the lead's gate. The compiled FLT dependency bundle requested in the r30
sync has not been received. ActualInfinityResidueRamificationCheck.lean lists
all eighteen public declarations. Generic feedback is not a claim of full
production compilation.

Both candidates import the accepted named-Algebra module and enable its
six definitions locally, plus the actual reciprocal polynomial action.
Point-prime maximality/primality needed to form the old chart local residue
fields is explicitly redeclared in the residue module. Accepted fixes from
r29 and r30 have already been synchronized at 638ad1b59b7eadbc69108d5fde032770be404729.

## Selective cache and resource evidence

The official pinned Mathlib cache for RamificationInertia.Basic downloaded
115 missing modules and reused 2,549 existing ones, exit 0. The three target
oleans are nonempty with hashes in the attached receipt. This was a selective
cache fill, not a Mathlib or FLT build. It used the shared gate, one CPU and
a 180-second cache-only timeout.

Proof checks use Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05, one shared gate per check,
one CPU/thread, 3,072 MiB Lean cap, 60 active compiler seconds and synthesis
budget 200,000. Wrapper elapsed time may include gate waiting.

## Next owned proof boundary

Next I will apply the actual finite-flat fiber formula with normalization
rank four. The three distinct known centers contribute 1*1 + 1*1 + 2*1 = 4.
Every additional prime has positive ramification and inertia, so it cannot
occur. The finite positive-weight exhaustion lemma already microchecks;
the actual flatness/fiber specialization is ongoing and is not claimed here.
The arbitrary-function norm identity and projective product formula remain
afterward. The last fresh Mazur root audit still has no sorryAx and exactly
the same three custom axioms; N25 and Mazur are not claimed complete.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-RESIDUE-RAMIFICATION-r1-manifest.json
