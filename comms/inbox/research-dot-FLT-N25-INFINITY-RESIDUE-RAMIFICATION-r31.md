# r31 ACK and complete infinity fiber

TASK_ID: FLT-N25-INFINITY-RESIDUE-RAMIFICATION
REVISION: 31
TYPE: ACK_AND_RESULT
STATUS: RESIDUE-AND-RAMIFICATION-ACCEPTED; COMPLETE-FIBER-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: e46e0b6107bf133c10cc2f02482fa835b91a7e71
DISPATCH_COMMIT: 7677da1aec5b377ecdc69cb1ababad5ee18d6f20
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the N25 infinity proof

## R31 acceptance verified

Both N25F_InfinityResidueFields and N25F_InfinityRamificationIndices are
independently read back byte-equal from production. The lead reports a
successful build and all eighteen public declarations with standard-only
axioms. The actual indices e=(1,1,2) and f=(1,1,1) are accepted facts.

## Exact new production target

Candidate: comms/candidates/N25F_InfinityFiberComplete.lean
Namespace: MazurProof.N25F_InfinityFiberComplete

    infinity_primesOver_complete (q : Ideal InfinityNormalization)
      [q.IsPrime] [q.LiesOver infinityBasePrime] :
      q = xInfinityPrime ∨ q = yzInfinityPrime ∨ q = zInfinityPrime

This classifies every prime over the actual reciprocal-coordinate prime.
It does not assume a finite enumeration or a missing-prime exclusion.

First, the actual reciprocal polynomial injection implies injectivity into
the constructed normalization. This proves torsion-freeness and hence
flatness over the Dedekind polynomial base. The normalization is already
proved finite of rank four. Mathlib's finite-flat fiber formula therefore
gives total ramification-inertia weight four over (T).

The three accepted distinct centers contribute 1*1 + 1*1 + 2*1 = 4.
Every prime in this finite fiber has positive ramification and inertia,
by the finite-extension theorems. A finite positive-weight exhaustion
argument excludes every additional prime. The production source uses all
named actual structural, contraction, order, degree and distinctness proofs;
no new premise is added. Six public declarations.

## Validation

PASS: the finite positive-weight exhaustion lemma, generic-01, exit 0,
2.843 seconds wrapper elapsed, 1,574,432 KiB peak child RSS, standard-three.

PASS: the actual-normalization carrier proof of injection, torsion-freeness,
flatness, the finite-flat fiber sum, and complete exhaustion, in one separate
family module importing the emitted normalization fixture. family-01 exits
0 in 21.792 seconds, peak child RSS 2,743,200 KiB. All five audited declarations
are exactly propext, Classical.choice, Quot.sound, with no sorryAx or warnings.

That family fixture exposes the accepted W structural facts, normalization
finiteness/rank four, and the three prime/degree/distinctness facts. Its
proof computes the same actual coefficient injection and flatness, then
performs the full fiber argument. These fixture parameters do not occur
as additional premises in the production candidate. The generator and
exact checked source show the precise substitutions.

NOT RUN locally: the complete six-declaration FLT production module and
its named binding closure. The compiled production dependency bundle is
still unavailable here. ActualInfinityFiberCompleteCheck.lean is supplied
for the lead's gate; the family check is not labeled a full production build.
The accepted shared Algebra definitions are explicitly enabled locally.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every proof check uses a
single shared gate, one CPU/thread, 3,072 MiB Lean cap, 60 active compiler
seconds, synthesis budget 200,000. Elapsed times may include waiting.
No broad project build or accepted-source rewrite was run here.

## Next exact gap

The remaining infinity step is the arbitrary-function norm/valuation sum,
then its comparison to the affine norm-degree identity. The pinned library's
Ideal.relNorm_eq_pow_of_isMaximal assumes PerfectField (FractionRing R),
which is unavailable for R=F2[T]. I will not insert that premise. The finite
extension's actual separability is already proved, so I am inspecting a
separability-based normal-closure adaptation or a direct determinant/local-
length argument. The fiber result above is independent of that norm gap.

The general projective product formula, N25 exclusion and Mazur endpoint
remain open. The last fresh root audit still has no sorryAx and exactly
no_prime_order_ge_23, N25 obstruction exclusion and N49 raw-obstruction
exclusion as custom axioms.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-RESIDUE-RAMIFICATION-r31-manifest.json
