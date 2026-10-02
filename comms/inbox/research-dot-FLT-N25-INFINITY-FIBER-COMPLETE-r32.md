# r32 ACK and relative prime norms without perfectness

TASK_ID: FLT-N25-INFINITY-FIBER-COMPLETE
REVISION: 32
TYPE: ACK_AND_RESULT
STATUS: FIBER-CLASSIFICATION-ACCEPTED; SEPARABLE-RELATIVE-NORM-KERNEL-CHECKED
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: a00509e7a5438c940ef079f1f867baf94c8b85cc
DISPATCH_COMMIT: f9a94dc2d074977527ccdafafc59143ace851e05
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the actual norm/product-formula route

## R32 accepted

N25F_InfinityFiberComplete is independently verified byte-equal to production.
The lead reports successful build and all six public declarations with
standard-only axioms. The exact three actual centers now exhaust the whole
fiber over (T), with the already accepted e=(1,1,2) and f=(1,1,1).

## Closed generic norm theorem

Candidate: comms/candidates/N25F_SeparableRelativeNorm.lean
Namespace: MazurProof.N25F_SeparableRelativeNorm

    relNorm_prime_of_separable (R S : Type*)
      [CommRing R] [CommRing S]
      [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
      [Module.Finite R S] [Module.IsTorsionFree R S]
      [Algebra.IsSeparable (FractionRing R) (FractionRing S)]
      (P : Ideal S) (p : Ideal R)
      [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
      Ideal.relNorm R P = p ^ p.inertiaDeg P

The fraction-field Algebra in this statement is the explicit canonical
FractionRing.liftAlgebra, not an unspecified new action. The printed full
type is in the audit log. There is no PerfectField premise.

The pinned library's comparable prime-norm theorem requires a perfect base
fraction field, which F2(T) does not supply. This candidate proves the needed
separability-based version rather than postulating that unavailable property.

The proof first shows that the field normal closure is separable: it is the
supremum of the separable images of the original field under base embeddings.
This does not require the ambient algebraic closure itself to be separable
over the base. It then obtains the ring normal closure's Galois fraction
field, finiteness and Dedekind structure using that genuine separability.
The existing Galois prime-norm and norm-transitivity theorems complete the
argument. Five public declarations; no assumed norm formula or new axiom.

## Exact production validation

PASS: the unchanged complete production source with its actual Mathlib
imports, norm-02 exit 0, 38.540 seconds wrapper elapsed, peak child RSS
2,879,508 KiB. This is not a stand-in family check or a source-only claim.

PASS: a byte copy of production plus full-type printing and five axiom
commands, audit-01 exit 0, 25.917 seconds, peak child RSS 2,882,140 KiB.
Every public declaration has exactly propext, Classical.choice, Quot.sound;
no sorryAx or warnings. The source also emitted an unchanged reusable
olean successfully (production-emit receipt attached).

The first full attempt hit the 60-second limit while using the general
FractionRing.liftAlgebra instance. That rejected attempt was repaired by
three specific canonical Algebra declarations, following the library's
own performance guidance. The final proof statements and premises above
are the checked ones. No resource limit was raised.

NOT RUN locally: integration into the complete FLT project and aggregate
endpoint audit. That remains the lead's gate. The supplied actual audit
file lists all five declarations.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per
invocation, one CPU/thread, 3,072 MiB Lean cap, 60 active compiler seconds,
synthesis budget 200,000. Elapsed time may include waiting; the 67.578-second
emission receipt includes that wait. The official selective relative-norm
cache fill downloaded six missing modules and reused 2,410; no broad build.

## Next actual specialization

I am proving the canonical fraction-ring separability of the actual infinity
normalization from the accepted coordinate-rigid common field. This keeps
the two Algebra actions distinct and supplies precisely the theorem's
canonical premise. The generic compatible-fraction-field transport already
microchecks; its actual-normalization family specialization has also just
passed with both audits standard-three and is queued for separate delivery.
After specializing relative norms, the arbitrary-function valuation sum and
affine norm-degree comparison remain. No global product formula is claimed.
The last fresh Mazur root audit still has no sorryAx and exactly the same
three custom axioms.

Manifest: comms/inbox/research-dot-FLT-N25-INFINITY-FIBER-COMPLETE-r32-manifest.json
