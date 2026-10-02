# Genuine bounded-pole spaces and negative-degree vanishing

TASK_ID: FLT-N25-RIEMANN-ROCH-SPACE
REVISION: 1
TYPE: RESULT
STATUS: ACTUAL-SECTION-SPACE-AND-NEGATIVE-DEGREE-VANISHING-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULTS: f5796e424266adb887c59a14696cdb6b13f64d40,
  8517a259e9d16fd5fc88635294bea0a964de01f8
SUPERSEDES: none; constructs the actual linear-system vector-space carrier

N25F_RiemannRochSpace.lean defines fullRiemannRochSpace25Two D as a genuine
Submodule (ZMod 2) of FractionRing W. Its elements are zero and precisely the
nonzero functions f satisfying D(A)+div(f)(A)>=0 at every full closed point A.
The divisor and all its coefficients are the existing actual ones.

Addition closure is proved from the delivered coefficient minimum inequality;
zero sums are handled explicitly. Scalar closure uses the actual binary field,
whose scalars are zero or one. Neither closure property is postulated.

The remaining two theorems prove:

- a nonzero section forces divisorDegree D >= 0;
- if divisorDegree D < 0, fullRiemannRochSpace25Two D = bottom.

The proof adds the genuine principal divisor of the section, obtains an
effective signed divisor, sums its nonnegative multiplicity-weighted terms,
and uses the delivered degree-zero product formula. There is no Riemann--Roch,
finite-dimensionality, genus or class-number premise.

## Validation

PASS: family-02, exit 0, 38.098 seconds wrapper elapsed including any gate
waiting, peak child RSS 1,955,056 KiB. All four public audits are exactly
[propext, Classical.choice, Quot.sound], with no warnings or sorryAx.
SHA-256: 30c1b5264b9f0865a0fb90b630b8666df3d78bac371f2e44477d722a623e8a44.

The family uses the exact repository grading and degree definitions. It
exposes the previously proved actual divisor-addition inequality and product
formula as inputs; production supplies those named proofs. All new submodule
axioms and vanishing arguments are checked in the family. The portable
generator reproduces the passing bytes exactly from the included sources.

FAILED: family-01 had an explicit ZMod.val-one simplification and a missing
Algebra import in the test fixture. Both were corrected; the failed receipt
and log are separate from PASS evidence.

NOT RUN locally: the full named FLT module and four production audits.
ActualRiemannRochSpaceCheck.lean lists the gate. All preceding packets remain
pending lead acceptance; no fresh root kernel closure is inferred.

Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Each invocation uses one
shared-gate acquisition, one CPU/thread, 3,072 MiB and 60 active seconds.
No broad build or duplicate successful check was run.

This constructs the actual section spaces; it does not assert that they
are finite-dimensional or satisfy the genus-four Riemann--Roch identity.
Those claims and the complete-linear-system fibre cardinality remain open.
The next concrete target is degree-zero constancy using the actual binary
residue field at X, so the principal map's constant-function kernel can be
proved rather than assumed. N25/Mazur and the root three-custom-axiom frontier
remain open.

Manifest: comms/inbox/research-dot-FLT-N25-RIEMANN-ROCH-SPACE-r1-manifest.json
