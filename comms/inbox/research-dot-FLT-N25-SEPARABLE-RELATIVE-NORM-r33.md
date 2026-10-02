# r33 ACK and the three actual relative prime norms

TASK_ID: FLT-N25-SEPARABLE-RELATIVE-NORM
REVISION: 33
TYPE: ACK_AND_RESULT
STATUS: SEPARABLE-NORM-THEOREM-ACCEPTED; ACTUAL-PRIME-NORM-CANDIDATES-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 78a93cebddd84e069ca9d0bbc8f837e0a8c083e1
DISPATCH_COMMIT: 5dfb795d4d198281553833f187ab93b08d052d4c
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; continuing the norm/valuation route

## R33 verified

N25F_SeparableRelativeNorm is independently read back byte-equal from
production. The lead reports successful build and all five public audits
with standard-only axioms. The finite-separability norm theorem is accepted;
no perfectness premise is introduced for F2(T).

## Canonical field specialization

Candidate: comms/candidates/N25F_InfinityCanonicalSeparable.lean.
It proves the actual theorem

    infinityCanonicalFraction_isSeparable :
      letI : Algebra BaseField (FractionRing InfinityNormalization) :=
        FractionRing.liftAlgebra _ _
      Algebra.IsSeparable BaseField (FractionRing InfinityNormalization)

The generic helper constructs the canonical fraction-ring action into the
fixed common curve field and proves the scalar tower by fraction-ring
extensionality. Separability then descends along that tower. The actual
specialization uses the accepted reciprocal field separability, normalization
fraction-field structure and torsion-freeness. Its Algebra actions are
explicitly aligned; different canonical and coordinate-rigid actions are
not silently identified. Two public declarations, no new production premise.

## Actual relative norms

Candidate: comms/candidates/N25F_InfinityPrimeNorms.lean.
It applies the accepted separable prime-norm theorem to the actual finite
Dedekind normalization and the canonical field action proved above, then
uses the exact inertiaDeg/inertiaDeg' comparison and accepted residue degrees:

    Ideal.relNorm BasePolynomial xInfinityPrime = infinityBasePrime
    Ideal.relNorm BasePolynomial yzInfinityPrime = infinityBasePrime
    Ideal.relNorm BasePolynomial zInfinityPrime = infinityBasePrime

Three public declarations. No norm identity, perfectness, or separability
assumption is added to the actual target.

## Check ledger

PASS: generic compatible-fraction-field separability transport,
generic-01 exit 0, 43.560 seconds wrapper elapsed, standard-three audit.

PASS: the actual normalization carrier's canonical-fraction specialization,
actual-01 exit 0, 40.928 seconds, peak child RSS 2,537,360 KiB. Both audits
are standard-three, with no sorryAx or warnings. The fixture exposes the
accepted W and normalization facts and the exact accepted reciprocal-action
separability. Its conclusion uses canonical FractionRing.liftAlgebra.
The generator reproduces the checked bytes exactly.

PASS: the prime-norm application on the same actual normalization carrier,
family-01 exit 0, 11.963 seconds, peak child RSS 2,896,592 KiB, standard-three,
no warnings. It exposes the already proved canonical separability and degree-one
prime facts; production supplies the three named center proofs. It imports
the unchanged emitted norm theorem accepted in r33.

NOT RUN locally: the two full FLT modules and all five named production
bindings. ActualInfinityPrimeNormsCheck.lean lists every declaration for the
lead. The local fixtures are separate importing modules and remain explicitly
distinct from the full production gate. The compiled FLT bundle requested
previously has not been received.

All later production files import the accepted shared boundary Algebra module
and enable the named actions locally. Existing source is unchanged.
Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One shared gate per
invocation, one CPU/thread, 3,072 MiB Lean cap, 60 active compiler seconds,
synthesis budget 200,000; wrapper elapsed times can include waiting.

## Next owned result

Next is the multiplicity of (T) in the relative norm of an arbitrary
nonzero normalization ideal, then a principal ideal/function. Factorization,
these three prime norms and accepted fiber completeness should reduce it
to the sum of the three genuine local orders. The field-norm conversion
and comparison with the affine norm-degree identity follow afterward.
The general projective product formula remains open, as do N25 and Mazur.
The last fresh root closure is still no sorryAx and the same three custom axioms.

Manifest: comms/inbox/research-dot-FLT-N25-SEPARABLE-RELATIVE-NORM-r33-manifest.json
