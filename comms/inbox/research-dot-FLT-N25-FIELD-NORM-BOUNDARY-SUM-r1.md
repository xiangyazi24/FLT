# Actual reciprocal field norm and all three boundary orders

TASK_ID: FLT-N25-FIELD-NORM-BOUNDARY-SUM
REVISION: 1
TYPE: RESULT
STATUS: GENERAL-NORM-ORDER-CANDIDATE-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULTS: 6a4110a03ca7bee2db5fb2e506eb75edd3643ce0,
  b6bae08bf96ddbd1fe1c81db4705ec2524a5ac83,
  fc653e9e48c5e2c66c3d315652b59f2b741bc85c
SUPERSEDES: none; continuing the explicit norm/valuation route

## Main mathematical result

N25F_InfinityNormBoundarySum.infinity_norm_boundary_order_sum states, for
every nonzero function f represented by Additive CurveField units:

    WithZero.log (infinityBaseFractionOrder
      (Algebra.norm BaseField (f.toMul : CurveField))) =
      xBoundaryOrder f + yzBoundaryOrder f + zBoundaryOrder f

Here CurveField is the existing FractionRing of the actual W-chart ring;
Algebra.norm uses the explicit reciprocal rational-base action. The base
order is literally Ring.ordFrac at the actual prime infinityBasePrime=(T).
The RHS uses the existing signed boundary coefficients, without replacing
their definitions. There is no function, norm, order or product-formula
compatibility hypothesis in the actual statement.

## Three candidates, six public declarations

N25F_InfinityNormFraction.lean proves that the integral norm in the actual
reciprocal normalization maps to the fixed-field norm under precisely the
established scalar towers; it proves the quotient formula for norms and the
existence of a nonzero normalization numerator/denominator for every nonzero
fixed-field function. These three declarations use accepted r34 inputs only.

N25F_LocalFractionFactorOrder.lean computes the signed order at a genuine
Dedekind prime in the canonical fraction field as the difference of numerator
and denominator prime-factor multiplicities. It uses the already delivered
length/factor and fraction-order proofs, retaining their exact bodies.

N25F_InfinityNormBoundarySum.lean defines the actual base fraction order and
proves the displayed theorem. It chooses a/b in the actual normalization,
converts the field norm to the quotient of integral norms, rewrites the three
existing boundary orders as localized quotient lengths, and applies the
previously proved arbitrary-ideal norm-multiplicity identity to span {a} and
span {b}. Integer addition then gives the required sum.

## Validation ledger

PASS: actual normalization-carrier norm conversion, actual-01, exit 0,
40.382 seconds wrapper elapsed, peak child RSS 2,675,576 KiB. All three audits
are exactly [propext, Classical.choice, Quot.sound], with no sorryAx. The
fixture imports the unchanged emitted normalization carrier and supplies its
accepted structural facts explicitly. Its final existence theorem has harmless
unused-fixture-parameter warnings; the checked source was kept unchanged.
SHA-256: eb57912877572d982e1efccf72782b428b3c0547532baca5f163390a8c4a1fee.

PASS: the local fraction-factor helper, local-fraction-01, exit 0,
17.935 seconds wrapper elapsed, peak child RSS 2,690,040 KiB. Exact production
declaration with the unchanged dependency bodies and standard-three audit.
SHA-256: bb52e678f88cf05c33301d75d82c408371bd787cde7d0273cd8af3e1df1892b0.

PASS: full norm/order assembly family, sum-family-02, exit 0, all six public
audits standard-three, no sorryAx. Wrapper elapsed 102.410 seconds includes
shared-lock waiting; the active compiler remained under the 60-second cap.
Peak child RSS 2,887,252 KiB. One unused generic fraction-ring parameter warning
in an auxiliary norm theorem is harmless; the passing bytes are retained.
SHA-256: feab732f1b0ee759e91b61db2315a6e61e09240a1a755f4e63829d65c4feb441.
The final assembly exposes the separately proved ideal-multiplicity and three
boundary-transport facts as explicit family parameters. The production proof
uses their exact names and closes all those facts. No product formula is an
input. The attached generator makes every substitution reviewable.

FAILED: sum-family-01 could not infer the generic normalization ring in the
fraction-existence call. The generic test now supplies N explicitly. The
actual production theorem fixes that ring in its declaration. The failed
source/log/receipt is retained separately; its sorryAx audit is not evidence.

NOT RUN locally: full named FLT imports and all six production audits.
ActualInfinityNormBoundarySumCheck.lean lists the exact gate. The latest
dispatch remains r34, so all three predecessor packets and this packet
remain pending production acceptance. No acceptance or byte-equal integration
is inferred from these local checks. No accepted source was changed.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Every invocation used one
shared-gate acquisition, one CPU/thread, 3,072 MiB Lean cap and 60 active
compiler seconds. No broad build or duplicate success check was performed.

## Next owned frontier

Next is comparison of this reciprocal norm with the norm for the existing
affine action by the proved base inversion, then evaluation of the base order
as minus the affine norm degree. Combined with the accepted affine
norm-degree/divisor identity this targets the general projective product
formula. That product formula is not yet claimed. N25 and Mazur remain open;
the last fresh root closure still has no sorryAx and exactly three custom axioms.

Manifest: comms/inbox/research-dot-FLT-N25-FIELD-NORM-BOUNDARY-SUM-r1-manifest.json
