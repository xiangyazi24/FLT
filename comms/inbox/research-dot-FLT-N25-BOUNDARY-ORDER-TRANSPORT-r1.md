# Genuine boundary orders of normalization fractions

TASK_ID: FLT-N25-BOUNDARY-ORDER-TRANSPORT
REVISION: 1
TYPE: RESULT
STATUS: INDEPENDENT-TRANSPORT-CANDIDATES-READY
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
SUPERSEDES: none; independent continuation of the boundary/norm route

## Dependency boundary

The latest retrieved dispatch remains r34. Norm multiplicities at 6a4110a03ca7bee2db5fb2e506eb75edd3643ce0
and principal norm orders at b6bae08bf96ddbd1fe1c81db4705ec2524a5ac83 are pending
lead acceptance. This new packet does not import either pending candidate.
It uses only the accepted actual boundary embeddings, localization equivalences,
signed orders and shared Algebra definitions. Six relevant production files
were read back at the exact source pin; their blob identities are attached.

## Two candidates, seven declarations

N25F_FractionOrderDifference.lean proves log_ordFrac_div directly from Mathlib:

    WithZero.log (Ring.ordFrac R (algebraMap R L a / algebraMap R L b)) =
      ((Ring.ord R a).toNat : ℤ) - ((Ring.ord R b).toNat : ℤ)

The hypotheses are the genuine dimension-one Noetherian domain/fraction-field
structures and a,b nonzero. The proof establishes that both quotient lengths
are finite, applies ordFrac_eq_ord and computes the logarithm of the quotient.

N25F_InfinityBoundaryOrderTransport.lean contains three localization-length
transport theorems and three existing signed-coefficient formulas. For each
of the actual X, YZ and Z centers and any f with common-field value a/b:

    boundaryOrder f =
      (ord_(normalization center)(a)).toNat - (ord_(normalization center)(b)).toNat

The displayed difference is in integers, and every order is the actual
Ring.ord quotient length. The Lean statements spell out the precise centers,
algebra maps and fixed W-chart function field. The nonzero normalization
numerator and denominator are carried through the injective accepted maps;
the coordinate-rigid composition identities retain the same function.
No ideal norm, norm multiplicity, valuation compatibility or product formula
is assumed. No previously accepted production source is changed.

## Validation ledger

PASS: the exact complete generic production source followed only by its audit,
generic-01 exit 0, 5.368 seconds, peak child RSS 2,490,204 KiB, standard-three.
Production source SHA-256:
0b4cfc13dad856ec28009261d7d6a1501fe44a0eac9add5c6b148aeec1e53796.

PASS: the complete six-declaration transport family plus the generic helper,
family-06 exit 0, 4.597 seconds, peak child RSS 2,726,380 KiB. All seven audits
are exactly [propext, Classical.choice, Quot.sound], with no warnings or sorryAx.
Family source SHA-256:
a07bf21a9eba8632066ba33e1a9d400f35508de0bd245299df54fbf4f4a43379.
The generator uses explicit typed algebra maps and the already accepted
injectivity, common-field compatibility and localization-equivalence data.
It generalizes the actual carriers, unfolds the signed-order definition,
and removes only redundant definitional changes in the generic setting.

REJECTED: family-03 and inspect-01 returned exit 0 but their axiom audits
contained sorryAx. The printed fixture type exposed a notation-corrupted
compatibility parameter of type N -> sorry. This was a test-fixture failure;
none of those terms are imported into the final check. The failed source,
logs and receipts are attached under rejected/ and excluded from PASS evidence.
Replacing notation aliases with explicit typed algebra maps removed the
corruption. family-01/02/04 also failed; family-05 was standard-only with
fixture warnings before the final cleanup. The ledger preserves all outcomes.

NOT RUN locally: full named FLT imports and seven production audits.
ActualBoundaryOrderTransportCheck.lean enumerates the exact gate for the lead.
The generic proof is checked directly; the actual named binding remains distinct
from its family test. Integration and full FLT acceptance stay with the lead.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. Each check acquired/released
the shared gate separately, one CPU/thread, 3,072 MiB cap, 60 active seconds.

## Next owned frontier

Next is the actual reciprocal fixed-field norm identity: the order at (T)
of that norm equals the sum of the existing signed X/YZ/Z boundary orders
for every nonzero function. The proved principal norm and present fraction
transport supply numerator/denominator terms; the remaining work is the exact
Algebra.intNorm-to-Algebra.norm scalar-tower conversion and base localization.
Research can proceed while the pending production gates run.

The general projective product formula and N25/Mazur remain open. The last
fresh root closure still has no sorryAx and the same three custom axioms.

Manifest: comms/inbox/research-dot-FLT-N25-BOUNDARY-ORDER-TRANSPORT-r1-manifest.json
