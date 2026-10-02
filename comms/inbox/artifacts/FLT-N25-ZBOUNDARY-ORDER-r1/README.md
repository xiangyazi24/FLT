# Actual Z-boundary order candidate; generalized feedback

N25F_ZBoundaryOrder.lean uses the existing ZChartRing, zPrime, ZLocalRing,
and zWGerm. It proves zPrime is nonzero, obtains the local DVR structure,
constructs the injective coordinate-rigid local field map, proves the common
field is its fraction field, and defines the genuine Ring.ordFrac signed
order. The accepted germ order two and image zWGerm=1/qz give signed order
of qz equal to -2. No production premise, custom axiom, sorry or admission
is added. The predecessor chart and field candidates are unchanged.

## Important verification distinction

The actual point specialization and full FLT imports have NOT RUN locally.
This packet is a source-reviewed actual specialization with a passed
GENERALIZED POINT-LOCALIZATION check, not an exact-source compilation of
the existing zPointEval definition.

The harness imports the tested actual Z-chart/field objects. It replaces the
point evaluator by a parameter f : ZChartRing →ₐ[F2] F2, forms its genuine
kernel/localization/germ, and supplies two explicit facts: f(zW)=0 and the
germ has length-order 2. These are exactly the facts already proved by the
accepted zPointEval_zW and zWGerm_ord_eq_two source theorems. Their full
source bodies and lines are recorded in validation.json. The production
proof uses the actual source evaluator and the existing theorems directly.
The first point fact is used through its registered simp lemma.

This generic check validates the algebraic DVR/localization/field-order
argument without reconstructing the original normalized-point evaluator
and Artin-quotient proof closure. It does not certify the actual point
binding. Both that binding and the real imports are explicit lead gates.

The harness also carries accepted W torsion-free/Dedekind structure as
ordinary parameters, as did its tested predecessors. The fixture adds
explicit point parameters to references and expands local notation where
needed; no production file is rewritten by these adjustments.

## Passed evidence

The third generic check passed: exit 0, 22.101 seconds, 2765020 KiB peak RSS,
one CPU/thread, 3072 MiB cap, 60-second timeout, shared flock gate. All 13 audited
declarations show only propext, Classical.choice, Quot.sound. Four unused
fixture-variable warnings remain. Prior failed fixture diagnostics are
retained and excluded from acceptance.

Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
The imported ZChartInjectiveCheck and ZChartFractionEquivCheck emissions are
recorded in the predecessor packet at 0e8b444e8295b7247f00008ff54869736e78ca98.
Use both emitted-module directories in LEAN_PATH; the manifest records exact
source and output hashes. The binaries are rebuildable and not committed.

ActualZBoundaryOrderCheck.lean requests the real point/import/axiom check
from the lead. The YZ overlap/local comparison, full boundary coefficient
triple, product formula, and N25 exclusion remain open.
