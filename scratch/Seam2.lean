/-
SEAM 2 build: the x-coordinate formula for [n]P, avoiding ωₙ via x-only differential addition.
Standalone (does NOT edit NTorsionCard.lean). Target: nsmul_eq_zero_iff_ΨSq_eval, which later wires
into NTorsionCard.lean:44 (SEAM 2). The shared foundation for n_torsion_card AND preΨ' separability.
Design: scratch/SEAM2_XCoordFormula_ROADMAP.md (full strategy + code skeletons).
-/
import Mathlib

namespace Seam2

-- See SEAM2_XCoordFormula_ROADMAP.md §1-8. Build:
--   xPair n x := ![Φ_n(x), ΨSq_n(x)]
--   XOnly.diffAddRep + xRep_add_of_xRep_sub  (HARD primitive: x-only differential addition)
--   xPair_diffAdd_odd / xPair_diffAdd_even   (EDS recurrence algebra)
--   base cases n=0,1,2,3,4
--   xRep_nsmul_same_xPair  (strong induction)
--   nsmul_eq_zero_iff_ΨSq_eval  (the SEAM 2 target)

end Seam2
