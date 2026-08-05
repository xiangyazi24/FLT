import FLT.Assumptions.MazurProof.TorsionBound

/-!
# Auditing the final Mazur torsion endpoint

This file records the authoritative axiom audit for the assembled numerical
torsion bound.  Rebuild stale dependencies from source before trusting the
printed list: an older `.olean` can retain assumptions that the current source
has already discharged.
-/

#print axioms MazurProof.mazur_torsion_bound
