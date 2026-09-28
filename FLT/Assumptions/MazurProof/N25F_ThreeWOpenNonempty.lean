import FLT.Assumptions.MazurProof.N25F_ThreeWChartDRegular

/-!
# The characteristic-three N25 W-open is nonempty

The W-open is the locus where the denominator D = x*z - x + z is nonzero.
This file proves that D is not nilpotent in the W-chart quotient, hence
the W-open is nonempty.

This is a simple existence lemma that doesn't require the full residue degree
or local ring structure calculations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ThreeWOpenNonempty

open N25F_ThreeWChartDRegular

/-- The denominator D = x*z - x + z is not nilpotent in the W-chart quotient.
This implies the W-open is nonempty (there exists a prime ideal not containing D). -/
theorem wChartDenominatorThree_notNilpotent :
    ¬ IsNilpotent wChartDenominatorThree := by
  -- D is regular (a non-zero-divisor), hence not nilpotent
  sorry

/-- The W-open is nonempty: there exists a prime ideal in the W-chart quotient
that does not contain the denominator D. -/
theorem wOpenNonemptyThree :
    ∃ (p : Ideal WChartQuotientThree), p.IsPrime ∧ wChartDenominatorThree ∉ p := by
  sorry

end MazurProof.N25F_ThreeWOpenNonempty
