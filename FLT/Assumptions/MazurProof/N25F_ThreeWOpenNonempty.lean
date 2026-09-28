import FLT.Assumptions.MazurProof.N25F_ThreeWChartDRegular
import FLT.Assumptions.MazurProof.N25F_ThreeBoundaryDiagnostic
import Mathlib.Data.ZMod.Basic

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
open N25F_ThreeBoundaryDiagnostic

local notation "k₃" => ZMod 3

/-- The W-chart quotient is nontrivial: 1 ≠ 0. -/
instance : Nontrivial WChartQuotientThree := by
  -- The evaluation map at [1,1,0] gives a homomorphism to ZMod 3
  -- Define the evaluation function: Fin 3 → ZMod 3
  let f : Fin 3 → k₃ := fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else 0
  let eval : WChartAmbientThree →+* k₃ :=
    MvPolynomial.eval f
  -- Helper: compute f at each index
  have hf0 : f 0 = (1 : k₃) := by simp [f]
  have hf1 : f 1 = (1 : k₃) := by simp [f]
  have hf2 : f 2 = (0 : k₃) := by simp [f]
  -- Check that the quadric and cubic vanish at this point
  have hq : eval wChartQuadricThree = 0 := by
    unfold wChartQuadricThree eval
    simp [MvPolynomial.eval_X, MvPolynomial.eval_add, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_neg,
      hf0, hf1, hf2]
  have hc : eval wChartCubicThree = 0 := by
    unfold wChartCubicThree eval
    simp [MvPolynomial.eval_X, MvPolynomial.eval_add, MvPolynomial.eval_sub,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow, hf0, hf1, hf2]
  -- The ideal is in the kernel of eval
  have hideal : wChartEquationIdealThree ≤ RingHom.ker eval := by
    rw [wChartEquationIdealThree, Ideal.span_le]
    intro f hf
    rcases hf with rfl | rfl
    · exact RingHom.mem_ker.mpr hq
    · exact RingHom.mem_ker.mpr hc
  -- Construct the quotient map
  let evalQuot : WChartQuotientThree →+* k₃ :=
    Ideal.Quotient.lift wChartEquationIdealThree eval hideal
  -- Since evalQuot 1 = 1 ≠ 0 in ZMod 3, the quotient is nontrivial
  exact RingHom.domain_nontrivial evalQuot

/-- The denominator D = x*z - x + z is not nilpotent in the W-chart quotient.
This implies the W-open is nonempty (there exists a prime ideal not containing D). -/
theorem wChartDenominatorThree_notNilpotent :
    ¬ IsNilpotent wChartDenominatorThree := by
  rintro ⟨n, hn⟩
  have h := wChartDenominatorThree_isRegular.pow n
  rw [hn] at h
  exact not_isRegular_zero h

/-- The W-open is nonempty: there exists a prime ideal in the W-chart quotient
that does not contain the denominator D. -/
theorem wOpenNonemptyThree :
    ∃ (p : Ideal WChartQuotientThree), p.IsPrime ∧ wChartDenominatorThree ∉ p := by
  have h := wChartDenominatorThree_notNilpotent
  rw [nilpotent_iff_mem_prime] at h
  push Not at h
  exact h

end MazurProof.N25F_ThreeWOpenNonempty
