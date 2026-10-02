import FLT.Assumptions.MazurProof.N13ConstructedKernelDoubling

/-!
Operative source pin: 29e80dbc17c5fdf3a194618d65dc0676199e19f5.
FLT-C13-KERNEL r1. Source candidate; Lean and axiom checks NOT RUN.

Feed the constructed compatible reduction and its actual separated kernel
into the existing rational-point endgame. The affine theorem has exactly
the proposition still declared as C13Sextic_affine_x_is_cuspidal in
CyclicExclusion13. This module has no direct import or use of that target
declaration; dependency tracing is separate. The lead owns replacement,
compilation, and emitted-axiom validation.
-/

namespace MazurProof.N13ConstructedRationalPointTheorem

noncomputable section
open N13ConstructedReductionClassifier

theorem quotient_kernel_eq :
    compatibleReduction.classifier.red.ker = N13ConstructedSpecialization.specialization.ker := by
  rw [N13ReductionClassifier.Data.red_ker]
  rfl

theorem quotient_kernel_separated :
    N18RouteC.Separated.NSeparated compatibleReduction.classifier.red.ker 2 := by
  rw [quotient_kernel_eq]
  exact N13ConstructedKernelDoubling.actual_kernel_separated

theorem curvePoint_eq_cusp (P : N13RationalPointEndgame.RationalCurvePoint) :
    ∃ c : N13Mumford.Cusp13, P = N13Mumford.cuspPoint c :=
  compatibleReduction.curvePoint_eq_cusp quotient_kernel_separated P

/-- Exact replacement proposition for the existing N13 arithmetic boundary. -/
theorem affine_x_is_cuspidal :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1 :=
  compatibleReduction.affine_x_is_cuspidal quotient_kernel_separated

end
end MazurProof.N13ConstructedRationalPointTheorem
