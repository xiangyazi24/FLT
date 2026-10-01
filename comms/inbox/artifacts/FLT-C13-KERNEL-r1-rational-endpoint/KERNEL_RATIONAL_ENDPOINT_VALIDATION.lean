import FLT.Assumptions.MazurProof.N13ConstructedRationalPointTheorem

/- Lead-owned validation harness. NOT RUN by dot. -/

namespace MazurProof

example : N13RationalKernelDoublingAdapter.MappedSpecialFamily
    N13ConstructedSpecialization.specialization.ker :=
  N13ConstructedMappedSpecialFamily.mappedSpecialFamily

example : N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility
    N13ConstructedMappedSpecialFamily.nearBaseFamily :=
  N13ConstructedKernelDoubling.firstJetCompatibility

example : N18RouteC.Separated.NSeparated
    N13ConstructedSpecialization.specialization.ker 2 :=
  N13ConstructedKernelDoubling.actual_kernel_separated

example : ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1 :=
  N13ConstructedRationalPointTheorem.affine_x_is_cuspidal

#print axioms N13ConstructedMappedSpecialFamily.mappedSpecialFamily
#print axioms N13ConstructedKernelDoubling.forFamily
#print axioms N13ConstructedKernelDoubling.firstJetCompatibility
#print axioms N13ConstructedKernelDoubling.actual_kernel_separated
#print axioms N13ConstructedRationalPointTheorem.curvePoint_eq_cusp
#print axioms N13ConstructedRationalPointTheorem.affine_x_is_cuspidal

end MazurProof
