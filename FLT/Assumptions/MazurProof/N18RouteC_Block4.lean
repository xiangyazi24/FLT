import FLT.Assumptions.MazurProof.N18RouteC_PhiPreimage
import FLT.Assumptions.MazurProof.N18RouteC_Composition

/-!
# Weak three-descent for N18 Route C

The two Kummer computations are combined here.  The dual descent first
subtracts one of the three rational kernel points.  The forward descent then
shows that the resulting dual-isogeny preimage lies in the image of the
forward isogeny.  Their composition is multiplication by three.
-/

namespace MazurProof.N18RouteC.Block4

open Isogeny IsogenyPoints

noncomputable section

/-- Every `L`-point is a rational kernel representative modulo three. -/
theorem weak_three_descent (P : E0Point) :
    ∃ h : E0Point, 3 • h = 0 ∧
      ∃ Q : E0Point, P = h + 3 • Q := by
  obtain ⟨n, c, hc⟩ := DualSurvivor.kappa_cube_after_sub_torsion P
  obtain ⟨R, hR⟩ :=
    DualPreimage.exists_phihat_preimage_of_kappa_cube
      (P - n.val • T) ⟨c, hc⟩
  obtain ⟨Q, hQ⟩ := PhiPreimage.phiPoint_surjective R
  refine ⟨n.val • T, ?_, Q, ?_⟩
  · calc
      3 • (n.val • T) = n.val • (3 • T) := by
        rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
      _ = 0 := by
        rw [three_nsmul_T]
        exact nsmul_zero n.val
  · calc
      P = n.val • T + (P - n.val • T) := by abel
      _ = n.val • T + phihatPoint R := by rw [hR]
      _ = n.val • T + phihatPoint (phiPoint Q) := by rw [hQ]
      _ = n.val • T + 3 • Q := by rw [Composition.phihat_phi_point]

end

end MazurProof.N18RouteC.Block4
