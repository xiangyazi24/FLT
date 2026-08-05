import FLT.Assumptions.MazurProof.X017HeightDescent
import FLT.Assumptions.MazurProof.X017SecondCoset
import FLT.Assumptions.MazurProof.X017TwoTorsion
import scratch.A6TorsionFinite

/-!
# Rank zero for the standard X₀(17) model

The explicit two-isogeny descent gives two representatives modulo doubling.
The rational projective `x`-height has the Northcott property and expands by a
factor four under doubling, up to a uniform constant.  Summing this height over
the four translates by the visible order-four point removes the remaining
translation estimate and proves finite generation.  The exact cardinal bound
modulo doubling then forces the free rank to vanish.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017RankZero

open WeierstrassCurve.Affine
open MazurProof.X017ExactSequence
open MazurProof.X017HeightDescent
open MazurProof.X017Model
open MazurProof.X017SecondCoset
open MazurProof.X017TwoTorsion

noncomputable section

/-- The rational projective `x`-height is nonnegative on every point of the
standard model. -/
theorem xHeight_nonneg (P : Point standard) :
    0 ≤ MazurProof.xHeight standard P :=
  MazurProof.P1Q.logHeight_nonneg (MazurProof.xRep standard P)

/-- The visible point has order dividing four, as required by the
four-translate height symmetrization. -/
theorem four_nsmul_T : 4 • T = 0 := by
  simpa [T_order_four] using addOrderOf_nsmul_eq_zero T

/-- The rational points on the standard `X₀(17)` model form a finitely
generated abelian group.  This is an explicit height-descent proof rather than
an invocation of the general Mordell-Weil theorem. -/
noncomputable instance standardPoint_fg : AddGroup.FG (Point standard) := by
  obtain ⟨C, hC, hdouble⟩ :=
    MazurProof.xHeight_double_lower standard
  exact
    @fg_of_fourOrbitHeight (Point standard) inferInstance
      T (MazurProof.xHeight standard)
      (MazurProof.xHeight_northcott standard) C hC
      four_nsmul_T double_twoCosetExhaustion xHeight_nonneg hdouble

/-- The standard model has Mordell-Weil free rank zero.  Its quotient modulo
doubling has at most two elements, exactly the cardinality of its rational
two-torsion subgroup, so no nonzero free summand can remain. -/
theorem freeRank_eq_zero :
    AddCommGroup.freeRank (Point standard) = 0 := by
  letI :
      Fintype
        (MazurProof.RationalPointsN15ExactSequence.DoubleQuotient
          (Point standard)) :=
    doubleQuotientFintype
  apply freeRank_eq_zero_of_doubleQuotient_le_twoTorsion
  rw [natCard_twoTorsion]
  exact natCard_doubleQuotient_le_two

end

end MazurProof.X017RankZero
