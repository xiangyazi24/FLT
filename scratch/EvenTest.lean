import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

open scoped Classical
namespace EvenTest
variable {R : Type*} [CommRing R]

-- Even recurrence step, b²-SCALED (LHS even·even → carries b², intrinsic).
-- AdjRel(M+2),(M+3),(M+4) ⟹ b²·(AdjRel(2M+6) diff) = 0.  Cofactors: sympy Gröbner, remainder 0.
example (b c d : R) (M : ℤ)
    (h2 : normEDS b c d (M+4) * normEDS b c d M
        = b^2 * normEDS b c d (M+3) * normEDS b c d (M+1) - c * normEDS b c d (M+2)^2)
    (h3 : normEDS b c d (M+5) * normEDS b c d (M+1)
        = b^2 * normEDS b c d (M+4) * normEDS b c d (M+2) - c * normEDS b c d (M+3)^2)
    (h4 : normEDS b c d (M+6) * normEDS b c d (M+2)
        = b^2 * normEDS b c d (M+5) * normEDS b c d (M+3) - c * normEDS b c d (M+4)^2) :
    b^2 * (normEDS b c d (2*M+8) * normEDS b c d (2*M+4)
            - (b^2 * normEDS b c d (2*M+7) * normEDS b c d (2*M+5) - c * normEDS b c d (2*M+6)^2)) = 0 := by
  have e8 : normEDS b c d (2*M+8) * b
      = normEDS b c d (M+3)^2 * normEDS b c d (M+4) * normEDS b c d (M+6)
        - normEDS b c d (M+2) * normEDS b c d (M+4) * normEDS b c d (M+5)^2 := by
    rw [show (2*M+8:ℤ) = 2*(M+4) by ring, normEDS_even b c d (M+4),
        show ((M+4)-1:ℤ)=M+3 by ring, show ((M+4)+2:ℤ)=M+6 by ring, show ((M+4)-2:ℤ)=M+2 by ring,
        show ((M+4)+1:ℤ)=M+5 by ring]
  have e6 : normEDS b c d (2*M+6) * b
      = normEDS b c d (M+2)^2 * normEDS b c d (M+3) * normEDS b c d (M+5)
        - normEDS b c d (M+1) * normEDS b c d (M+3) * normEDS b c d (M+4)^2 := by
    rw [show (2*M+6:ℤ) = 2*(M+3) by ring, normEDS_even b c d (M+3),
        show ((M+3)-1:ℤ)=M+2 by ring, show ((M+3)-2:ℤ)=M+1 by ring, show ((M+3)+2:ℤ)=M+5 by ring,
        show ((M+3)+1:ℤ)=M+4 by ring]
  have e4 : normEDS b c d (2*M+4) * b
      = normEDS b c d (M+1)^2 * normEDS b c d (M+2) * normEDS b c d (M+4)
        - normEDS b c d M * normEDS b c d (M+2) * normEDS b c d (M+3)^2 := by
    rw [show (2*M+4:ℤ) = 2*(M+2) by ring, normEDS_even b c d (M+2),
        show ((M+2)-1:ℤ)=M+1 by ring, show ((M+2)-2:ℤ)=M by ring, show ((M+2)+2:ℤ)=M+4 by ring,
        show ((M+2)+1:ℤ)=M+3 by ring]
  have o7 : normEDS b c d (2*M+7)
      = normEDS b c d (M+5) * normEDS b c d (M+3)^3 - normEDS b c d (M+2) * normEDS b c d (M+4)^3 := by
    rw [show (2*M+7:ℤ) = 2*(M+3)+1 by ring, normEDS_odd b c d (M+3),
        show ((M+3)+2:ℤ)=M+5 by ring, show ((M+3)-1:ℤ)=M+2 by ring, show ((M+3)+1:ℤ)=M+4 by ring]
  have o5 : normEDS b c d (2*M+5)
      = normEDS b c d (M+4) * normEDS b c d (M+2)^3 - normEDS b c d (M+1) * normEDS b c d (M+3)^3 := by
    rw [show (2*M+5:ℤ) = 2*(M+2)+1 by ring, normEDS_odd b c d (M+2),
        show ((M+2)+2:ℤ)=M+4 by ring, show ((M+2)-1:ℤ)=M+1 by ring, show ((M+2)+1:ℤ)=M+3 by ring]
  linear_combination
      (b * normEDS b c d (2*M+4)) * e8
    + (b * c * normEDS b c d (2*M+6) - c * normEDS b c d (M+1) * normEDS b c d (M+3) * normEDS b c d (M+4)^2
        + c * normEDS b c d (M+2)^2 * normEDS b c d (M+3) * normEDS b c d (M+5)) * e6
    + (- normEDS b c d (M+2) * normEDS b c d (M+4) * normEDS b c d (M+5)^2
        + normEDS b c d (M+3)^2 * normEDS b c d (M+4) * normEDS b c d (M+6)) * e4
    + (- b^4 * normEDS b c d (2*M+5)) * o7
    + (b^4 * normEDS b c d (M+2) * normEDS b c d (M+4)^3 - b^4 * normEDS b c d (M+3)^3 * normEDS b c d (M+5)) * o5
    + (normEDS b c d (M+2)^2 * normEDS b c d (M+3)^2 * normEDS b c d (M+5)^2
        - normEDS b c d (M+2) * normEDS b c d (M+3)^4 * normEDS b c d (M+6)) * h2
    + (b^2 * normEDS b c d (M+1) * normEDS b c d (M+3)^3 * normEDS b c d (M+4)^2
        - b^2 * normEDS b c d (M+2)^3 * normEDS b c d (M+4)^3
        + b^2 * normEDS b c d (M+2)^2 * normEDS b c d (M+3)^3 * normEDS b c d (M+5)
        - c * normEDS b c d (M+2)^2 * normEDS b c d (M+3)^2 * normEDS b c d (M+4)^2
        - normEDS b c d (M+1) * normEDS b c d (M+2)^2 * normEDS b c d (M+4)^2 * normEDS b c d (M+5)) * h3
    + (- b^2 * normEDS b c d (M+1) * normEDS b c d (M+3)^5
        + c * normEDS b c d (M+2)^2 * normEDS b c d (M+3)^4
        + normEDS b c d (M+1)^2 * normEDS b c d (M+3)^2 * normEDS b c d (M+4)^2) * h4

end EvenTest
