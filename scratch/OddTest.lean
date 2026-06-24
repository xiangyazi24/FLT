import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

open scoped Classical
namespace OddTest
variable {R : Type*} [CommRing R]

-- Odd recurrence step (over m : ℤ), direct in general R (no universal ring).
-- AdjRel(m+1..m+4) ⟹ AdjRel(2m+5).  Cofactors from sympy Gröbner (remainder 0).
example (b c d : R) (m : ℤ)
    (h2 : normEDS b c d (m+4) * normEDS b c d m
        = b^2 * normEDS b c d (m+3) * normEDS b c d (m+1) - c * normEDS b c d (m+2)^2)
    (h3 : normEDS b c d (m+5) * normEDS b c d (m+1)
        = b^2 * normEDS b c d (m+4) * normEDS b c d (m+2) - c * normEDS b c d (m+3)^2) :
    normEDS b c d (2*m+7) * normEDS b c d (2*m+3)
      = b^2 * normEDS b c d (2*m+6) * normEDS b c d (2*m+4) - c * normEDS b c d (2*m+5)^2 := by
  have o7 : normEDS b c d (2*m+7)
      = normEDS b c d (m+5) * normEDS b c d (m+3)^3 - normEDS b c d (m+2) * normEDS b c d (m+4)^3 := by
    rw [show (2*m+7:ℤ) = 2*(m+3)+1 by ring, normEDS_odd b c d (m+3),
        show ((m+3)+2:ℤ)=m+5 by ring, show ((m+3)-1:ℤ)=m+2 by ring, show ((m+3)+1:ℤ)=m+4 by ring]
  have o3 : normEDS b c d (2*m+3)
      = normEDS b c d (m+3) * normEDS b c d (m+1)^3 - normEDS b c d m * normEDS b c d (m+2)^3 := by
    rw [show (2*m+3:ℤ) = 2*(m+1)+1 by ring, normEDS_odd b c d (m+1),
        show ((m+1)+2:ℤ)=m+3 by ring, show ((m+1)-1:ℤ)=m by ring, show ((m+1)+1:ℤ)=m+2 by ring]
  have o5 : normEDS b c d (2*m+5)
      = normEDS b c d (m+4) * normEDS b c d (m+2)^3 - normEDS b c d (m+1) * normEDS b c d (m+3)^3 := by
    rw [show (2*m+5:ℤ) = 2*(m+2)+1 by ring, normEDS_odd b c d (m+2),
        show ((m+2)+2:ℤ)=m+4 by ring, show ((m+2)-1:ℤ)=m+1 by ring, show ((m+2)+1:ℤ)=m+3 by ring]
  have e6 : normEDS b c d (2*m+6) * b
      = normEDS b c d (m+2)^2 * normEDS b c d (m+3) * normEDS b c d (m+5)
        - normEDS b c d (m+1) * normEDS b c d (m+3) * normEDS b c d (m+4)^2 := by
    rw [show (2*m+6:ℤ) = 2*(m+3) by ring, normEDS_even b c d (m+3),
        show ((m+3)-1:ℤ)=m+2 by ring, show ((m+3)-2:ℤ)=m+1 by ring, show ((m+3)+2:ℤ)=m+5 by ring,
        show ((m+3)+1:ℤ)=m+4 by ring]
  have e4 : normEDS b c d (2*m+4) * b
      = normEDS b c d (m+1)^2 * normEDS b c d (m+2) * normEDS b c d (m+4)
        - normEDS b c d m * normEDS b c d (m+2) * normEDS b c d (m+3)^2 := by
    rw [show (2*m+4:ℤ) = 2*(m+2) by ring, normEDS_even b c d (m+2),
        show ((m+2)-1:ℤ)=m+1 by ring, show ((m+2)-2:ℤ)=m by ring, show ((m+2)+2:ℤ)=m+4 by ring,
        show ((m+2)+1:ℤ)=m+3 by ring]
  linear_combination
      (normEDS b c d (2*m+3)) * o7
    + (- normEDS b c d (m+2) * normEDS b c d (m+4)^3 + normEDS b c d (m+3)^3 * normEDS b c d (m+5)) * o3
    + (- b * normEDS b c d (2*m+4)) * e6
    + (normEDS b c d (m+1) * normEDS b c d (m+3) * normEDS b c d (m+4)^2
        - normEDS b c d (m+2)^2 * normEDS b c d (m+3) * normEDS b c d (m+5)) * e4
    + (- c * normEDS b c d (m+1) * normEDS b c d (m+3)^3 + c * normEDS b c d (m+2)^3 * normEDS b c d (m+4)
        + c * normEDS b c d (2*m+5)) * o5
    + (- normEDS b c d (m+1) * normEDS b c d (m+2) * normEDS b c d (m+3)^3 * normEDS b c d (m+4)
        + normEDS b c d (m+2)^4 * normEDS b c d (m+4)^2) * h2
    + (normEDS b c d (m+1)^2 * normEDS b c d (m+3)^4
        - normEDS b c d (m+1) * normEDS b c d (m+2)^3 * normEDS b c d (m+3) * normEDS b c d (m+4)) * h3

end OddTest
