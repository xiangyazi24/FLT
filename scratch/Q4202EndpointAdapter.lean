import Mathlib
import scratch.FermatFourthDifferenceN16

set_option autoImplicit false

namespace MazurProof.CyclicExclusion16

lemma no_coprime_fourth_difference_of_data
    {X Y Z : ℤ}
    (hXY : IsCoprime X Y) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hEq : Z ^ 2 = X ^ 4 - Y ^ 4) : False := by
  apply no_coprime_fourth_difference
  aesop

lemma no_twice_square_fourth_difference_of_data
    {a b c : ℤ}
    (hab : IsCoprime a b) (ha : Odd a) (hb : Odd b)
    (hEq : a ^ 4 + b ^ 4 = 2 * c ^ 2)
    (hne : a ^ 2 ≠ b ^ 2) : False := by
  apply no_twice_square_fourth_difference
  aesop

end MazurProof.CyclicExclusion16
