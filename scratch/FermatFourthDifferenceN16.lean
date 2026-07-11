import Mathlib

set_option autoImplicit false

namespace MazurProof.CyclicExclusion16

structure CoprimeFourthDifference where
  X Y Z : ℤ
  hXY : IsCoprime X Y
  hX : X ≠ 0
  hY : Y ≠ 0
  hEq : Z ^ 2 = X ^ 4 - Y ^ 4

structure TwiceSquareFourthDifference where
  a b c : ℤ
  hab : IsCoprime a b
  ha : Odd a
  hb : Odd b
  hEq : a ^ 4 + b ^ 4 = 2 * c ^ 2
  hne : a ^ 2 ≠ b ^ 2

axiom no_coprime_fourth_difference (h : CoprimeFourthDifference) : False
axiom no_twice_square_fourth_difference (h : TwiceSquareFourthDifference) : False

end MazurProof.CyclicExclusion16
