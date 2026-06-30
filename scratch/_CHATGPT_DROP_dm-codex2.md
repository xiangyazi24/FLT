# Q2431-RETRY denominator clearing Lean code

```lean
import Mathlib

def IntFourSqAP (a b c d : ℤ) : Prop :=
  b^2 - a^2 = c^2 - b^2 ∧ c^2 - b^2 = d^2 - c^2

structure RatIntScale4 (w x y z : ℚ) where
  M : ℤ
  hM : M ≠ 0
  W X Y Z : ℤ
  hW : (W : ℚ) = (M : ℚ) * w
  hX : (X : ℚ) = (M : ℚ) * x
  hY : (Y : ℚ) = (M : ℚ) * y
  hZ : (Z : ℚ) = (M : ℚ) * z

private theorem rat_int_scale_exists (q : ℚ) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ Q : ℤ, (Q : ℚ) = (M : ℚ) * q := by
  refine ⟨(q.den : ℤ), ?_, q.num, ?_⟩
  · exact_mod_cast (Rat.den_nz q)
  · have hden : (q.den : ℚ) ≠ 0 := by
      exact_mod_cast (Rat.den_nz q)
    calc
      (q.num : ℚ) = (q.den : ℚ) * ((q.num : ℚ) / q.den) := by
        field_simp [hden]
        ring
      _ = ((q.den : ℤ) : ℚ) * q := by
        rw [Rat.num_div_den q]
        simp

theorem rat_int_scale4_exists (w x y z : ℚ) : ∃ s : RatIntScale4 w x y z := by
  rcases rat_int_scale_exists w with ⟨mw, hmw, ww, hww⟩
  rcases rat_int_scale_exists x with ⟨mx, hmx, xx, hxx⟩
  rcases rat_int_scale_exists y with ⟨my, hmy, yy, hyy⟩
  rcases rat_int_scale_exists z with ⟨mz, hmz, zz, hzz⟩
  refine ⟨{
    M := mw * mx * my * mz
    hM := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero hmw hmx) hmy) hmz
    W := ww * mx * my * mz
    X := xx * mw * my * mz
    Y := yy * mw * mx * mz
    Z := zz * mw * mx * my
    hW := by
      push_cast
      rw [hww]
      ring
    hX := by
      push_cast
      rw [hxx]
      ring
    hY := by
      push_cast
      rw [hyy]
      ring
    hZ := by
      push_cast
      rw [hzz]
      ring
  }⟩

theorem intFourSqAP_of_ratIntScale4
    {w x y z : ℚ} (s : RatIntScale4 w x y z)
    (hAP : x^2 - w^2 = y^2 - x^2 ∧ y^2 - x^2 = z^2 - y^2) :
    IntFourSqAP s.W s.X s.Y s.Z := by
  constructor
  · have hq : ((s.X^2 - s.W^2 : ℤ) : ℚ) = ((s.Y^2 - s.X^2 : ℤ) : ℚ) := by
      calc
        ((s.X^2 - s.W^2 : ℤ) : ℚ)
            = ((s.M : ℚ) * x)^2 - ((s.M : ℚ) * w)^2 := by
              push_cast
              rw [s.hX, s.hW]
        _ = (s.M : ℚ)^2 * (x^2 - w^2) := by
              ring
        _ = (s.M : ℚ)^2 * (y^2 - x^2) := by
              rw [hAP.1]
        _ = ((s.M : ℚ) * y)^2 - ((s.M : ℚ) * x)^2 := by
              ring
        _ = ((s.Y^2 - s.X^2 : ℤ) : ℚ) := by
              push_cast
              rw [s.hY, s.hX]
    exact Int.cast_injective hq
  · have hq : ((s.Y^2 - s.X^2 : ℤ) : ℚ) = ((s.Z^2 - s.Y^2 : ℤ) : ℚ) := by
      calc
        ((s.Y^2 - s.X^2 : ℤ) : ℚ)
            = ((s.M : ℚ) * y)^2 - ((s.M : ℚ) * x)^2 := by
              push_cast
              rw [s.hY, s.hX]
        _ = (s.M : ℚ)^2 * (y^2 - x^2) := by
              ring
        _ = (s.M : ℚ)^2 * (z^2 - y^2) := by
              rw [hAP.2]
        _ = ((s.M : ℚ) * z)^2 - ((s.M : ℚ) * y)^2 := by
              ring
        _ = ((s.Z^2 - s.Y^2 : ℤ) : ℚ) := by
              push_cast
              rw [s.hZ, s.hY]
    exact Int.cast_injective hq
```
