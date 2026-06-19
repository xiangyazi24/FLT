import Mathlib

/-!
# Rational-to-integer bridge for `20.a4`

The only curve-specific hard input is `rat_den_one_of_curve`: the denominator of
`u` is `1` for a nonzero rational point on `w²=u³+u²-u`.

The remaining two axioms are elementary facts about normalized rationals.  They
are separated so the remaining descent gap is exactly the `u.den = 1` theorem.
-/

/-- Hard denominator theorem supplied by the descent/quartic obstruction. -/
axiom rat_den_one_of_curve (u w : ℚ)
    (h : w ^ 2 = u ^ 3 + u ^ 2 - u)
    (hu : u ≠ 0) :
    u.den = 1

/-- Elementary rational API lemma: denominator `1` means the rational is its numerator. -/
axiom rat_eq_int_of_den_eq_one (r : ℚ) (hden : r.den = 1) :
    r = (r.num : ℚ)

/-- Elementary rational API/number-theory lemma: if a rational square is an integer, then the rational is an integer. -/
axiom rat_den_one_of_sq_int (r : ℚ) (N : ℤ)
    (h : r ^ 2 = (N : ℚ)) :
    r.den = 1

/--
Rational points on `w²=u³+u²-u` are integral, assuming the denominator theorem
for `u`.
-/
theorem rational_point_to_integer_point_20a4
    (u w : ℚ) (h : w ^ 2 = u ^ 3 + u ^ 2 - u) :
    ∃ U W : ℤ, u = ↑U ∧ w = ↑W ∧ W ^ 2 = U ^ 3 + U ^ 2 - U := by
  by_cases hu : u = 0
  · have hw_sq_zero : w ^ 2 = 0 := by
      simpa [hu] using h
    have hw_zero : w = 0 := by
      nlinarith [sq_nonneg w]
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · simpa using hu
    · simpa using hw_zero
    · norm_num
  · have hden_u : u.den = 1 := rat_den_one_of_curve u w h hu
    let U : ℤ := u.num
    have huU : u = (U : ℚ) := by
      dsimp [U]
      exact rat_eq_int_of_den_eq_one u hden_u

    have hw_sq_int : w ^ 2 = ((U ^ 3 + U ^ 2 - U : ℤ) : ℚ) := by
      calc
        w ^ 2 = (U : ℚ) ^ 3 + (U : ℚ) ^ 2 - (U : ℚ) := by
          simpa [huU] using h
        _ = ((U ^ 3 + U ^ 2 - U : ℤ) : ℚ) := by
          norm_num

    have hden_w : w.den = 1 :=
      rat_den_one_of_sq_int w (U ^ 3 + U ^ 2 - U) hw_sq_int
    let W : ℤ := w.num
    have hwW : w = (W : ℚ) := by
      dsimp [W]
      exact rat_eq_int_of_den_eq_one w hden_w

    have hcast : ((W ^ 2 : ℤ) : ℚ) = ((U ^ 3 + U ^ 2 - U : ℤ) : ℚ) := by
      have hw_sq_cast : w ^ 2 = ((W ^ 2 : ℤ) : ℚ) := by
        rw [hwW]
        norm_num
      exact hw_sq_cast.symm.trans hw_sq_int

    have hW : W ^ 2 = U ^ 3 + U ^ 2 - U := by
      exact_mod_cast hcast

    exact ⟨U, W, huU, hwW, hW⟩
