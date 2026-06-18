import Mathlib

/-!
# Partial local obstructions for the quartic

Target task:
`no_quartic_solution (s d t : ℤ) (hd : 2 ≤ d) (hcop : Int.gcd s d = 1) :
  s^4 + s^2*d^2 - d^4 = t^2 → False`

The global hard case is still open here.  This file records two reusable, compiling
branches which match the task notes:

* mod 4 obstruction: `s` even and `d` odd;
* mod 3 obstruction: `3 ∣ s` and `d` is a unit modulo 3.

Both are stated first in the clean `ZMod` residue form, then with elementary
integer parametrisations.
-/

private lemma sq_zmod4_ne_three (x : ZMod 4) : x ^ 2 ≠ (3 : ZMod 4) := by
  fin_cases x <;> decide

private lemma sq_zmod3_ne_two (x : ZMod 3) : x ^ 2 ≠ (2 : ZMod 3) := by
  fin_cases x <;> decide

private lemma cast_quartic_mod (m : ℕ) (s d t : ℤ)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) :
    (s : ZMod m) ^ 4 + (s : ZMod m) ^ 2 * (d : ZMod m) ^ 2 - (d : ZMod m) ^ 4 =
      (t : ZMod m) ^ 2 := by
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow] using
    congrArg (fun x : ℤ => (x : ZMod m)) h

/-- The task's easy mod-4 branch: if `s² = 0` and `d² = 1` mod 4, then the
right side would be `3` mod 4, impossible for a square. -/
theorem no_quartic_solution_mod4_branch (s d t : ℤ)
    (hs2 : (s : ZMod 4) ^ 2 = 0)
    (hd2 : (d : ZMod 4) ^ 2 = 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  have hc := cast_quartic_mod 4 s d t h
  have ht : (t : ZMod 4) ^ 2 = 3 := by
    calc
      (t : ZMod 4) ^ 2 =
          (s : ZMod 4) ^ 4 + (s : ZMod 4) ^ 2 * (d : ZMod 4) ^ 2 -
            (d : ZMod 4) ^ 4 := hc.symm
      _ = 3 := by
        rw [show (s : ZMod 4) ^ 4 = ((s : ZMod 4) ^ 2) ^ 2 by ring]
        rw [show (d : ZMod 4) ^ 4 = ((d : ZMod 4) ^ 2) ^ 2 by ring]
        rw [hs2, hd2]
        decide
  exact sq_zmod4_ne_three (t : ZMod 4) ht

/-- Integer-parametrised form of the mod-4 branch: `s` even and `d` odd. -/
theorem no_quartic_solution_s_even_d_odd (s d t : ℤ)
    (hs_even : ∃ a : ℤ, s = 2 * a)
    (hd_odd : ∃ b : ℤ, d = 2 * b + 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  apply no_quartic_solution_mod4_branch s d t
  · rcases hs_even with ⟨a, rfl⟩
    ring_nf
  · rcases hd_odd with ⟨b, rfl⟩
    ring_nf
  · exact h

/-- The task's easy mod-3 branch: if `s² = 0` and `d² = 1` mod 3, then the
right side would be `2` mod 3, impossible for a square. -/
theorem no_quartic_solution_mod3_branch (s d t : ℤ)
    (hs2 : (s : ZMod 3) ^ 2 = 0)
    (hd2 : (d : ZMod 3) ^ 2 = 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  have hc := cast_quartic_mod 3 s d t h
  have ht : (t : ZMod 3) ^ 2 = 2 := by
    calc
      (t : ZMod 3) ^ 2 =
          (s : ZMod 3) ^ 4 + (s : ZMod 3) ^ 2 * (d : ZMod 3) ^ 2 -
            (d : ZMod 3) ^ 4 := hc.symm
      _ = 2 := by
        rw [show (s : ZMod 3) ^ 4 = ((s : ZMod 3) ^ 2) ^ 2 by ring]
        rw [show (d : ZMod 3) ^ 4 = ((d : ZMod 3) ^ 2) ^ 2 by ring]
        rw [hs2, hd2]
        decide
  exact sq_zmod3_ne_two (t : ZMod 3) ht

/-- Integer-parametrised mod-3 branch, residue `d ≡ 1 (mod 3)`. -/
theorem no_quartic_solution_three_dvd_s_d_eq_one_mod3 (s d t : ℤ)
    (hs : ∃ a : ℤ, s = 3 * a)
    (hd : ∃ b : ℤ, d = 3 * b + 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  apply no_quartic_solution_mod3_branch s d t
  · rcases hs with ⟨a, rfl⟩
    ring_nf
  · rcases hd with ⟨b, rfl⟩
    ring_nf
  · exact h

/-- Integer-parametrised mod-3 branch, residue `d ≡ -1 (mod 3)`. -/
theorem no_quartic_solution_three_dvd_s_d_eq_neg_one_mod3 (s d t : ℤ)
    (hs : ∃ a : ℤ, s = 3 * a)
    (hd : ∃ b : ℤ, d = 3 * b - 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  apply no_quartic_solution_mod3_branch s d t
  · rcases hs with ⟨a, rfl⟩
    ring_nf
  · rcases hd with ⟨b, rfl⟩
    ring_nf
  · exact h
