import Mathlib

/-!
# Partial local obstructions for the quartic

Target task:
`no_quartic_solution (s d t : ℤ) (hd : 2 ≤ d) (hcop : Int.gcd s d = 1) :
  s^4 + s^2*d^2 - d^4 = t^2 → False`

The global hard case is still open here.  This file records two reusable branches
which match the task notes and the `DescentN14.lean` style:

* mod 4 obstruction: `s` even and `d` odd;
* mod 3 obstruction: `3 ∣ s` and `d` is a unit modulo 3.

No `ZMod` normalization is used below.  Instead we split residues by explicit
integer parametrisations, expand the square with `nlinarith`, and let `omega`
close the resulting linear modular contradiction.
-/

private lemma int_mod_three_cases (z : ℤ) :
    (∃ q : ℤ, z = 3 * q) ∨
      (∃ q : ℤ, z = 3 * q + 1) ∨
        (∃ q : ℤ, z = 3 * q - 1) := by
  omega

private lemma square_not_four_mul_sub_one (t K : ℤ)
    (h : t ^ 2 = 4 * K - 1) : False := by
  rcases Int.even_or_odd t with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have : 4 * c ^ 2 = 4 * K - 1 := by nlinarith
    omega
  · have : 4 * c ^ 2 + 4 * c + 1 = 4 * K - 1 := by nlinarith
    omega

private lemma square_not_three_mul_sub_one (t K : ℤ)
    (h : t ^ 2 = 3 * K - 1) : False := by
  rcases int_mod_three_cases t with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
  · have : 9 * c ^ 2 = 3 * K - 1 := by nlinarith
    omega
  · have : 9 * c ^ 2 + 6 * c + 1 = 3 * K - 1 := by nlinarith
    omega
  · have : 9 * c ^ 2 - 6 * c + 1 = 3 * K - 1 := by nlinarith
    omega

/-- The task's easy mod-4 branch: `s` even and `d` odd. -/
theorem no_quartic_solution_mod4_branch (s d t : ℤ)
    (hs_even : ∃ a : ℤ, s = 2 * a)
    (hd_odd : ∃ b : ℤ, d = 2 * b + 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  rcases hs_even with ⟨a, rfl⟩
  rcases hd_odd with ⟨b, rfl⟩
  have hmod : t ^ 2 =
      4 * (4 * a ^ 4 + 4 * a ^ 2 * b ^ 2 + 4 * a ^ 2 * b + a ^ 2
        - 4 * b ^ 4 - 8 * b ^ 3 - 6 * b ^ 2 - 2 * b) - 1 := by
    nlinarith
  exact square_not_four_mul_sub_one t _ hmod

/-- Alias with the task-note wording. -/
theorem no_quartic_solution_s_even_d_odd (s d t : ℤ)
    (hs_even : ∃ a : ℤ, s = 2 * a)
    (hd_odd : ∃ b : ℤ, d = 2 * b + 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False :=
  no_quartic_solution_mod4_branch s d t hs_even hd_odd h

/-- Integer-parametrised mod-3 branch, residue `d ≡ 1 (mod 3)`. -/
theorem no_quartic_solution_three_dvd_s_d_eq_one_mod3 (s d t : ℤ)
    (hs : ∃ a : ℤ, s = 3 * a)
    (hd : ∃ b : ℤ, d = 3 * b + 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  rcases hs with ⟨a, rfl⟩
  rcases hd with ⟨b, rfl⟩
  have hmod : t ^ 2 =
      3 * (27 * a ^ 4 + 27 * a ^ 2 * b ^ 2 + 18 * a ^ 2 * b + 3 * a ^ 2
        - 27 * b ^ 4 - 36 * b ^ 3 - 18 * b ^ 2 - 4 * b) - 1 := by
    nlinarith
  exact square_not_three_mul_sub_one t _ hmod

/-- Integer-parametrised mod-3 branch, residue `d ≡ -1 (mod 3)`. -/
theorem no_quartic_solution_three_dvd_s_d_eq_neg_one_mod3 (s d t : ℤ)
    (hs : ∃ a : ℤ, s = 3 * a)
    (hd : ∃ b : ℤ, d = 3 * b - 1)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  rcases hs with ⟨a, rfl⟩
  rcases hd with ⟨b, rfl⟩
  have hmod : t ^ 2 =
      3 * (27 * a ^ 4 + 27 * a ^ 2 * b ^ 2 - 18 * a ^ 2 * b + 3 * a ^ 2
        - 27 * b ^ 4 + 36 * b ^ 3 - 18 * b ^ 2 + 4 * b) - 1 := by
    nlinarith
  exact square_not_three_mul_sub_one t _ hmod

/-- Combined mod-3 branch: `3 ∣ s` and `3 ∤ d`. -/
theorem no_quartic_solution_three_dvd_s_three_not_dvd_d (s d t : ℤ)
    (hs : ∃ a : ℤ, s = 3 * a)
    (hd : ¬ (3 : ℤ) ∣ d)
    (h : s ^ 4 + s ^ 2 * d ^ 2 - d ^ 4 = t ^ 2) : False := by
  rcases int_mod_three_cases d with ⟨b, hb⟩ | ⟨b, hb⟩ | ⟨b, hb⟩
  · exact False.elim (hd ⟨b, hb⟩)
  · exact no_quartic_solution_three_dvd_s_d_eq_one_mod3 s d t hs ⟨b, hb⟩ h
  · exact no_quartic_solution_three_dvd_s_d_eq_neg_one_mod3 s d t hs ⟨b, hb⟩ h
