import FLT.Assumptions.MazurProof.RationalPointsN18Descent

/-!
# The first 5-adic split for the order-18 rational-point obstruction

`RationalPointsN18Descent` proves that a noncuspidal point produces positive
pairwise-coprime integers `A`, `D`, `A + D` and positive coprime norm
parameters `e`, `f`, with

`e f = A D (A + D)`.

It also proves that the prime `5` occurs in exactly one member of each of
these two collections.  This file combines that allocation with the two
primitive `ℤ[√-2]` norm branches.  The result is a twelve-case congruence
split: the unit cube contributed by the unique 5-adic cusp factor is forced
to equal one of four explicit quadratic residues modulo five.
-/

namespace MazurProof.RationalPointsN18FiveDescent

open RationalPointsN18
open RationalPointsN18Descent

noncomputable section

/-- The three possible locations of `5` among `A`, `D`, `A + D`, together
with the corresponding unit-cube value of `normReal A D` modulo five. -/
def FiveCuspCongruence (A D rhs : ℤ) : Prop :=
  ((5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A + D ∧
      D ^ 3 ≡ rhs [ZMOD 5]) ∨
  ((5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ A + D ∧
      -A ^ 3 ≡ rhs [ZMOD 5]) ∨
  ((5 : ℤ) ∣ A + D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧
      A ^ 3 ≡ rhs [ZMOD 5])

/-- The exact mod-five alternatives in the branch
`normReal A D = e² - 2 f²`. -/
def FiveBranchOne (A D e f : ℤ) : Prop :=
  ((5 : ℤ) ∣ e ∧ ¬(5 : ℤ) ∣ f ∧
      FiveCuspCongruence A D (-2 * f ^ 2)) ∨
  ((5 : ℤ) ∣ f ∧ ¬(5 : ℤ) ∣ e ∧
      FiveCuspCongruence A D (e ^ 2))

/-- The exact mod-five alternatives in the branch
`normReal A D = 2 e² - f²`. -/
def FiveBranchTwo (A D e f : ℤ) : Prop :=
  ((5 : ℤ) ∣ e ∧ ¬(5 : ℤ) ∣ f ∧
      FiveCuspCongruence A D (-f ^ 2)) ∨
  ((5 : ℤ) ∣ f ∧ ¬(5 : ℤ) ∣ e ∧
      FiveCuspCongruence A D (2 * e ^ 2))

/-! ## The cusp-side unit cube -/

theorem normReal_mod_five_of_dvd_A {A D : ℤ} (hA : (5 : ℤ) ∣ A) :
    normReal A D ≡ D ^ 3 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd]
  have hdiv : (5 : ℤ) ∣ A * (A ^ 2 + A * D - 2 * D ^ 2) :=
    dvd_mul_of_dvd_left hA _
  convert hdiv using 1
  simp only [normReal]
  ring

theorem normReal_mod_five_of_dvd_D {A D : ℤ} (hD : (5 : ℤ) ∣ D) :
    normReal A D ≡ -A ^ 3 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd]
  have hdiv : (5 : ℤ) ∣ D * (A ^ 2 - 2 * A * D - D ^ 2) :=
    dvd_mul_of_dvd_left hD _
  convert hdiv using 1
  simp only [normReal]
  ring

theorem normReal_mod_five_of_dvd_sum {A D : ℤ} (hS : (5 : ℤ) ∣ A + D) :
    normReal A D ≡ A ^ 3 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd]
  have hdiv : (5 : ℤ) ∣ (A + D) * (A - D) * (2 * A + D) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hS _) _
  convert hdiv using 1
  simp only [normReal]
  ring

/-! ## The norm-parameter side -/

theorem branch_one_mod_five_of_dvd_e {A D e f : ℤ}
    (hform : normReal A D = e ^ 2 - 2 * f ^ 2) (he : (5 : ℤ) ∣ e) :
    normReal A D ≡ -2 * f ^ 2 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd, hform]
  have hsq : (5 : ℤ) ∣ e ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left he e
  have hneg : (5 : ℤ) ∣ -(e ^ 2) := by
    obtain ⟨k, hk⟩ := hsq
    exact ⟨-k, by rw [hk]; ring⟩
  convert hneg using 1 <;> try ring

theorem branch_one_mod_five_of_dvd_f {A D e f : ℤ}
    (hform : normReal A D = e ^ 2 - 2 * f ^ 2) (hf : (5 : ℤ) ∣ f) :
    normReal A D ≡ e ^ 2 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd, hform]
  have hsq : (5 : ℤ) ∣ f ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hf f
  have htwo : (5 : ℤ) ∣ 2 * f ^ 2 := dvd_mul_of_dvd_right hsq 2
  convert htwo using 1 <;> ring

theorem branch_two_mod_five_of_dvd_e {A D e f : ℤ}
    (hform : normReal A D = 2 * e ^ 2 - f ^ 2) (he : (5 : ℤ) ∣ e) :
    normReal A D ≡ -f ^ 2 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd, hform]
  have hsq : (5 : ℤ) ∣ e ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left he e
  have htwo : (5 : ℤ) ∣ 2 * e ^ 2 := dvd_mul_of_dvd_right hsq 2
  have hneg : (5 : ℤ) ∣ -(2 * e ^ 2) := by
    obtain ⟨k, hk⟩ := htwo
    exact ⟨-k, by rw [hk]; ring⟩
  convert hneg using 1 <;> try ring

theorem branch_two_mod_five_of_dvd_f {A D e f : ℤ}
    (hform : normReal A D = 2 * e ^ 2 - f ^ 2) (hf : (5 : ℤ) ∣ f) :
    normReal A D ≡ 2 * e ^ 2 [ZMOD 5] := by
  rw [Int.modEq_iff_dvd, hform]
  have hsq : (5 : ℤ) ∣ f ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hf f
  convert hsq using 1
  ring

/-! ## Combining the two unique allocations -/

theorem cusp_congruence_of_allocation {A D rhs : ℤ}
    (hP : normReal A D ≡ rhs [ZMOD 5])
    (hfactor :
      ((5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ A + D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D)) :
    FiveCuspCongruence A D rhs := by
  rcases hfactor with hA | hD | hS
  · exact Or.inl ⟨hA.1, hA.2.1, hA.2.2,
      (normReal_mod_five_of_dvd_A hA.1).symm.trans hP⟩
  · exact Or.inr (Or.inl ⟨hD.1, hD.2.1, hD.2.2,
      (normReal_mod_five_of_dvd_D hD.1).symm.trans hP⟩)
  · exact Or.inr (Or.inr ⟨hS.1, hS.2.1, hS.2.2,
      (normReal_mod_five_of_dvd_sum hS.1).symm.trans hP⟩)

theorem branch_one_five_split {A D e f : ℤ}
    (hform : normReal A D = e ^ 2 - 2 * f ^ 2)
    (hroot :
      ((5 : ℤ) ∣ e ∧ ¬(5 : ℤ) ∣ f) ∨
      ((5 : ℤ) ∣ f ∧ ¬(5 : ℤ) ∣ e))
    (hfactor :
      ((5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ A + D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D)) :
    FiveBranchOne A D e f := by
  rcases hroot with he | hf
  · exact Or.inl ⟨he.1, he.2,
      cusp_congruence_of_allocation (branch_one_mod_five_of_dvd_e hform he.1) hfactor⟩
  · exact Or.inr ⟨hf.1, hf.2,
      cusp_congruence_of_allocation (branch_one_mod_five_of_dvd_f hform hf.1) hfactor⟩

theorem branch_two_five_split {A D e f : ℤ}
    (hform : normReal A D = 2 * e ^ 2 - f ^ 2)
    (hroot :
      ((5 : ℤ) ∣ e ∧ ¬(5 : ℤ) ∣ f) ∨
      ((5 : ℤ) ∣ f ∧ ¬(5 : ℤ) ∣ e))
    (hfactor :
      ((5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ A + D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D)) :
    FiveBranchTwo A D e f := by
  rcases hroot with he | hf
  · exact Or.inl ⟨he.1, he.2,
      cusp_congruence_of_allocation (branch_two_mod_five_of_dvd_e hform he.1) hfactor⟩
  · exact Or.inr ⟨hf.1, hf.2,
      cusp_congruence_of_allocation (branch_two_mod_five_of_dvd_f hform hf.1) hfactor⟩

/-! ## Downstream seam from a rational point -/

/-- Every hypothetical noncuspidal rational point lies in one of the twelve
explicit mod-five norm/cusp cases encoded by `FiveBranchOne` and
`FiveBranchTwo`. -/
theorem noncuspidal_point_to_twelve_five_cases {U Y : ℚ}
    (hU0 : U ≠ 0) (hU1 : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    ∃ A D C e f : ℤ,
      0 < A ∧ 0 < D ∧ 0 < e ∧ 0 < f ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧ Int.gcd D (A + D) = 1 ∧
      Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      ((normReal A D = e ^ 2 - 2 * f ^ 2 ∧
          |C| = e ^ 2 + 2 * f ^ 2 ∧ FiveBranchOne A D e f) ∨
       (normReal A D = 2 * e ^ 2 - f ^ 2 ∧
          |C| = 2 * e ^ 2 + f ^ 2 ∧ FiveBranchTwo A D e f)) := by
  obtain ⟨A, D, C, e, f, hA, hD, he, hf, hcop, hcopAS, hcopDS,
      hcopEF, hmul, hforms, hroot, hfactor⟩ :=
    noncuspidal_point_to_five_descent hU0 hU1 hY
  refine ⟨A, D, C, e, f, hA, hD, he, hf, hcop, hcopAS, hcopDS,
    hcopEF, hmul, ?_⟩
  rcases hforms with hbranch | hbranch
  · exact Or.inl ⟨hbranch.1, hbranch.2,
      branch_one_five_split hbranch.1 hroot hfactor⟩
  · exact Or.inr ⟨hbranch.1, hbranch.2,
      branch_two_five_split hbranch.1 hroot hfactor⟩

end

end MazurProof.RationalPointsN18FiveDescent
