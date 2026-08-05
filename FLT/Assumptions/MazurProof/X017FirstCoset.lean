import FLT.Assumptions.MazurProof.X017Descent

/-!
# The target squareclasses in the `X₀(17)` two-isogeny descent

The standard dual curve is

`y² = x(x² - 60x - 256)`.

Primitive denominator clearing initially permits first-coordinate
squareclasses `±1` and `±2`.  The two classes supported by `2` are excluded
by a three-stage parity descent.  Each parity step is certified by a small
kernel reduction over `ZMod 8`; the intervening divisions by `2` and `4` are
performed over the integers.

This file stops at the squareclass statement.  Converting square and
negative-square coordinates into the two forward-isogeny cosets is the next
separate layer.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FirstCoset

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.RationalPointsN15Descent
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model

/-! ## Small parity certificates -/

private def reduce8to2 : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `8³` residue triples in the first positive stage.
private theorem pos_stage0_mod8 :
    ∀ r B z : ZMod 8,
      z ^ 2 = 2 * r ^ 4 - 60 * r ^ 2 * B ^ 2 - 128 * B ^ 4 →
      reduce8to2 r = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- With `B` odd, the first divided equation forces `s` to be even.
private theorem pos_stage1_mod8 :
    ∀ s B u : ZMod 8,
      reduce8to2 B ≠ 0 →
      u ^ 2 = 2 * s ^ 4 - 15 * s ^ 2 * B ^ 2 - 8 * B ^ 4 →
      reduce8to2 s = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The second divided positive equation has no solution when `B` is odd.
private theorem no_pos_stage2_mod8 :
    ∀ t B v : ZMod 8,
      reduce8to2 B ≠ 0 →
      v ^ 2 ≠ 8 * t ^ 4 - 15 * t ^ 2 * B ^ 2 - 2 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `8³` residue triples in the first negative stage.
private theorem neg_stage0_mod8 :
    ∀ r B z : ZMod 8,
      z ^ 2 = -(2 * r ^ 4) - 60 * r ^ 2 * B ^ 2 + 128 * B ^ 4 →
      reduce8to2 r = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- With `B` odd, the first divided negative equation forces `s` to be even.
private theorem neg_stage1_mod8 :
    ∀ s B u : ZMod 8,
      reduce8to2 B ≠ 0 →
      u ^ 2 = -(2 * s ^ 4) - 15 * s ^ 2 * B ^ 2 + 8 * B ^ 4 →
      reduce8to2 s = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The second divided negative equation has no solution when `B` is odd.
private theorem no_neg_stage2_mod8 :
    ∀ t B v : ZMod 8,
      reduce8to2 B ≠ 0 →
      v ^ 2 ≠ -(8 * t ^ 4) - 15 * t ^ 2 * B ^ 2 + 2 * B ^ 4 := by
  decide

/-- Coprime integers cannot both vanish after reduction modulo two. -/
private theorem primitive_mod_two {r B : ℤ} (hcop : Int.gcd r B = 1) :
    reduce8to2 (r : ZMod 8) ≠ 0 ∨
      reduce8to2 (B : ZMod 8) ≠ 0 := by
  have hnot : ¬ ((2 : ℤ) ∣ r ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h2g : (2 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h2g
    norm_num at h2g
  have hmod2 : (r : ZMod 2) ≠ 0 ∨ (B : ZMod 2) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot
      ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp h.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp h.2⟩
  simpa [reduce8to2, ZMod.castHom_apply] using hmod2

/-- Vanishing modulo two is equivalent to integer divisibility by two. -/
private theorem two_dvd_of_reduce8to2_eq_zero {r : ℤ}
    (h : reduce8to2 (r : ZMod 8) = 0) :
    (2 : ℤ) ∣ r := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp
  simpa [reduce8to2, ZMod.castHom_apply] using h

/-! ## Exclusion of the two provisional `2`-classes -/

/-- The positive provisional `2`-squareclass has no primitive integral point
on its homogeneous quartic cover. -/
theorem no_standardDual_pos_two_cover
    (r B z : ℤ) (hcop : Int.gcd r B = 1)
    (h :
      z ^ 2 =
        2 * r ^ 4 - 60 * r ^ 2 * B ^ 2 - 128 * B ^ 4) :
    False := by
  have hmod0 := congrArg (fun n : ℤ => (n : ZMod 8)) h
  push_cast at hmod0
  have hrEvenMod :=
    pos_stage0_mod8 (r : ZMod 8) (B : ZMod 8) (z : ZMod 8) hmod0
  have hrEven : (2 : ℤ) ∣ r :=
    two_dvd_of_reduce8to2_eq_zero hrEvenMod
  obtain ⟨s, rfl⟩ := hrEven
  have hBOdd : reduce8to2 (B : ZMod 8) ≠ 0 := by
    rcases primitive_mod_two hcop with hs | hB
    · exact (hs hrEvenMod).elim
    · exact hB
  have hz4 : (4 : ℤ) ∣ z := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨2 * s ^ 4 - 15 * s ^ 2 * B ^ 2 - 8 * B ^ 4, ?_⟩
    rw [h]
    ring
  obtain ⟨u, rfl⟩ := hz4
  have h1 :
      u ^ 2 = 2 * s ^ 4 - 15 * s ^ 2 * B ^ 2 - 8 * B ^ 4 := by
    nlinarith [h]
  have hmod1 := congrArg (fun n : ℤ => (n : ZMod 8)) h1
  push_cast at hmod1
  have hsEvenMod :=
    pos_stage1_mod8 (s : ZMod 8) (B : ZMod 8) (u : ZMod 8)
      hBOdd hmod1
  have hsEven : (2 : ℤ) ∣ s :=
    two_dvd_of_reduce8to2_eq_zero hsEvenMod
  obtain ⟨t, rfl⟩ := hsEven
  have hu2 : (2 : ℤ) ∣ u := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨8 * t ^ 4 - 15 * t ^ 2 * B ^ 2 - 2 * B ^ 4, ?_⟩
    rw [h1]
    ring
  obtain ⟨v, rfl⟩ := hu2
  have h2 :
      v ^ 2 = 8 * t ^ 4 - 15 * t ^ 2 * B ^ 2 - 2 * B ^ 4 := by
    nlinarith [h1]
  have hmod2 := congrArg (fun n : ℤ => (n : ZMod 8)) h2
  push_cast at hmod2
  exact
    (no_pos_stage2_mod8 (t : ZMod 8) (B : ZMod 8) (v : ZMod 8)
      hBOdd) hmod2

/-- The negative provisional `2`-squareclass has no primitive integral point
on its homogeneous quartic cover. -/
theorem no_standardDual_neg_two_cover
    (r B z : ℤ) (hcop : Int.gcd r B = 1)
    (h :
      z ^ 2 =
        -(2 * r ^ 4) - 60 * r ^ 2 * B ^ 2 + 128 * B ^ 4) :
    False := by
  have hmod0 := congrArg (fun n : ℤ => (n : ZMod 8)) h
  push_cast at hmod0
  have hrEvenMod :=
    neg_stage0_mod8 (r : ZMod 8) (B : ZMod 8) (z : ZMod 8) hmod0
  have hrEven : (2 : ℤ) ∣ r :=
    two_dvd_of_reduce8to2_eq_zero hrEvenMod
  obtain ⟨s, rfl⟩ := hrEven
  have hBOdd : reduce8to2 (B : ZMod 8) ≠ 0 := by
    rcases primitive_mod_two hcop with hs | hB
    · exact (hs hrEvenMod).elim
    · exact hB
  have hz4 : (4 : ℤ) ∣ z := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨-(2 * s ^ 4) - 15 * s ^ 2 * B ^ 2 + 8 * B ^ 4, ?_⟩
    rw [h]
    ring
  obtain ⟨u, rfl⟩ := hz4
  have h1 :
      u ^ 2 = -(2 * s ^ 4) - 15 * s ^ 2 * B ^ 2 + 8 * B ^ 4 := by
    nlinarith [h]
  have hmod1 := congrArg (fun n : ℤ => (n : ZMod 8)) h1
  push_cast at hmod1
  have hsEvenMod :=
    neg_stage1_mod8 (s : ZMod 8) (B : ZMod 8) (u : ZMod 8)
      hBOdd hmod1
  have hsEven : (2 : ℤ) ∣ s :=
    two_dvd_of_reduce8to2_eq_zero hsEvenMod
  obtain ⟨t, rfl⟩ := hsEven
  have hu2 : (2 : ℤ) ∣ u := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨-(8 * t ^ 4) - 15 * t ^ 2 * B ^ 2 + 2 * B ^ 4, ?_⟩
    rw [h1]
    ring
  obtain ⟨v, rfl⟩ := hu2
  have h2 :
      v ^ 2 = -(8 * t ^ 4) - 15 * t ^ 2 * B ^ 2 + 2 * B ^ 4 := by
    nlinarith [h1]
  have hmod2 := congrArg (fun n : ℤ => (n : ZMod 8)) h2
  push_cast at hmod2
  exact
    (no_neg_stage2_mod8 (t : ZMod 8) (B : ZMod 8) (v : ZMod 8)
      hBOdd) hmod2

/-! ## Integral and rational squareclass exhaustion -/

/-- A squarefree divisor of `2⁸` is either `1` or `2`. -/
theorem squarefree_dvd_256 {d : ℕ} (hd : Squarefree d)
    (hdiv : d ∣ 256) :
    d = 1 ∨ d = 2 := by
  have hpow : d ∣ 2 ^ 8 := by
    norm_num at hdiv ⊢
    exact hdiv
  have hd2 : d ∣ 2 :=
    (hd.dvd_pow_iff_dvd (by norm_num : 8 ≠ 0)).mp hpow
  exact (Nat.dvd_prime Nat.prime_two).mp hd2

/-- Only squareclasses `1` and `-1` remain for a nonzero primitive first
coordinate on the standard dual curve. -/
theorem standardDual_first_squareclasses_reduced
    {A B C : ℤ} (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel :
      C ^ 2 = A * (A ^ 2 - 60 * A * B ^ 2 - 256 * B ^ 4)) :
    ∃ r : ℤ, A = r ^ 2 ∨ A = -(r ^ 2) := by
  have hmodel' :
      C ^ 2 =
        A * (A ^ 2 + (-60) * A * B ^ 2 + (-256) * B ^ 4) := by
    simpa [sub_eq_add_neg] using hmodel
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel'
  rcases squarefree_dvd_256 hd (by simpa using hdiv) with rfl | rfl
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · left
      simpa using h
    · right
      simpa using h
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA, hr]
        norm_num
      obtain ⟨z, hz⟩ :=
        quartic_cover_of_squareclass
          (a := -60) (b := -256) (d := 2) (e := -128)
          (by norm_num) hr0 (by norm_num) hA hmodel'
      exact
        (no_standardDual_pos_two_cover r B z
          (root_coprime_denominator hcop hA)
          (by simpa [sub_eq_add_neg] using hz)).elim
    · have hA' : A = (-2) * (r : ℤ) ^ 2 := by
        simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA', hr]
        norm_num
      obtain ⟨z, hz⟩ :=
        quartic_cover_of_squareclass
          (a := -60) (b := -256) (d := -2) (e := 128)
          (by norm_num) hr0 (by norm_num) hA' hmodel'
      exact
        (no_standardDual_neg_two_cover r B z
          (root_coprime_denominator hcop hA')
          (by simpa [sub_eq_add_neg] using hz)).elim

/-- Every nonkernel rational affine point on the standard dual curve has
square or negative-square first coordinate. -/
theorem standardDual_x_squareclass {x y : ℚ}
    (h : Equation standardDual x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 ∨ x = -(q ^ 2) := by
  have hcurve0 :=
    (StandardTwoIsogeny.curve_equation
      (a := -2 * a17) (b := a17 ^ 2 - 4 * b17)).mp h
  have hcurve :
      y ^ 2 = x ^ 3 + (-60 : ℚ) * x ^ 2 + (-256 : ℚ) * x := by
    norm_num [a17, b17, veluT] at hcurve0
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    integral_model_monic (-60) (-256) x y hcurve
  have hA0 : A ≠ 0 := by
    intro hA
    apply hx0
    rw [hx, hA]
    norm_num
  obtain ⟨r, hr | hr⟩ :=
    standardDual_first_squareclasses_reduced hcop hA0 (by
      simpa [sub_eq_add_neg] using hmodel)
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
    rw [hx, hr]
    push_cast
    ring
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
    rw [hx, hr]
    push_cast
    ring

end MazurProof.X017FirstCoset
