import Mathlib

set_option autoImplicit false

namespace N15FormalBackup

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev v2 (q : ℚ) : ℤ := padicValRat 2 q

/-- `VAtLeast k q` is the finite-valued replacement for `v₂(q) ≥ k`, with
    zero treated as having infinite valuation. -/
def VAtLeast (k : ℤ) (q : ℚ) : Prop := q = 0 ∨ k ≤ v2 q

lemma VAtLeast.zero (k : ℤ) : VAtLeast k 0 := Or.inl rfl

lemma VAtLeast.of_ne {k : ℤ} {q : ℚ} (_hq0 : q ≠ 0) (hq : k ≤ v2 q) :
    VAtLeast k q := Or.inr hq

lemma VAtLeast.mono {j k : ℤ} {q : ℚ} (hjk : j ≤ k) (hq : VAtLeast k q) :
    VAtLeast j q := by
  rcases hq with rfl | hq
  · exact VAtLeast.zero _
  · exact Or.inr (hjk.trans hq)

lemma VAtLeast.neg {k : ℤ} {q : ℚ} (hq : VAtLeast k q) : VAtLeast k (-q) := by
  rcases hq with rfl | hq
  · simp [VAtLeast]
  · right
    simpa using hq

lemma VAtLeast.add {k : ℤ} {q r : ℚ}
    (hq : VAtLeast k q) (hr : VAtLeast k r) : VAtLeast k (q + r) := by
  by_cases hsum : q + r = 0
  · exact Or.inl hsum
  right
  rcases hq with hq0 | hq
  · subst q
    simpa using hr.resolve_left (by simpa using hsum)
  rcases hr with hr0 | hr
  · subst r
    simpa using hq
  exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add hsum)

lemma VAtLeast.sub {k : ℤ} {q r : ℚ}
    (hq : VAtLeast k q) (hr : VAtLeast k r) : VAtLeast k (q - r) := by
  simpa [sub_eq_add_neg] using hq.add hr.neg

lemma VAtLeast.mul {j k : ℤ} {q r : ℚ}
    (hq : VAtLeast j q) (hr : VAtLeast k r) : VAtLeast (j + k) (q * r) := by
  rcases hq with hqzero | hq
  · subst q
    simp [VAtLeast]
  rcases hr with hrzero | hr
  · subst r
    simp [VAtLeast]
  by_cases hq0 : q = 0
  · simp [hq0, VAtLeast]
  by_cases hr0 : r = 0
  · simp [hr0, VAtLeast]
  right
  change j ≤ padicValRat 2 q at hq
  change k ≤ padicValRat 2 r at hr
  change j + k ≤ padicValRat 2 (q * r)
  rw [padicValRat.mul hq0 hr0]
  omega

lemma VAtLeast.pow_two {k : ℤ} {q : ℚ} (hq : VAtLeast k q) :
    VAtLeast (2 * k) (q ^ 2) := by
  rcases hq with rfl | hq
  · simp [VAtLeast]
  by_cases hq0 : q = 0
  · simp [hq0, VAtLeast]
  right
  change k ≤ padicValRat 2 q at hq
  change 2 * k ≤ padicValRat 2 (q ^ 2)
  rw [padicValRat.pow hq0]
  omega

lemma VAtLeast.natCast (n : ℕ) : VAtLeast 0 (n : ℚ) := by
  by_cases hn : n = 0
  · simp [hn, VAtLeast]
  right
  exact zero_le_padicValRat_of_nat n

lemma VAtLeast.intCast (z : ℤ) : VAtLeast 0 (z : ℚ) := by
  by_cases hz : (z : ℚ) = 0
  · exact Or.inl hz
  right
  change 0 ≤ padicValRat 2 (z : ℚ)
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

lemma VAtLeast.mul_natCast_left (n : ℕ) {k : ℤ} {q : ℚ}
    (hq : VAtLeast k q) : VAtLeast k ((n : ℚ) * q) := by
  have h := (VAtLeast.natCast n).mul hq
  simpa only [zero_add] using h

lemma v2_two : v2 (2 : ℚ) = 1 := by
  exact padicValRat.self (by norm_num)

lemma VAtLeast.two_mul {k : ℤ} {q : ℚ} (hq : VAtLeast k q) :
    VAtLeast (k + 1) (2 * q) := by
  have h2 : VAtLeast 1 (2 : ℚ) := Or.inr (le_of_eq v2_two.symm)
  have h := h2.mul hq
  simpa only [add_comm] using h

/-- An element congruent to `1` modulo `2` is a 2-adic unit. -/
lemma v2_one_add_eq_zero {r : ℚ} (hr : VAtLeast 1 r) :
    1 + r ≠ 0 ∧ v2 (1 + r) = 0 := by
  rcases hr with rfl | hr
  · simp [v2]
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    norm_num [v2] at hr
  have hsum : (1 : ℚ) + r ≠ 0 := by
    intro h
    have hre : r = -1 := by linarith
    rw [hre] at hr
    norm_num [v2] at hr
  refine ⟨hsum, ?_⟩
  have hlt : padicValRat 2 (1 : ℚ) < padicValRat 2 r := by
    simp only [padicValRat.one]
    change 0 < v2 r
    omega
  simpa [v2] using padicValRat.add_eq_of_lt hsum one_ne_zero hr0 hlt

lemma v2_one_sub_eq_zero {r : ℚ} (hr : VAtLeast 1 r) :
    1 - r ≠ 0 ∧ v2 (1 - r) = 0 := by
  simpa [sub_eq_add_neg] using v2_one_add_eq_zero hr.neg

lemma VAtLeast.div_unit {k : ℤ} {q u : ℚ} (hq : VAtLeast k q)
    (hu0 : u ≠ 0) (hu : v2 u = 0) : VAtLeast k (q / u) := by
  rcases hq with rfl | hq
  · simp [VAtLeast]
  by_cases hq0 : q = 0
  · simp [hq0, VAtLeast]
  right
  change k ≤ padicValRat 2 q at hq
  change k ≤ padicValRat 2 (q / u)
  rw [padicValRat.div hq0 hu0]
  change k ≤ padicValRat 2 q - v2 u
  rw [hu, sub_zero]
  exact hq

/-- The exact finite rational expressions occurring in the tangent construction
    for the model `y²+xy+y=x³+x²-5x+2`. -/
def tangentA (t w : ℚ) : ℚ := 3 * t ^ 2 + w + 2 * t * w - 5 * w ^ 2

def tangentD (t w : ℚ) : ℚ := 1 - (t + t ^ 2 + 2 * w - 10 * t * w + 6 * w ^ 2)

def tangentLambda (t w : ℚ) : ℚ := tangentA t w / tangentD t w

def tangentNu (t w : ℚ) : ℚ := w - tangentLambda t w * t

def thirdDen (t w : ℚ) : ℚ :=
  1 + tangentLambda t w - 5 * tangentLambda t w ^ 2 + 2 * tangentLambda t w ^ 3

def thirdCorrNum (t w : ℚ) : ℚ :=
  tangentLambda t w + tangentLambda t w ^ 2 + tangentNu t w
    - 10 * tangentLambda t w * tangentNu t w
    + 6 * tangentLambda t w ^ 2 * tangentNu t w

def thirdT (t w : ℚ) : ℚ :=
  -2 * t - thirdCorrNum t w / thirdDen t w

def thirdW (t w : ℚ) : ℚ :=
  tangentLambda t w * thirdT t w + tangentNu t w

def formalDoubleT (t w : ℚ) : ℚ :=
  - thirdT t w / (1 - thirdT t w - thirdW t w)

/-- The local valuation calculation behind formal-group separatedness.  It is
    entirely finite: no power-series API or completeness theorem is used. -/
theorem n15_v2_formal_double_explicit {t w : ℚ}
    (_ht0 : t ≠ 0) (_hw0 : w ≠ 0)
    (ht : 1 ≤ v2 t)
    (hw : 3 * v2 t ≤ v2 w) :
    VAtLeast (v2 t + 1) (formalDoubleT t w) := by
  let a : ℤ := v2 t
  have ha : 1 ≤ a := ht
  have htA : VAtLeast a t := Or.inr (le_rfl)
  have ht1 : VAtLeast 1 t := htA.mono ha
  have ht2a : VAtLeast (2 * a) (t ^ 2) := htA.pow_two
  have ht2one : VAtLeast 1 (t ^ 2) := ht2a.mono (by omega)
  have hw3a : VAtLeast (3 * a) w := Or.inr hw
  have hw1 : VAtLeast 1 w := hw3a.mono (by omega)
  have hw2 : VAtLeast (6 * a) (w ^ 2) := by
    simpa only [mul_assoc] using hw3a.pow_two
  have hw2one : VAtLeast 1 (w ^ 2) := hw2.mono (by omega)
  have htw : VAtLeast (4 * a) (t * w) := by
    have h := htA.mul hw3a
    simpa only [add_eq_add_iff_left] using h
  have htw1 : VAtLeast 1 (t * w) := htw.mono (by omega)

  have h2w1 : VAtLeast 1 (2 * w) :=
    VAtLeast.mul_natCast_left 2 hw1
  have h10tw1 : VAtLeast 1 (10 * t * w) := by
    simpa only [mul_assoc] using VAtLeast.mul_natCast_left 10 htw1
  have h6w2one : VAtLeast 1 (6 * w ^ 2) :=
    VAtLeast.mul_natCast_left 6 hw2one
  have htailD : VAtLeast 1
      (-(t + t ^ 2 + 2 * w - 10 * t * w + 6 * w ^ 2)) := by
    apply VAtLeast.neg
    exact ((ht1.add ht2one).add h2w1).sub h10tw1 |>.add h6w2one
  have hDunit : tangentD t w ≠ 0 ∧ v2 (tangentD t w) = 0 := by
    rw [show tangentD t w =
      1 + (-(t + t ^ 2 + 2 * w - 10 * t * w + 6 * w ^ 2)) by
        unfold tangentD
        ring]
    exact v2_one_add_eq_zero htailD

  have h3t2 : VAtLeast (2 * a) (3 * t ^ 2) :=
    VAtLeast.mul_natCast_left 3 ht2a
  have hw2a : VAtLeast (2 * a) w := hw3a.mono (by omega)
  have h2tw2a : VAtLeast (2 * a) (2 * t * w) := by
    have h := VAtLeast.mul_natCast_left 2 htw
    simpa only [mul_assoc] using h.mono (by omega)
  have h5w2_2a : VAtLeast (2 * a) (5 * w ^ 2) :=
    (VAtLeast.mul_natCast_left 5 hw2).mono (by omega)
  have hA : VAtLeast (2 * a) (tangentA t w) := by
    unfold tangentA
    exact ((h3t2.add hw2a).add h2tw2a).sub h5w2_2a
  have hlam : VAtLeast (2 * a) (tangentLambda t w) := by
    unfold tangentLambda
    exact hA.div_unit hDunit.1 hDunit.2
  have hlam1 : VAtLeast 1 (tangentLambda t w) := hlam.mono (by omega)
  have hlam2 : VAtLeast (4 * a) (tangentLambda t w ^ 2) := by
    simpa only [mul_assoc] using hlam.pow_two
  have hlam3 : VAtLeast (6 * a) (tangentLambda t w ^ 3) := by
    have h := hlam2.mul hlam
    simpa only [add_eq_add_iff_left, pow_succ] using h
  have hnu : VAtLeast (3 * a) (tangentNu t w) := by
    unfold tangentNu
    apply VAtLeast.sub hw3a
    have h := hlam.mul htA
    simpa only [add_eq_add_iff_left] using h

  have h5lam2one : VAtLeast 1 (5 * tangentLambda t w ^ 2) :=
    (VAtLeast.mul_natCast_left 5 hlam2).mono (by omega)
  have h2lam3one : VAtLeast 1 (2 * tangentLambda t w ^ 3) :=
    (VAtLeast.mul_natCast_left 2 hlam3).mono (by omega)
  have hthirdTail : VAtLeast 1
      (tangentLambda t w - 5 * tangentLambda t w ^ 2
        + 2 * tangentLambda t w ^ 3) :=
    (hlam1.sub h5lam2one).add h2lam3one
  have hthirdDen : thirdDen t w ≠ 0 ∧ v2 (thirdDen t w) = 0 := by
    rw [show thirdDen t w = 1 +
        (tangentLambda t w - 5 * tangentLambda t w ^ 2 +
          2 * tangentLambda t w ^ 3) by
      unfold thirdDen
      ring]
    exact v2_one_add_eq_zero hthirdTail

  have hlam2_2a : VAtLeast (2 * a) (tangentLambda t w ^ 2) :=
    hlam2.mono (by omega)
  have hnu2a : VAtLeast (2 * a) (tangentNu t w) := hnu.mono (by omega)
  have h10lamnu : VAtLeast (2 * a)
      (10 * tangentLambda t w * tangentNu t w) := by
    have h := VAtLeast.mul_natCast_left 10 (hlam.mul hnu)
    simpa only [mul_assoc] using h.mono (by omega)
  have h6lam2nu : VAtLeast (2 * a)
      (6 * tangentLambda t w ^ 2 * tangentNu t w) := by
    have h := VAtLeast.mul_natCast_left 6 (hlam2.mul hnu)
    simpa only [mul_assoc] using h.mono (by omega)
  have hcorrNum : VAtLeast (2 * a) (thirdCorrNum t w) := by
    unfold thirdCorrNum
    exact ((hlam.add hlam2_2a).add hnu2a).sub h10lamnu |>.add h6lam2nu
  have hcorr : VAtLeast (2 * a) (thirdCorrNum t w / thirdDen t w) :=
    hcorrNum.div_unit hthirdDen.1 hthirdDen.2
  have h2t : VAtLeast (a + 1) (2 * t) := by
    simpa only [add_comm] using htA.two_mul
  have hneg2t : VAtLeast (a + 1) (-2 * t) := by
    simpa only [neg_mul] using h2t.neg
  have hthirdT : VAtLeast (a + 1) (thirdT t w) := by
    unfold thirdT
    exact hneg2t.sub (hcorr.mono (by omega))
  have hthirdT1 : VAtLeast 1 (thirdT t w) := hthirdT.mono (by omega)
  have hthirdW : VAtLeast 1 (thirdW t w) := by
    unfold thirdW
    apply VAtLeast.add
    · exact (hlam.mul hthirdT).mono (by omega)
    · exact hnu.mono (by omega)
  have hinvTail : VAtLeast 1 (thirdT t w + thirdW t w) :=
    hthirdT1.add hthirdW
  have hinvDen : 1 - (thirdT t w + thirdW t w) ≠ 0 ∧
      v2 (1 - (thirdT t w + thirdW t w)) = 0 :=
    v2_one_sub_eq_zero hinvTail
  unfold formalDoubleT
  rw [show 1 - thirdT t w - thirdW t w =
      1 - (thirdT t w + thirdW t w) by ring]
  exact hthirdT.neg.div_unit hinvDen.1 hinvDen.2

end N15FormalBackup
