import Mathlib

set_option autoImplicit false

namespace N15FormalBackup

open WeierstrassCurve
open WeierstrassCurve.Affine
open WeierstrassCurve.Affine.Point

/-- The good integral model used at `2`. -/
def E0 : WeierstrassCurve.Affine ℚ where
  a₁ := 1
  a₂ := 1
  a₃ := 1
  a₄ := -5
  a₆ := 2

instance : E0.IsElliptic where
  isUnit := by
    rw [isUnit_iff_ne_zero]
    norm_num [E0, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

lemma p2_on_E0 : E0.Equation (3 / 4 : ℚ) (-7 / 8 : ℚ) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [E0]

/-- The image on `E0` of the rational two-torsion point `(15,0)` on
`Y² = X(X-15)(X-16)`. -/
def P2 : E0.Point :=
  .some (3 / 4 : ℚ) (-7 / 8 : ℚ)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp p2_on_E0)

lemma P2_ne_zero : P2 ≠ 0 := by
  exact Point.some_ne_zero _

lemma P2_add_self : P2 + P2 = 0 := by
  apply Point.add_self_of_Y_eq
  norm_num [P2, E0, WeierstrassCurve.Affine.negY]

lemma two_smul_P2 : (2 : ℕ) • P2 = 0 := by
  simpa [two_nsmul] using P2_add_self

/-- The affine formal parameter `t=-x/y`, extended by `t(O)=0`. -/
def formalT : E0.Point → ℚ
  | 0 => 0
  | .some x y _ => -x / y

@[simp] lemma formalT_zero : formalT (0 : E0.Point) = 0 := rfl

lemma formalT_P2 : formalT P2 = 6 / 7 := by
  norm_num [formalT, P2]

lemma v2_formalT_P2 : padicValRat 2 (formalT P2) = 1 := by
  rw [formalT_P2]
  native_decide

/-- A deliberately minimal description of the first formal filtration.  The
zero point belongs to every filtration level. -/
def InFormalLevel (n : ℤ) (P : E0.Point) : Prop :=
  P = 0 ∨ formalT P ≠ 0 ∧ n ≤ padicValRat 2 (formalT P)

abbrev FormalKernel (P : E0.Point) : Prop := InFormalLevel 1 P

lemma P2_mem_formalKernel : FormalKernel P2 := by
  right
  constructor
  · rw [formalT_P2]
    norm_num
  · rw [v2_formalT_P2]

/-- The proposed finite-valued statement is false: `P2` is a nonzero point in
    the formal kernel, while `2P2=O`, and Mathlib defines
    `padicValRat 2 0 = 0`. -/
theorem proposed_n15_v2_formal_double_is_false :
    ¬ (∀ P : E0.Point, FormalKernel P → P ≠ 0 →
        padicValRat 2 (formalT ((2 : ℕ) • P)) ≥
          padicValRat 2 (formalT P) + 1) := by
  intro h
  have bad := h P2 P2_mem_formalKernel P2_ne_zero
  rw [two_smul_P2, formalT_zero, v2_formalT_P2] at bad
  norm_num [padicValRat] at bad

/-- Correct filtration form of the doubling estimate.  It treats `O` as
    belonging to every level, exactly as the extended valuation `v(0)=∞`
    would. -/
def FormalDoublingRaises : Prop :=
  ∀ (n : ℤ) (P : E0.Point), 1 ≤ n → InFormalLevel n P →
    InFormalLevel (n + 1) ((2 : ℕ) • P)

section AbstractWeakDescent

variable {G : Type*} [AddCommGroup G]

/-- Membership in every image of multiplication by a power of two. -/
def InfinitelyTwoDivisible (x : G) : Prop :=
  ∀ n : ℕ, ∃ y : G, x = (2 ^ n : ℕ) • y

/-- The separatedness statement needed after local formal-group analysis. -/
def TwoAdicallySeparated (G : Type*) [AddCommGroup G] : Prop :=
  ∀ x : G, InfinitelyTwoDivisible x → x = 0

/-- Iteration of `G = H + 2G`.  The weighted sum of representatives is folded
    back into the subgroup `H`, so the statement stays small. -/
theorem iterated_decomposition (H : AddSubgroup G)
    (hdecomp : ∀ x : G, ∃ h : H, ∃ y : G, x = (h : G) + (2 : ℕ) • y)
    (x : G) :
    ∀ n : ℕ, ∃ h : H, ∃ y : G, x = (h : G) + (2 ^ n : ℕ) • y := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, x, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨h, y, hxy⟩ := ih
      obtain ⟨h', z, hyz⟩ := hdecomp y
      refine ⟨h + (2 ^ n : ℕ) • h', z, ?_⟩
      rw [hxy, hyz]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, nsmul_add, pow_succ,
        ← mul_nsmul]
      rw [Nat.mul_comm (2 ^ n) 2]
      abel

/-- Multiplying by four removes all subgroup representatives.  Hence every
    `4x` is infinitely two-divisible. -/
theorem four_mul_infinitelyTwoDivisible (H : AddSubgroup G)
    (hdecomp : ∀ x : G, ∃ h : H, ∃ y : G, x = (h : G) + (2 : ℕ) • y)
    (hexp : ∀ h : H, (4 : ℕ) • (h : G) = 0)
    (x : G) : InfinitelyTwoDivisible ((4 : ℕ) • x) := by
  intro n
  obtain ⟨h, y, hxy⟩ := iterated_decomposition H hdecomp x n
  refine ⟨(4 : ℕ) • y, ?_⟩
  calc
    (4 : ℕ) • x = (4 : ℕ) • ((h : G) + (2 ^ n : ℕ) • y) := by rw [hxy]
    _ = (4 : ℕ) • (h : G) + (4 : ℕ) • ((2 ^ n : ℕ) • y) := by rw [nsmul_add]
    _ = (4 : ℕ) • ((2 ^ n : ℕ) • y) := by rw [hexp, zero_add]
    _ = (2 ^ n : ℕ) • ((4 : ℕ) • y) := by
      simp only [← mul_nsmul]
      rw [Nat.mul_comm]

/-- The exact group-theoretic final assembly used by the N15 argument. -/
theorem weak_descent_final (H : AddSubgroup G)
    (hdecomp : ∀ x : G, ∃ h : H, ∃ y : G, x = (h : G) + (2 : ℕ) • y)
    (hexp : ∀ h : H, (4 : ℕ) • (h : G) = 0)
    (hsep : TwoAdicallySeparated G)
    (hfour : ∀ x : G, (4 : ℕ) • x = 0 → x ∈ H) :
    ∀ x : G, x ∈ H := by
  intro x
  apply hfour x
  apply hsep
  exact four_mul_infinitelyTwoDivisible H hdecomp hexp x

end AbstractWeakDescent

end N15FormalBackup

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
    convert hw3a.pow_two using 1 <;> ring
  have hw2one : VAtLeast 1 (w ^ 2) := hw2.mono (by omega)
  have htw : VAtLeast (4 * a) (t * w) := by
    convert htA.mul hw3a using 1 <;> ring
  have htw1 : VAtLeast 1 (t * w) := htw.mono (by omega)

  have h2w1 : VAtLeast 1 (2 * w) := by
    convert VAtLeast.mul_natCast_left 2 hw1 using 1 <;> norm_num <;> ring
  have h10tw1 : VAtLeast 1 (10 * t * w) := by
    convert VAtLeast.mul_natCast_left 10 htw1 using 1 <;> norm_num <;> ring
  have h6w2one : VAtLeast 1 (6 * w ^ 2) := by
    convert VAtLeast.mul_natCast_left 6 hw2one using 1 <;> norm_num <;> ring
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

  have h3t2 : VAtLeast (2 * a) (3 * t ^ 2) := by
    convert VAtLeast.mul_natCast_left 3 ht2a using 1 <;> norm_num <;> ring
  have hw2a : VAtLeast (2 * a) w := hw3a.mono (by omega)
  have h2tw2a : VAtLeast (2 * a) (2 * t * w) := by
    have hraw := VAtLeast.mul_natCast_left 2 htw
    have hmono : VAtLeast (2 * a) ((2 : ℚ) * (t * w)) := hraw.mono (by omega)
    convert hmono using 1 <;> norm_num <;> ring
  have h5w2_2a : VAtLeast (2 * a) (5 * w ^ 2) := by
    have hraw := VAtLeast.mul_natCast_left 5 hw2
    have hmono : VAtLeast (2 * a) ((5 : ℚ) * w ^ 2) := hraw.mono (by omega)
    convert hmono using 1 <;> norm_num <;> ring
  have hA : VAtLeast (2 * a) (tangentA t w) := by
    unfold tangentA
    exact ((h3t2.add hw2a).add h2tw2a).sub h5w2_2a
  have hlam : VAtLeast (2 * a) (tangentLambda t w) := by
    unfold tangentLambda
    exact hA.div_unit hDunit.1 hDunit.2
  have hlam1 : VAtLeast 1 (tangentLambda t w) := hlam.mono (by omega)
  have hlam2 : VAtLeast (4 * a) (tangentLambda t w ^ 2) := by
    convert hlam.pow_two using 1 <;> ring
  have hlam3 : VAtLeast (6 * a) (tangentLambda t w ^ 3) := by
    convert hlam2.mul hlam using 1 <;> ring
  have hnu : VAtLeast (3 * a) (tangentNu t w) := by
    unfold tangentNu
    apply VAtLeast.sub hw3a
    convert hlam.mul htA using 1 <;> ring

  have h5lam2one : VAtLeast 1 (5 * tangentLambda t w ^ 2) := by
    have hraw := VAtLeast.mul_natCast_left 5 hlam2
    have hmono : VAtLeast 1 ((5 : ℚ) * tangentLambda t w ^ 2) := hraw.mono (by omega)
    convert hmono using 1 <;> norm_num <;> ring
  have h2lam3one : VAtLeast 1 (2 * tangentLambda t w ^ 3) := by
    have hraw := VAtLeast.mul_natCast_left 2 hlam3
    have hmono : VAtLeast 1 ((2 : ℚ) * tangentLambda t w ^ 3) := hraw.mono (by omega)
    convert hmono using 1 <;> norm_num <;> ring
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
    have hraw := VAtLeast.mul_natCast_left 10 (hlam.mul hnu)
    have hmono : VAtLeast (2 * a)
        ((10 : ℚ) * (tangentLambda t w * tangentNu t w)) := hraw.mono (by omega)
    convert hmono using 1 <;> norm_num <;> ring
  have h6lam2nu : VAtLeast (2 * a)
      (6 * tangentLambda t w ^ 2 * tangentNu t w) := by
    have hraw := VAtLeast.mul_natCast_left 6 (hlam2.mul hnu)
    have hmono : VAtLeast (2 * a)
        ((6 : ℚ) * (tangentLambda t w ^ 2 * tangentNu t w)) := hraw.mono (by omega)
    convert hmono using 1 <;> norm_num <;> ring
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
namespace N15FormalBackup

section ReductionKernel

variable {A : Type*} [AddCommGroup A]

/-- What `4P ∈ ker(red₂)` reduces to once a point-reduction homomorphism has
been supplied.  The pinned Mathlib has no such point-reduction map. -/
theorem n15_four_mul_mem_formalKernel
    (red : E0.Point →+ A)
    (hexp : ∀ Q : A, (4 : ℕ) • Q = 0)
    (hkernel : ∀ Q : E0.Point, FormalKernel Q ↔ red Q = 0)
    (P : E0.Point) : FormalKernel ((4 : ℕ) • P) := by
  rw [hkernel]
  rw [map_nsmul, hexp]

end ReductionKernel

section Separatedness

variable {G : Type*} [AddCommGroup G]

lemma iterate_level
    (L : ℕ → G → Prop)
    (hraise : ∀ n P, L n P → L (n + 1) ((2 : ℕ) • P))
    {P : G} (hP : L 1 P) :
    ∀ n : ℕ, L (n + 1) ((2 ^ n : ℕ) • P) := by
  intro n
  induction n with
  | zero => simpa using hP
  | succ n ih =>
      have h := hraise (n + 1) ((2 ^ n : ℕ) • P) ih
      simpa [pow_succ', smul_smul, Nat.mul_assoc] using h

/-- Abstract, axiom-free separatedness lemma.  For the actual elliptic curve,
`L n P` is the nth formal filtration and `hfinite` follows from the finite
2-adic valuation of the fixed nonzero rational parameter `t(P)`. -/
theorem n15_no_infinitely_two_divisible
    (L : ℕ → G → Prop)
    (hfour : ∀ Q : G, L 1 ((4 : ℕ) • Q))
    (hraise : ∀ n P, L n P → L (n + 1) ((2 : ℕ) • P))
    (hfinite : ∀ P : G, P ≠ 0 → ∃ B : ℕ, ¬ L (B + 1) P) :
    ∀ P : G, InfinitelyTwoDivisible P → P = 0 := by
  intro P hdiv
  by_contra hP0
  obtain ⟨B, hB⟩ := hfinite P hP0
  obtain ⟨Q, hQ⟩ := hdiv (B + 2)
  apply hB
  have hlev := iterate_level L hraise (n := B) (hfour Q)
  rw [hQ]
  simpa [smul_smul, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hlev

end Separatedness

/-- Final group-theoretic assembly after the curve-specific Kummer and local
formal-filtration hypotheses have actually been proved. -/
theorem n15_weak_descent_final
    (H : AddSubgroup E0.Point)
    (hdecomp : ∀ P : E0.Point,
      ∃ h : H, ∃ Q : E0.Point, P = (h : E0.Point) + (2 : ℕ) • Q)
    (hexp : ∀ h : H, (4 : ℕ) • (h : E0.Point) = 0)
    (hsep : TwoAdicallySeparated E0.Point)
    (hfour : ∀ P : E0.Point, (4 : ℕ) • P = 0 → P ∈ H) :
    ∀ P : E0.Point, P ∈ H :=
  weak_descent_final H hdecomp hexp hsep hfour

end N15FormalBackup
