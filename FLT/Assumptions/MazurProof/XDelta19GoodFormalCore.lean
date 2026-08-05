import FLT.Assumptions.MazurProof.XDelta19GoodWeakDescent

/-!
# The three-adic formal core for the good level-nineteen model

This file defines the formal-kernel filtration at three and proves that
tripling raises its level by one.  The proof uses exact rational
coordinates for the verified dual-forward composition.  It also packages
the separatedness argument and connects it to the weak three-descent.

The only input left to the reduction file is that `6P` belongs to this
formal kernel for every rational point `P`; the factor six is the order of
the good special fibre over `𝔽₃`.
-/

namespace MazurProof.XDelta19GoodFormalCore

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodWeakDescent

noncomputable section

/-! ## Rational coordinates of tripling -/

/-- The common denominator in the affine tripling formulas. -/
def tripleDen (x : ℚ) : ℚ :=
  x * (3 * x + 76) * (x ^ 2 + 60 * x + 912)

/-- The numerator of the horizontal tripling coordinate. -/
def tripleXNum (x : ℚ) : ℚ :=
  x ^ 9 - 14592 * x ^ 7 - 1177088 * x ^ 6 -
    35487744 * x ^ 5 - 168566784 * x ^ 4 +
    15985750016 * x ^ 3 + 409954418688 * x ^ 2 +
    3894566977536 * x + 12332795428864

/-- The factored numerator of the vertical tripling coordinate. -/
def tripleYNum (x y : ℚ) : ℚ :=
  y * (x ^ 3 - 2432 * x - 46208) *
    (x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104) *
    (x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
      516800 * x ^ 3 + 10905088 * x ^ 2 +
      119401472 * x + 533794816)

/-- The tripling denominator does not vanish away from the visible
three-torsion kernel. -/
theorem tripleDen_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    tripleDen x ≠ 0 := by
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hlin
    have hxval : x = -76 / 3 := by
      linarith
    rw [hxval] at h
    norm_num [OnGood] at h
    nlinarith [sq_nonneg y]
  exact mul_ne_zero (mul_ne_zero hx hlin) hquad

/-- The forward horizontal isogeny coordinate is the tripling
denominator in factored form. -/
private theorem threeIsogenyX_eq_den (x : ℚ) (hx : x ≠ 0) :
    threeIsogenyX x = 3 * tripleDen x / x ^ 3 := by
  unfold threeIsogenyX tripleDen
  field_simp [hx]
  ring

/-- The forward vertical isogeny coordinate has the displayed cubic
factor. -/
private theorem threeIsogenyY_eq_factor (x y : ℚ) (hx : x ≠ 0) :
    threeIsogenyY x y =
      27 * y * (x ^ 3 - 2432 * x - 46208) / x ^ 3 := by
  unfold threeIsogenyY
  field_simp [hx]
  ring

set_option maxHeartbeats 0 in
/-- The verified dual-forward composition has the displayed horizontal
rational function. -/
theorem tripleX_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyX (threeIsogenyX x) =
      tripleXNum x / tripleDen x ^ 2 := by
  have hd := tripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx]
  unfold dualThreeIsogenyX tripleXNum
  field_simp [hx, hd]
  unfold tripleDen
  ring

set_option maxHeartbeats 0 in
/-- The verified dual-forward composition has the displayed vertical
rational function. -/
theorem tripleY_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      tripleYNum x y / tripleDen x ^ 3 := by
  have hd := tripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx, threeIsogenyY_eq_factor x y hx]
  unfold dualThreeIsogenyY tripleYNum
  field_simp [hx, hd]
  unfold tripleDen
  ring

/-! ## Valuation helpers -/

/-- The three-adic valuation of an integer is nonnegative. -/
theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 3 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

/-- In a sum of unequal valuations, the term of smaller valuation
controls the sum. -/
theorem val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 3 a < padicValRat 3 b) :
    padicValRat 3 (a + b) = padicValRat 3 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by
      linarith
    have : padicValRat 3 b = padicValRat 3 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

/-- A finite sum of terms of valuation larger than `q` is zero or still
has valuation larger than `q`. -/
theorem val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    l.sum = 0 ∨ padicValRat 3 q < padicValRat 3 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 3 q < padicValRat 3 a :=
        hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 3 q < padicValRat 3 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

/-- Adding terms of strictly larger valuation does not change the
valuation of a nonzero leading term. -/
theorem val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    padicValRat 3 (q + l.sum) = padicValRat 3 q := by
  rcases val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact val_add_eq_left_of_lt hq hsum

/-- The valuation of an integral-coefficient monomial is bounded below
by the valuations of its variables. -/
theorem val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 3 x + (b : ℤ) * padicValRat 3 y ≤
      padicValRat 3 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow hx, padicValRat.pow hy]
  have hcval := val_int_nonneg c
  omega

/-- A monic polynomial at a negative-valuation argument is controlled by
its highest-degree term when every other degree is smaller. -/
theorem val_leading_poly {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hvx : padicValRat 3 x = -2 * k)
    (n : ℕ) (l : List (ℤ × ℕ))
    (hval : ∀ cb ∈ l,
      -2 * (n : ℤ) * k < -2 * (cb.2 : ℤ) * k)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    padicValRat 3
        (x ^ n +
          (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) =
      -2 * (n : ℤ) * k := by
  rw [val_add_list_eq (q := x ^ n)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero n hx
  · intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨cb, hcb, rfl⟩ := hz
    have hge := val_monomial_ge hx hy cb.1
      (hcoeff cb hcb) cb.2 0
    rw [hvx] at hge
    have hlead : padicValRat 3 (x ^ n) =
        -2 * (n : ℤ) * k := by
      rw [padicValRat.pow hx, hvx]
      ring
    rw [hlead]
    norm_num at hge ⊢
    have hge' : -2 * (cb.2 : ℤ) * k ≤
        padicValRat 3 ((cb.1 : ℚ) * x ^ cb.2) := by
      convert hge using 1
      ring
    rw [show -(2 * (n : ℤ) * k) = -2 * (n : ℤ) * k by ring]
    exact (hval cb hcb).trans_le hge'

/-! ## Valuations of the tripling coordinates -/

/-- The tripling denominator has valuation `1-8k` at formal level `k`. -/
private theorem tripleDen_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hcurve : OnGood x y)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (tripleDen x) = 1 - 8 * k := by
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hz
    apply tripleDen_ne_zero hx hcurve
    unfold tripleDen
    rw [hz]
    ring
  have hv3x : padicValRat 3 (3 * x) = 1 - 2 * k := by
    have hthree : padicValRat 3 (3 : ℚ) = 1 :=
      padicValRat.self (p := 3) (by norm_num)
    rw [padicValRat.mul (by norm_num) hx, hthree, hvx]
    ring
  have hvlin : padicValRat 3 (3 * x + 76) = 1 - 2 * k := by
    rw [val_add_eq_left_of_lt (a := 3 * x) (b := 76)
      (mul_ne_zero (by norm_num) hx) (by
        rw [hv3x]
        have h76 : 0 ≤ padicValRat 3 (76 : ℚ) := by
          simpa using val_int_nonneg 76
        omega), hv3x]
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hvquad :
      padicValRat 3 (x ^ 2 + 60 * x + 912) = -4 * k := by
    have hshape : x ^ 2 + 60 * x + 912 =
        x ^ 2 + [60 * x, (912 : ℚ)].sum := by
      simp
      ring
    rw [hshape, val_add_list_eq (q := x ^ 2)]
    · rw [padicValRat.pow hx, hvx]
      ring
    · exact pow_ne_zero 2 hx
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · have hge := val_monomial_ge hx hy 60 (by norm_num) 1 0
        rw [padicValRat.pow hx, hvx]
        norm_num at hge ⊢
        omega
      · have hge := val_int_nonneg 912
        rw [padicValRat.pow hx, hvx]
        norm_num at hge ⊢
        omega
  unfold tripleDen
  rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
    padicValRat.mul hx hlin, hvx, hvlin, hvquad]
  ring

/-- The horizontal tripling numerator has valuation `-18k`. -/
private theorem tripleXNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (tripleXNum x) = -18 * k := by
  let l : List (ℤ × ℕ) :=
    [(-14592, 7), (-1177088, 6), (-35487744, 5),
      (-168566784, 4), (15985750016, 3),
      (409954418688, 2), (3894566977536, 1),
      (12332795428864, 0)]
  have h := val_leading_poly hx hy hvx 9 l
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num <;> omega)
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  convert h using 1
  · simp [l, tripleXNum]
    ring
  · ring

/-- The vertical tripling numerator has valuation `-27k`. -/
private theorem tripleYNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k)
    (hvy : padicValRat 3 y = -3 * k) :
    padicValRat 3 (tripleYNum x y) = -27 * k := by
  let l1 : List (ℤ × ℕ) := [(-2432, 1), (-46208, 0)]
  let l2 : List (ℤ × ℕ) := [(76, 2), (2128, 1), (23104, 0)]
  let l3 : List (ℤ × ℕ) :=
    [(180, 5), (13376, 4), (516800, 3), (10905088, 2),
      (119401472, 1), (533794816, 0)]
  have hv1 :
      padicValRat 3 (x ^ 3 - 2432 * x - 46208) = -6 * k := by
    have h := val_leading_poly hx hy hvx 3 l1
      (by
        intro cb hcb
        simp [l1] at hcb
        rcases hcb with rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l1] at hcb
        rcases hcb with rfl | rfl <;> norm_num)
    convert h using 1
    · simp [l1]
      ring
    · ring
  have hv2 :
      padicValRat 3
        (x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104) = -6 * k := by
    have h := val_leading_poly hx hy hvx 3 l2
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num)
    convert h using 1
    · simp [l2]
      ring
    · ring
  have hv3 :
      padicValRat 3
        (x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
          516800 * x ^ 3 + 10905088 * x ^ 2 +
          119401472 * x + 533794816) = -12 * k := by
    have h := val_leading_poly hx hy hvx 6 l3
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num <;> omega)
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num)
    convert h using 1
    · simp [l3]
      ring
    · ring
  have hf1 : x ^ 3 - 2432 * x - 46208 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv1
    omega
  have hf2 : x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv2
    omega
  have hf3 :
      x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
        516800 * x ^ 3 + 10905088 * x ^ 2 +
        119401472 * x + 533794816 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv3
    omega
  unfold tripleYNum
  rw [padicValRat.mul
      (mul_ne_zero (mul_ne_zero hy hf1) hf2) hf3,
    padicValRat.mul (mul_ne_zero hy hf1) hf2,
    padicValRat.mul hy hf1, hvy, hv1, hv2, hv3]
  ring

/-! ## The formal filtration and tripling -/

/-- Membership in the formal kernel at three, expressed by affine
coordinate valuations. -/
def FormalAtThree : GoodPoint → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 3 x = -2 * k ∧
        padicValRat 3 y = -3 * k

/-- The exact positive level of a nonzero formal point. -/
def FormalLevel : GoodPoint → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 3 x = -2 * k ∧
        padicValRat 3 y = -3 * k

/-- Formal-kernel membership is zero or membership at a unique positive
level. -/
theorem FormalAtThree_iff (P : GoodPoint) :
    FormalAtThree P ↔ P = 0 ∨ ∃ k : ℤ, FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [FormalAtThree, FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

/-- Tripling raises the exact formal level by one. -/
theorem FormalLevel_triple {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) :
    FormalLevel (3 • P) (k + 1) := by
  cases P with
  | zero => simp [FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hcurve : OnGood x y :=
        (goodCurve_equation_iff x y).mp h.1
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      have hdval := tripleDen_val hx hy hk hcurve hvx
      have hXval := tripleXNum_val hx hy hk hvx
      have hYval := tripleYNum_val hx hy hk hvx hvy
      have hd : tripleDen x ≠ 0 := tripleDen_ne_zero hx hcurve
      have hX : tripleXNum x ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hXval
        omega
      have hY : tripleYNum x y ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hYval
        omega
      have hphi := threeIsogenyX_ne_zero hx hcurve
      have hcomp := dual_comp_threeIsogenyPoint
        (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)
      rw [threeIsogenyPoint_some_of_x_ne_zero h hx] at hcomp
      unfold WeierstrassCurve.Affine.Point.mk at hcomp
      rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
      rw [← hcomp]
      change 0 < k + 1 ∧
        padicValRat 3
          (dualThreeIsogenyX (threeIsogenyX x)) = -2 * (k + 1) ∧
        padicValRat 3
          (dualThreeIsogenyY
            (threeIsogenyX x) (threeIsogenyY x y)) =
              -3 * (k + 1)
      refine ⟨by omega, ?_, ?_⟩
      · rw [tripleX_formula hx hcurve,
          padicValRat.div hX (pow_ne_zero 2 hd), hXval,
          padicValRat.pow hd, hdval]
        ring
      · rw [tripleY_formula hx hcurve,
          padicValRat.div hY (pow_ne_zero 3 hd), hYval,
          padicValRat.pow hd, hdval]
        ring

/-- Tripling preserves the formal kernel and raises nonzero points one
level. -/
theorem FormalAtThree_triple {P : GoodPoint}
    (hP : FormalAtThree P) :
    FormalAtThree (3 • P) := by
  rw [FormalAtThree_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · exact Or.inr ⟨k + 1, FormalLevel_triple hk⟩

/-! ## Separatedness and weak descent -/

/-- A nonzero point has at most one exact formal level. -/
private theorem FormalLevel_unique {P : GoodPoint} {k l : ℤ}
    (hk : FormalLevel P k) (hl : FormalLevel P l) :
    k = l := by
  cases P with
  | zero => simp [FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

/-- Multiplication by `3^n` raises a formal level by exactly `n`. -/
theorem FormalLevel_three_power {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) (n : ℕ) :
    ∃ k' : ℤ, k' = k + (n : ℤ) ∧
      FormalLevel ((3 ^ n : ℕ) • P) k' := by
  induction n with
  | zero =>
      exact ⟨k, by simp, by simpa using hP⟩
  | succ n ih =>
      obtain ⟨l, hl, hlevel⟩ := ih
      have hpow : (3 ^ (n + 1) : ℕ) • P =
          3 • ((3 ^ n : ℕ) • P) := by
        rw [pow_succ, mul_nsmul]
      refine ⟨l + 1, by norm_num at hl ⊢; omega, ?_⟩
      rw [hpow]
      exact FormalLevel_triple hlevel

/-- A formal point divisible through formal points by every power of
three is zero. -/
theorem formal_separated (P : GoodPoint)
    (hP : FormalAtThree P)
    (hdiv : ∀ n : ℕ, ∃ Q : GoodPoint,
      FormalAtThree Q ∧ P = (3 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, FormalLevel P k := by
    rw [FormalAtThree_iff] at hP
    exact hP.resolve_left hP0
  obtain ⟨k, hk⟩ := hlevelP
  have hkpos : 0 < k := by
    cases P with
    | zero => exact (hP0 rfl).elim
    | some x y h => exact hk.1
  let n : ℕ := k.toNat + 1
  obtain ⟨Q, hQformal, hPQ⟩ := hdiv n
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, nsmul_zero] at hPQ
    exact hP0 hPQ
  have hlevelQ : ∃ l : ℤ, FormalLevel Q l := by
    rw [FormalAtThree_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  obtain ⟨l', hl', hlevel⟩ := FormalLevel_three_power hl n
  have hlevelP' : FormalLevel P l' := by
    rw [hPQ]
    exact hlevel
  have heq : l' = k := FormalLevel_unique hlevelP' hk
  have hkNat : (k.toNat : ℤ) = k :=
    Int.toNat_of_nonneg (le_of_lt hkpos)
  have hncast : (n : ℤ) = k + 1 := by
    dsimp [n]
    rw [hkNat]
  have hlpos : 0 < l := by
    cases Q with
    | zero => simp [FormalLevel] at hl
    | some x y h => exact hl.1
  omega

/-- Weak three-descent makes `3P` divisible by every power of three. -/
theorem three_nsmul_three_power_divisible
    (P : GoodPoint) (n : ℕ) :
    ∃ Q : GoodPoint,
      3 • P = (3 ^ n : ℕ) • (3 • Q) := by
  induction n with
  | zero =>
      exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨R, hR | hR | hR⟩ := weak_three_descent Q
      all_goals
        have hthreeQ : 3 • Q = 3 • (3 • R) := by
          subst Q
          simp [nsmul_add]
        refine ⟨R, ?_⟩
        calc
          3 • P = (3 ^ n : ℕ) • (3 • Q) := hQ
          _ = (3 ^ n : ℕ) • (3 • (3 • R)) := by rw [hthreeQ]
          _ = (3 ^ (n + 1) : ℕ) • (3 • R) := by
            have hp : (3 ^ (n + 1) : ℕ) = 3 ^ n * 3 := by
              simp [pow_succ, Nat.mul_comm]
            rw [hp, mul_nsmul']

/-- Weak descent and formal entry of every `6P` imply that every rational
point is killed by six. -/
theorem six_nsmul_eq_zero
    (hentry : ∀ Q : GoodPoint, FormalAtThree (6 • Q))
    (P : GoodPoint) :
    6 • P = 0 := by
  apply formal_separated (6 • P) (hentry P)
  intro n
  obtain ⟨Q, hQ⟩ := three_nsmul_three_power_divisible P n
  refine ⟨6 • Q, hentry Q, ?_⟩
  calc
    6 • P = (2 * 3) • P := by norm_num
    _ = 2 • (3 • P) := mul_nsmul' P 2 3
    _ = 2 • ((3 ^ n : ℕ) • (3 • Q)) := by rw [hQ]
    _ = (2 * 3 ^ n) • (3 • Q) :=
      (mul_nsmul' (3 • Q) 2 (3 ^ n)).symm
    _ = (3 ^ n * 2) • (3 • Q) := by rw [Nat.mul_comm 2]
    _ = (3 ^ n : ℕ) • (2 • (3 • Q)) :=
      mul_nsmul' (3 • Q) (3 ^ n) 2
    _ = (3 ^ n : ℕ) • (6 • Q) := by
      rw [show 6 • Q = 2 • (3 • Q) by
        exact mul_nsmul' Q 2 3]

end

end MazurProof.XDelta19GoodFormalCore
