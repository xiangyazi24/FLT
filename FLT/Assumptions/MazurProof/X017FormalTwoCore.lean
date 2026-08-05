import FLT.Assumptions.MazurProof.X017Model

/-!
# The two-adic formal kernel of the integral X₀(17) model

This file proves the local part of the good-reduction argument on

`y² + xy + y = x³ - x² - x - 14`.

For a nonzero formal point, the affine valuations have the shape
`v₂(x) = -2k`, `v₂(y) = -3k` with `k > 0`.  Explicit duplication formulas
show that doubling either gives zero or raises `k` by at least one.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FormalTwoCore

open WeierstrassCurve.Affine
open MazurProof.X017Model

noncomputable section

/-! ## Elementary valuation lemmas -/

private theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 2 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

private theorem val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 2 a < padicValRat 2 b) :
    padicValRat 2 (a + b) = padicValRat 2 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by linarith
    have : padicValRat 2 b = padicValRat 2 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

private theorem val_const_mul_ge {a : ℚ} (z : ℤ) (hz : z ≠ 0) (ha : a ≠ 0) :
    padicValRat 2 a ≤ padicValRat 2 ((z : ℚ) * a) := by
  rw [padicValRat.mul (Int.cast_ne_zero.mpr hz) ha]
  have hzval := val_int_nonneg z
  omega

private theorem val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    l.sum = 0 ∨ padicValRat 2 q < padicValRat 2 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 2 q < padicValRat 2 a := hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 2 q < padicValRat 2 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

private theorem val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    padicValRat 2 (q + l.sum) = padicValRat 2 q := by
  rcases val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact val_add_eq_left_of_lt hq hsum

private theorem val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 2 x + (b : ℤ) * padicValRat 2 y ≤
      padicValRat 2 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow hx, padicValRat.pow hy]
  have hcval := val_int_nonneg c
  omega

/-! ## Explicit duplication formulas -/

/-- Denominator of the tangent slope on the integral model. -/
def doubleDen (x y : ℚ) : ℚ :=
  2 * y + x + 1

/-- Numerator of the horizontal coordinate after doubling. -/
def doubleXNum (x : ℚ) : ℚ :=
  x ^ 4 + x ^ 2 + 110 * x - 41

/-- Numerator of the vertical coordinate after doubling. -/
def doubleYNum (x y : ℚ) : ℚ :=
  x ^ 6 - 2 * x ^ 5 - 5 * x ^ 4 - 276 * x ^ 3 + 152 * x ^ 2 -
    95 * x + y * (-x ^ 4 - 4 * x ^ 3 + 2 * x ^ 2 - 108 * x + 96) - 1485

/-- The tangent formula for the horizontal coordinate has denominator
`doubleDen²`. -/
theorem doubleX_formula {x y : ℚ}
    (hd : doubleDen x y ≠ 0)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14) :
    addX X017 x x (slope X017 x x y y) =
      doubleXNum x / doubleDen x y ^ 2 := by
  have hneg : y ≠ negY X017 x y := by
    intro h
    apply hd
    simp [doubleDen, negY] at h ⊢
    linarith
  have hslope :
      slope X017 x x y y =
        (3 * x ^ 2 - 2 * x - 1 - y) / doubleDen x y := by
    rw [slope_of_Y_ne rfl hneg]
    simp [doubleDen, negY]
    ring
  rw [hslope]
  unfold addX doubleXNum
  field_simp [hd]
  field_simp [hd]
  unfold doubleDen
  linear_combination (-8 * x + 3) * hE

/-- The tangent formula for the vertical coordinate has denominator
`doubleDen³`. -/
theorem doubleY_formula {x y : ℚ}
    (hd : doubleDen x y ≠ 0)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14) :
    addY X017 x x y (slope X017 x x y y) =
      doubleYNum x y / doubleDen x y ^ 3 := by
  have hneg : y ≠ negY X017 x y := by
    intro h
    apply hd
    simp [doubleDen, negY] at h ⊢
    linarith
  have hslope :
      slope X017 x x y y =
        (3 * x ^ 2 - 2 * x - 1 - y) / doubleDen x y := by
    rw [slope_of_Y_ne rfl hneg]
    simp [doubleDen, negY]
    ring
  rw [hslope]
  unfold addY negAddY negY addX doubleYNum
  simp
  field_simp [hd]
  unfold doubleDen
  linear_combination
    (28 * x ^ 3 - 19 * x ^ 2 - x - 8 * y ^ 2 - 15 * y + 106) * hE

private theorem doubleXNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k) :
    padicValRat 2 (doubleXNum x) = -8 * k := by
  have hshape :
      doubleXNum x = x ^ 4 + [x ^ 2, 110 * x, (-41 : ℚ)].sum := by
    simp [doubleXNum]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 4)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 4 hx
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · have hval2 : padicValRat 2 (x ^ 2) = -4 * k := by
        rw [padicValRat.pow hx, hvx]
        ring
      have hval4 : padicValRat 2 (x ^ 4) = -8 * k := by
        rw [padicValRat.pow hx, hvx]
        ring
      rw [hval4, hval2]
      omega
    · have hge := val_monomial_ge hx hy 110 (by norm_num) 1 0
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-41)
      rw [padicValRat.pow hx, hvx]
      norm_num at hge ⊢
      omega

private theorem doubleYNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k)
    (hvy : padicValRat 2 y = -3 * k) :
    padicValRat 2 (doubleYNum x y) = -12 * k := by
  let l : List ℚ :=
    [-2 * x ^ 5, -5 * x ^ 4, -276 * x ^ 3, 152 * x ^ 2, -95 * x,
      (-1 : ℚ) * x ^ 4 * y, -4 * x ^ 3 * y, 2 * x ^ 2 * y,
      -108 * x * y, 96 * y, (-1485 : ℚ)]
  have hshape : doubleYNum x y = x ^ 6 + l.sum := by
    simp [doubleYNum, l]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 6)]
  · rw [padicValRat.pow hx, hvx]
    ring
  · exact pow_ne_zero 6 hx
  · intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals rw [padicValRat.pow hx, hvx]
    · have hge := val_monomial_ge hx hy (-2) (by norm_num) 5 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-5) (by norm_num) 4 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-276) (by norm_num) 3 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 152 (by norm_num) 2 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-95) (by norm_num) 1 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-1) (by norm_num) 4 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-4) (by norm_num) 3 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 2 (by norm_num) 2 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-108) (by norm_num) 1 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 96 (by norm_num) 0 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-1485)
      norm_num at hge ⊢
      omega

/-! ## Formal levels and doubling -/

/-- A point lies in the two-adic formal kernel when its affine valuations are
`(-2k,-3k)` for some positive level `k`. -/
def FormalAtTwo : Point X017 → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

/-- The exact positive level of a nonzero formal point. -/
def FormalLevel : Point X017 → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

/-- A formal point is either infinity or a nonzero point with an exact
positive level. -/
theorem formalAtTwo_iff (P : Point X017) :
    FormalAtTwo P ↔ P = 0 ∨ ∃ k : ℤ, FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [FormalAtTwo, FormalLevel, Point.some_ne_zero, false_or]

/-- Doubling either reaches infinity or raises the formal level by at least
one.  This is the explicit `v₂([2]z) ≥ v₂(z)+1` estimate. -/
theorem formalLevel_double {P : Point X017} {k : ℤ}
    (hP : FormalLevel P k) :
    2 • P = 0 ∨
      ∃ k' : ℤ, k + 1 ≤ k' ∧ FormalLevel (2 • P) k' := by
  cases P with
  | zero => simp [FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      by_cases hd : doubleDen x y = 0
      · left
        rw [two_nsmul]
        apply Point.add_self_of_Y_eq
        simp [doubleDen, negY] at hd ⊢
        linarith
      · have hv2y : padicValRat 2 (2 * y) = 1 - 3 * k := by
          have hv2 : padicValRat 2 (2 : ℚ) = 1 :=
            padicValRat.self (by norm_num : 1 < 2)
          rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hy, hv2, hvy]
          ring
        have hvfirst :
            1 - 3 * k ≤ padicValRat 2 (2 * y + x) := by
          by_cases hfirst : 2 * y + x = 0
          · rw [hfirst, padicValRat.zero]
            omega
          · have hmin := padicValRat.min_le_padicValRat_add (p := 2)
              (q := 2 * y) (r := x) hfirst
            rw [hv2y, hvx, min_eq_left (by omega)] at hmin
            exact hmin
        have hvdenLower :
            1 - 3 * k ≤ padicValRat 2 (doubleDen x y) := by
          have hmin := padicValRat.min_le_padicValRat_add (p := 2)
            (q := 2 * y + x) (r := 1)
            (by simpa [doubleDen] using hd)
          rw [padicValRat.one] at hmin
          have hlower :
              1 - 3 * k ≤ min (padicValRat 2 (2 * y + x)) 0 :=
            le_min hvfirst (by omega)
          exact hlower.trans (by simpa [doubleDen] using hmin)
        let k' : ℤ := 4 * k + padicValRat 2 (doubleDen x y)
        have hkstep : k + 1 ≤ k' := by
          dsimp [k']
          omega
        have hk' : 0 < k' := by omega
        have hvN := doubleXNum_val hx hy hk hvx
        have hvY := doubleYNum_val hx hy hk hvx hvy
        have hN : doubleXNum x ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvN
          omega
        have hY : doubleYNum x y ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvY
          omega
        have hE := (X017_equation_iff x y).mp h.left
        have hxform := doubleX_formula hd hE
        have hyform := doubleY_formula hd hE
        have hvx2 :
            padicValRat 2 (addX X017 x x (slope X017 x x y y)) =
              -2 * k' := by
          rw [hxform, padicValRat.div hN (pow_ne_zero 2 hd), hvN,
            padicValRat.pow hd]
          dsimp [k']
          ring
        have hvy2 :
            padicValRat 2 (addY X017 x x y (slope X017 x x y y)) =
              -3 * k' := by
          rw [hyform, padicValRat.div hY (pow_ne_zero 3 hd), hvY,
            padicValRat.pow hd]
          dsimp [k']
          ring
        right
        refine ⟨k', hkstep, ?_⟩
        have hneg : y ≠ negY X017 x y := by
          intro heq
          apply hd
          simp [doubleDen, negY] at heq ⊢
          linarith
        rw [two_nsmul, Point.add_self_of_Y_ne hneg]
        exact ⟨hk', hvx2, hvy2⟩

/-- Doubling preserves the two-adic formal kernel. -/
theorem formalAtTwo_double {P : Point X017}
    (hP : FormalAtTwo P) : FormalAtTwo (2 • P) := by
  rw [formalAtTwo_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · rcases formalLevel_double hk with hzero | ⟨k', _, hk'⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨k', hk'⟩

/-! ## Integral-or-formal dichotomy -/

/-- Good reduction at two gives the usual valuation dichotomy: an affine
rational point has two-integral coordinates, or it belongs to the formal
kernel with valuations `(-2k,-3k)`. -/
theorem formal_or_integral (P : Point X017) :
    FormalAtTwo P ∨
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat 2 x ∧ 0 ≤ padicValRat 2 y := by
  cases P with
  | zero => exact Or.inl trivial
  | some x y h =>
      have hE := (X017_equation_iff x y).mp h.left
      let vx := padicValRat 2 x
      let vy := padicValRat 2 y
      by_cases hxint : 0 ≤ vx
      · right
        refine ⟨hxint, ?_⟩
        by_contra hyint
        have hvyneg : vy < 0 := lt_of_not_ge hyint
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vy] at hvyneg
          rw [hy0, padicValRat.zero] at hvyneg
          omega
        let l : List ℚ :=
          [x * y, (1 : ℚ) * y, -(x ^ 3), x ^ 2,
            (1 : ℚ) * x, (14 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          linarith
        have hlead : padicValRat 2 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow hy]
          rfl
        have hgt :
            ∀ a ∈ l, padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · rw [hx0, zero_mul, padicValRat.zero, hlead]
              omega
            · rw [padicValRat.mul hx0 hy, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · rw [one_mul, hlead]
            dsimp [vy] at hvyneg ⊢
            omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 3 ≠ 0), neg_zero,
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 2 ≠ 0),
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.pow hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · rw [one_mul]
            by_cases hx0 : x = 0
            · rw [hx0, padicValRat.zero, hlead]
              omega
            · rw [hlead]
              dsimp [vx] at hxint ⊢
              omega
          · have hge := val_int_nonneg 14
            rw [hlead]
            norm_num at hge ⊢
            omega
        have hval := val_add_list_eq l (pow_ne_zero 2 hy) hgt
        rw [hshape, padicValRat.zero, hlead] at hval
        omega
      · have hvxneg : vx < 0 := lt_of_not_ge hxint
        have hx : x ≠ 0 := by
          intro hx0
          dsimp [vx] at hvxneg
          rw [hx0, padicValRat.zero] at hvxneg
          omega
        have hvylt : vy < vx := by
          by_contra hnot
          have hvxley : vx ≤ vy := le_of_not_gt hnot
          let l : List ℚ :=
            [y ^ 2, x * y, (1 : ℚ) * y, x ^ 2,
              (1 : ℚ) * x, (14 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            linarith
          have hlead : padicValRat 2 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow hx]
            rfl
          have hgt :
              ∀ a ∈ l, padicValRat 2 (-(x ^ 3)) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · rw [hy0, zero_pow (by norm_num : 2 ≠ 0),
                  padicValRat.zero, hlead]
                omega
              · rw [padicValRat.pow hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · by_cases hy0 : y = 0
              · rw [hy0, mul_zero, padicValRat.zero, hlead]
                omega
              · rw [padicValRat.mul hx hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · rw [one_mul, hlead]
              dsimp [vx, vy] at hvxneg hvxley ⊢
              omega
            · rw [hlead, padicValRat.pow hx]
              dsimp [vx] at hvxneg ⊢
              omega
            · rw [one_mul, hlead]
              dsimp [vx] at hvxneg ⊢
              omega
            · have hge := val_int_nonneg 14
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval :=
            val_add_list_eq l (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        let lleft : List ℚ := [x * y, y]
        have hleftshape :
            y ^ 2 + lleft.sum = y ^ 2 + x * y + y := by
          simp [lleft]
          ring
        have hleftgt :
            ∀ a ∈ lleft, padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [lleft, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [padicValRat.pow hy, padicValRat.mul hx hy]
            dsimp [vx, vy] at hvylt ⊢
            omega
          · rw [padicValRat.pow hy]
            dsimp [vy] at hvylt ⊢
            omega
        have hvleft0 :=
          val_add_list_eq lleft (pow_ne_zero 2 hy) hleftgt
        have hvleft :
            padicValRat 2 (y ^ 2 + x * y + y) = 2 * vy := by
          rw [← hleftshape, hvleft0, padicValRat.pow hy]
          rfl
        let lright : List ℚ := [-(x ^ 2), -x, (-14 : ℚ)]
        have hrightshape :
            x ^ 3 + lright.sum = x ^ 3 - x ^ 2 - x - 14 := by
          simp [lright]
          ring
        have hrightgt :
            ∀ a ∈ lright, padicValRat 2 (x ^ 3) < padicValRat 2 a := by
          intro a ha
          simp only [lright, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · rw [padicValRat.neg, padicValRat.pow hx,
              padicValRat.pow hx]
            dsimp [vx] at hvxneg ⊢
            omega
          · rw [padicValRat.neg, padicValRat.pow hx]
            dsimp [vx] at hvxneg ⊢
            omega
          · have hge := val_int_nonneg (-14)
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
        have hvright0 :=
          val_add_list_eq lright (pow_ne_zero 3 hx) hrightgt
        have hvright :
            padicValRat 2 (x ^ 3 - x ^ 2 - x - 14) = 3 * vx := by
          rw [← hrightshape, hvright0, padicValRat.pow hx]
          rfl
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 2 (y ^ 2 + x * y + y) := hvleft.symm
            _ = padicValRat 2 (x ^ 3 - x ^ 2 - x - 14) := by rw [hE]
            _ = 3 * vx := hvright
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

end

end MazurProof.X017FormalTwoCore
