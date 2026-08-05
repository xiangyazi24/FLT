import FLT.Assumptions.MazurProof.XDelta19GoodFormalCore

/-!
# Reduction into the three-adic formal kernel at level nineteen

The good model has six points over `𝔽₃`.  An integral rational point
reduces to one of

`(0,±1)`, `(1,±1)`, `(2,0)`.

For the first two pairs, doubling has positive horizontal valuation and
unit vertical valuation, so a further tripling enters the formal kernel.
For `(2,0)`, doubling itself enters the formal kernel.  Points with
negative horizontal valuation are already formal.  Consequently `[6]P`
is formal for every rational point.
-/

namespace MazurProof.XDelta19GoodFormalReduction

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodFormalCore

noncomputable section

/-! ## Integral-or-formal dichotomy -/

/-- An integral coefficient does not lower the valuation of a monomial
in one rational variable. -/
private theorem val_x_monomial_ge
    {x : ℚ} (hx : x ≠ 0) (c : ℤ) (hc : c ≠ 0) (a : ℕ) :
    (a : ℤ) * padicValRat 3 x ≤
      padicValRat 3 ((c : ℚ) * x ^ a) := by
  rw [padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow hx]
  have hcval := val_int_nonneg c
  omega

/-- Every rational affine point is either three-adically integral or
belongs to the formal kernel. -/
theorem formal_or_integral (P : GoodPoint) :
    FormalAtThree P ∨
      match P with
      | .zero => True
      | .some x y _ =>
          0 ≤ padicValRat 3 x ∧ 0 ≤ padicValRat 3 y := by
  cases P with
  | zero =>
      exact Or.inl trivial
  | some x y h =>
      have hE : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      let vx := padicValRat 3 x
      let vy := padicValRat 3 y
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
          [-(x ^ 3), -(64 * x ^ 2), -(1216 * x), (-5776 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnGood at hE
          linear_combination hE
        have hlead : padicValRat 3 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow hy]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 3 (y ^ 2) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow hx0, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := val_x_monomial_ge hx0 64 (by norm_num) 2
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := val_x_monomial_ge hx0 1216 (by norm_num) 1
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              norm_num at hge
              omega
          · have hge := val_int_nonneg (-5776)
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
            [y ^ 2, -(64 * x ^ 2), -(1216 * x), (-5776 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnGood at hE
            linear_combination hE
          have hlead : padicValRat 3 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow hx]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 3 (-(x ^ 3)) < padicValRat 3 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · simp [hy0, hlead]
                omega
              · rw [padicValRat.pow hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · have hge := val_x_monomial_ge hx 64 (by norm_num) 2
              simp only [padicValRat.neg]
              rw [padicValRat.pow hx]
              dsimp [vx] at hvxneg hge ⊢
              omega
            · have hge := val_x_monomial_ge hx 1216 (by norm_num) 1
              simp only [padicValRat.neg]
              rw [padicValRat.pow hx]
              dsimp [vx] at hvxneg hge ⊢
              norm_num at hge
              omega
            · have hge := val_int_nonneg (-5776)
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval := val_add_list_eq l
            (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        let l : List ℚ :=
          [64 * x ^ 2, 1216 * x, (5776 : ℚ)]
        have hshape : x ^ 3 + l.sum =
            x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 := by
          simp [l]
          ring
        have hgt : ∀ a ∈ l,
            padicValRat 3 (x ^ 3) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · have hge := val_x_monomial_ge hx 64 (by norm_num) 2
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
          · have hge := val_x_monomial_ge hx 1216 (by norm_num) 1
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg hge ⊢
            norm_num at hge
            omega
          · have hge := val_int_nonneg 5776
            rw [padicValRat.pow hx]
            dsimp [vx] at hvxneg ⊢
            norm_num at hge ⊢
            omega
        have hvright := val_add_list_eq l (pow_ne_zero 3 hx) hgt
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 3 (y ^ 2) := by
              rw [padicValRat.pow hy]
              dsimp [vy]
            _ = padicValRat 3 (x ^ 3 + (8 * x + 76) ^ 2) := by
              rw [hE]
            _ = padicValRat 3
                (x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776) := by
              congr 1
              ring
            _ = padicValRat 3 (x ^ 3 + l.sum) := by rw [hshape]
            _ = 3 * vx := by
              rw [hvright, padicValRat.pow hx]
              dsimp [vx]
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 3 x = -2 * k ∧
          padicValRat 3 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

/-! ## Reduction of integral rational coordinates -/

/-- A rational number of nonnegative valuation viewed as a three-adic
integer. -/
private noncomputable def ratPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 3 q) : ℤ_[3] :=
  ⟨(q : ℚ_[3]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

/-- Positive rational valuation is equivalent to zero reduction for a
nonzero integral rational number. -/
private theorem ratPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 3 q) :
    PadicInt.toZMod (ratPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[3])‖ < 1
  have hqcast : (q : ℚ_[3]) ≠ 0 := by
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (3 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (3 : ℝ))
    (by norm_num : (1 : ℝ) < 3)).2 (by omega)

/-- Zero reduction of a nonzero integral rational number forces positive
valuation. -/
private theorem val_pos_of_padicInt_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) = 0) :
    0 < padicValRat 3 q := by
  by_contra hnot
  have hv0 : padicValRat 3 q = 0 := by
    omega
  have hm : ratPadicInt q hqi ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [← PadicInt.ker_toZMod]
    exact hred
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖(q : ℚ_[3])‖ < 1 at hm
  have hqcast : (q : ℚ_[3]) ≠ 0 := by
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv0] at hm
  norm_num at hm

/-- Nonzero reduction of an integral nonzero rational number forces
valuation zero. -/
private theorem val_zero_of_padicInt_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) ≠ 0) :
    padicValRat 3 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 3 q :=
    lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := ratPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : ratPadicInt q hqi =
      ratPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

/-- The good equation holds in the three-adic integers for integral
rational coordinates. -/
private theorem padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnGood x y) :
    (ratPadicInt y hy) ^ 2 =
      (ratPadicInt x hx) ^ 3 + 64 * (ratPadicInt x hx) ^ 2 +
        1216 * ratPadicInt x hx + 5776 := by
  apply Subtype.ext
  change (y : ℚ_[3]) ^ 2 =
    (x : ℚ_[3]) ^ 3 + 64 * (x : ℚ_[3]) ^ 2 +
      1216 * (x : ℚ_[3]) + 5776
  unfold OnGood at hE
  exact_mod_cast
    (show y ^ 2 = x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 by
      nlinarith [hE])

set_option maxHeartbeats 0 in
/-- Exhaustive classification of affine points on the good special fibre
over `𝔽₃`. -/
private theorem mod_three_affine_points :
    ∀ X Y : ZMod 3,
      Y ^ 2 = X ^ 3 + 64 * X ^ 2 + 1216 * X + 5776 →
      (X = 0 ∧ Y ≠ 0) ∨ (X = 1 ∧ Y ≠ 0) ∨ (X = 2 ∧ Y = 0) := by
  decide

/-- Integral rational coordinates reduce to one of the three affine
residue types. -/
private theorem integral_reduction {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnGood x y) :
    let X := PadicInt.toZMod (ratPadicInt x hx)
    let Y := PadicInt.toZMod (ratPadicInt y hy)
    (X = 0 ∧ Y ≠ 0) ∨ (X = 1 ∧ Y ≠ 0) ∨ (X = 2 ∧ Y = 0) := by
  have hpadic := padicInt_equation hx hy hE
  have hred :
      PadicInt.toZMod (ratPadicInt y hy) ^ 2 =
        PadicInt.toZMod (ratPadicInt x hx) ^ 3 +
          64 * PadicInt.toZMod (ratPadicInt x hx) ^ 2 +
          1216 * PadicInt.toZMod (ratPadicInt x hx) + 5776 := by
    simpa only [map_pow, map_add, map_mul, map_ofNat] using
      congrArg PadicInt.toZMod hpadic
  exact mod_three_affine_points _ _ hred

/-! ## Explicit doubling coordinates -/

/-- Horizontal coordinate of twice an affine good-model point. -/
def doubleX (x y : ℚ) : ℚ :=
  x * (x ^ 3 - 2432 * x - 46208) / (4 * y ^ 2)

/-- Vertical coordinate of twice an affine good-model point. -/
def doubleY (x y : ℚ) : ℚ :=
  (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 + 115520 * x ^ 3 -
      28094464 * x - 266897408) / (8 * y ^ 3)

/-- The library doubling formula has the displayed horizontal
coordinate. -/
private theorem addX_self_eq_doubleX {x y : ℚ}
    (hy : y ≠ 0) (h : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x x y y
    WeierstrassCurve.Affine.addX goodCurve x x L = doubleX x y := by
  dsimp
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  unfold WeierstrassCurve.Affine.negY goodCurve doubleX
  field_simp [hy]
  unfold OnGood at h
  ring_nf at h ⊢
  linear_combination
    -32 * y ^ 2 * (x + 32) * h

/-- The library doubling formula has the displayed vertical
coordinate. -/
private theorem addY_self_eq_doubleY {x y : ℚ}
    (hy : y ≠ 0) (h : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x x y y
    WeierstrassCurve.Affine.addY goodCurve x x y L = doubleY x y := by
  dsimp
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  unfold WeierstrassCurve.Affine.addY
  unfold WeierstrassCurve.Affine.negAddY
  unfold WeierstrassCurve.Affine.negY
  unfold WeierstrassCurve.Affine.addX
  unfold goodCurve doubleY
  field_simp [hy]
  unfold OnGood at h
  ring_nf at h ⊢
  linear_combination
    32 * y ^ 3 *
      (7 * x ^ 3 + 448 * x ^ 2 + 9408 * x -
        2 * y ^ 2 + 66272) * h

/-- The displayed doubling coordinates are nonsingular because they are the
coordinates produced by the affine group law. -/
private theorem double_nonsingular {x y : ℚ}
    (hy : y ≠ 0)
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y) :
    WeierstrassCurve.Affine.Nonsingular goodCurve
      (doubleX x y) (doubleY x y) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  have hxadd := addX_self_eq_doubleX hy hcurve
  have hyadd := addY_self_eq_doubleY hy hcurve
  rw [← hxadd, ← hyadd]
  exact WeierstrassCurve.Affine.nonsingular_add h h
    (fun hxy => hneg hxy.right)

/-- Doubling a good-model point agrees with the two displayed rational
coordinate functions. -/
private theorem two_nsmul_eq_double_point {x y : ℚ}
    (hy : y ≠ 0)
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) =
      WeierstrassCurve.Affine.Point.some (doubleX x y) (doubleY x y)
        (double_nonsingular hy h) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_self_eq_doubleX hy hcurve,
    addY_self_eq_doubleY hy hcurve⟩

/-- A rational integer prime to three has valuation zero. -/
private theorem val_int_unit (z : ℤ) (hz : ¬(3 : ℤ) ∣ z) :
    padicValRat 3 (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
  norm_num

/-- A polynomial with unit constant term and all other terms of positive
valuation is a three-adic unit. -/
private theorem val_unit_constant_poly
    {x : ℚ} (hx : x ≠ 0) (hvx : 0 < padicValRat 3 x)
    (c : ℤ) (hc : ¬(3 : ℤ) ∣ c) (l : List (ℤ × ℕ))
    (hexp : ∀ cb ∈ l, 0 < cb.2)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    (c : ℚ) +
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 ∧
      padicValRat 3
        ((c : ℚ) +
          (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) = 0 := by
  have hc0 : (c : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (fun hz => hc (by simp [hz]))
  have hgt : ∀ a ∈
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2),
      padicValRat 3 (c : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨cb, hcb, rfl⟩ := ha
    have hge := val_x_monomial_ge hx cb.1
      (hcoeff cb hcb) cb.2
    rw [val_int_unit c hc]
    have hp := hexp cb hcb
    have hpZ : (0 : ℤ) < (cb.2 : ℤ) := by
      exact_mod_cast hp
    exact (mul_pos hpZ hvx).trans_le hge
  have hval := val_add_list_eq
    (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hc0 hgt
  have hne :
      (c : ℚ) +
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 := by
    intro hz
    have hsum :
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum = -(c : ℚ) := by
      linarith
    rcases val_sum_gt_or_zero
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hgt with
      hzero | hsumgt
    · rw [hzero] at hsum
      exact hc0 (by linarith)
    · rw [hsum, padicValRat.neg] at hsumgt
      omega
  exact ⟨hne, by rw [hval, val_int_unit c hc]⟩

/-! ## Doubling and tripling inside the formal kernel -/

/-- Doubling preserves every positive formal level. -/
theorem FormalLevel_double {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) :
    FormalLevel (2 • P) k := by
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
      let l3 : List (ℤ × ℕ) := [(-2432, 1), (-46208, 0)]
      have hv3 :
          padicValRat 3 (x ^ 3 - 2432 * x - 46208) = -6 * k := by
        have hv := val_leading_poly hx hy hvx 3 l3
          (by
            intro cb hcb
            simp [l3] at hcb
            rcases hcb with rfl | rfl <;> norm_num <;> omega)
          (by
            intro cb hcb
            simp [l3] at hcb
            rcases hcb with rfl | rfl <;> norm_num)
        convert hv using 1
        · simp [l3]
          ring
        · ring
      have hf3 : x ^ 3 - 2432 * x - 46208 ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hv3
        omega
      let l6 : List (ℤ × ℕ) :=
        [(128, 5), (6080, 4), (115520, 3),
          (-28094464, 1), (-266897408, 0)]
      have hv6 :
          padicValRat 3
            (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408) =
            -12 * k := by
        have hv := val_leading_poly hx hy hvx 6 l6
          (by
            intro cb hcb
            simp [l6] at hcb
            rcases hcb with rfl | rfl | rfl | rfl | rfl <;>
              norm_num <;> omega)
          (by
            intro cb hcb
            simp [l6] at hcb
            rcases hcb with rfl | rfl | rfl | rfl | rfl <;>
              norm_num)
        convert hv using 1
        · simp [l6]
          ring
        · ring
      have hf6 :
          x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
            115520 * x ^ 3 - 28094464 * x - 266897408 ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hv6
        omega
      have hdx : doubleX x y ≠ 0 := by
        unfold doubleX
        exact div_ne_zero (mul_ne_zero hx hf3)
          (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
      have hdy : doubleY x y ≠ 0 := by
        unfold doubleY
        exact div_ne_zero hf6
          (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
      have hvdx : padicValRat 3 (doubleX x y) = -2 * k := by
        have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
          val_int_unit 4 (by norm_num)
        unfold doubleX
        rw [padicValRat.div (mul_ne_zero hx hf3)
            (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
          padicValRat.mul hx hf3, hvx, hv3,
          padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
          hv4, padicValRat.pow hy, hvy]
        ring
      have hvdy : padicValRat 3 (doubleY x y) = -3 * k := by
        have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
          val_int_unit 8 (by norm_num)
        unfold doubleY
        rw [padicValRat.div hf6
            (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
          hv6, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
          hv8, padicValRat.pow hy, hvy]
        ring
      have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
        rw [goodCurve_negY]
        intro heq
        apply hy
        linarith
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
      change 0 < k ∧
        padicValRat 3
          (WeierstrassCurve.Affine.addX goodCurve x x
            (WeierstrassCurve.Affine.slope goodCurve x x y y)) =
              -2 * k ∧
        padicValRat 3
          (WeierstrassCurve.Affine.addY goodCurve x x y
            (WeierstrassCurve.Affine.slope goodCurve x x y y)) =
              -3 * k
      rw [addX_self_eq_doubleX hy hcurve,
        addY_self_eq_doubleY hy hcurve]
      exact ⟨hk, hvdx, hvdy⟩

/-- Doubling preserves the three-adic formal kernel. -/
theorem FormalAtThree_double {P : GoodPoint}
    (hP : FormalAtThree P) :
    FormalAtThree (2 • P) := by
  rw [FormalAtThree_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · exact Or.inr ⟨k, FormalLevel_double hk⟩

/-- A point with positive horizontal valuation and unit vertical
valuation enters the formal kernel after tripling. -/
private theorem triple_formal_of_x_pos
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hvx : 0 < padicValRat 3 x)
    (hvy : padicValRat 3 y = 0) :
    FormalAtThree
      (3 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, padicValRat.zero] at hvx
    omega
  have hy : y ≠ 0 := good_y_ne_zero hcurve
  have hd := tripleDen_ne_zero hx hcurve
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hz
    apply hd
    unfold tripleDen
    rw [hz]
    ring
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hv3 : padicValRat 3 (3 : ℚ) = 1 :=
    padicValRat.self (p := 3) (by norm_num)
  have hv76 : padicValRat 3 (76 : ℚ) = 0 :=
    val_int_unit 76 (by norm_num)
  have hv3x : padicValRat 3 (3 * x) =
      1 + padicValRat 3 x := by
    rw [padicValRat.mul (by norm_num) hx, hv3]
  have hvlin : padicValRat 3 (3 * x + 76) = 0 := by
    rw [add_comm, val_add_eq_left_of_lt (a := (76 : ℚ))
      (b := 3 * x) (by norm_num)
      (by rw [hv76, hv3x]; omega), hv76]
  have hv20 : padicValRat 3 (20 : ℚ) = 0 :=
    val_int_unit 20 (by norm_num)
  have hv60 : padicValRat 3 (60 : ℚ) = 1 := by
    rw [show (60 : ℚ) = 3 * 20 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv20]
    norm_num
  have hv304 : padicValRat 3 (304 : ℚ) = 0 :=
    val_int_unit 304 (by norm_num)
  have hv912 : padicValRat 3 (912 : ℚ) = 1 := by
    rw [show (912 : ℚ) = 3 * 304 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv304]
    norm_num
  let lq : List ℚ := [x ^ 2, 60 * x]
  have hshape : (912 : ℚ) + lq.sum =
      x ^ 2 + 60 * x + 912 := by
    simp [lq]
    ring
  have hgt : ∀ a ∈ lq,
      padicValRat 3 (912 : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [lq, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hv912, padicValRat.pow hx]
      omega
    · rw [hv912, padicValRat.mul (by norm_num) hx, hv60]
      omega
  have hvquad := val_add_list_eq lq (by norm_num) hgt
  rw [hshape, hv912] at hvquad
  have hdval : padicValRat 3 (tripleDen x) =
      padicValRat 3 x + 1 := by
    unfold tripleDen
    rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
      padicValRat.mul hx hlin, hvlin, hvquad]
    ring
  let lx : List (ℤ × ℕ) :=
    [(1, 9), (-14592, 7), (-1177088, 6), (-35487744, 5),
      (-168566784, 4), (15985750016, 3), (409954418688, 2),
      (3894566977536, 1)]
  have hX := val_unit_constant_poly hx hvx 12332795428864
    (by norm_num) lx
    (by
      intro cb hcb
      simp [lx] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by
      intro cb hcb
      simp [lx] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  have hXshape : ((12332795428864 : ℤ) : ℚ) +
      (lx.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        tripleXNum x := by
    simp [lx, tripleXNum]
    ring
  rw [hXshape] at hX
  obtain ⟨hXne, hXval⟩ := hX
  let l1 : List (ℤ × ℕ) := [(1, 3), (-2432, 1)]
  let l2 : List (ℤ × ℕ) := [(1, 3), (76, 2), (2128, 1)]
  let l3 : List (ℤ × ℕ) :=
    [(1, 6), (180, 5), (13376, 4), (516800, 3),
      (10905088, 2), (119401472, 1)]
  have h1 := val_unit_constant_poly hx hvx (-46208) (by norm_num) l1
    (by
      intro cb hcb
      simp [l1] at hcb
      rcases hcb with rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l1] at hcb
      rcases hcb with rfl | rfl <;> norm_num)
  have h2 := val_unit_constant_poly hx hvx 23104 (by norm_num) l2
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
  have h3 := val_unit_constant_poly hx hvx 533794816
    (by norm_num) l3
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  have hs1 : (((-46208 : ℤ) : ℚ)) +
      (l1.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 - 2432 * x - 46208 := by
    simp [l1]
    ring
  have hs2 : ((23104 : ℤ) : ℚ) +
      (l2.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104 := by
    simp [l2]
    ring
  have hs3 : ((533794816 : ℤ) : ℚ) +
      (l3.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
          516800 * x ^ 3 + 10905088 * x ^ 2 +
          119401472 * x + 533794816 := by
    simp [l3]
    ring
  rw [hs1] at h1
  rw [hs2] at h2
  rw [hs3] at h3
  rcases h1 with ⟨hne1, hv1⟩
  rcases h2 with ⟨hne2, hv2⟩
  rcases h3 with ⟨hne3, hv3f⟩
  have hYne : tripleYNum x y ≠ 0 := by
    unfold tripleYNum
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3
  have hYval : padicValRat 3 (tripleYNum x y) = 0 := by
    unfold tripleYNum
    rw [padicValRat.mul
        (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3,
      padicValRat.mul (mul_ne_zero hy hne1) hne2,
      padicValRat.mul hy hne1, hvy, hv1, hv2, hv3f]
    ring
  have hphi := threeIsogenyX_ne_zero hx hcurve
  have hcomp := dual_comp_threeIsogenyPoint
    (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)
  rw [threeIsogenyPoint_some_of_x_ne_zero h hx] at hcomp
  unfold WeierstrassCurve.Affine.Point.mk at hcomp
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
  rw [← hcomp]
  change ∃ k : ℤ, 0 < k ∧
    padicValRat 3
      (dualThreeIsogenyX (threeIsogenyX x)) = -2 * k ∧
    padicValRat 3
      (dualThreeIsogenyY
        (threeIsogenyX x) (threeIsogenyY x y)) = -3 * k
  refine ⟨padicValRat 3 x + 1, by omega, ?_, ?_⟩
  · rw [tripleX_formula hx hcurve,
      padicValRat.div hXne (pow_ne_zero 2 hd), hXval,
      padicValRat.pow hd, hdval]
    ring
  · rw [tripleY_formula hx hcurve,
      padicValRat.div hYne (pow_ne_zero 3 hd), hYval,
      padicValRat.pow hd, hdval]
    ring

/-- An affine point with first coordinate zero is killed by three and
therefore is formally trivial after tripling. -/
private theorem triple_formal_of_x_zero
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hx : x = 0) :
    FormalAtThree
      (3 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)) := by
  rw [three_nsmul_of_x_zero h hx]
  trivial

/-! ## Reading valuations from explicit PadicInt models -/

/-- A PadicInt expression whose value is rational certifies nonnegative
rational valuation. -/
private theorem val_nonneg_of_padicInt_model
    {q : ℚ} (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3])) :
    0 ≤ padicValRat 3 q := by
  have hp := qi.property
  rw [hcoe, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hp
  exact_mod_cast hp

/-- Nonzero reduction of a rational PadicInt model forces rational
valuation zero. -/
private theorem val_zero_of_padicInt_model
    {q : ℚ} (hq : q ≠ 0) (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3]))
    (hred : PadicInt.toZMod qi ≠ 0) :
    padicValRat 3 q = 0 := by
  have hqint := val_nonneg_of_padicInt_model qi hcoe
  have heq : ratPadicInt q hqint = qi := by
    apply Subtype.ext
    exact hcoe.symm
  apply val_zero_of_padicInt_red_nonzero hq hqint
  rwa [heq]

/-- Zero reduction of a nonzero rational PadicInt model forces positive
rational valuation. -/
private theorem val_pos_of_padicInt_model
    {q : ℚ} (hq : q ≠ 0) (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3]))
    (hred : PadicInt.toZMod qi = 0) :
    0 < padicValRat 3 q := by
  have hqint := val_nonneg_of_padicInt_model qi hcoe
  have heq : ratPadicInt q hqint = qi := by
    apply Subtype.ext
    exact hcoe.symm
  apply val_pos_of_padicInt_red_zero hq hqint
  rwa [heq]

/-! ## Entry after multiplication by six -/

set_option maxHeartbeats 0 in
/-- Every rational point enters the three-adic formal kernel after
multiplication by six. -/
theorem six_nsmul_formal (P : GoodPoint) :
    FormalAtThree (6 • P) := by
  rcases formal_or_integral P with hformal | hintegral
  · have hdouble := FormalAtThree_double hformal
    have htriple := FormalAtThree_triple hdouble
    simpa only [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul'] using htriple
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hxint, hyint⟩
        have hcurve : OnGood x y :=
          (goodCurve_equation_iff x y).mp h.1
        have hy : y ≠ 0 := good_y_ne_zero hcurve
        let xi : ℤ_[3] := ratPadicInt x hxint
        let yi : ℤ_[3] := ratPadicInt y hyint
        obtain hred | hred | hred :=
          integral_reduction hxint hyint hcurve
        · rcases hred with ⟨hxred, hyred⟩
          have hvy : padicValRat 3 y = 0 :=
            val_zero_of_padicInt_red_nonzero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi = 0 := by
            simp [nxi, xi, hxred]
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          by_cases hnx : nx = 0
          · have hdx : doubleX x y = 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) = 0
              rw [hnx]
              simp
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_zero hd hdx
          · have hvnx : 0 < padicValRat 3 nx :=
              val_pos_of_padicInt_model hnx nxi hnxcoe hnxred
            have hdx : doubleX x y ≠ 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) ≠ 0
              exact div_ne_zero hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
            have hdy : doubleY x y ≠ 0 := by
              unfold doubleY
              change ny / (8 * y ^ 3) ≠ 0
              exact div_ne_zero hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
            have hvdx : 0 < padicValRat 3 (doubleX x y) := by
              have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
                val_int_unit 4 (by norm_num)
              unfold doubleX
              change 0 < padicValRat 3 (nx / (4 * y ^ 2))
              rw [padicValRat.div hnx
                  (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
                padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
                hv4, padicValRat.pow hy, hvy]
              omega
            have hvdy : padicValRat 3 (doubleY x y) = 0 := by
              have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
                val_int_unit 8 (by norm_num)
              unfold doubleY
              change padicValRat 3 (ny / (8 * y ^ 3)) = 0
              rw [padicValRat.div hny
                  (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
                hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
                hv8, padicValRat.pow hy, hvy]
              ring
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_pos hd hvdx hvdy
        · rcases hred with ⟨hxred, hyred⟩
          have hvy : padicValRat 3 y = 0 :=
            val_zero_of_padicInt_red_nonzero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi = 0 := by
            simp [nxi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          by_cases hnx : nx = 0
          · have hdx : doubleX x y = 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) = 0
              rw [hnx]
              simp
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_zero hd hdx
          · have hvnx : 0 < padicValRat 3 nx :=
              val_pos_of_padicInt_model hnx nxi hnxcoe hnxred
            have hdx : doubleX x y ≠ 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) ≠ 0
              exact div_ne_zero hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
            have hdy : doubleY x y ≠ 0 := by
              unfold doubleY
              change ny / (8 * y ^ 3) ≠ 0
              exact div_ne_zero hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
            have hvdx : 0 < padicValRat 3 (doubleX x y) := by
              have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
                val_int_unit 4 (by norm_num)
              unfold doubleX
              change 0 < padicValRat 3 (nx / (4 * y ^ 2))
              rw [padicValRat.div hnx
                  (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
                padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
                hv4, padicValRat.pow hy, hvy]
              omega
            have hvdy : padicValRat 3 (doubleY x y) = 0 := by
              have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
                val_int_unit 8 (by norm_num)
              unfold doubleY
              change padicValRat 3 (ny / (8 * y ^ 3)) = 0
              rw [padicValRat.div hny
                  (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
                hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
                hv8, padicValRat.pow hy, hvy]
              ring
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_pos hd hvdx hvdy
        · rcases hred with ⟨hxred, hyred⟩
          have hx : x ≠ 0 := by
            intro hx0
            subst x
            simp [ratPadicInt] at hxred
            exact (by decide : (0 : ZMod 3) ≠ 2) hxred
          have hvx : padicValRat 3 x = 0 :=
            val_zero_of_padicInt_red_nonzero hx hxint (by
              rw [hxred]
              decide)
          have hvypos : 0 < padicValRat 3 y :=
            val_pos_of_padicInt_red_zero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi ≠ 0 := by
            simp [nxi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hnx : nx ≠ 0 := by
            intro hzero
            apply hnxred
            have : nxi = 0 := by
              apply Subtype.ext
              rw [hnxcoe]
              change ((nx : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvnx : padicValRat 3 nx = 0 :=
            val_zero_of_padicInt_model hnx nxi hnxcoe hnxred
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          have hdx : doubleX x y ≠ 0 := by
            unfold doubleX
            change nx / (4 * y ^ 2) ≠ 0
            exact div_ne_zero hnx
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
          have hdy : doubleY x y ≠ 0 := by
            unfold doubleY
            change ny / (8 * y ^ 3) ≠ 0
            exact div_ne_zero hny
              (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
          have hvdx :
              padicValRat 3 (doubleX x y) =
                -2 * padicValRat 3 y := by
            have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
              val_int_unit 4 (by norm_num)
            unfold doubleX
            change padicValRat 3 (nx / (4 * y ^ 2)) =
              -2 * padicValRat 3 y
            rw [padicValRat.div hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
              hvnx, padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
              hv4, padicValRat.pow hy]
            ring
          have hvdy :
              padicValRat 3 (doubleY x y) =
                -3 * padicValRat 3 y := by
            have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
              val_int_unit 8 (by norm_num)
            unfold doubleY
            change padicValRat 3 (ny / (8 * y ^ 3)) =
              -3 * padicValRat 3 y
            rw [padicValRat.div hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
              hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
              hv8, padicValRat.pow hy]
            ring
          let hd := double_nonsingular hy h
          have hdouble := two_nsmul_eq_double_point hy h
          have hlevel :
              FormalLevel
                (WeierstrassCurve.Affine.Point.some
                  (doubleX x y) (doubleY x y) hd)
                (padicValRat 3 y) :=
            ⟨hvypos, hvdx, hvdy⟩
          have hformal2 : FormalAtThree
              (2 • (WeierstrassCurve.Affine.Point.some x y h :
                GoodPoint)) := by
            rw [hdouble, FormalAtThree_iff]
            exact Or.inr ⟨padicValRat 3 y, hlevel⟩
          have hformal6 := FormalAtThree_triple hformal2
          simpa only [show (6 : ℕ) = 3 * 2 by norm_num,
            mul_nsmul'] using hformal6

end

end MazurProof.XDelta19GoodFormalReduction
