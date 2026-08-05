import FLT.Assumptions.MazurProof.X017FormalTwoCore

/-!
# Mod-two entry into the X₀(17) formal kernel

The integral model has four points on its good fibre at two.  Instead of
constructing a general reduction homomorphism, this file follows the explicit
duplication formulas.  For integral coordinates, the residue of `x` is zero
or one:

* residue one makes the first double a formal point;
* residue zero makes the first double integral with `x`-residue one, so the
  second double is formal.

Thus four times every rational point belongs to the two-adic formal kernel.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FormalTwoReduction

open WeierstrassCurve.Affine
open MazurProof.X017FormalTwoCore
open MazurProof.X017Model

noncomputable section

/-! ## Integral rational numbers and their residues -/

/-- Regard a rational number of nonnegative two-adic valuation as a two-adic
integer. -/
private noncomputable def ratPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 2 q) : ℤ_[2] :=
  ⟨(q : ℚ_[2]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

private theorem zmod2_nonzero_eq_one (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact (hz rfl).elim
  · rfl

private theorem ratPadicInt_red_eq_one_of_val_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    PadicInt.toZMod (ratPadicInt q (by omega)) = 1 := by
  apply zmod2_nonzero_eq_one
  intro hz0
  have hm : ratPadicInt q (by omega) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod]
    exact hz0
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖((ratPadicInt q (by omega) : ℤ_[2]) : ℚ_[2])‖ < 1 at hm
  change ‖(q : ℚ_[2])‖ < 1 at hm
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv] at hm
  norm_num at hm

private theorem ratPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 2 q) :
    PadicInt.toZMod (ratPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[2])‖ < 1
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (2 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (2 : ℝ))
    (by norm_num : (1 : ℝ) < 2)).2 (by omega)

private theorem val_pos_of_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) = 0) :
    0 < padicValRat 2 q := by
  by_contra hnot
  have hv0 : padicValRat 2 q = 0 := by omega
  have hone := ratPadicInt_red_eq_one_of_val_zero hq hv0
  have heq : ratPadicInt q hqi = ratPadicInt q (by omega) := by
    apply Subtype.ext
    rfl
  rw [heq, hone] at hred
  norm_num at hred

private theorem val_zero_of_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) ≠ 0) :
    padicValRat 2 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 2 q := lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := ratPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : ratPadicInt q hqi = ratPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

/-! ## Duplication polynomials over the two-adic integers -/

private noncomputable def doubleDenPadic (x y : ℤ_[2]) : ℤ_[2] :=
  2 * y + x + 1

private noncomputable def doubleXNumPadic (x : ℤ_[2]) : ℤ_[2] :=
  x ^ 4 + x ^ 2 + 110 * x - 41

private noncomputable def doubleYNumPadic (x y : ℤ_[2]) : ℤ_[2] :=
  x ^ 6 - 2 * x ^ 5 - 5 * x ^ 4 - 276 * x ^ 3 + 152 * x ^ 2 -
    95 * x + y * (-x ^ 4 - 4 * x ^ 3 + 2 * x ^ 2 - 108 * x + 96) - 1485

private theorem doubleDenPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((doubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((doubleDen x y : ℚ) : ℚ_[2]) := by
  change 2 * (y : ℚ_[2]) + (x : ℚ_[2]) + 1 =
    (((2 * y + x + 1 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem doubleXNumPadic_coe (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    ((doubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2]) =
      ((doubleXNum x : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 4 + (x : ℚ_[2]) ^ 2 + 110 * (x : ℚ_[2]) - 41 =
    (((x ^ 4 + x ^ 2 + 110 * x - 41 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem doubleYNumPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((doubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((doubleYNum x y : ℚ) : ℚ_[2]) := by
  change
    (x : ℚ_[2]) ^ 6 - 2 * (x : ℚ_[2]) ^ 5 - 5 * (x : ℚ_[2]) ^ 4 -
        276 * (x : ℚ_[2]) ^ 3 + 152 * (x : ℚ_[2]) ^ 2 - 95 * (x : ℚ_[2]) +
        (y : ℚ_[2]) * (-(x : ℚ_[2]) ^ 4 - 4 * (x : ℚ_[2]) ^ 3 +
          2 * (x : ℚ_[2]) ^ 2 - 108 * (x : ℚ_[2]) + 96) - 1485 =
      (((doubleYNum x y : ℚ)) : ℚ_[2])
  rfl

private theorem doubleDen_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (doubleDen x y) := by
  have hnorm := (doubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((doubleDenPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [doubleDenPadic_coe x y hx hy, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem doubleXNum_integral (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    0 ≤ padicValRat 2 (doubleXNum x) := by
  have hnorm := (doubleXNumPadic (ratPadicInt x hx)).2
  change ‖((doubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [doubleXNumPadic_coe x hx, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem doubleYNum_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (doubleYNum x y) := by
  have hnorm := (doubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((doubleYNumPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [doubleYNumPadic_coe x y hx hy, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14) :
    (ratPadicInt y hy) ^ 2 + ratPadicInt x hx * ratPadicInt y hy +
        ratPadicInt y hy =
      (ratPadicInt x hx) ^ 3 - (ratPadicInt x hx) ^ 2 -
        ratPadicInt x hx - 14 := by
  apply Subtype.ext
  change (y : ℚ_[2]) ^ 2 + (x : ℚ_[2]) * (y : ℚ_[2]) + (y : ℚ_[2]) =
    (x : ℚ_[2]) ^ 3 - (x : ℚ_[2]) ^ 2 - (x : ℚ_[2]) - 14
  exact_mod_cast hE

/-! ## Kernel-checked residue identities -/

private theorem doubleDenPadic_red_zero
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (doubleDenPadic z w) = 1 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [doubleDenPadic, map_add, map_mul, map_ofNat, hz, htwo]

private theorem doubleDenPadic_red_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (doubleDenPadic z w) = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [doubleDenPadic, map_add, map_mul, map_ofNat, hz, htwo]
  decide

private theorem doubleXNumPadic_red_zero
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (doubleXNumPadic z) = 1 := by
  simp [doubleXNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz]
  decide

private theorem doubleXNumPadic_red_one
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (doubleXNumPadic z) = 1 := by
  simp [doubleXNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz]
  decide

private theorem doubleYNumPadic_red_zero
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (doubleYNumPadic z w) = 1 := by
  simp [doubleYNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz]
  have h96 : (96 : ZMod 2) = 0 := by decide
  have hm1485 : (-1485 : ZMod 2) = 1 := by decide
  rw [h96, mul_zero, zero_sub]
  exact hm1485

private theorem doubleYNumPadic_red_one_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1)
    (hw : PadicInt.toZMod w = 1) :
    PadicInt.toZMod (doubleYNumPadic z w) = 1 := by
  simp [doubleYNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz, hw]
  decide

private theorem ratPadicInt_doubleDen
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (doubleDen x y) (doubleDen_integral x y hx hy) =
      doubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (doubleDenPadic_coe x y hx hy).symm

private theorem ratPadicInt_doubleXNum
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ratPadicInt (doubleXNum x) (doubleXNum_integral x hx) =
      doubleXNumPadic (ratPadicInt x hx) := by
  apply Subtype.ext
  exact (doubleXNumPadic_coe x hx).symm

private theorem ratPadicInt_doubleYNum
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (doubleYNum x y) (doubleYNum_integral x y hx hy) =
      doubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (doubleYNumPadic_coe x y hx hy).symm

private theorem y_red_one_of_x_red_one
    {x y : ℚ} (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14)
    (hxred : PadicInt.toZMod (ratPadicInt x hx) = 1) :
    PadicInt.toZMod (ratPadicInt y hy) = 1 := by
  have heq := congrArg PadicInt.toZMod (padicInt_equation hx hy hE)
  simp [map_add, map_sub, map_mul, map_pow, map_ofNat, hxred] at heq
  by_cases hyred : PadicInt.toZMod (ratPadicInt y hy) = 0
  · rw [hyred] at heq
    have hbad : (0 : ZMod 2) ≠ 1 - 14 := by decide
    exact (hbad (by simpa using heq)).elim
  · exact zmod2_nonzero_eq_one _ hyred

private theorem rat_ne_zero_of_red_one
    {q : ℚ} (hq : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hq) = 1) :
    q ≠ 0 := by
  intro hzero
  have hz : ratPadicInt q hq = 0 := by
    apply Subtype.ext
    change (q : ℚ_[2]) = 0
    simp [hzero]
  rw [hz, map_zero] at hred
  norm_num at hred

/-! ## Integral points enter the formal kernel after at most two doublings -/

private theorem double_formal_of_integral_x_unit
    {x y : ℚ} {h : Nonsingular X017 x y}
    (hxn : x ≠ 0) (hx : padicValRat 2 x = 0)
    (hy : 0 ≤ padicValRat 2 y) :
    FormalAtTwo (2 • Point.some x y h) := by
  have hx0 : 0 ≤ padicValRat 2 x := by omega
  have hE := (X017_equation_iff x y).mp h.left
  have hxred := ratPadicInt_red_eq_one_of_val_zero hxn hx
  have hyred := y_red_one_of_x_red_one hx0 hy hE hxred
  have hDi := doubleDen_integral x y hx0 hy
  have hDred :
      PadicInt.toZMod (ratPadicInt (doubleDen x y) hDi) = 0 := by
    rw [ratPadicInt_doubleDen x y hx0 hy]
    exact doubleDenPadic_red_one hxred
  by_cases hd : doubleDen x y = 0
  · rw [two_nsmul]
    have hYeq : y = negY X017 x y := by
      simp [doubleDen, negY] at hd ⊢
      linarith
    rw [Point.add_self_of_Y_eq hYeq]
    trivial
  · have hvd : 0 < padicValRat 2 (doubleDen x y) :=
      val_pos_of_red_zero hd hDi hDred
    have hNi := doubleXNum_integral x hx0
    have hYi := doubleYNum_integral x y hx0 hy
    have hNred :
        PadicInt.toZMod (ratPadicInt (doubleXNum x) hNi) = 1 := by
      rw [ratPadicInt_doubleXNum x hx0]
      exact doubleXNumPadic_red_one hxred
    have hYred :
        PadicInt.toZMod (ratPadicInt (doubleYNum x y) hYi) = 1 := by
      rw [ratPadicInt_doubleYNum x y hx0 hy]
      exact doubleYNumPadic_red_one_one hxred hyred
    have hN : doubleXNum x ≠ 0 :=
      rat_ne_zero_of_red_one hNi hNred
    have hY : doubleYNum x y ≠ 0 :=
      rat_ne_zero_of_red_one hYi hYred
    have hvN : padicValRat 2 (doubleXNum x) = 0 :=
      val_zero_of_red_nonzero hN hNi (by rw [hNred]; norm_num)
    have hvY : padicValRat 2 (doubleYNum x y) = 0 :=
      val_zero_of_red_nonzero hY hYi (by rw [hYred]; norm_num)
    have hneg : y ≠ negY X017 x y := by
      intro heq
      apply hd
      simp [doubleDen, negY] at heq ⊢
      linarith
    rw [two_nsmul, Point.add_self_of_Y_ne hneg]
    refine ⟨padicValRat 2 (doubleDen x y), hvd, ?_, ?_⟩
    · rw [doubleX_formula hd hE,
        padicValRat.div hN (pow_ne_zero 2 hd), hvN,
        padicValRat.pow hd]
      ring
    · rw [doubleY_formula hd hE,
        padicValRat.div hY (pow_ne_zero 3 hd), hvY,
        padicValRat.pow hd]
      ring

private theorem four_formal_of_integral_x_red_zero
    {x y : ℚ} {h : Nonsingular X017 x y}
    (hx0 : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hxred : PadicInt.toZMod (ratPadicInt x hx0) = 0) :
    FormalAtTwo (4 • Point.some x y h) := by
  have hE := (X017_equation_iff x y).mp h.left
  have hDi := doubleDen_integral x y hx0 hy
  have hDred :
      PadicInt.toZMod (ratPadicInt (doubleDen x y) hDi) = 1 := by
    rw [ratPadicInt_doubleDen x y hx0 hy]
    exact doubleDenPadic_red_zero hxred
  have hd : doubleDen x y ≠ 0 :=
    rat_ne_zero_of_red_one hDi hDred
  have hvd : padicValRat 2 (doubleDen x y) = 0 :=
    val_zero_of_red_nonzero hd hDi (by rw [hDred]; norm_num)
  have hNi := doubleXNum_integral x hx0
  have hYi := doubleYNum_integral x y hx0 hy
  have hNred :
      PadicInt.toZMod (ratPadicInt (doubleXNum x) hNi) = 1 := by
    rw [ratPadicInt_doubleXNum x hx0]
    exact doubleXNumPadic_red_zero hxred
  have hYred :
      PadicInt.toZMod (ratPadicInt (doubleYNum x y) hYi) = 1 := by
    rw [ratPadicInt_doubleYNum x y hx0 hy]
    exact doubleYNumPadic_red_zero hxred
  have hN : doubleXNum x ≠ 0 :=
    rat_ne_zero_of_red_one hNi hNred
  have hY : doubleYNum x y ≠ 0 :=
    rat_ne_zero_of_red_one hYi hYred
  have hvN : padicValRat 2 (doubleXNum x) = 0 :=
    val_zero_of_red_nonzero hN hNi (by rw [hNred]; norm_num)
  have hvY : padicValRat 2 (doubleYNum x y) = 0 :=
    val_zero_of_red_nonzero hY hYi (by rw [hYred]; norm_num)
  have hneg : y ≠ negY X017 x y := by
    intro heq
    apply hd
    simp [doubleDen, negY] at heq ⊢
    linarith
  have hfour :
      4 • Point.some x y h =
        2 • (Point.some x y h + Point.some x y h) := by
    rw [← two_nsmul]
    norm_num [← mul_nsmul]
  rw [hfour, Point.add_self_of_Y_ne hneg]
  have hx2ne : addX X017 x x (slope X017 x x y y) ≠ 0 := by
    rw [doubleX_formula hd hE]
    exact div_ne_zero hN (pow_ne_zero 2 hd)
  apply double_formal_of_integral_x_unit
  · exact hx2ne
  · rw [doubleX_formula hd hE,
      padicValRat.div hN (pow_ne_zero 2 hd),
      padicValRat.pow hd, hvN, hvd]
    norm_num
  · rw [doubleY_formula hd hE,
      padicValRat.div hY (pow_ne_zero 3 hd),
      padicValRat.pow hd, hvY, hvd]
    norm_num

/-- Four times every rational point on the good integral model belongs to
the two-adic formal kernel. -/
theorem four_nsmul_formal (P : Point X017) :
    FormalAtTwo (4 • P) := by
  rcases formal_or_integral P with hformal | hintegral
  · have h2 := formalAtTwo_double hformal
    have h4 := formalAtTwo_double h2
    rw [show 4 • P = 2 • (2 • P) by norm_num [← mul_nsmul]]
    exact h4
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hx, hy⟩
        by_cases hxzero : x = 0
        · have hxred : PadicInt.toZMod (ratPadicInt x hx) = 0 := by
            have hxi : ratPadicInt x hx = 0 := by
              apply Subtype.ext
              change (x : ℚ_[2]) = 0
              simp [hxzero]
            rw [hxi, map_zero]
          exact four_formal_of_integral_x_red_zero hx hy hxred
        · by_cases hxunit : padicValRat 2 x = 0
          · have h2 :=
              double_formal_of_integral_x_unit (h := h) hxzero hxunit hy
            have h4 := formalAtTwo_double h2
            rw [show 4 • Point.some x y h =
                2 • (2 • Point.some x y h) by
                  norm_num [← mul_nsmul]]
            exact h4
          · have hxpos : 0 < padicValRat 2 x :=
              lt_of_le_of_ne hx (Ne.symm hxunit)
            have hxred :=
              ratPadicInt_red_eq_zero_of_val_pos hxzero hxpos
            exact four_formal_of_integral_x_red_zero hx hy hxred

/-! ## Separatedness of the formal filtration -/

private theorem formalLevel_unique {P : Point X017} {k l : ℤ}
    (hk : FormalLevel P k) (hl : FormalLevel P l) : k = l := by
  cases P with
  | zero => simp [FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

/-- Repeated doubling either reaches infinity or raises the formal level by
at least the number of doublings. -/
theorem formalLevel_two_power {P : Point X017} {k : ℤ}
    (hP : FormalLevel P k) (n : ℕ) :
    (2 ^ n : ℕ) • P = 0 ∨
      ∃ k' : ℤ, k + n ≤ k' ∧
        FormalLevel ((2 ^ n : ℕ) • P) k' := by
  induction n with
  | zero =>
      right
      refine ⟨k, by simp, ?_⟩
      simpa using hP
  | succ n ih =>
      rcases ih with hzero | ⟨l, hkl, hl⟩
      · left
        rw [pow_succ', Nat.mul_comm, mul_nsmul, hzero, nsmul_zero]
      · rcases formalLevel_double hl with hzero | ⟨l', hll', hl'⟩
        · left
          rw [pow_succ', Nat.mul_comm, mul_nsmul]
          exact hzero
        · right
          refine ⟨l', ?_, ?_⟩
          · norm_num at hkl ⊢
            omega
          · rw [pow_succ', Nat.mul_comm, mul_nsmul]
            exact hl'

/-- A formal point divisible by every power of two through formal points is
zero.  Otherwise its fixed level would exceed itself after sufficiently many
doublings. -/
theorem formal_separated (P : Point X017)
    (hP : FormalAtTwo P)
    (hdiv : ∀ n : ℕ, ∃ Q : Point X017,
      FormalAtTwo Q ∧ P = (2 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, FormalLevel P k := by
    rw [formalAtTwo_iff] at hP
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
    rw [formalAtTwo_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  have hlpos : 0 < l := by
    cases Q with
    | zero => simp [FormalLevel] at hl
    | some x y h => exact hl.1
  rcases formalLevel_two_power hl n with hzero | ⟨l', hbound, hl'⟩
  · exact hP0 (hPQ.trans hzero)
  · have hl'P : FormalLevel P l' := by
      rw [hPQ]
      exact hl'
    have heq : l' = k := formalLevel_unique hl'P hk
    have hkNat : (k.toNat : ℤ) = k :=
      Int.toNat_of_nonneg (le_of_lt hkpos)
    dsimp [n] at hbound
    norm_num [hkNat] at hbound
    omega

end

end MazurProof.X017FormalTwoReduction
