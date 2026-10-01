import FLT.Assumptions.MazurProof.N18RouteC_CyclotomicReduction

set_option maxHeartbeats 0

open scoped NumberField

namespace MazurProof.N18RouteC.PhiLocal

open NumberField
open Cyclotomic CyclotomicUnits CyclotomicValuation CyclotomicTwo
  CyclotomicReduction
open Isogeny IsogenyPoints

noncomputable section

theorem phiKappa_integral_formula
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta) :
    phiKappa (.some xi eta h) =
      embedL (eta + 1) + embedL (3 * xi) * zeta ^ 3 := by
  simp only [phiKappa, Isogeny.dualZ, qM, map_add, map_sub, map_mul, map_div₀,
    map_ofNat, map_one]
  ring

theorem ehat_equation
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta) :
    eta ^ 2 - 3 * xi * eta + 2 * eta = xi ^ 3 + 30 * xi + 26 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  simp only [Ehat0] at heq
  linear_combination heq

theorem ordAt_p2_three : ordAt p2 (3 : M) = 0 := by
  have hnot : (3 : OM) ∉ p2.asIdeal := by
    intro hmem
    have hcomap : (3 : ℤ) ∈ p2.asIdeal.comap (algebraMap ℤ OM) := hmem
    have hover := primeAboveTwo_mem.2.over
    change (3 : ℤ) ∈ primeAboveTwo.under ℤ at hcomap
    rw [← hover, Ideal.mem_span_singleton] at hcomap
    norm_num at hcomap
  have hv : p2.valuation M (3 : M) = 1 := by
    change p2.valuation M (algebraMap OM M (3 : OM)) = 1
    exact (p2.valuation_eq_one_iff_notMem (K := M)).2 hnot
  simp [ordAt, hv]

theorem ordAt_p2_zeta : ordAt p2 zeta = 0 := by
  have hnot : zetaInteger ∉ p2.asIdeal := by
    intro hmem
    have htop := p2.asIdeal.eq_top_of_isUnit_mem hmem
      (IsPrimitiveRoot.isUnit zeta_primitive.toInteger_isPrimitiveRoot (by norm_num))
    exact p2.isPrime.ne_top htop
  have hv : p2.valuation M zeta = 1 := by
    change p2.valuation M (algebraMap OM M zetaInteger) = 1
    exact (p2.valuation_eq_one_iff_notMem (K := M)).2 hnot
  simp [ordAt, hv]

theorem ordAt_p2_zeta_pow (e : ℕ) : ordAt p2 (zeta ^ e) = 0 := by
  rw [ordAt_pow p2 zeta_ne_zero e, ordAt_p2_zeta]
  simp

theorem residue_cubic_sum :
    zetaBar ^ 6 + zetaBar ^ 3 + 1 = 0 := by
  have hrel : zetaInteger ^ 6 + zetaInteger ^ 3 + 1 = 0 := by
    apply NumberField.RingOfIntegers.ext
    simpa [zetaInteger] using zeta_cubic_sum
  have hmap := congrArg (algebraMap OM k2) hrel
  simpa only [zetaBar, map_add, map_pow, map_one, map_zero] using hmap

theorem affine_residue_pow_twenty_one (x y : k2)
    (hx8 : x ^ 8 = x) (hy8 : y ^ 8 = y)
    (hcurve : y ^ 2 + x * y = x ^ 3) :
    (y + 1 + x * zetaBar ^ 3) ^ 21 = 1 := by
  let t : k2 := zetaBar ^ 3
  have ht : t ^ 2 + t + 1 = 0 := by
    change (zetaBar ^ 3) ^ 2 + zetaBar ^ 3 + 1 = 0
    rw [← pow_mul]
    norm_num
    exact residue_cubic_sum
  have hchar : (2 : k2) = 0 := CharP.cast_eq_zero k2 2
  have hthree : (3 : k2) = 1 := by linear_combination hchar
  have hfour : (4 : k2) = 0 := by linear_combination 2 * hchar
  have hsix : (6 : k2) = 0 := by linear_combination 3 * hchar
  have hneg (a : k2) : -a = a := by linear_combination -a * hchar
  by_cases hx0 : x = 0
  · subst x
    have hy0 : y = 0 := by
      have hySq : y ^ 2 = 0 := by simpa using hcurve
      exact sq_eq_zero_iff.mp hySq
    subst y
    simp
  · let u : k2 := y / x
    have hu8 : u ^ 8 = u := by
      dsimp [u]
      rw [div_pow, hx8, hy8]
    have hxu : x = u ^ 2 + u := by
      calc
        x = x ^ 3 / x ^ 2 := by field_simp [hx0]
        _ = (y ^ 2 + x * y) / x ^ 2 := by rw [hcurve]
        _ = u ^ 2 + u := by
          dsimp [u]
          field_simp [hx0]
    have htrace : x ^ 4 + x ^ 2 + x = 0 := by
      rw [hxu]
      calc
        (u ^ 2 + u) ^ 4 + (u ^ 2 + u) ^ 2 + (u ^ 2 + u) =
            u ^ 8 + u := by ring_nf; rw [hchar, hfour, hsix]; ring
        _ = 0 := by rw [hu8]; linear_combination u * hchar
    have hxcubic : x ^ 3 + x + 1 = 0 := by
      apply mul_left_cancel₀ hx0
      linear_combination htrace
    have htSq : t ^ 2 = t + 1 := by
      calc
        t ^ 2 = -(t + 1) := by linear_combination ht
        _ = t + 1 := hneg _
    have hySq : y ^ 2 = x ^ 3 + x * y := by
      calc
        y ^ 2 = x ^ 3 - x * y := by linear_combination hcurve
        _ = x ^ 3 + x * y := by rw [sub_eq_add_neg, hneg]
    have hxCube : x ^ 3 = x + 1 := by
      calc
        x ^ 3 = -(x + 1) := by linear_combination hxcubic
        _ = x + 1 := hneg _
    have hxFourth : x ^ 4 = x ^ 2 + x := by
      calc
        x ^ 4 = -(x ^ 2 + x) := by linear_combination htrace
        _ = x ^ 2 + x := hneg _
    have hyCube : y ^ 3 = x ^ 3 * y + x ^ 4 + x ^ 2 * y := by
      calc
        y ^ 3 = y * y ^ 2 := by ring
        _ = y * (x ^ 3 + x * y) := by rw [hySq]
        _ = x ^ 3 * y + x * y ^ 2 := by ring
        _ = x ^ 3 * y + x * (x ^ 3 + x * y) := by rw [hySq]
        _ = x ^ 3 * y + x ^ 4 + x ^ 2 * y := by ring
    have htCube : t ^ 3 = 1 := by
      dsimp [t]
      rw [← pow_mul]
      norm_num
      exact zetaBar_pow_nine
    have hh3 : (y + 1 + x * t) ^ 3 = x + 1 := by
      calc
        (y + 1 + x * t) ^ 3 =
            (y ^ 3 + y ^ 2 + y + 1 + x ^ 3 + x ^ 2 * y + x ^ 2) +
              (x * y ^ 2 + x + x ^ 2 * y + x ^ 2) * t := by
                ring_nf
                rw [hthree, hsix, htSq, htCube]
                ring
        _ = x + 1 := by
          rw [hyCube, hySq, hxCube, hxFourth]
          ring_nf
          rw [hchar, hthree]
          ring
    have hxSeven : x ^ 7 = 1 := by
      calc
        x ^ 7 = x ^ 4 * x ^ 3 := by ring
        _ = (x ^ 2 + x) * (x + 1) := by rw [hxFourth, hxCube]
        _ = x ^ 3 + x := by ring_nf; rw [hchar]; ring
        _ = 1 := by rw [hxCube]; ring_nf; rw [hchar]; ring
    calc
      (y + 1 + x * zetaBar ^ 3) ^ 21 =
          ((y + 1 + x * t) ^ 3) ^ 7 := by simp [t, ← pow_mul]
      _ = (x + 1) ^ 7 := by rw [hh3]
      _ = (x ^ 3) ^ 7 := by rw [hxCube]
      _ = (x ^ 7) ^ 3 := by ring
      _ = 1 := by rw [hxSeven]; simp

theorem reduces_int (z : ℤ) : Reduces (z : M) (z : k2) := by
  refine ⟨(z : OM), 1, ?_, ?_⟩ <;> simp

theorem k2_intCast_three : ((3 : ℤ) : k2) = 1 := by
  have htwo : (2 : k2) = 0 := CharP.cast_eq_zero k2 2
  push_cast
  linear_combination htwo

theorem k2_intCast_two : ((2 : ℤ) : k2) = 0 := by
  have htwo : (2 : k2) = 0 := CharP.cast_eq_zero k2 2
  push_cast
  exact htwo

theorem k2_intCast_neg_three : ((-3 : ℤ) : k2) = 1 := by
  have htwo : (2 : k2) = 0 := CharP.cast_eq_zero k2 2
  push_cast
  linear_combination -2 * htwo

theorem k2_intCast_thirty : ((30 : ℤ) : k2) = 0 := by
  have htwo : (2 : k2) = 0 := CharP.cast_eq_zero k2 2
  push_cast
  linear_combination 15 * htwo

theorem k2_intCast_twenty_six : ((26 : ℤ) : k2) = 0 := by
  have htwo : (2 : k2) = 0 := CharP.cast_eq_zero k2 2
  push_cast
  linear_combination 13 * htwo

theorem reduces_three_one : Reduces (3 : M) (1 : k2) := by
  convert reduces_int 3 using 1
  · norm_num
  · exact k2_intCast_three.symm

theorem reduces_two_zero : Reduces (2 : M) (0 : k2) := by
  convert reduces_int 2 using 1
  · norm_num
  · exact k2_intCast_two.symm

theorem reduces_zeta : Reduces zeta zetaBar := by
  refine ⟨zetaInteger, 1, ?_, ?_⟩ <;> simp [zetaInteger, zetaBar]

theorem reduce_phiKappa_formula
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta)
    (hxi : IntegralAtTwo (embedL xi)) (heta : IntegralAtTwo (embedL eta))
    (hH : IntegralAtTwo (phiKappa (.some xi eta h))) :
    reduce (phiKappa (.some xi eta h)) hH =
      reduce (embedL eta) heta + 1 + reduce (embedL xi) hxi * zetaBar ^ 3 := by
  have hr : Reduces
      (embedL eta + 1 + (3 : M) * embedL xi * zeta ^ 3)
      (reduce (embedL eta) heta + 1 + reduce (embedL xi) hxi * zetaBar ^ 3) := by
    convert ((reduce_spec (embedL eta) heta).add reduces_one).add
      ((reduces_three_one.mul (reduce_spec (embedL xi) hxi)).mul
        (reduces_zeta.pow 3)) using 1 <;> ring
  have hformula := phiKappa_integral_formula h
  have hfield : phiKappa (.some xi eta h) =
      embedL eta + 1 + (3 : M) * embedL xi * zeta ^ 3 := by
    rw [hformula]
    simp only [map_add, map_mul, map_one, map_ofNat]
  rw [← hfield] at hr
  exact reduce_eq_of_reduces hH hr

theorem reduce_ehat_equation
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta)
    (hxi : IntegralAtTwo (embedL xi)) (heta : IntegralAtTwo (embedL eta)) :
    reduce (embedL eta) heta ^ 2 +
        reduce (embedL xi) hxi * reduce (embedL eta) heta =
      reduce (embedL xi) hxi ^ 3 := by
  have hm3 : Reduces (-3 : M) (1 : k2) := by
    convert reduces_int (-3) using 1
    · norm_num
    · exact k2_intCast_neg_three.symm
  have htwo : Reduces (2 : M) (0 : k2) := reduces_two_zero
  have h30 : Reduces (30 : M) (0 : k2) := by
    convert reduces_int 30 using 1
    · norm_num
    · exact k2_intCast_thirty.symm
  have h26 : Reduces (26 : M) (0 : k2) := by
    convert reduces_int 26 using 1
    · norm_num
    · exact k2_intCast_twenty_six.symm
  let xbar := reduce (embedL xi) hxi
  let ybar := reduce (embedL eta) heta
  have hleft : Reduces
      (embedL eta ^ 2 + (-3 : M) * embedL xi * embedL eta + 2 * embedL eta)
      (ybar ^ 2 + xbar * ybar) := by
    convert (((reduce_spec (embedL eta) heta).pow 2).add
      ((hm3.mul (reduce_spec (embedL xi) hxi)).mul
        (reduce_spec (embedL eta) heta))).add
      (htwo.mul (reduce_spec (embedL eta) heta)) using 1 <;>
      simp [xbar, ybar] <;> ring
  have hright : Reduces
      (embedL xi ^ 3 + 30 * embedL xi + 26)
      (xbar ^ 3) := by
    convert (((reduce_spec (embedL xi) hxi).pow 3).add
      (h30.mul (reduce_spec (embedL xi) hxi))).add h26 using 1 <;>
      simp [xbar] <;> ring
  have hfield :
      embedL eta ^ 2 + (-3 : M) * embedL xi * embedL eta + 2 * embedL eta =
        embedL xi ^ 3 + 30 * embedL xi + 26 := by
    have hm := congrArg embedL (ehat_equation h)
    convert hm using 1 <;> simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] <;> ring
  rw [hfield] at hleft
  simpa [xbar, ybar] using reduces_unique hleft hright

theorem complexConj_two_zpow_embedL (n : ℤ) (u : L) :
    NumberField.IsCMField.complexConj M ((2 : M) ^ n * embedL u) =
      (2 : M) ^ n * embedL u := by
  rw [map_mul, map_zpow₀, complexConj_embedL]
  have htwo : NumberField.IsCMField.complexConj M (2 : M) = 2 := by
    simpa only [map_ofNat]
  rw [htwo]

theorem normalized_zero_reduction_pow_twenty_one
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta)
    (hordH : ordAt p2 (phiKappa (.some xi eta h)) = 0)
    (hordX : ordAt p2 (embedL (Isogeny.dualX xi)) = 0) :
    let hHInt := integralAtTwo_of_ordAt_nonneg
      (phiKappa_ne_zero (.some xi eta h)) hordH.ge
    reduce (phiKappa (.some xi eta h)) hHInt ^ 21 = 1 := by
  let H : M := phiKappa (.some xi eta h)
  let XM : M := embedL (Isogeny.dualX xi)
  let xiM : M := embedL xi
  let etaM : M := embedL eta
  have hH : H ≠ 0 := phiKappa_ne_zero (.some xi eta h)
  have hX : XM ≠ 0 := by
    intro hz
    apply dualX_ne_zero_of_nonsingular h
    apply embedL.injective
    simpa [XM] using hz
  have hHInt : IntegralAtTwo H :=
    integralAtTwo_of_ordAt_nonneg hH hordH.ge
  have hXInt : IntegralAtTwo XM :=
    integralAtTwo_of_ordAt_nonneg hX hordX.ge
  have hm3ord : ordAt p2 (-3 : M) = 0 := by
    rw [ordAt_neg, ordAt_p2_three]
  have hm3Int : IntegralAtTwo (-3 : M) :=
    integralAtTwo_of_ordAt_nonneg (by norm_num) hm3ord.ge
  have hxiField : xiM = XM + (-3 : M) := by
    simp only [xiM, XM, Isogeny.dualX, map_add, map_ofNat]
    ring
  have hxiInt : IntegralAtTwo xiM := by
    rw [hxiField]
    exact hXInt.add hm3Int
  have hthreeInt : IntegralAtTwo (3 : M) :=
    integralAtTwo_of_ordAt_nonneg (by norm_num) ordAt_p2_three.ge
  have hzetaInt : IntegralAtTwo zeta :=
    integralAtTwo_of_ordAt_nonneg zeta_ne_zero ordAt_p2_zeta.ge
  have htermInt : IntegralAtTwo ((3 : M) * xiM * zeta ^ 3) :=
    (hthreeInt.mul hxiInt).mul (hzetaInt.pow 3)
  have hetaField : etaM = H - 1 - (3 : M) * xiM * zeta ^ 3 := by
    have hf := phiKappa_integral_formula h
    dsimp [H, xiM, etaM]
    rw [hf]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  have hetaInt : IntegralAtTwo etaM := by
    rw [hetaField]
    exact (hHInt.sub integralAtTwo_one).sub htermInt
  let xbar := reduce xiM hxiInt
  let ybar := reduce etaM hetaInt
  have hx8 : xbar ^ 8 = xbar := by
    apply reduce_pow_eight_of_complexConj_eq
    simpa [xiM] using complexConj_embedL xi
  have hy8 : ybar ^ 8 = ybar := by
    apply reduce_pow_eight_of_complexConj_eq
    simpa [etaM] using complexConj_embedL eta
  have hcurve : ybar ^ 2 + xbar * ybar = xbar ^ 3 := by
    simpa [xbar, ybar, xiM, etaM] using reduce_ehat_equation h hxiInt hetaInt
  have hphi : reduce H hHInt = ybar + 1 + xbar * zetaBar ^ 3 := by
    simpa [H, xbar, ybar, xiM, etaM] using
      reduce_phiKappa_formula h hxiInt hetaInt hHInt
  have hout := affine_residue_pow_twenty_one xbar ybar hx8 hy8 hcurve
  rw [← hphi] at hout
  simpa [H] using hout

theorem normalized_positive_impossible
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta)
    (n : ℤ) (hn : 0 < n)
    (hordH : ordAt p2 (phiKappa (.some xi eta h)) = 3 * n)
    (hordX : ordAt p2 (embedL (Isogeny.dualX xi)) = 2 * n) : False := by
  let H : M := phiKappa (.some xi eta h)
  let XM : M := embedL (Isogeny.dualX xi)
  let xiM : M := embedL xi
  let etaM : M := embedL eta
  have hH : H ≠ 0 := phiKappa_ne_zero (.some xi eta h)
  have hX : XM ≠ 0 := by
    intro hz
    apply dualX_ne_zero_of_nonsingular h
    apply embedL.injective
    simpa [XM] using hz
  have hHpos : 0 < ordAt p2 H := by dsimp [H]; rw [hordH]; omega
  have hXpos : 0 < ordAt p2 XM := by dsimp [XM]; rw [hordX]; omega
  have hHInt : IntegralAtTwo H := integralAtTwo_of_ordAt_nonneg hH hHpos.le
  have hXInt : IntegralAtTwo XM := integralAtTwo_of_ordAt_nonneg hX hXpos.le
  have hm3ord : ordAt p2 (-3 : M) = 0 := by rw [ordAt_neg, ordAt_p2_three]
  have hm3Int : IntegralAtTwo (-3 : M) :=
    integralAtTwo_of_ordAt_nonneg (by norm_num) hm3ord.ge
  have hxiField : xiM = XM + (-3 : M) := by
    simp only [xiM, XM, Isogeny.dualX, map_add, map_ofNat]
    ring
  have hxiInt : IntegralAtTwo xiM := by rw [hxiField]; exact hXInt.add hm3Int
  have hthreeInt : IntegralAtTwo (3 : M) :=
    integralAtTwo_of_ordAt_nonneg (by norm_num) ordAt_p2_three.ge
  have hzetaInt : IntegralAtTwo zeta :=
    integralAtTwo_of_ordAt_nonneg zeta_ne_zero ordAt_p2_zeta.ge
  have htermInt : IntegralAtTwo ((3 : M) * xiM * zeta ^ 3) :=
    (hthreeInt.mul hxiInt).mul (hzetaInt.pow 3)
  have hetaField : etaM = H - 1 - (3 : M) * xiM * zeta ^ 3 := by
    have hf := phiKappa_integral_formula h
    dsimp [H, xiM, etaM]
    rw [hf]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  have hetaInt : IntegralAtTwo etaM := by
    rw [hetaField]
    exact (hHInt.sub integralAtTwo_one).sub htermInt
  have hXred : Reduces XM (0 : k2) := by
    have hz := reduce_eq_zero_of_ordAt_pos hX hXpos
    simpa [hz] using reduce_spec XM (integralAtTwo_of_ordAt_nonneg hX hXpos.le)
  have hxiReduces : Reduces xiM (1 : k2) := by
    rw [hxiField]
    have hm3R := reduces_int (-3)
    rw [k2_intCast_neg_three] at hm3R
    simpa only [zero_add] using hXred.add (by simpa using hm3R)
  have hxiRed : reduce xiM hxiInt = 1 := reduce_eq_of_reduces hxiInt hxiReduces
  let ybar := reduce etaM hetaInt
  have hy8 : ybar ^ 8 = ybar := by
    apply reduce_pow_eight_of_complexConj_eq
    simpa [etaM] using complexConj_embedL eta
  have hcurve := reduce_ehat_equation h hxiInt hetaInt
  rw [hxiRed] at hcurve
  have hyEq : ybar ^ 2 + ybar = 1 := by simpa [ybar] using hcurve
  have hchar : (2 : k2) = 0 := CharP.cast_eq_zero k2 2
  have hyEq2 : ybar ^ 4 + ybar ^ 2 = 1 := by
    calc
      ybar ^ 4 + ybar ^ 2 = (ybar ^ 2 + ybar) ^ 2 := by
        ring_nf
        rw [hchar]
        ring
      _ = 1 := by rw [hyEq]; simp
  have hyEq4 : ybar ^ 8 + ybar ^ 4 = 1 := by
    calc
      ybar ^ 8 + ybar ^ 4 = (ybar ^ 4 + ybar ^ 2) ^ 2 := by
        ring_nf
        rw [hchar]
        ring
      _ = 1 := by rw [hyEq2]; simp
  have htrace : ybar ^ 8 + ybar = 1 := by
    calc
      ybar ^ 8 + ybar = (ybar ^ 8 + ybar ^ 4) +
          (ybar ^ 4 + ybar ^ 2) + (ybar ^ 2 + ybar) := by
            ring_nf
            rw [hchar]
            ring
      _ = 1 + 1 + 1 := by rw [hyEq4, hyEq2, hyEq]
      _ = 1 := by linear_combination hchar
  rw [hy8] at htrace
  have hzero : ybar + ybar = 0 := by linear_combination ybar * hchar
  rw [hzero] at htrace
  exact zero_ne_one htrace

theorem normalized_negative_reduction_pow_twenty_one
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta)
    (n : ℤ) (hn : n < 0)
    (hordH : ordAt p2 (phiKappa (.some xi eta h)) = 3 * n)
    (hordX : ordAt p2 (embedL (Isogeny.dualX xi)) = 2 * n) :
    let H0 := (2 : M) ^ (-3 * n) * phiKappa (.some xi eta h)
    ∀ hH0Int : IntegralAtTwo H0, reduce H0 hH0Int ^ 21 = 1 := by
  dsimp only
  let H : M := phiKappa (.some xi eta h)
  let XM : M := embedL (Isogeny.dualX xi)
  let xiM : M := embedL xi
  let etaM : M := embedL eta
  let term : M := (3 : M) * xiM * zeta ^ 3
  let H0 : M := (2 : M) ^ (-3 * n) * H
  let y0 : M := (2 : M) ^ (-3 * n) * etaM
  let s1 : M := (2 : M) ^ (-3 * n)
  let sTerm : M := (2 : M) ^ (-3 * n) * term
  have hH : H ≠ 0 := phiKappa_ne_zero (.some xi eta h)
  have hX : XM ≠ 0 := by
    intro hz
    apply dualX_ne_zero_of_nonsingular h
    apply embedL.injective
    simpa [XM] using hz
  have hm3ne : (-3 : M) ≠ 0 := by norm_num
  have hm3ord : ordAt p2 (-3 : M) = 0 := by rw [ordAt_neg, ordAt_p2_three]
  have hxiField : xiM = XM + (-3 : M) := by
    simp only [xiM, XM, Isogeny.dualX, map_add, map_ofNat]
    ring
  have hXlt : ordAt p2 XM < ordAt p2 (-3 : M) := by
    rw [hordX, hm3ord]
    omega
  have hxiOrd : ordAt p2 xiM = 2 * n := by
    rw [hxiField]
    exact (ordAt_add_eq_left_of_lt p2 hX hm3ne hXlt).trans hordX
  have hxi : xiM ≠ 0 := by
    intro hzero
    rw [hzero] at hxiOrd
    simp [ordAt] at hxiOrd
    omega
  have hterm : term ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hxi) (pow_ne_zero 3 zeta_ne_zero)
  have htermOrd : ordAt p2 term = 2 * n := by
    dsimp [term]
    rw [ordAt_mul p2 (mul_ne_zero (by norm_num) hxi) (pow_ne_zero 3 zeta_ne_zero),
      ordAt_mul p2 (by norm_num) hxi,
      ordAt_pow p2 zeta_ne_zero 3, ordAt_p2_three, ordAt_p2_zeta,
      hxiOrd]
    ring
  have hetaField : etaM = H - 1 - term := by
    have hf := phiKappa_integral_formula h
    dsimp [H, xiM, etaM, term]
    rw [hf]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  have hHminusOrd : ordAt p2 (H + (-1 : M)) = 3 * n := by
    have hlt : ordAt p2 H < ordAt p2 (-1 : M) := by
      dsimp [H]
      rw [hordH]
      simp [ordAt]
      omega
    exact (ordAt_add_eq_left_of_lt p2 hH (by norm_num) hlt).trans hordH
  have hHminus : H + (-1 : M) ≠ 0 := by
    intro hzero
    rw [hzero] at hHminusOrd
    simp [ordAt] at hHminusOrd
    omega
  have hetaOrd : ordAt p2 etaM = 3 * n := by
    rw [hetaField, sub_eq_add_neg, sub_eq_add_neg]
    have hlt : ordAt p2 (H + -1) < ordAt p2 (-term) := by
      rw [hHminusOrd, ordAt_neg, htermOrd]
      omega
    exact (ordAt_add_eq_left_of_lt p2 hHminus (neg_ne_zero.mpr hterm) hlt).trans
      hHminusOrd
  have heta : etaM ≠ 0 := by
    intro hzero
    rw [hzero] at hetaOrd
    simp [ordAt] at hetaOrd
    omega
  have hH0 : H0 ≠ 0 := by
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) hH
  have hy0 : y0 ≠ 0 := by
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num)) heta
  have hs1 : s1 ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hsTerm : sTerm ≠ 0 := mul_ne_zero hs1 hterm
  have hH0Ord : ordAt p2 H0 = 0 := by
    dsimp [H0]
    rw [ordAt_two_zpow_mul hH]
    dsimp [H]
    rw [hordH]
    ring
  have hy0Ord : ordAt p2 y0 = 0 := by
    dsimp [y0]
    rw [ordAt_two_zpow_mul heta, hetaOrd]
    ring
  have hs1Ord : ordAt p2 s1 = -3 * n := by
    exact ordAt_two_zpow (-3 * n)
  have hs1Pos : 0 < ordAt p2 s1 := by rw [hs1Ord]; omega
  have hsTermOrd : ordAt p2 sTerm = -n := by
    dsimp [sTerm]
    rw [ordAt_two_zpow_mul hterm, htermOrd]
    ring
  have hsTermPos : 0 < ordAt p2 sTerm := by rw [hsTermOrd]; omega
  have hy0Int : IntegralAtTwo y0 :=
    integralAtTwo_of_ordAt_nonneg hy0 hy0Ord.ge
  have hs1Int : IntegralAtTwo s1 :=
    integralAtTwo_of_ordAt_nonneg hs1 hs1Pos.le
  have hsTermInt : IntegralAtTwo sTerm :=
    integralAtTwo_of_ordAt_nonneg hsTerm hsTermPos.le
  have hfield : H0 = y0 + s1 + sTerm := by
    have hf := phiKappa_integral_formula h
    dsimp [H0, y0, s1, sTerm, H, etaM, xiM, term]
    rw [hf]
    simp only [map_add, map_mul, map_one, map_ofNat]
    ring
  have hs1Red : Reduces s1 (0 : k2) := by
    have hz := reduce_eq_zero_of_ordAt_pos hs1 hs1Pos
    simpa [hz] using reduce_spec s1 hs1Int
  have hsTermRed : Reduces sTerm (0 : k2) := by
    have hz := reduce_eq_zero_of_ordAt_pos hsTerm hsTermPos
    simpa [hz] using reduce_spec sTerm hsTermInt
  have hYSeven : reduce y0 hy0Int ^ 7 = 1 := by
    exact reduce_pow_seven_eq_one_of_complexConj_eq hy0 hy0Ord <|
      by simpa [y0, etaM] using complexConj_two_zpow_embedL (-3 * n) eta
  intro hH0Int
  have hHReduces : Reduces H0 (reduce y0 hy0Int) := by
    rw [hfield]
    simpa using ((reduce_spec y0 hy0Int).add hs1Red).add hsTermRed
  have hred : reduce H0 hH0Int = reduce y0 hy0Int :=
    reduce_eq_of_reduces hH0Int hHReduces
  rw [hred]
  calc
    reduce y0 hy0Int ^ 21 = (reduce y0 hy0Int ^ 7) ^ 3 := by ring
    _ = 1 := by rw [hYSeven]; simp

theorem phiKappa_candidate_exponent_zero
    {xi eta : L} (h : WeierstrassCurve.Affine.Nonsingular Ehat0 xi eta)
    (e : Fin 3) (c : M)
    (hcand : phiKappa (.some xi eta h) = zeta ^ e.val * c ^ 3) : e = 0 := by
  let H : M := phiKappa (.some xi eta h)
  let XM : M := embedL (Isogeny.dualX xi)
  have hH : H ≠ 0 := phiKappa_ne_zero (.some xi eta h)
  have hc : c ≠ 0 := by
    intro hc0
    apply hH
    dsimp [H]
    rw [hcand, hc0]
    norm_num
  have hX : XM ≠ 0 := by
    intro hz
    apply dualX_ne_zero_of_nonsingular h
    apply embedL.injective
    simpa [XM] using hz
  let n : ℤ := ordAt p2 c
  have hordH : ordAt p2 H = 3 * n := by
    dsimp [H]
    rw [hcand, ordAt_mul p2 (pow_ne_zero e.val zeta_ne_zero)
      (pow_ne_zero 3 hc), ordAt_p2_zeta_pow,
      ordAt_pow p2 hc 3]
    dsimp [n]
    ring
  have hHC : NumberField.IsCMField.complexConj M H ≠ 0 := by
    simpa only [map_zero] using
      (NumberField.IsCMField.complexConj M).injective.ne_iff.mpr hH
  have hnorm : H * NumberField.IsCMField.complexConj M H = XM ^ 3 := by
    simpa [H, XM, phiKappaX] using phiKappa_norm (.some xi eta h)
  have hordX : ordAt p2 XM = 2 * n := by
    have hmul := ordAt_mul p2 hH hHC
    have hpow := ordAt_pow p2 hX 3
    rw [hnorm] at hmul
    have hconj := ordAt_p2_complexConj hH
    rw [hconj, hordH, hpow] at hmul
    omega
  let d : M := (2 : M) ^ (-n) * c
  let H0 : M := (2 : M) ^ (-3 * n) * H
  have hd : d ≠ 0 := mul_ne_zero (zpow_ne_zero _ (by norm_num)) hc
  have hH0 : H0 ≠ 0 := mul_ne_zero (zpow_ne_zero _ (by norm_num)) hH
  have hdOrd : ordAt p2 d = 0 := by
    dsimp [d]
    rw [ordAt_two_zpow_mul hc]
    dsimp [n]
    ring
  have hH0Ord : ordAt p2 H0 = 0 := by
    dsimp [H0]
    rw [ordAt_two_zpow_mul hH, hordH]
    ring
  have hdInt : IntegralAtTwo d := integralAtTwo_of_ordAt_nonneg hd hdOrd.ge
  have hH0Int : IntegralAtTwo H0 := integralAtTwo_of_ordAt_nonneg hH0 hH0Ord.ge
  have hscaleCube : d ^ 3 = (2 : M) ^ (-3 * n) * c ^ 3 := by
    dsimp [d]
    rw [mul_pow]
    have hz : ((2 : M) ^ (-n)) ^ 3 = (2 : M) ^ ((-n) * 3) := by
      have hz0 := (zpow_mul (2 : M) (-n) (3 : ℤ)).symm
      calc
        ((2 : M) ^ (-n)) ^ (3 : ℕ) = ((2 : M) ^ (-n)) ^ (3 : ℤ) :=
          (zpow_natCast _ 3).symm
        _ = (2 : M) ^ ((-n) * 3) := hz0
    rw [hz]
    congr 2
    ring
  have hH0cand : H0 = zeta ^ e.val * d ^ 3 := by
    dsimp [H0, H]
    rw [hcand, hscaleCube]
    ring
  have hactual : reduce H0 hH0Int ^ 21 = 1 := by
    rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
    · exact normalized_negative_reduction_pow_twenty_one h n hnneg hordH hordX hH0Int
    · have hordH' : ordAt p2 (phiKappa (.some xi eta h)) = 0 := by
        simpa [H, hnzero] using hordH
      have hordX' : ordAt p2 (embedL (Isogeny.dualX xi)) = 0 := by
        simpa [XM, hnzero] using hordX
      have hz := normalized_zero_reduction_pow_twenty_one h hordH' hordX'
      simpa [H0, H, hnzero] using hz
    · exact (normalized_positive_impossible h n hnpos hordH hordX).elim
  have hredCand : reduce H0 hH0Int =
      zetaBar ^ e.val * reduce d hdInt ^ 3 := by
    apply reduce_eq_of_reduces
    rw [hH0cand]
    exact (reduces_zeta.pow e.val).mul ((reduce_spec d hdInt).pow 3)
  have hdbar : reduce d hdInt ≠ 0 := reduce_ne_zero_of_ordAt_eq_zero hd hdOrd
  have hp := zetaBar_mul_cube_pow_twenty_one e (reduce d hdInt) hdbar
  rw [← hredCand, hactual] at hp
  exact (zetaBar_pow_fin_three_eq_one_iff e).mp hp.symm

theorem phiKappa_is_cube (Q : Ehat0Point) :
    ∃ c : M, phiKappa Q = c ^ 3 := by
  cases Q with
  | zero => exact ⟨1, by simp [phiKappa]⟩
  | some xi eta h =>
      obtain ⟨e, c, hc⟩ := phiKappa_global_candidate (.some xi eta h)
      have he : e = 0 := phiKappa_candidate_exponent_zero h e c hc
      subst e
      exact ⟨c, by simpa using hc⟩

end

end MazurProof.N18RouteC.PhiLocal
