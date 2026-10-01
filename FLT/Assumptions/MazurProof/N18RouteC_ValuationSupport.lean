import FLT.Assumptions.MazurProof.N18RouteC_Composition
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# Valuation support of the dual Kummer value

This file proves the coordinate-local statement behind the global dual
cube-class list.  At every height-one prime where `2` and `3` are units, the
order of the Tate coordinate `w` is divisible by three.  The proof works
directly with the discrete valuation of the field and therefore does not
need a separately normalized integral Weierstrass triple.
-/

namespace MazurProof.N18RouteC.ValuationSupport

open FieldArithmetic Isogeny KummerGeometry

noncomputable section

set_option maxHeartbeats 500000

abbrev OL := NumberField.RingOfIntegers L

def ordAt (q : IsDedekindDomain.HeightOneSpectrum OL) (x : L) : ℤ :=
  -WithZero.log (q.valuation L x)

private theorem val_ne_zero
    (q : IsDedekindDomain.HeightOneSpectrum OL) {x : L} (hx : x ≠ 0) :
    q.valuation L x ≠ 0 :=
  (Valuation.ne_zero_iff (q.valuation L)).2 hx

@[simp] theorem ordAt_one (q : IsDedekindDomain.HeightOneSpectrum OL) :
    ordAt q 1 = 0 := by simp [ordAt]

theorem ordAt_mul (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt q (x * y) = ordAt q x + ordAt q y := by
  unfold ordAt
  rw [map_mul, WithZero.log_mul (val_ne_zero q hx) (val_ne_zero q hy)]
  ring

theorem ordAt_div (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt q (x / y) = ordAt q x - ordAt q y := by
  unfold ordAt
  rw [map_div₀, WithZero.log_div (val_ne_zero q hx) (val_ne_zero q hy)]
  ring

theorem ordAt_pow (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x : L} (hx : x ≠ 0) (n : ℕ) :
    ordAt q (x ^ n) = n * ordAt q x := by
  unfold ordAt
  rw [map_pow, WithZero.log_pow]
  simp only [nsmul_eq_mul]
  ring

@[simp] theorem ordAt_neg (q : IsDedekindDomain.HeightOneSpectrum OL)
    (x : L) : ordAt q (-x) = ordAt q x := by
  unfold ordAt
  rw [(q.valuation L).map_neg]

private theorem val_lt_of_ord_lt
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ordAt q x < ordAt q y) :
    q.valuation L y < q.valuation L x := by
  rw [← WithZero.log_lt_log (val_ne_zero q hy) (val_ne_zero q hx)]
  unfold ordAt at hxy
  omega

theorem ordAt_add_eq_left_of_lt
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ordAt q x < ordAt q y) :
    ordAt q (x + y) = ordAt q x := by
  unfold ordAt
  rw [(q.valuation L).map_add_eq_of_lt_left
    (val_lt_of_ord_lt q hx hy hxy)]

theorem ordAt_add_eq_right_of_lt
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0)
    (hyx : ordAt q y < ordAt q x) :
    ordAt q (x + y) = ordAt q y := by
  rw [add_comm]
  exact ordAt_add_eq_left_of_lt q hy hx hyx

theorem ordAt_add_ge_min
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (ordAt q x) (ordAt q y) ≤ ordAt q (x + y) := by
  rcases lt_trichotomy (ordAt q x) (ordAt q y) with hlt | heq | hgt
  · rw [ordAt_add_eq_left_of_lt q hx hy hlt, min_eq_left hlt.le]
  · rw [min_eq_left heq.le]
    have hlogs :
        WithZero.log (q.valuation L x) = WithZero.log (q.valuation L y) := by
      unfold ordAt at heq
      omega
    have hvalYX : q.valuation L y ≤ q.valuation L x := by
      rw [← WithZero.log_le_log (val_ne_zero q hy) (val_ne_zero q hx), ← hlogs]
    have hv := (q.valuation L).map_add x y
    rw [max_eq_left hvalYX] at hv
    have hlog := (WithZero.log_le_log (val_ne_zero q hxy) (val_ne_zero q hx)).2 hv
    unfold ordAt
    exact neg_le_neg hlog
  · rw [ordAt_add_eq_right_of_lt q hx hy hgt, min_eq_right hgt.le]

theorem ordAt_sum3_eq_first_of_lt
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y z : L} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : ordAt q x < ordAt q y) (hxz : ordAt q x < ordAt q z) :
    ordAt q (x + y + z) = ordAt q x := by
  have hxyOrd := ordAt_add_eq_left_of_lt q hx hy hxy
  have hxy0 : x + y ≠ 0 := by
    intro hzero
    have hv := (q.valuation L).map_add_eq_of_lt_left
      (val_lt_of_ord_lt q hx hy hxy)
    rw [hzero, map_zero] at hv
    exact (val_ne_zero q hx) hv.symm
  have hlt : ordAt q (x + y) < ordAt q z := by rwa [hxyOrd]
  rw [ordAt_add_eq_left_of_lt q hxy0 hz hlt, hxyOrd]

theorem ordAt_sum3_ge_min
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    {x y z : L} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x + y ≠ 0) (hxyz : x + y + z ≠ 0) :
    min (min (ordAt q x) (ordAt q y)) (ordAt q z) ≤
      ordAt q (x + y + z) := by
  exact le_trans
    (min_le_min_right _ (ordAt_add_ge_min q hx hy hxy))
    (ordAt_add_ge_min q hxy hz hxyz)

/-- Outside the primes dividing `6`, the dual Kummer coordinate has order
divisible by three. -/
theorem tateW_order_mod_three
    (q : IsDedekindDomain.HeightOneSpectrum OL)
    {u w : L} (hu : u ≠ 0) (hw : w ≠ 0)
    (hcurve : w * (w - 3 * u + 2) = u ^ 3)
    (hTwo : ordAt q (2 : L) = 0)
    (hThree : ordAt q (3 : L) = 0) :
    (3 : ℤ) ∣ ordAt q w := by
  have h3 : (3 : L) ≠ 0 := by norm_num
  have h2 : (2 : L) ≠ 0 := by norm_num
  have h3u : (3 : L) * u ≠ 0 := mul_ne_zero h3 hu
  have hz : w - 3 * u + 2 ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero] at hcurve
    exact hu ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hcurve.symm)
  have hmul := ordAt_mul q hw hz
  have hpow := ordAt_pow q hu 3
  rw [hcurve] at hmul
  have heq : ordAt q w + ordAt q (w - 3 * u + 2) = 3 * ordAt q u := by
    rw [← hmul, hpow]
    norm_num
  have h3uOrd : ordAt q ((3 : L) * u) = ordAt q u := by
    rw [ordAt_mul q h3 hu, hThree, zero_add]
  have hneg3uOrd : ordAt q (-((3 : L) * u)) = ordAt q u := by
    rw [ordAt_neg, h3uOrd]
  let r := ordAt q u
  let s := ordAt q w
  by_cases hrneg : r < 0
  · have hsneg : s < 0 := by
      by_contra hsnot
      have hsnonneg : 0 ≤ s := le_of_not_gt hsnot
      have hterm : ordAt q (-((3 : L) * u)) = r := by
        simpa [r] using hneg3uOrd
      have hdom1 : ordAt q (-((3 : L) * u)) < ordAt q w := by
        dsimp [r, s] at hrneg hsnonneg ⊢
        omega
      have hdom2 : ordAt q (-((3 : L) * u)) < ordAt q (2 : L) := by
        rw [hterm, hTwo]
        exact hrneg
      have hord : ordAt q (w + (-((3 : L) * u)) + 2) = r := by
        rw [add_comm w]
        calc
          ordAt q (-((3 : L) * u) + w + 2) = ordAt q (-((3 : L) * u)) :=
            ordAt_sum3_eq_first_of_lt q (x := -((3 : L) * u)) (y := w) (z := 2)
              (neg_ne_zero.mpr h3u) hw h2 hdom1 hdom2
          _ = r := hterm
      have hshape : w + (-((3 : L) * u)) + 2 = w - 3 * u + 2 := by ring
      rw [hshape] at hord
      rw [hord] at heq
      dsimp [r, s] at hrneg hsnonneg heq
      omega
    rcases lt_trichotomy s r with hsr | hsr | hsr
    · have hterm : ordAt q (-((3 : L) * u)) = r := by
        simpa [r] using hneg3uOrd
      have hs0 : s < ordAt q (2 : L) := by rw [hTwo]; exact hsneg
      have hord : ordAt q (w + (-((3 : L) * u)) + 2) = s :=
        ordAt_sum3_eq_first_of_lt q hw (neg_ne_zero.mpr h3u) h2
          (by rwa [hterm]) hs0
      have hshape : w + (-((3 : L) * u)) + 2 = w - 3 * u + 2 := by ring
      rw [hshape] at hord
      have htwo : 2 * s = 3 * r := by omega
      have hthreeMul : (3 : ℤ) ∣ 2 * s := ⟨r, by omega⟩
      rcases (Int.prime_three.dvd_mul.mp hthreeMul) with hthreeTwo | hthreeS
      · norm_num at hthreeTwo
      · simpa [s] using hthreeS
    · have hterm : ordAt q (-((3 : L) * u)) = r := by
        simpa [r] using hneg3uOrd
      by_cases hsum0 : w + (-((3 : L) * u)) = 0
      · have hord : ordAt q (w - 3 * u + 2) = 0 := by
          have hshape : w - 3 * u + 2 = (w + (-((3 : L) * u))) + 2 := by ring
          rw [hshape, hsum0, zero_add, hTwo]
        exfalso
        rw [hord] at heq
        dsimp [r, s] at heq hsr hrneg
        omega
      · have hge := ordAt_sum3_ge_min q hw (neg_ne_zero.mpr h3u) h2
          hsum0 (by simpa [sub_eq_add_neg, add_assoc] using hz)
        rw [hterm, hTwo] at hge
        change min (min s r) 0 ≤ ordAt q (w + (-((3 : L) * u)) + 2) at hge
        rw [hsr, min_self, min_eq_left hrneg.le] at hge
        have hge' : r ≤ ordAt q (w - 3 * u + 2) := by
          simpa [sub_eq_add_neg, add_assoc] using hge
        exfalso
        dsimp [r, s] at heq hsr hrneg hge'
        omega
    · have hterm : ordAt q (-((3 : L) * u)) = r := by
        simpa [r] using hneg3uOrd
      have hr0 : r < ordAt q (2 : L) := by rw [hTwo]; exact hrneg
      have hord : ordAt q (-((3 : L) * u) + w + 2) = r := by
        calc
          ordAt q (-((3 : L) * u) + w + 2) = ordAt q (-((3 : L) * u)) :=
            ordAt_sum3_eq_first_of_lt q (neg_ne_zero.mpr h3u) hw h2
              (by rwa [hterm]) (by rwa [hterm])
          _ = r := hterm
      have hshape : -((3 : L) * u) + w + 2 = w - 3 * u + 2 := by ring
      rw [hshape] at hord
      rw [hord] at heq
      dsimp [r, s] at heq hsr hrneg
      omega
  · have hrnonneg : 0 ≤ r := le_of_not_gt hrneg
    by_cases hspos : 0 < s
    · by_cases hrpos : 0 < r
      · have hterm : ordAt q (-((3 : L) * u)) = r := by
          simpa [r] using hneg3uOrd
        have h2w : ordAt q (2 : L) < ordAt q w := by rw [hTwo]; exact hspos
        have h2u : ordAt q (2 : L) < ordAt q (-((3 : L) * u)) := by
          rw [hTwo, hterm]
          exact hrpos
        have hord : ordAt q ((2 : L) + w + (-((3 : L) * u))) = 0 := by
          have := ordAt_sum3_eq_first_of_lt q h2 hw (neg_ne_zero.mpr h3u)
            h2w h2u
          simpa [hTwo] using this
        have hshape : (2 : L) + w + (-((3 : L) * u)) = w - 3 * u + 2 := by ring
        rw [hshape] at hord
        rw [hord] at heq
        refine ⟨r, ?_⟩
        dsimp [r, s] at heq ⊢
        omega
      · have hr0 : r = 0 := by omega
        have hterm : ordAt q (-((3 : L) * u)) = 0 := by
          simpa [r, hr0] using hneg3uOrd
        have hsum0 : w + (-((3 : L) * u)) ≠ 0 := by
          intro hzero
          have hwEq : w = (3 : L) * u := by linear_combination hzero
          have hs0 : s = 0 := by
            dsimp [s]
            rw [hwEq, h3uOrd]
            simpa [r] using hr0
          omega
        have hge := ordAt_sum3_ge_min q hw (neg_ne_zero.mpr h3u) h2
          hsum0 (by simpa [sub_eq_add_neg, add_assoc] using hz)
        rw [hterm, hTwo, min_eq_right hspos.le, min_self] at hge
        have hge' : 0 ≤ ordAt q (w - 3 * u + 2) := by
          simpa [sub_eq_add_neg, add_assoc] using hge
        dsimp [r, s] at heq hspos hge'
        omega
    · have hsnonpos : s ≤ 0 := le_of_not_gt hspos
      have hs0 : s = 0 := by
        by_contra hsne
        have hsneg : s < 0 := lt_of_le_of_ne hsnonpos hsne
        have hterm : ordAt q (-((3 : L) * u)) = r := by
          simpa [r] using hneg3uOrd
        have hsw : s < ordAt q (-((3 : L) * u)) := by
          rw [hterm]
          omega
        have hs2 : s < ordAt q (2 : L) := by rw [hTwo]; exact hsneg
        have hord : ordAt q (w + (-((3 : L) * u)) + 2) = s :=
          ordAt_sum3_eq_first_of_lt q hw (neg_ne_zero.mpr h3u) h2 hsw hs2
        have hshape : w + (-((3 : L) * u)) + 2 = w - 3 * u + 2 := by ring
        rw [hshape] at hord
        rw [hord] at heq
        dsimp [r, s] at heq hsneg hrnonneg
        omega
      exact ⟨0, by simpa [s, hs0]⟩

end

end MazurProof.N18RouteC.ValuationSupport
