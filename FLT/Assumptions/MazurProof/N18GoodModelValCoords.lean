import FLT.Assumptions.MazurProof.N18RouteC_GoodModel
import FLT.Assumptions.MazurProof.N18AddCongr

/-!
# Coordinate valuations on the good model at `pi`

This ports the Newton-polygon coordinate calculation for `E0` to the good
model `E0Good`.  The only new input is that the coefficients of `E0Good` are
algebraic integers, hence have nonnegative `pi`-adic order.
-/

namespace MazurProof.N18RouteC.GoodModel

open MazurProof.N18RouteC.FieldArithmetic
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18Block5Instantiation.AddCongr

noncomputable section

local macro "n18_ring" : tactic =>
  `(tactic|
    (ring_nf
     simp only [a_pow_four, a_cubic]
     ring))

/-- An algebraic integer has nonnegative additive order at `pi`. -/
theorem zero_le_ordPi_of_isIntegral {u : L} (hu : IsIntegral ℤ u) : 0 ≤ ordPi u := by
  rcases eq_or_ne u 0 with rfl | hu0
  · rw [ordPi_zero]
  · have hle : v3 u ≤ 1 := by
      show p3.valuation L u ≤ 1
      simpa using
        (IsDedekindDomain.HeightOneSpectrum.valuation_le_one
          (K := L) p3 (⟨u, hu⟩ : NumberField.RingOfIntegers L))
    have hlog : WithZero.log (v3 u) ≤ 0 := by
      have h := (WithZero.log_le_log (v3_ne_zero hu0) one_ne_zero).mpr hle
      rwa [WithZero.log_one] at h
    unfold ordPi
    linarith

/-- Every element of the ring of integers has nonnegative additive order at
`pi`. -/
theorem zero_le_ordPi_ringOfIntegers (u : NumberField.RingOfIntegers L) :
    0 ≤ ordPi (u : L) :=
  zero_le_ordPi_of_isIntegral u.isIntegral_coe

/-- If a finite point `(x,y)` on `E0Good` has negative `pi`-adic `x`-order,
then its coordinate orders are determined by the formal parameter `-x/y`.

This is the Newton-polygon argument from `AddCongr.val_coords`.  Integrality
of the good-model coefficients replaces the integer-cast calculation used
for the original model. -/
theorem val_coords {x y : L} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (heq : y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y
         = x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆)
    (hx : ordPi x < 0) :
    ordPi x = -2 * ordPi (-x / y) ∧ ordPi y = -3 * ordPi (-x / y) := by
  have ha : ordPi x ≤ -1 := by omega
  -- The coefficients used multiplicatively below are nonzero.
  have ha1_mul : E0Good.a₁ * (a ^ 2 - a - 1) = 1 := by
    simp only [E0Good]
    n18_ring
  have ha1_ne : E0Good.a₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha1_mul
    exact zero_ne_one ha1_mul
  have ha2_mul : E0Good.a₂ * (-2 * a ^ 2 + a + 6) = 1 := by
    simp only [E0Good]
    n18_ring
  have ha2_ne : E0Good.a₂ ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha2_mul
    exact zero_ne_one ha2_mul
  have ha3_mul : E0Good.a₃ * (-a ^ 2 + a + 2) = 1 := by
    simp only [E0Good]
    n18_ring
  have ha3_ne : E0Good.a₃ ≠ 0 := by
    intro h
    rw [h, zero_mul] at ha3_mul
    exact zero_ne_one ha3_mul
  have hpi_ne : pi ≠ 0 := by
    intro h
    have hv := ordPi_pi
    rw [h, ordPi_zero] at hv
    omega
  have ha4_eq : E0Good.a₄ = -pi * (a + 1) := by
    simp only [E0Good]
    unfold a
    ring
  have ha4_ne : E0Good.a₄ ≠ 0 := by
    rw [ha4_eq]
    exact mul_ne_zero (neg_ne_zero.mpr hpi_ne) ha3_ne
  -- Every coefficient is the image of an explicit element of O_L.
  let c1 : NumberField.RingOfIntegers L := aInteger ^ 2 - 2
  let c2 : NumberField.RingOfIntegers L := -aInteger ^ 2 + 2 * aInteger + 1
  let c3 : NumberField.RingOfIntegers L := aInteger + 1
  let c4 : NumberField.RingOfIntegers L := -aInteger ^ 2 + 1
  let c6 : NumberField.RingOfIntegers L := 4 * aInteger ^ 2 - 7 * aInteger - 3
  have hmapNat (n : ℕ) :
      algebraMap (NumberField.RingOfIntegers L) L
          (n : NumberField.RingOfIntegers L) = (n : L) :=
    map_natCast (algebraMap (NumberField.RingOfIntegers L) L) n
  have hc1_eq : (c1 : L) = E0Good.a₁ := by
    simp [c1, aInteger, E0Good]
    exact hmapNat 2
  have hc2_eq : (c2 : L) = E0Good.a₂ := by
    simp [c2, aInteger, E0Good]
    left
    exact hmapNat 2
  have hc3_eq : (c3 : L) = E0Good.a₃ := by
    simp [c3, aInteger, E0Good]
  have hc4_eq : (c4 : L) = E0Good.a₄ := by
    simp [c4, aInteger, E0Good]
  have hc6_eq : (c6 : L) = E0Good.a₆ := by
    simp [c6, aInteger, E0Good]
    rw [map_ofNat (algebraMap (NumberField.RingOfIntegers L) L) 4,
      map_ofNat (algebraMap (NumberField.RingOfIntegers L) L) 7,
      map_ofNat (algebraMap (NumberField.RingOfIntegers L) L) 3]
  have hc1 : 0 ≤ ordPi E0Good.a₁ := by
    rw [← hc1_eq]
    exact zero_le_ordPi_ringOfIntegers c1
  have hc2 : 0 ≤ ordPi E0Good.a₂ := by
    rw [← hc2_eq]
    exact zero_le_ordPi_ringOfIntegers c2
  have hc3 : 0 ≤ ordPi E0Good.a₃ := by
    rw [← hc3_eq]
    exact zero_le_ordPi_ringOfIntegers c3
  have hc4 : 0 ≤ ordPi E0Good.a₄ := by
    rw [← hc4_eq]
    exact zero_le_ordPi_ringOfIntegers c4
  have hc6 : 0 ≤ ordPi E0Good.a₆ := by
    rw [← hc6_eq]
    exact zero_le_ordPi_ringOfIntegers c6
  -- Monomial valuations.
  have hy2 : ordPi (y ^ 2) = 2 * ordPi y := by
    rw [show y ^ 2 = y * y by ring, ordPi_mul hy0 hy0]
    ring
  have hx2 : ordPi (x ^ 2) = 2 * ordPi x := by
    rw [show x ^ 2 = x * x by ring, ordPi_mul hx0 hx0]
    ring
  have hx3 : ordPi (x ^ 3) = 3 * ordPi x := by
    rw [show x ^ 3 = x * x * x by ring,
      ordPi_mul (mul_ne_zero hx0 hx0) hx0, ordPi_mul hx0 hx0]
    ring
  have hxy :
      ordPi (E0Good.a₁ * x * y) =
        ordPi E0Good.a₁ + ordPi x + ordPi y := by
    rw [ordPi_mul (mul_ne_zero ha1_ne hx0) hy0, ordPi_mul ha1_ne hx0]
  have ha3y :
      ordPi (E0Good.a₃ * y) = ordPi E0Good.a₃ + ordPi y := by
    rw [ordPi_mul ha3_ne hy0]
  have ha2x :
      ordPi (E0Good.a₂ * x ^ 2) = ordPi E0Good.a₂ + 2 * ordPi x := by
    rw [ordPi_mul ha2_ne (pow_ne_zero 2 hx0), hx2]
  have ha4x :
      ordPi (E0Good.a₄ * x) = ordPi E0Good.a₄ + ordPi x := by
    rw [ordPi_mul ha4_ne hx0]
  -- On the right-hand side, x^3 strictly dominates all remaining terms.
  have htail_lb :
      3 * ordPi x + 1 ≤
        ordPi (E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    apply le_ordPi_add _ _ (by omega)
    · apply le_ordPi_add _ _ (by omega)
      · rw [ha2x]
        omega
      · rw [ha4x]
        omega
    · exact le_trans (by omega) hc6
  have hRHS :
      ordPi (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) =
        3 * ordPi x := by
    by_cases htail : E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ = 0
    · rw [show x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ =
            x ^ 3 + (E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) by ring,
          htail, add_zero, hx3]
    · rw [show x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ =
            x ^ 3 + (E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) by ring,
          ordPi_add_eq_of_lt (pow_ne_zero 3 hx0) htail
            (by rw [hx3]; linarith [htail_lb]),
          hx3]
  have hLHS :
      ordPi (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y) =
        3 * ordPi x := by
    rw [heq]
    exact hRHS
  -- The equation first forces v(y) < 0, then v(y) < v(x).
  have hb_neg : ordPi y < 0 := by
    by_contra hbn
    push Not at hbn
    have hlb :
        3 * ordPi x + 1 ≤
          ordPi (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y) := by
      apply le_ordPi_add _ _ (by omega)
      · apply le_ordPi_add _ _ (by omega)
        · rw [hy2]
          omega
        · rw [hxy]
          omega
      · rw [ha3y]
        omega
    omega
  have hb_lt : ordPi y < ordPi x := by
    by_contra hba
    push Not at hba
    have hlb :
        3 * ordPi x + 1 ≤
          ordPi (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y) := by
      apply le_ordPi_add _ _ (by omega)
      · apply le_ordPi_add _ _ (by omega)
        · rw [hy2]
          omega
        · rw [hxy]
          omega
      · rw [ha3y]
        omega
    omega
  -- On the left-hand side, y^2 now strictly dominates.
  have hrest_lb :
      2 * ordPi y + 1 ≤ ordPi (E0Good.a₁ * x * y + E0Good.a₃ * y) := by
    apply le_ordPi_add _ _ (by omega)
    · rw [hxy]
      omega
    · rw [ha3y]
      omega
  have hkey : 2 * ordPi y = 3 * ordPi x := by
    by_cases hrest : E0Good.a₁ * x * y + E0Good.a₃ * y = 0
    · have hcollapse :
          ordPi (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y) =
            ordPi (y ^ 2) := by
        rw [show y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y =
              y ^ 2 + (E0Good.a₁ * x * y + E0Good.a₃ * y) by ring,
            hrest, add_zero]
      rw [hcollapse, hy2] at hLHS
      exact hLHS
    · have hdom :
          ordPi (y ^ 2 + (E0Good.a₁ * x * y + E0Good.a₃ * y)) =
            ordPi (y ^ 2) :=
        ordPi_add_eq_of_lt (pow_ne_zero 2 hy0) hrest
          (by rw [hy2]; linarith [hrest_lb])
      rw [show y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y =
            y ^ 2 + (E0Good.a₁ * x * y + E0Good.a₃ * y) by ring,
          hdom, hy2] at hLHS
      exact hLHS
  have hc : ordPi (-x / y) = ordPi x - ordPi y := by
    rw [ordPi_div (neg_ne_zero.mpr hx0) hy0, ordPi_neg]
  exact ⟨by rw [hc]; omega, by rw [hc]; omega⟩

end

end MazurProof.N18RouteC.GoodModel
