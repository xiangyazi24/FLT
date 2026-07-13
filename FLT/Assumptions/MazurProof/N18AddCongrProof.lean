import FLT.Assumptions.MazurProof.N18AddCongr
import FLT.Assumptions.MazurProof.N18RouteC_TorsionTable

/-!
# Audit of the proposed `N18AddCongr.add_congr` statement

The concrete chart polynomial identities are recorded first.  The proposed
valuation statement cannot be proved: the explicit order-21 table already in
the repository supplies a counterexample.
-/

open scoped Classical
open scoped WeierstrassCurve.Affine

namespace MazurProof.N18Block5Instantiation.AddCongrProof

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18RouteC.TorsionTable
open MazurProof.N18Block5Instantiation.AddCongr

noncomputable section

/-! ## The concrete chart algebra -/

def G (t w : L) : L :=
  w - t * w + t ^ 2 * w - w ^ 2 + 5 * t * w ^ 2 - 5 * w ^ 3 - t ^ 3

def A (m : L) : L := 1 - m - 5 * m ^ 2 + 5 * m ^ 3

def B (m b : L) : L := m - b + m ^ 2 - 10 * m * b + 15 * m ^ 2 * b

def C (m b : L) : L := m - b - 2 * m * b + 5 * b ^ 2 - 15 * m * b ^ 2

def D (b : L) : L := b - b ^ 2 - 5 * b ^ 3

def H (m b : L) : L := -8 * m + 16 * m ^ 2 - 4 * b + 20 * m * b

theorem G_line (t m b : L) :
    G t (m * t + b) =
      -A m * t ^ 3 - B m b * t ^ 2 + C m b * t + D b := by
  simp only [G, A, B, C, D]
  ring

theorem BC_factor (m b : L) :
    B m b * (1 - b) - (1 + m) * C m b = b * H m b := by
  simp only [B, C, H]
  ring

/-- Identity (8), implied by the first two Vieta equations and `BC_factor`. -/
theorem identity8 (m b t₁ t₂ u t₃ d : L)
    (hsum : A m * (t₁ + t₂ + u) + B m b = 0)
    (hpair : A m * (t₁ * t₂ + (t₁ + t₂) * u) + C m b = 0)
    (hd : d = 1 - (1 + m) * u - b)
    (ht₃ : d * t₃ = -u) :
    A m * d * (t₃ - t₁ - t₂) =
      b * H m b - A m * (t₁ * t₂) * (1 + m) - A m * b * u := by
  have hBC := BC_factor m b
  rw [hd] at ht₃ ⊢
  linear_combination
    A m * ht₃ + (b - 1) * hsum + (1 + m) * hpair + hBC

private def OrdGood (N : ℤ) (a : L) : Prop := a = 0 ∨ N ≤ ordPi a

private theorem OrdGood.neg {N : ℤ} {a : L} (ha : OrdGood N a) : OrdGood N (-a) := by
  rcases ha with rfl | ha
  · left; simp
  · right; rwa [ordPi_neg]

private theorem OrdGood.add {N : ℤ} {a b : L}
    (ha : OrdGood N a) (hb : OrdGood N b) : OrdGood N (a + b) := by
  by_cases hab : a + b = 0
  · exact Or.inl hab
  right
  rcases ha with ha | ha
  · subst a
    simpa using hb.resolve_left (by intro h; apply hab; simp [h])
  rcases hb with hb | hb
  · subst b
    simpa using ha
  by_cases ha0 : a = 0
  · simp only [ha0, zero_add] at hab ⊢
    exact hb
  by_cases hb0 : b = 0
  · simp only [hb0, add_zero] at hab ⊢
    exact ha
  exact le_trans (le_min ha hb) (ordPi_add_ge ha0 hb0 hab)

private theorem OrdGood.sub {N : ℤ} {a b : L}
    (ha : OrdGood N a) (hb : OrdGood N b) : OrdGood N (a - b) := by
  rw [sub_eq_add_neg]
  exact ha.add hb.neg

private theorem OrdGood.mul {M N : ℤ} {a b : L}
    (ha : OrdGood M a) (hb : OrdGood N b) : OrdGood (M + N) (a * b) := by
  rcases ha with rfl | ha
  · left; simp
  rcases hb with rfl | hb
  · left; simp
  by_cases ha0 : a = 0
  · left; simp [ha0]
  by_cases hb0 : b = 0
  · left; simp [hb0]
  right
  rw [ordPi_mul ha0 hb0]
  omega

private theorem OrdGood.mono {M N : ℤ} {a : L}
    (hMN : M ≤ N) (ha : OrdGood N a) : OrdGood M a := by
  rcases ha with rfl | ha
  · left; rfl
  · right; omega

private theorem OrdGood.int_mul (c : ℤ) {N : ℤ} {a : L}
    (ha : OrdGood N a) : OrdGood N ((c : L) * a) := by
  by_cases hc : (c : L) = 0
  · left; simp [hc]
  rcases ha with rfl | ha
  · left; simp
  by_cases ha0 : a = 0
  · left; simp [ha0]
  right
  rw [ordPi_mul hc ha0]
  have hcval := zero_le_ordPi_intCast c
  omega

private theorem OrdGood.div_unit {N : ℤ} {a b : L}
    (ha : OrdGood N a) (hb0 : b ≠ 0) (hbv : ordPi b = 0) : OrdGood N (a / b) := by
  rcases ha with rfl | ha
  · left; simp
  by_cases ha0 : a = 0
  · left; simp [ha0]
  right
  rw [ordPi_div ha0 hb0, hbv]
  omega

private theorem OrdGood.unit_one_add {q : L} (hq : OrdGood 1 q) :
    1 + q ≠ 0 ∧ ordPi (1 + q) = 0 := by
  rcases hq with rfl | hq
  · simp [ordPi_one]
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hq
    omega
  constructor
  · intro h
    have : q = -1 := by linear_combination h
    rw [this, ordPi_neg, ordPi_one] at hq
    omega
  · simpa only [ordPi_one] using
      ordPi_add_eq_of_lt one_ne_zero hq0 (by rw [ordPi_one]; omega)

private theorem chartG_eq_zero {x y : L} (hy0 : y ≠ 0)
    (heq : y ^ 2 + E0.a₁ * x * y + E0.a₃ * y =
      x ^ 3 + E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆) :
    G (-x / y) (-1 / y) = 0 := by
  simp only [G, E0] at heq ⊢
  field_simp [hy0]
  linear_combination -heq

private theorem secant_vieta_aux (m b t₁ t₂ : L)
    (h₁ : G t₁ (m * t₁ + b) = 0)
    (h₂ : G t₂ (m * t₂ + b) = 0)
    (ht : t₁ ≠ t₂) (hA : A m ≠ 0) :
    let u' := -B m b / A m - t₁ - t₂
    A m * (t₁ + t₂ + u') + B m b = 0 ∧
    A m * (t₁ * t₂ + (t₁ + t₂) * u') + C m b = 0 ∧
    A m * t₁ * t₂ * u' = D b := by
  let u' := -B m b / A m - t₁ - t₂
  have hp₁ := h₁
  have hp₂ := h₂
  rw [G_line] at hp₁ hp₂
  have hsum : A m * (t₁ + t₂ + u') + B m b = 0 := by
    dsimp [u']
    field_simp [hA]
    ring
  have hdiff :
      -A m * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) - B m b * (t₁ + t₂) + C m b = 0 := by
    have hmul : (t₁ - t₂) *
        (-A m * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
          B m b * (t₁ + t₂) + C m b) = 0 := by
      linear_combination hp₁ - hp₂
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ht)
  have hpair : A m * (t₁ * t₂ + (t₁ + t₂) * u') + C m b = 0 := by
    linear_combination hdiff + (t₁ + t₂) * hsum
  have hprod : A m * t₁ * t₂ * u' = D b := by
    linear_combination -hp₁ - t₁ ^ 2 * hsum + t₁ * hpair
  exact ⟨hsum, hpair, hprod⟩

private theorem vieta_x_sum_aux (m b t₁ t₂ u : L)
    (hA : A m ≠ 0) (hb : b ≠ 0)
    (hsum : A m * (t₁ + t₂ + u) + B m b = 0)
    (hpair : A m * (t₁ * t₂ + (t₁ + t₂) * u) + C m b = 0)
    (hprod : A m * t₁ * t₂ * u = D b) :
    let q := (m * t₁ + b) * (m * t₂ + b) * (m * u + b)
    q ≠ 0 ∧
    t₁ / (m * t₁ + b) + t₂ / (m * t₂ + b) + u / (m * u + b) =
      (m / b) ^ 2 + m / b + 1 := by
  let q := (m * t₁ + b) * (m * t₂ + b) * (m * u + b)
  let n := t₁ * (m * t₂ + b) * (m * u + b) +
    t₂ * (m * t₁ + b) * (m * u + b) +
    u * (m * t₁ + b) * (m * t₂ + b)
  have hcoeffQ :
      m ^ 3 * D b - m ^ 2 * b * C m b - m * b ^ 2 * B m b + b ^ 3 * A m - b ^ 3 = 0 := by
    simp only [A, B, C, D]
    ring
  have hprod0 : A m * t₁ * t₂ * u - D b = 0 := sub_eq_zero.mpr hprod
  have hQ : A m * q = b ^ 3 := by
    dsimp [q]
    linear_combination m ^ 3 * hprod0 + m ^ 2 * b * hpair +
      m * b ^ 2 * hsum + hcoeffQ
  have hcoeffN :
      3 * m ^ 2 * D b - 2 * m * b * C m b - b ^ 2 * B m b -
        b * (b ^ 2 + b * m + m ^ 2) = 0 := by
    simp only [B, C, D]
    ring
  have hN : A m * n = b * (b ^ 2 + b * m + m ^ 2) := by
    dsimp [n]
    linear_combination 3 * m ^ 2 * hprod0 + 2 * m * b * hpair +
      b ^ 2 * hsum + hcoeffN
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ
    exact (pow_ne_zero 3 hb) hQ.symm
  have h₁0 : m * t₁ + b ≠ 0 := by
    intro h
    apply hq0
    simp [q, h]
  have h₂0 : m * t₂ + b ≠ 0 := by
    intro h
    apply hq0
    simp [q, h]
  have hu0 : m * u + b ≠ 0 := by
    intro h
    apply hq0
    simp [q, h]
  have h₁0' : t₁ * m + b ≠ 0 := by simpa only [mul_comm] using h₁0
  have h₂0' : t₂ * m + b ≠ 0 := by simpa only [mul_comm] using h₂0
  have hu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hu0
  have hcleared :
      b ^ 2 * n = (b ^ 2 + b * m + m ^ 2) * q := by
    apply mul_left_cancel₀ hA
    linear_combination b ^ 2 * hN - (b ^ 2 + b * m + m ^ 2) * hQ
  refine ⟨hq0, ?_⟩
  have hleft :
      t₁ / (m * t₁ + b) + t₂ / (m * t₂ + b) + u / (m * u + b) = n / q := by
    field_simp [hq0, h₁0, h₂0, hu0, h₁0', h₂0', hu0']
    simp only [n, q]
    ring
  rw [hleft]
  field_simp [hq0, hb]
  linear_combination hcleared

/-! ## Inverse branch of add_congr (P+Q=O, Q=-P)

For P=(x,y) finite with v(zP)=r≥1 and Q=-P:
  error = 0 - zP - z(-P) = x(x+1)/(y(y+x+1))
  v(error) = v(x)+v(x+1)-v(y)-v(y+x+1) = (-2r)+(-2r)-(-3r)-(-3r) = 2r = r+r.
So the right disjunct holds with equality. -/

theorem add_congr_inverse_branch {x y : L}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular E0 x y)
    (hxneg : ordPi x < 0) :
    let P := WeierstrassCurve.Affine.Point.some x y hns
    zParam (P + (-P)) - zParam P - zParam (-P) = 0 ∨
    v (zParam P) + v (zParam (-P)) ≤
      v (zParam (P + (-P)) - zParam P - zParam (-P)) := by
  let P : E0Point := WeierstrassCurve.Affine.Point.some x y hns
  let r : ℤ := ordPi (-x / y)
  have hPneg : P + (-P) = 0 := add_neg_cancel P
  have heq :
      y ^ 2 + E0.a₁ * x * y + E0.a₃ * y =
        x ^ 3 + E0.a₂ * x ^ 2 + E0.a₄ * x + E0.a₆ :=
    (WeierstrassCurve.Affine.equation_iff x y).mp hns.1
  have hcoords := val_coords hx0 hy0 heq hxneg
  have hxv : ordPi x = -2 * r := hcoords.1
  have hyv : ordPi y = -3 * r := hcoords.2
  have hx1v : ordPi (x + 1) = -2 * r := by
    rw [ordPi_add_eq_of_lt hx0 one_ne_zero]
    · exact hxv
    · rw [hxv, ordPi_one]
      omega
  have hx1ne : x + 1 ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hx1v
    omega
  have hdenv : ordPi (y + x + 1) = -3 * r := by
    rw [show y + x + 1 = y + (x + 1) by ring,
      ordPi_add_eq_of_lt hy0 hx1ne]
    · exact hyv
    · rw [hyv, hx1v]
      omega
  have hden : y + x + 1 ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hdenv
    omega
  have hzneg : zParam (-P) = x / (y + x + 1) := by
    change -x / WeierstrassCurve.Affine.negY E0 x y = x / (y + x + 1)
    rw [show WeierstrassCurve.Affine.negY E0 x y = -(y + x + 1) by
      simp only [WeierstrassCurve.Affine.negY, E0]
      ring]
    field_simp [hden]
  have herr :
      (0 : L) - (-x / y) - x / (y + x + 1) =
        x * (x + 1) / (y * (y + x + 1)) := by
    field_simp [hy0, hden]
    ring
  have herrv :
      ordPi (x * (x + 1) / (y * (y + x + 1))) = 2 * r := by
    rw [ordPi_div (mul_ne_zero hx0 hx1ne) (mul_ne_zero hy0 hden),
      ordPi_mul hx0 hx1ne, ordPi_mul hy0 hden, hxv, hx1v, hyv, hdenv]
    omega
  dsimp only
  right
  rw [show WeierstrassCurve.Affine.Point.some x y hns +
        -WeierstrassCurve.Affine.Point.some x y hns = 0 from hPneg,
    zParam_zero, hzneg]
  change ordPi (-x / y) + ordPi (x / (y + x + 1)) ≤
    ordPi ((0 : L) - (-x / y) - x / (y + x + 1))
  rw [herr, herrv]
  change r + ordPi (x / (y + x + 1)) ≤ 2 * r
  rw [ordPi_div hx0 hden, hxv, hdenv]
  omega

theorem add_congr_distinct_x_branch {x₁ y₁ x₂ y₂ : L}
    (hx₁0 : x₁ ≠ 0) (hy₁0 : y₁ ≠ 0) (hx₂0 : x₂ ≠ 0) (hy₂0 : y₂ ≠ 0)
    (hns₁ : WeierstrassCurve.Affine.Nonsingular E0 x₁ y₁)
    (hns₂ : WeierstrassCurve.Affine.Nonsingular E0 x₂ y₂)
    (hxne : x₁ ≠ x₂)
    (hx₁neg : ordPi x₁ < 0)
    (hx₂neg : ordPi x₂ < 0) :
    let P := WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁
    let Q := WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂
    zParam (P + Q) - zParam P - zParam Q = 0 ∨
    v (zParam P) + v (zParam Q) ≤ v (zParam (P + Q) - zParam P - zParam Q) := by
  let P : E0Point := WeierstrassCurve.Affine.Point.some x₁ y₁ hns₁
  let Q : E0Point := WeierstrassCurve.Affine.Point.some x₂ y₂ hns₂
  change zParam (P + Q) - zParam P - zParam Q = 0 ∨
    ordPi (zParam P) + ordPi (zParam Q) ≤
      ordPi (zParam (P + Q) - zParam P - zParam Q)
  let t₁ : L := -x₁ / y₁
  let w₁ : L := -1 / y₁
  let t₂ : L := -x₂ / y₂
  let w₂ : L := -1 / y₂
  let r₁ : ℤ := ordPi t₁
  let r₂ : ℤ := ordPi t₂
  let r : ℤ := min r₁ r₂
  have heq₁ := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp hns₁.1
  have heq₂ := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp hns₂.1
  have hcoords₁ := val_coords hx₁0 hy₁0 heq₁ hx₁neg
  have hcoords₂ := val_coords hx₂0 hy₂0 heq₂ hx₂neg
  have hx₁v : ordPi x₁ = -2 * r₁ := hcoords₁.1
  have hy₁v : ordPi y₁ = -3 * r₁ := hcoords₁.2
  have hx₂v : ordPi x₂ = -2 * r₂ := hcoords₂.1
  have hy₂v : ordPi y₂ = -3 * r₂ := hcoords₂.2
  have hr₁ : 1 ≤ r₁ := by omega
  have hr₂ : 1 ≤ r₂ := by omega
  have hr : 1 ≤ r := by simp only [r, le_min_iff]; exact ⟨hr₁, hr₂⟩
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := min_le_right _ _
  have ht₁0 : t₁ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₁0) hy₁0
  have ht₂0 : t₂ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₂0) hy₂0
  have hw₁0 : w₁ ≠ 0 := div_ne_zero (by norm_num) hy₁0
  have hw₂0 : w₂ ≠ 0 := div_ne_zero (by norm_num) hy₂0
  have ht₁v : ordPi t₁ = r₁ := rfl
  have ht₂v : ordPi t₂ = r₂ := rfl
  have hw₁v : ordPi w₁ = 3 * r₁ := by
    dsimp [w₁]
    rw [ordPi_div (by norm_num) hy₁0, ordPi_neg, ordPi_one, hy₁v]
    omega
  have hw₂v : ordPi w₂ = 3 * r₂ := by
    dsimp [w₂]
    rw [ordPi_div (by norm_num) hy₂0, ordPi_neg, ordPi_one, hy₂v]
    omega
  have ht₁r : OrdGood r t₁ := Or.inr (by rw [ht₁v]; exact hrr₁)
  have ht₂r : OrdGood r t₂ := Or.inr (by rw [ht₂v]; exact hrr₂)
  have hw₁r : OrdGood (3 * r) w₁ := Or.inr (by rw [hw₁v]; omega)
  have hw₂r : OrdGood (3 * r) w₂ := Or.inr (by rw [hw₂v]; omega)
  have hG₁ : G t₁ w₁ = 0 := chartG_eq_zero hy₁0 heq₁
  have hG₂ : G t₂ w₂ = 0 := chartG_eq_zero hy₂0 heq₂
  let SU : L := 1 - t₂ + t₂ ^ 2 - (w₁ + w₂) +
    5 * t₂ * (w₁ + w₂) - 5 * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
  let SN : L := w₁ - (t₁ + t₂) * w₁ - 5 * w₁ ^ 2 +
    (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)
  have hcross : (w₁ - w₂) * SU = (t₁ - t₂) * SN := by
    dsimp [SU, SN]
    simp only [G] at hG₁ hG₂
    linear_combination hG₁ - hG₂
  have ht₂1 : OrdGood 1 t₂ := ht₂r.mono (by omega)
  have hw₁1 : OrdGood 1 w₁ := hw₁r.mono (by omega)
  have hw₂1 : OrdGood 1 w₂ := hw₂r.mono (by omega)
  have hwsum1 : OrdGood 1 (w₁ + w₂) := hw₁1.add hw₂1
  have ht₂sq1 : OrdGood 1 (t₂ ^ 2) := by
    rw [pow_two]
    exact (ht₂1.mul ht₂1).mono (by omega)
  have htw1 : OrdGood 1 (5 * t₂ * (w₁ + w₂)) := by
    have h := ht₂1.mul hwsum1
    simpa only [Int.cast_ofNat, mul_assoc] using (h.int_mul 5).mono (by omega)
  have hww1 : OrdGood 1 (5 * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) := by
    have h₁ : OrdGood 1 (w₁ ^ 2) := by
      rw [pow_two]
      exact (hw₁1.mul hw₁1).mono (by omega)
    have h₂ : OrdGood 1 (w₁ * w₂) := (hw₁1.mul hw₂1).mono (by omega)
    have h₃ : OrdGood 1 (w₂ ^ 2) := by
      rw [pow_two]
      exact (hw₂1.mul hw₂1).mono (by omega)
    exact (h₁.add h₂ |>.add h₃).int_mul 5
  let qSU : L := -t₂ + t₂ ^ 2 - (w₁ + w₂) +
    5 * t₂ * (w₁ + w₂) - 5 * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
  have hqSU : OrdGood 1 qSU := by
    dsimp [qSU]
    exact ((ht₂1.neg.add ht₂sq1).sub hwsum1 |>.add htw1).sub hww1
  have hSUeq : SU = 1 + qSU := by simp only [SU, qSU]; ring
  have hSUunit : SU ≠ 0 ∧ ordPi SU = 0 := by
    rw [hSUeq]
    exact hqSU.unit_one_add
  have htne : t₁ ≠ t₂ := by
    intro ht
    have hwdiff : w₁ - w₂ = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hSUunit.1
      rw [hcross, ht, sub_self, zero_mul]
    have hw : w₁ = w₂ := sub_eq_zero.mp hwdiff
    apply hxne
    have hx₁tw : x₁ = t₁ / w₁ := by
      dsimp [t₁, w₁]
      field_simp [hy₁0]
    have hx₂tw : x₂ = t₂ / w₂ := by
      dsimp [t₂, w₂]
      field_simp [hy₂0]
    rw [hx₁tw, hx₂tw, ht, hw]
  let m : L := (w₁ - w₂) / (t₁ - t₂)
  let b : L := w₁ - m * t₁
  have hm₁ : w₁ = m * t₁ + b := by dsimp [b]; ring
  have hm₂ : w₂ = m * t₂ + b := by
    dsimp [m, b]
    field_simp [sub_ne_zero.mpr htne]
    ring
  have hmEq : SU * m = SN := by
    dsimp [m]
    field_simp [sub_ne_zero.mpr htne]
    linear_combination hcross
  have hsumr : OrdGood r (t₁ + t₂) := ht₁r.add ht₂r
  have hSN : OrdGood (2 * r) SN := by
    have h₁ : OrdGood (2 * r) w₁ := hw₁r.mono (by omega)
    have h₂ : OrdGood (2 * r) ((t₁ + t₂) * w₁) :=
      (hsumr.mul hw₁r).mono (by omega)
    have h₃ : OrdGood (2 * r) (5 * w₁ ^ 2) := by
      rw [pow_two]
      exact ((hw₁r.mul hw₁r).int_mul 5).mono (by omega)
    have h₄ : OrdGood (2 * r) (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) := by
      have h11 : OrdGood (2 * r) (t₁ ^ 2) := by
        rw [pow_two]
        simpa only [two_mul] using ht₁r.mul ht₁r
      have h12 : OrdGood (2 * r) (t₁ * t₂) := by
        simpa only [two_mul] using ht₁r.mul ht₂r
      have h22 : OrdGood (2 * r) (t₂ ^ 2) := by
        rw [pow_two]
        simpa only [two_mul] using ht₂r.mul ht₂r
      exact (h11.add h12).add h22
    dsimp [SN]
    exact ((h₁.sub h₂).sub h₃).add h₄
  have hmGood : OrdGood (2 * r) m := by
    rcases hSN with hSN | hSN
    · left
      apply (mul_eq_zero.mp ?_).resolve_left hSUunit.1
      rw [hmEq, hSN]
    · have hSN0 : SN ≠ 0 := by
        intro h
        rw [h, ordPi_zero] at hSN
        omega
      have hm0 : m ≠ 0 := by
        intro h
        rw [h, mul_zero] at hmEq
        exact hSN0 hmEq.symm
      right
      have hv := congrArg ordPi hmEq
      rw [ordPi_mul hSUunit.1 hm0, hSUunit.2] at hv
      omega
  have hbGood : OrdGood (3 * r) b := by
    have hmt : OrdGood (3 * r) (m * t₁) :=
      (hmGood.mul ht₁r).mono (by omega)
    dsimp [b]
    exact hw₁r.sub hmt
  have hb0 : b ≠ 0 := by
    intro hb
    have hm0 : m ≠ 0 := by
      intro hm
      rw [hb, hm, zero_mul, add_zero] at hm₁
      exact hw₁0 hm₁
    apply hxne
    have hx₁tw : x₁ = t₁ / w₁ := by
      dsimp [t₁, w₁]
      field_simp [hy₁0]
    have hx₂tw : x₂ = t₂ / w₂ := by
      dsimp [t₂, w₂]
      field_simp [hy₂0]
    rw [hx₁tw, hx₂tw, hm₁, hm₂, hb]
    field_simp [hm0, ht₁0, ht₂0]
    ring
  have hm1 : OrdGood 1 m := hmGood.mono (by omega)
  have hmSq1 : OrdGood 1 (m ^ 2) := by
    rw [pow_two]
    exact (hm1.mul hm1).mono (by omega)
  have hmCube1 : OrdGood 1 (m ^ 3) := by
    rw [show m ^ 3 = m ^ 2 * m by ring]
    exact (hmSq1.mul hm1).mono (by omega)
  let qA : L := -m - 5 * m ^ 2 + 5 * m ^ 3
  have hqA : OrdGood 1 qA := by
    dsimp [qA]
    exact (hm1.neg.sub (hmSq1.int_mul 5)).add (hmCube1.int_mul 5)
  have hAeq : A m = 1 + qA := by simp only [A, qA]; ring
  have hAunit : A m ≠ 0 ∧ ordPi (A m) = 0 := by
    rw [hAeq]
    exact hqA.unit_one_add
  have hOneMunit : 1 + m ≠ 0 ∧ ordPi (1 + m) = 0 := hm1.unit_one_add
  have hb1 : OrdGood 1 b := hbGood.mono (by omega)
  have hbSq1 : OrdGood 1 (b ^ 2) := by
    rw [pow_two]
    exact (hb1.mul hb1).mono (by omega)
  let e : L := 1 - b - 5 * b ^ 2
  let qe : L := -b - 5 * b ^ 2
  have hqe : OrdGood 1 qe := by
    dsimp [qe]
    exact hb1.neg.sub (hbSq1.int_mul 5)
  have heeq : e = 1 + qe := by simp only [e, qe]; ring
  have heunit : e ≠ 0 ∧ ordPi e = 0 := by
    rw [heeq]
    exact hqe.unit_one_add
  have hlineG₁ : G t₁ (m * t₁ + b) = 0 := by rw [← hm₁]; exact hG₁
  have hlineG₂ : G t₂ (m * t₂ + b) = 0 := by rw [← hm₂]; exact hG₂
  let u : L := -B m b / A m - t₁ - t₂
  have hvieta := secant_vieta_aux m b t₁ t₂ hlineG₁ hlineG₂ htne hAunit.1
  change A m * (t₁ + t₂ + u) + B m b = 0 ∧
    A m * (t₁ * t₂ + (t₁ + t₂) * u) + C m b = 0 ∧
    A m * t₁ * t₂ * u = D b at hvieta
  rcases hvieta with ⟨hsum, hpair, hprod⟩
  have hprod' : A m * t₁ * t₂ * u = b * e := by
    rw [hprod]
    simp only [D, e]
    ring
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu, mul_zero] at hprod'
    exact (mul_ne_zero hb0 heunit.1) hprod'.symm
  have hb2r : OrdGood (2 * r) b := hbGood.mono (by omega)
  have hmSq2r : OrdGood (2 * r) (m ^ 2) := by
    rw [pow_two]
    exact (hmGood.mul hmGood).mono (by omega)
  have hmb2r : OrdGood (2 * r) (m * b) := (hmGood.mul hbGood).mono (by omega)
  have hmSqb2r : OrdGood (2 * r) (m ^ 2 * b) :=
    (hmSq2r.mul hbGood).mono (by omega)
  have hBGood : OrdGood (2 * r) (B m b) := by
    simp only [B]
    simpa only [Int.cast_ofNat, mul_assoc] using
      (((hmGood.sub hb2r).add hmSq2r).sub (hmb2r.int_mul 10)).add
        (hmSqb2r.int_mul 15)
  have huGood : OrdGood r u := by
    dsimp [u]
    have hquot : OrdGood (2 * r) (-B m b / A m) :=
      hBGood.neg.div_unit hAunit.1 hAunit.2
    exact ((hquot.mono (by omega)).sub ht₁r).sub ht₂r
  have huv : r ≤ ordPi u := huGood.resolve_left hu0
  have hbStrong : ordPi b = r₁ + r₂ + ordPi u := by
    have hv := congrArg ordPi hprod'
    rw [ordPi_mul (mul_ne_zero (mul_ne_zero hAunit.1 ht₁0) ht₂0) hu0,
      ordPi_mul (mul_ne_zero hAunit.1 ht₁0) ht₂0,
      ordPi_mul hAunit.1 ht₁0, hAunit.2, ht₁v, ht₂v,
      ordPi_mul hb0 heunit.1, heunit.2] at hv
    omega
  let qd : L := -(1 + m) * u - b
  have hqd : OrdGood 1 qd := by
    have hOneM : OrdGood 0 (1 + m) := Or.inr (by rw [hOneMunit.2])
    have hterm : OrdGood r ((1 + m) * u) := by
      simpa only [zero_add] using hOneM.mul (Or.inr huv)
    dsimp [qd]
    simpa only [neg_mul] using (hterm.neg.mono (by omega)).sub hb1
  let d : L := 1 - (1 + m) * u - b
  have hdeq : d = 1 + qd := by simp only [d, qd]; ring
  have hdunit : d ≠ 0 ∧ ordPi d = 0 := by
    rw [hdeq]
    exact hqd.unit_one_add
  let t₃ : L := -u / d
  have hdt₃ : d * t₃ = -u := by
    dsimp [t₃]
    field_simp [hdunit.1]
  have hxsumData := vieta_x_sum_aux m b t₁ t₂ u hAunit.1 hb0 hsum hpair hprod
  dsimp only at hxsumData
  rcases hxsumData with ⟨hqprod, hxsum⟩
  have hmu0 : m * u + b ≠ 0 := by
    intro h
    apply hqprod
    simp [h]
  have hmt₁0 : m * t₁ + b ≠ 0 := by simpa only [← hm₁] using hw₁0
  have hmt₂0 : m * t₂ + b ≠ 0 := by simpa only [← hm₂] using hw₂0
  have hx₁chart : x₁ = t₁ / (m * t₁ + b) := by
    rw [← hm₁]
    dsimp [t₁, w₁]
    field_simp [hy₁0]
  have hx₂chart : x₂ = t₂ / (m * t₂ + b) := by
    rw [← hm₂]
    dsimp [t₂, w₂]
    field_simp [hy₂0]
  have hy₁chart : y₁ = -1 / (m * t₁ + b) := by
    rw [← hm₁]
    dsimp [w₁]
    field_simp [hy₁0]
  have hy₂chart : y₂ = -1 / (m * t₂ + b) := by
    rw [← hm₂]
    dsimp [w₂]
    field_simp [hy₂0]
  let ell : L := WeierstrassCurve.Affine.slope E0 x₁ x₂ y₁ y₂
  have hell : ell = m / b := by
    dsimp only [ell]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxne]
    rw [hx₁chart, hx₂chart, hy₁chart, hy₂chart]
    have hxdiff : t₁ / (m * t₁ + b) - t₂ / (m * t₂ + b) ≠ 0 := by
      simpa only [← hx₁chart, ← hx₂chart] using sub_ne_zero.mpr hxne
    have hbdiff : -(b * t₂) + b * t₁ ≠ 0 := by
      rw [show -(b * t₂) + b * t₁ = b * (t₁ - t₂) by ring]
      exact mul_ne_zero hb0 (sub_ne_zero.mpr htne)
    field_simp [hmt₁0, hmt₂0, hxdiff, hb0, hbdiff]
    calc
      b * (-(m * t₂ + b) - -(m * t₁ + b)) /
          (t₁ * (m * t₂ + b) - (m * t₁ + b) * t₂) =
          m * (-(b * t₂) + b * t₁) / (-(b * t₂) + b * t₁) := by
            congr 1 <;> ring
      _ = m := by
        have htdiff : -t₂ + t₁ ≠ 0 := by
          simpa only [neg_add_eq_sub, sub_ne_zero] using htne
        field_simp [htdiff]
  let x₃ : L := WeierstrassCurve.Affine.addX E0 x₁ x₂ ell
  have hx₃ : x₃ = u / (m * u + b) := by
    change ell ^ 2 + E0.a₁ * ell - E0.a₂ - x₁ - x₂ = u / (m * u + b)
    rw [hell, hx₁chart, hx₂chart]
    have ha1 : E0.a₁ = (1 : L) := by norm_num [E0]
    have ha2 : E0.a₂ = (-1 : L) := by norm_num [E0]
    rw [ha1, ha2]
    rw [one_mul, sub_neg_eq_add]
    rw [← hxsum]
    abel
  let ybar : L := WeierstrassCurve.Affine.negAddY E0 x₁ x₂ y₁ ell
  have hybar : ybar = -1 / (m * u + b) := by
    change ell * (x₃ - x₁) + y₁ = -1 / (m * u + b)
    rw [hx₃, hell, hx₁chart, hy₁chart]
    field_simp [hb0, hmt₁0, hmu0]
    ring
  let y₃ : L := WeierstrassCurve.Affine.addY E0 x₁ x₂ y₁ ell
  have hy₃ : y₃ = d / (m * u + b) := by
    change WeierstrassCurve.Affine.negY E0 x₃ ybar = d / (m * u + b)
    rw [hybar, hx₃]
    simp only [WeierstrassCurve.Affine.negY, E0]
    dsimp [d]
    field_simp [hmu0]
    ring
  have hbridge : zParam (P + Q) = t₃ := by
    dsimp [P, Q]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
    change -WeierstrassCurve.Affine.addX E0 x₁ x₂
        (WeierstrassCurve.Affine.slope E0 x₁ x₂ y₁ y₂) /
      WeierstrassCurve.Affine.addY E0 x₁ x₂ y₁
        (WeierstrassCurve.Affine.slope E0 x₁ x₂ y₁ y₂) = t₃
    change -x₃ / y₃ = t₃
    rw [hx₃, hy₃]
    dsimp [t₃]
    have hmu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hmu0
    field_simp [hmu0, hmu0', hdunit.1]
  have hHGood : OrdGood (2 * r) (H m b) := by
    have h₁' := hmGood.int_mul (-8)
    have h₁ : OrdGood (2 * r) (-8 * m) := by
      convert h₁' using 1
      norm_num
    have h₂ : OrdGood (2 * r) (16 * m ^ 2) := hmSq2r.int_mul 16
    have h₃' := hb2r.int_mul (-4)
    have h₃ : OrdGood (2 * r) (-(4 * b)) := by
      convert h₃' using 1
      norm_num
    have h₄ : OrdGood (2 * r) (20 * m * b) := by
      simpa only [Int.cast_ofNat, mul_assoc] using (hmb2r.int_mul 20)
    simp only [H]
    simpa only [sub_eq_add_neg] using ((h₁.add h₂).add h₃).add h₄
  have hbVeryGood : OrdGood (r₁ + r₂ + r) b := Or.inr (by rw [hbStrong]; omega)
  have hBH : OrdGood (r₁ + r₂) (b * H m b) :=
    (hbVeryGood.mul hHGood).mono (by omega)
  have hA0 : OrdGood 0 (A m) := Or.inr (by rw [hAunit.2])
  have hOneM0 : OrdGood 0 (1 + m) := Or.inr (by rw [hOneMunit.2])
  have ht₁exact : OrdGood r₁ t₁ := Or.inr (by rw [ht₁v])
  have ht₂exact : OrdGood r₂ t₂ := Or.inr (by rw [ht₂v])
  have hAt₁t₂ : OrdGood (r₁ + r₂) (A m * (t₁ * t₂) * (1 + m)) := by
    have h := hA0.mul (ht₁exact.mul ht₂exact) |>.mul hOneM0
    simpa only [zero_add, add_zero, add_assoc] using h
  have hAbu : OrdGood (r₁ + r₂) (A m * b * u) := by
    have h := hA0.mul hbVeryGood |>.mul (Or.inr huv)
    exact h.mono (by omega)
  let err : L := t₃ - t₁ - t₂
  have hid := identity8 m b t₁ t₂ u t₃ d hsum hpair rfl hdt₃
  change A m * d * err =
    b * H m b - A m * (t₁ * t₂) * (1 + m) - A m * b * u at hid
  have hRHS : OrdGood (r₁ + r₂)
      (b * H m b - A m * (t₁ * t₂) * (1 + m) - A m * b * u) :=
    (hBH.sub hAt₁t₂).sub hAbu
  have herr : err = 0 ∨ r₁ + r₂ ≤ ordPi err := by
    by_cases herr0 : err = 0
    · exact Or.inl herr0
    right
    have hlhs0 : A m * d * err ≠ 0 := mul_ne_zero (mul_ne_zero hAunit.1 hdunit.1) herr0
    have hrhs0 : b * H m b - A m * (t₁ * t₂) * (1 + m) - A m * b * u ≠ 0 := by
      intro h
      rw [h] at hid
      exact hlhs0 hid
    have hrhs := hRHS.resolve_left hrhs0
    have hv := congrArg ordPi hid
    rw [ordPi_mul (mul_ne_zero hAunit.1 hdunit.1) herr0,
      ordPi_mul hAunit.1 hdunit.1, hAunit.2, hdunit.2] at hv
    omega
  rw [hbridge]
  change err = 0 ∨ r₁ + r₂ ≤ ordPi err
  exact herr

/-! ## Exact valuation lemmas for the counterexample -/

private theorem add_ne_zero_of_ordPi_ne {x y : L}
    (hxy : ordPi x ≠ ordPi y) : x + y ≠ 0 := by
  intro h
  have hy : y = -x := by linear_combination h
  apply hxy
  rw [hy, ordPi_neg]

private theorem pi_ne_zero : pi ≠ 0 := by
  intro h
  have hv := ordPi_pi
  rw [h, ordPi_zero] at hv
  omega

private theorem ordPi_two : ordPi (2 : L) = 0 := by
  have hnegone : ordPi (-1 : L) = 0 := by rw [ordPi_neg, ordPi_one]
  calc
    ordPi (2 : L) = ordPi ((-1 : L) + 3) := by norm_num
    _ = ordPi (-1 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [hnegone, ordPi_three]; omega)
    _ = 0 := hnegone

private theorem ordPi_five : ordPi (5 : L) = 0 := by
  calc
    ordPi (5 : L) = ordPi ((2 : L) + 3) := by norm_num
    _ = ordPi (2 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_two, ordPi_three]; omega)
    _ = 0 := ordPi_two

private theorem ordPi_nine : ordPi (9 : L) = 6 := by
  rw [show (9 : L) = 3 * 3 by norm_num, ordPi_mul (by norm_num) (by norm_num),
    ordPi_three]
  norm_num

private theorem ordPi_ten : ordPi (10 : L) = 0 := by
  calc
    ordPi (10 : L) = ordPi ((1 : L) + 9) := by norm_num
    _ = ordPi (1 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_one, ordPi_nine]; omega)
    _ = 0 := ordPi_one

private theorem ordPi_fifty : ordPi (50 : L) = 0 := by
  have h48 : 3 ≤ ordPi (48 : L) := by
    rw [show (48 : L) = 3 * 16 by norm_num, ordPi_mul (by norm_num) (by norm_num),
      ordPi_three]
    have : 0 ≤ ordPi (16 : L) := by
      simpa only [Int.cast_ofNat] using zero_le_ordPi_intCast 16
    omega
  calc
    ordPi (50 : L) = ordPi ((2 : L) + 48) := by norm_num
    _ = ordPi (2 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_two]; omega)
    _ = 0 := ordPi_two

private theorem ordPi_sixty_eight : ordPi (68 : L) = 0 := by
  have h66 : 3 ≤ ordPi (66 : L) := by
    rw [show (66 : L) = 3 * 22 by norm_num, ordPi_mul (by norm_num) (by norm_num),
      ordPi_three]
    have : 0 ≤ ordPi (22 : L) := by
      simpa only [Int.cast_ofNat] using zero_le_ordPi_intCast 22
    omega
  calc
    ordPi (68 : L) = ordPi ((2 : L) + 66) := by norm_num
    _ = ordPi (2 : L) :=
      ordPi_add_eq_of_lt (by norm_num) (by norm_num) (by rw [ordPi_two]; omega)
    _ = 0 := ordPi_two

private theorem ordPi_generator21_z : ordPi (zParam generator21) = 1 := by
  let qx : L := 9 + 5 * pi
  let ux : L := -10 + pi * qx
  let qy : L := 50 + 30 * pi
  have h5pi : ordPi (5 * pi) = 1 := by
    rw [ordPi_mul (by norm_num) pi_ne_zero, ordPi_five, ordPi_pi]
    norm_num
  have hqx : ordPi qx = 1 := by
    change ordPi (9 + 5 * pi) = 1
    rw [add_comm, ordPi_add_eq_of_lt (mul_ne_zero (by norm_num) pi_ne_zero) (by norm_num)]
    · exact h5pi
    · rw [h5pi, ordPi_nine]
      omega
  have hqx0 : qx ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hqx
    omega
  have hpqx : ordPi (pi * qx) = 2 := by
    rw [ordPi_mul pi_ne_zero hqx0, ordPi_pi, hqx]
    norm_num
  have hux : ordPi ux = 0 := by
    change ordPi ((-10 : L) + pi * qx) = 0
    rw [ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero pi_ne_zero hqx0)]
    · rw [ordPi_neg, ordPi_ten]
    · rw [ordPi_neg, ordPi_ten, hpqx]
      omega
  have hux0 : ux ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_neg, ordPi_ten, hpqx]
    omega
  have hxform : torsionX 0 = pi * ux := by
    change -6 * a ^ 2 + 2 * a + 19 = pi * (-10 + pi * (9 + 5 * pi))
    unfold a
    linear_combination -5 * pi_relation
  have hx0 : torsionX 0 ≠ 0 := by rw [hxform]; exact mul_ne_zero pi_ne_zero hux0
  have hxv : ordPi (torsionX 0) = 1 := by
    rw [hxform, ordPi_mul pi_ne_zero hux0, ordPi_pi, hux]
    norm_num
  have h30 : ordPi (30 : L) = 3 := by
    rw [show (30 : L) = 3 * 10 by norm_num, ordPi_mul (by norm_num) (by norm_num),
      ordPi_three, ordPi_ten]
    norm_num
  have h30pi : ordPi (30 * pi) = 4 := by
    rw [ordPi_mul (by norm_num) pi_ne_zero, h30, ordPi_pi]
    norm_num
  have hqy : ordPi qy = 0 := by
    change ordPi ((50 : L) + 30 * pi) = 0
    rw [ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero (by norm_num) pi_ne_zero)]
    · exact ordPi_fifty
    · rw [ordPi_fifty, h30pi]
      omega
  have hqy0 : qy ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_fifty, h30pi]
    omega
  have hpy : ordPi (pi * qy) = 1 := by
    rw [ordPi_mul pi_ne_zero hqy0, ordPi_pi, hqy]
    norm_num
  have hyform : torsionY 0 = -68 + pi * qy := by
    change 30 * a ^ 2 - 10 * a - 88 = -68 + pi * (50 + 30 * pi)
    unfold a
    ring
  have hy0 : torsionY 0 ≠ 0 := by
    rw [hyform]
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_neg, ordPi_sixty_eight, hpy]
    omega
  have hyv : ordPi (torsionY 0) = 0 := by
    rw [hyform, ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero pi_ne_zero hqy0)]
    · rw [ordPi_neg, ordPi_sixty_eight]
    · rw [ordPi_neg, ordPi_sixty_eight, hpy]
      omega
  change ordPi (-torsionX 0 / torsionY 0) = 1
  rw [ordPi_div (neg_ne_zero.mpr hx0) hy0, ordPi_neg, hxv, hyv]
  omega

private theorem ordPi_six_generator_z : ordPi (zParam (torsionAffine 5)) = 1 := by
  have h2pi : ordPi (2 * pi) = 1 := by
    rw [ordPi_mul (by norm_num) pi_ne_zero, ordPi_two, ordPi_pi]
    norm_num
  have hy0 : (1 : L) + 2 * pi ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_one, h2pi]
    omega
  have hyv : ordPi ((1 : L) + 2 * pi) = 0 := by
    rw [ordPi_add_eq_of_lt (by norm_num) (mul_ne_zero (by norm_num) pi_ne_zero)]
    · exact ordPi_one
    · rw [ordPi_one, h2pi]
      omega
  change ordPi (-(-a + 1) / (2 * a - 1)) = 1
  have hx : -a + 1 = -pi := by unfold a; ring
  have hy : 2 * a - 1 = 1 + 2 * pi := by unfold a; ring
  rw [hx, hy, neg_neg, ordPi_div pi_ne_zero hy0, ordPi_pi, hyv]
  omega

private theorem seven_generator_z : zParam (torsionAffine 6) = (1 / 2 : L) := by
  change -((1 : L)) / (-2) = 1 / 2
  norm_num

private theorem ordPi_seven_generator_z : ordPi (zParam (torsionAffine 6)) = 0 := by
  rw [seven_generator_z, ordPi_div (by norm_num) (by norm_num), ordPi_one, ordPi_two]
  omega

private theorem generator_add_six_generator :
    generator21 + torsionAffine 5 = torsionAffine 6 :=
  (add_comm generator21 (torsionAffine 5)).trans
    (add_generator_consecutive (4 : Fin 18))

private theorem ordPi_counterexample_error :
    ordPi (zParam (generator21 + torsionAffine 5) -
      zParam generator21 - zParam (torsionAffine 5)) = 0 := by
  rw [generator_add_six_generator]
  have hz7 : zParam (torsionAffine 6) ≠ 0 := by
    rw [seven_generator_z]
    norm_num
  have hz1 : zParam generator21 ≠ 0 := by
    intro h
    have hv := ordPi_generator21_z
    rw [h, ordPi_zero] at hv
    omega
  have hz6 : zParam (torsionAffine 5) ≠ 0 := by
    intro h
    have hv := ordPi_six_generator_z
    rw [h, ordPi_zero] at hv
    omega
  have hfirst0 :
      ordPi (zParam (torsionAffine 6) + -zParam generator21) = 0 := by
    rw [ordPi_add_eq_of_lt hz7 (neg_ne_zero.mpr hz1)]
    · exact ordPi_seven_generator_z
    · rw [ordPi_seven_generator_z, ordPi_neg, ordPi_generator21_z]
      omega
  have hfirstne : zParam (torsionAffine 6) + -zParam generator21 ≠ 0 := by
    apply add_ne_zero_of_ordPi_ne
    rw [ordPi_seven_generator_z, ordPi_neg, ordPi_generator21_z]
    omega
  rw [show zParam (torsionAffine 6) - zParam generator21 - zParam (torsionAffine 5) =
      (zParam (torsionAffine 6) + -zParam generator21) + -zParam (torsionAffine 5) by
        ring]
  rw [ordPi_add_eq_of_lt hfirstne (neg_ne_zero.mpr hz6) (by
    rw [hfirst0, ordPi_neg, ordPi_six_generator_z]
    omega), hfirst0]

/-- The requested signature is false on two entries of the existing explicit
order-21 point table. -/
theorem not_add_congr_signature :
    ¬ ∀ (P Q : E0Point),
      (1 ≤ v (zParam P)) → (1 ≤ v (zParam Q)) →
        v (zParam P) + v (zParam Q) ≤
          v (zParam (P + Q) - zParam P - zParam Q) := by
  intro h
  have hbad := h generator21 (torsionAffine 5)
    (by change 1 ≤ ordPi (zParam generator21); rw [ordPi_generator21_z])
    (by change 1 ≤ ordPi (zParam (torsionAffine 5)); rw [ordPi_six_generator_z])
  change ordPi (zParam generator21) + ordPi (zParam (torsionAffine 5)) ≤
    ordPi (zParam (generator21 + torsionAffine 5) -
      zParam generator21 - zParam (torsionAffine 5)) at hbad
  rw [ordPi_generator21_z, ordPi_six_generator_z, ordPi_counterexample_error] at hbad
  omega

end

end MazurProof.N18Block5Instantiation.AddCongrProof
