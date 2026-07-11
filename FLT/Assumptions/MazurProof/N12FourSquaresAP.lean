import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12E1CoverResiduals
import FLT.Assumptions.MazurProof.N12EulerAux

/-!
# Four-square arithmetic progression wrappers for the N=12 cover

This file isolates the elementary denominator-clearing layer between the
rational four-square AP residual used in the N=12 cover and an integer
four-square AP theorem.

The optional residual `FourSquaresAPToFermat42Bridge` is kept explicit because
it would imply the integer theorem via Mathlib's `not_fermat_42`, but the
current audited route treats primitive centered AP descent as the honest
mathematical frontier.
-/

namespace MazurProof.RationalPointsN12

/-- Four integer squares in arithmetic progression, written as equal first
differences. -/
def IntFourSqAP (a b c d : ℤ) : Prop :=
  b ^ 2 - a ^ 2 = c ^ 2 - b ^ 2 ∧ c ^ 2 - b ^ 2 = d ^ 2 - c ^ 2

/-- The four integer square terms are constant. -/
def FourSqAPConst (w x y z : ℤ) : Prop :=
  w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2

/-- The common gcd of the four square roots, measured by absolute values. -/
def rootGCD4 (a b c d : ℤ) : ℕ :=
  Nat.gcd a.natAbs (Nat.gcd b.natAbs (Nat.gcd c.natAbs d.natAbs))

/-- Centered primitive four-square AP with only a global root-gcd condition.
Pairwise coprimality and parity are derived in a later layer. -/
structure WeakPrimitiveCenteredFourSqAP where
  X : ℤ
  N : ℤ
  hNpos : 0 < N
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
  hp : p ^ 2 = X - 6 * N
  hq : q ^ 2 = X - 2 * N
  hr : r ^ 2 = X + 2 * N
  hs : s ^ 2 = X + 6 * N
  hroot : rootGCD4 p q r s = 1

/-- The root gcd divides the first root absolute value. -/
theorem rootGCD4_dvd_left (a b c d : ℤ) :
    rootGCD4 a b c d ∣ a.natAbs := by
  unfold rootGCD4
  exact Nat.gcd_dvd_left _ _

/-- The root gcd divides the second root absolute value. -/
theorem rootGCD4_dvd_second (a b c d : ℤ) :
    rootGCD4 a b c d ∣ b.natAbs := by
  unfold rootGCD4
  exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)

/-- The root gcd divides the third root absolute value. -/
theorem rootGCD4_dvd_third (a b c d : ℤ) :
    rootGCD4 a b c d ∣ c.natAbs := by
  unfold rootGCD4
  exact Nat.dvd_trans
    (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_dvd_left _ _)

/-- The root gcd divides the fourth root absolute value. -/
theorem rootGCD4_dvd_fourth (a b c d : ℤ) :
    rootGCD4 a b c d ∣ d.natAbs := by
  unfold rootGCD4
  exact Nat.dvd_trans
    (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_dvd_right _ _)

/-- Any natural number dividing all four root absolute values divides the
four-root gcd. -/
theorem dvd_rootGCD4 {k : ℕ} {a b c d : ℤ}
    (ha : k ∣ a.natAbs) (hb : k ∣ b.natAbs)
    (hc : k ∣ c.natAbs) (hd : k ∣ d.natAbs) :
    k ∣ rootGCD4 a b c d := by
  unfold rootGCD4
  exact Nat.dvd_gcd ha (Nat.dvd_gcd hb (Nat.dvd_gcd hc hd))

/-- Integer divisibility form for the first root. -/
theorem rootGCD4_intCast_dvd_left (a b c d : ℤ) :
    (rootGCD4 a b c d : ℤ) ∣ a := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_left a b c d

/-- Integer divisibility form for the second root. -/
theorem rootGCD4_intCast_dvd_second (a b c d : ℤ) :
    (rootGCD4 a b c d : ℤ) ∣ b := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_second a b c d

/-- Integer divisibility form for the third root. -/
theorem rootGCD4_intCast_dvd_third (a b c d : ℤ) :
    (rootGCD4 a b c d : ℤ) ∣ c := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_third a b c d

/-- Integer divisibility form for the fourth root. -/
theorem rootGCD4_intCast_dvd_fourth (a b c d : ℤ) :
    (rootGCD4 a b c d : ℤ) ∣ d := by
  rw [Int.natCast_dvd]
  exact rootGCD4_dvd_fourth a b c d

/-- A positive first square gap forces the root gcd to be positive. -/
theorem rootGCD4_pos_of_first_gap {w x y z Δ : ℤ}
    (hΔpos : 0 < Δ)
    (hxw : x ^ 2 - w ^ 2 = Δ) :
    0 < rootGCD4 w x y z := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hw0 : w = 0 := by
    rcases rootGCD4_intCast_dvd_left w x y z with ⟨k, hk⟩
    simpa [hzero] using hk
  have hx0 : x = 0 := by
    rcases rootGCD4_intCast_dvd_second w x y z with ⟨k, hk⟩
    simpa [hzero] using hk
  rw [hw0, hx0] at hxw
  norm_num at hxw
  nlinarith

/-- The square of the four-root gcd divides the first square gap. -/
theorem rootGCD4_sq_dvd_gap_xw (w x y z : ℤ) :
    ((rootGCD4 w x y z : ℤ) ^ 2) ∣ x ^ 2 - w ^ 2 := by
  rcases rootGCD4_intCast_dvd_second w x y z with ⟨qx, hx⟩
  rcases rootGCD4_intCast_dvd_left w x y z with ⟨qw, hw⟩
  refine ⟨qx ^ 2 - qw ^ 2, ?_⟩
  let G : ℤ := (rootGCD4 w x y z : ℤ)
  have hxG : x = G * qx := by
    simpa [G] using hx
  have hwG : w = G * qw := by
    simpa [G] using hw
  change x ^ 2 - w ^ 2 = G ^ 2 * (qx ^ 2 - qw ^ 2)
  rw [hxG, hwG]
  ring

/-- If the first square gap is named `Δ`, then the gcd square divides `Δ`. -/
theorem rootGCD4_sq_dvd_delta_of_first_gap {w x y z Δ : ℤ}
    (hxw : x ^ 2 - w ^ 2 = Δ) :
    ((rootGCD4 w x y z : ℤ) ^ 2) ∣ Δ := by
  rw [← hxw]
  exact rootGCD4_sq_dvd_gap_xw w x y z

/-- If `g` is the positive four-root gcd and `w,x,y,z` are all `g` times
signed quotients, then the quotient tuple is primitive. -/
theorem rootGCD4_eq_one_of_common_factor
    {w x y z p q r s : ℤ} {g : ℕ}
    (hgpos : 0 < g)
    (hgroot : g = rootGCD4 w x y z)
    (hw : w = (g : ℤ) * p)
    (hx : x = (g : ℤ) * q)
    (hy : y = (g : ℤ) * r)
    (hz : z = (g : ℤ) * s) :
    rootGCD4 p q r s = 1 := by
  let K : ℕ := rootGCD4 p q r s
  have hKp : K ∣ p.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_left p q r s
  have hKq : K ∣ q.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_second p q r s
  have hKr : K ∣ r.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_third p q r s
  have hKs : K ∣ s.natAbs := by
    dsimp [K]
    exact rootGCD4_dvd_fourth p q r s
  have hKg_w : K * g ∣ w.natAbs := by
    have hwa : w.natAbs = g * p.natAbs := by
      rw [hw, Int.natAbs_mul]
      simp
    rcases hKp with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hwa, ht]
    ring
  have hKg_x : K * g ∣ x.natAbs := by
    have hxa : x.natAbs = g * q.natAbs := by
      rw [hx, Int.natAbs_mul]
      simp
    rcases hKq with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hxa, ht]
    ring
  have hKg_y : K * g ∣ y.natAbs := by
    have hya : y.natAbs = g * r.natAbs := by
      rw [hy, Int.natAbs_mul]
      simp
    rcases hKr with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hya, ht]
    ring
  have hKg_z : K * g ∣ z.natAbs := by
    have hza : z.natAbs = g * s.natAbs := by
      rw [hz, Int.natAbs_mul]
      simp
    rcases hKs with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hza, ht]
    ring
  have hKg_root : K * g ∣ rootGCD4 w x y z :=
    dvd_rootGCD4 hKg_w hKg_x hKg_y hKg_z
  have hKg_g : K * g ∣ g := by
    simpa [← hgroot] using hKg_root
  rcases hKg_g with ⟨t, ht⟩
  have hKt : 1 = K * t := by
    have hmul : g * 1 = g * (K * t) := by
      calc
        g * 1 = g := by ring
        _ = (K * g) * t := ht
        _ = g * (K * t) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos hmul
  have hK_dvd_one : K ∣ 1 := ⟨t, hKt⟩
  have hK_one : K = 1 := Nat.dvd_one.mp hK_dvd_one
  simpa [K] using hK_one

/-- Integer version of Fermat's theorem that four squares in arithmetic
progression are constant. -/
def FourIntSquaresAPConst : Prop :=
  ∀ {w x y z : ℤ}, IntFourSqAP w x y z → FourSqAPConst w x y z

/-- Bridge from a nonconstant integer four-square AP to Mathlib's exponent-four
Fermat obstruction. -/
def FourSquaresAPToFermat42Bridge : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
      ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2

/-- The integer AP theorem would follow from the AP-to-FLT4 bridge and
Mathlib's `not_fermat_42`.  This is a conditional wrapper, not the current
preferred proof route. -/
theorem fourIntSquaresAPConst_of_fermat42_bridge
    (hbridge : FourSquaresAPToFermat42Bridge) :
    FourIntSquaresAPConst := by
  intro w x y z hap
  by_contra hconst
  rcases hbridge hap hconst with ⟨a, b, c, ha, hb, h42⟩
  exact (not_fermat_42 ha hb) h42

/-- In a four-square AP, equality of any adjacent square terms forces all four
square terms to be equal. -/
theorem intFourSqAP_const_of_adjacent_eq
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hzero : w ^ 2 = x ^ 2 ∨ x ^ 2 = y ^ 2 ∨ y ^ 2 = z ^ 2) :
    FourSqAPConst w x y z := by
  unfold IntFourSqAP FourSqAPConst at *
  rcases hAP with ⟨h1, h2⟩
  rcases hzero with h | h | h
  · exact ⟨h, by constructor <;> nlinarith⟩
  · exact ⟨by nlinarith, h, by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith, h⟩

/-- A nonconstant integer four-square AP has nonzero common difference. -/
theorem intFourSqAP_nonconst_commonDiff_ne_zero
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    x ^ 2 - w ^ 2 ≠ 0 := by
  intro h
  apply hnonconst
  apply intFourSqAP_const_of_adjacent_eq hAP
  left
  nlinarith

/-- The first three squares in a four-square AP form a symmetric three-square AP. -/
theorem intFourSqAP_left_three
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    w ^ 2 + y ^ 2 = 2 * x ^ 2 := by
  rcases hAP with ⟨hleft, _hright⟩
  nlinarith

/-- The last three squares in a four-square AP form a symmetric three-square AP. -/
theorem intFourSqAP_right_three
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    x ^ 2 + z ^ 2 = 2 * y ^ 2 := by
  rcases hAP with ⟨_hleft, hright⟩
  nlinarith

/-- The outer-pair and middle-pair sums agree in a four-square AP. -/
theorem intFourSqAP_outer_sum
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    w ^ 2 + z ^ 2 = x ^ 2 + y ^ 2 := by
  rcases hAP with ⟨hleft, hright⟩
  nlinarith

/-- The full outer difference is three times the middle common difference. -/
theorem intFourSqAP_outer_diff
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    z ^ 2 - w ^ 2 = 3 * (y ^ 2 - x ^ 2) := by
  rcases hAP with ⟨hleft, hright⟩
  nlinarith

/-- If the middle common difference is zero, the AP is constant as squares. -/
theorem fourSqAPConst_of_intFourSqAP_commonDiff_zero
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hzero : y ^ 2 - x ^ 2 = 0) :
    FourSqAPConst w x y z := by
  rcases hAP with ⟨hleft, hright⟩
  unfold FourSqAPConst
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-- In a nonconstant four-square AP, the middle common difference is nonzero. -/
theorem intFourSqAP_middle_commonDiff_ne_zero_of_nonconst
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hnonconst : ¬ FourSqAPConst w x y z) :
    y ^ 2 - x ^ 2 ≠ 0 := by
  intro hzero
  exact hnonconst (fourSqAPConst_of_intFourSqAP_commonDiff_zero hAP hzero)

/-- A square-product identity for the middle roots and endpoints. -/
theorem intFourSqAP_factor_xy_wz
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    (x * y - w * z) * (x * y + w * z) =
      2 * (y ^ 2 - x ^ 2) ^ 2 := by
  have hw : w ^ 2 = 2 * x ^ 2 - y ^ 2 := by
    nlinarith [intFourSqAP_left_three hAP]
  have hz : z ^ 2 = 2 * y ^ 2 - x ^ 2 := by
    nlinarith [intFourSqAP_right_three hAP]
  calc
    (x * y - w * z) * (x * y + w * z)
        = x ^ 2 * y ^ 2 - w ^ 2 * z ^ 2 := by ring
    _ = x ^ 2 * y ^ 2 - (2 * x ^ 2 - y ^ 2) * (2 * y ^ 2 - x ^ 2) := by
          rw [hw, hz]
    _ = 2 * (y ^ 2 - x ^ 2) ^ 2 := by ring

/-- A second square-product identity for a four-square AP. -/
theorem intFourSqAP_factor_xz_wy
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    (x * z - w * y) * (x * z + w * y) =
      (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
  have hw : w ^ 2 = 2 * x ^ 2 - y ^ 2 := by
    nlinarith [intFourSqAP_left_three hAP]
  have hz : z ^ 2 = 2 * y ^ 2 - x ^ 2 := by
    nlinarith [intFourSqAP_right_three hAP]
  calc
    (x * z - w * y) * (x * z + w * y)
        = x ^ 2 * z ^ 2 - w ^ 2 * y ^ 2 := by ring
    _ = x ^ 2 * (2 * y ^ 2 - x ^ 2) - (2 * x ^ 2 - y ^ 2) * y ^ 2 := by
          rw [hw, hz]
    _ = (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by ring

/-- A third square-product identity for a four-square AP. -/
theorem intFourSqAP_factor_yz_wx
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    (y * z - w * x) * (y * z + w * x) =
      2 * (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by
  have hw : w ^ 2 = 2 * x ^ 2 - y ^ 2 := by
    nlinarith [intFourSqAP_left_three hAP]
  have hz : z ^ 2 = 2 * y ^ 2 - x ^ 2 := by
    nlinarith [intFourSqAP_right_three hAP]
  calc
    (y * z - w * x) * (y * z + w * x)
        = y ^ 2 * z ^ 2 - w ^ 2 * x ^ 2 := by ring
    _ = y ^ 2 * (2 * y ^ 2 - x ^ 2) - (2 * x ^ 2 - y ^ 2) * x ^ 2 := by
          rw [hw, hz]
    _ = 2 * (y ^ 2 - x ^ 2) * (x ^ 2 + y ^ 2) := by ring

/-- Reversing a four-square AP preserves the AP property. -/
theorem intFourSqAP_reverse
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    IntFourSqAP z y x w := by
  unfold IntFourSqAP at *
  rcases hAP with ⟨h1, h2⟩
  constructor <;> nlinarith

/-- Choose the original or reversed order so that the common difference is
positive. -/
def APOrReversedPositiveDiff : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    ∃ p q r s Δ : ℤ,
      0 < Δ ∧
      q ^ 2 - p ^ 2 = Δ ∧
      r ^ 2 - q ^ 2 = Δ ∧
      s ^ 2 - r ^ 2 = Δ ∧
      ((p = w ∧ q = x ∧ r = y ∧ s = z) ∨
        (p = z ∧ q = y ∧ r = x ∧ s = w))

/-- The positive-difference order can be chosen unconditionally for a
nonconstant integer four-square AP. -/
theorem ap_or_reversed_positive_diff :
    APOrReversedPositiveDiff := by
  intro w x y z hAP hnonconst
  let δ : ℤ := x ^ 2 - w ^ 2
  have hδ_ne : δ ≠ 0 := by
    simpa [δ] using intFourSqAP_nonconst_commonDiff_ne_zero hAP hnonconst
  rcases hAP with ⟨h1, h2⟩
  rcases lt_trichotomy δ 0 with hδneg | hδzero | hδpos
  · refine ⟨z, y, x, w, -δ, ?_, ?_, ?_, ?_, Or.inr ?_⟩
    · nlinarith
    · dsimp [δ]
      nlinarith [h1, h2]
    · dsimp [δ]
      nlinarith [h1]
    · dsimp [δ]
      ring
    · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact False.elim (hδ_ne hδzero)
  · refine ⟨w, x, y, z, δ, hδpos, ?_, ?_, ?_, Or.inl ?_⟩
    · rfl
    · simpa [δ] using h1.symm
    · calc
        z ^ 2 - y ^ 2 = y ^ 2 - x ^ 2 := h2.symm
        _ = δ := by
          simpa [δ] using h1.symm
    · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Normalized centered primitive four-square arithmetic progression with
positive common step `4*N`. -/
structure PrimitiveCenteredFourSqAP where
  X : ℤ
  N : ℤ
  hNpos : 0 < N
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
  hp : p ^ 2 = X - 6 * N
  hq : q ^ 2 = X - 2 * N
  hr : r ^ 2 = X + 2 * N
  hs : s ^ 2 = X + 6 * N
  hpq : Int.gcd p q = 1
  hpr : Int.gcd p r = 1
  hps : Int.gcd p s = 1
  hqr : Int.gcd q r = 1
  hqs : Int.gcd q s = 1
  hrs : Int.gcd r s = 1
  hp_odd : p % 2 = 1
  hq_odd : q % 2 = 1
  hr_odd : r % 2 = 1
  hs_odd : s % 2 = 1

/-- The first square gap in a primitive centered AP is `4*N`. -/
theorem primitiveCentered_gap_pq (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 2 - S.p ^ 2 = 4 * S.N := by
  nlinarith [S.hp, S.hq]

/-- The middle square gap in a primitive centered AP is `4*N`. -/
theorem primitiveCentered_gap_qr (S : PrimitiveCenteredFourSqAP) :
    S.r ^ 2 - S.q ^ 2 = 4 * S.N := by
  nlinarith [S.hq, S.hr]

/-- The last square gap in a primitive centered AP is `4*N`. -/
theorem primitiveCentered_gap_rs (S : PrimitiveCenteredFourSqAP) :
    S.s ^ 2 - S.r ^ 2 = 4 * S.N := by
  nlinarith [S.hr, S.hs]

/-- The left three squares form a three-square AP. -/
theorem primitiveCentered_three_left (S : PrimitiveCenteredFourSqAP) :
    S.p ^ 2 + S.r ^ 2 = 2 * S.q ^ 2 := by
  nlinarith [S.hp, S.hq, S.hr]

/-- The right three squares form a three-square AP. -/
theorem primitiveCentered_three_right (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 2 + S.s ^ 2 = 2 * S.r ^ 2 := by
  nlinarith [S.hq, S.hr, S.hs]

/-- Endpoint symmetry of the centered AP. -/
theorem primitiveCentered_outer_inner_sum (S : PrimitiveCenteredFourSqAP) :
    S.p ^ 2 + S.s ^ 2 = S.q ^ 2 + S.r ^ 2 := by
  nlinarith [S.hp, S.hq, S.hr, S.hs]

/-- Pythagorean identity from the left three-square AP, without division by `2`. -/
theorem primitiveCentered_halfsum_left_num (S : PrimitiveCenteredFourSqAP) :
    (S.r - S.p) ^ 2 + (S.r + S.p) ^ 2 = (2 * S.q) ^ 2 := by
  have h := primitiveCentered_three_left S
  nlinarith

/-- Pythagorean identity from the right three-square AP, without division by `2`. -/
theorem primitiveCentered_halfsum_right_num (S : PrimitiveCenteredFourSqAP) :
    (S.s - S.q) ^ 2 + (S.s + S.q) ^ 2 = (2 * S.r) ^ 2 := by
  have h := primitiveCentered_three_right S
  nlinarith

/-- Numerator area identity for the left half-sum triangle. -/
theorem primitiveCentered_halfsum_left_area_num (S : PrimitiveCenteredFourSqAP) :
    (S.r - S.p) * (S.r + S.p) = 8 * S.N := by
  nlinarith [S.hp, S.hr]

/-- Numerator area identity for the right half-sum triangle. -/
theorem primitiveCentered_halfsum_right_area_num (S : PrimitiveCenteredFourSqAP) :
    (S.s - S.q) * (S.s + S.q) = 8 * S.N := by
  nlinarith [S.hq, S.hs]

/-- A useful Pythagorean-square identity on the left side of the centered AP. -/
theorem primitiveCentered_q4_pyth (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 4 = (S.p * S.r) ^ 2 + (4 * S.N) ^ 2 := by
  have hpq : S.q ^ 2 = S.p ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_pq S]
  have hqr : S.r ^ 2 = S.q ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_qr S]
  calc
    S.q ^ 4 = (S.q ^ 2) ^ 2 := by ring
    _ = (S.p ^ 2 + 4 * S.N) ^ 2 := by rw [hpq]
    _ = S.p ^ 2 * (S.q ^ 2 + 4 * S.N) + (4 * S.N) ^ 2 := by
      rw [hpq]
      ring
    _ = S.p ^ 2 * S.r ^ 2 + (4 * S.N) ^ 2 := by rw [hqr]
    _ = (S.p * S.r) ^ 2 + (4 * S.N) ^ 2 := by ring

/-- A useful Pythagorean-square identity on the right side of the centered AP. -/
theorem primitiveCentered_r4_pyth (S : PrimitiveCenteredFourSqAP) :
    S.r ^ 4 = (S.q * S.s) ^ 2 + (4 * S.N) ^ 2 := by
  have hqr : S.r ^ 2 = S.q ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_qr S]
  have hrs : S.s ^ 2 = S.r ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_rs S]
  calc
    S.r ^ 4 = (S.r ^ 2) ^ 2 := by ring
    _ = (S.q ^ 2 + 4 * S.N) ^ 2 := by rw [hqr]
    _ = S.q ^ 2 * (S.r ^ 2 + 4 * S.N) + (4 * S.N) ^ 2 := by
      rw [hqr]
      ring
    _ = S.q ^ 2 * S.s ^ 2 + (4 * S.N) ^ 2 := by rw [hrs]
    _ = (S.q * S.s) ^ 2 + (4 * S.N) ^ 2 := by ring

/-- The large Pythagorean identity underlying the Euler-pair descent route. -/
theorem primitiveCentered_big_pyth_identity (S : PrimitiveCenteredFourSqAP) :
    (S.X ^ 2 - 20 * S.N ^ 2) ^ 2 =
      (S.p * S.q * S.r * S.s) ^ 2 + (16 * S.N ^ 2) ^ 2 := by
  have hps : (S.p * S.s) ^ 2 = S.X ^ 2 - (6 * S.N) ^ 2 := by
    calc
      (S.p * S.s) ^ 2 = S.p ^ 2 * S.s ^ 2 := by ring
      _ = (S.X - 6 * S.N) * (S.X + 6 * S.N) := by rw [S.hp, S.hs]
      _ = S.X ^ 2 - (6 * S.N) ^ 2 := by ring
  have hqr : (S.q * S.r) ^ 2 = S.X ^ 2 - (2 * S.N) ^ 2 := by
    calc
      (S.q * S.r) ^ 2 = S.q ^ 2 * S.r ^ 2 := by ring
      _ = (S.X - 2 * S.N) * (S.X + 2 * S.N) := by rw [S.hq, S.hr]
      _ = S.X ^ 2 - (2 * S.N) ^ 2 := by ring
  have hsub :
      (S.X ^ 2 - 20 * S.N ^ 2) ^ 2 - (16 * S.N ^ 2) ^ 2 =
        (S.p * S.q * S.r * S.s) ^ 2 := by
    calc
      (S.X ^ 2 - 20 * S.N ^ 2) ^ 2 - (16 * S.N ^ 2) ^ 2
          = (S.X ^ 2 - (6 * S.N) ^ 2) *
              (S.X ^ 2 - (2 * S.N) ^ 2) := by ring
      _ = (S.p * S.s) ^ 2 * (S.q * S.r) ^ 2 := by rw [← hps, ← hqr]
      _ = (S.p * S.q * S.r * S.s) ^ 2 := by ring
  nlinarith

@[simp] def primitiveCenteredRootProduct (S : PrimitiveCenteredFourSqAP) : ℤ :=
  S.p * S.q * S.r * S.s

theorem primitiveCentered_p_odd (S : PrimitiveCenteredFourSqAP) : Odd S.p :=
  (Int.odd_iff (n := S.p)).mpr S.hp_odd

theorem primitiveCentered_q_odd (S : PrimitiveCenteredFourSqAP) : Odd S.q :=
  (Int.odd_iff (n := S.q)).mpr S.hq_odd

theorem primitiveCentered_r_odd (S : PrimitiveCenteredFourSqAP) : Odd S.r :=
  (Int.odd_iff (n := S.r)).mpr S.hr_odd

theorem primitiveCentered_s_odd (S : PrimitiveCenteredFourSqAP) : Odd S.s :=
  (Int.odd_iff (n := S.s)).mpr S.hs_odd

theorem primitiveCentered_p_ne_zero (S : PrimitiveCenteredFourSqAP) : S.p ≠ 0 := by
  intro hp0
  have hodd := S.hp_odd
  rw [hp0] at hodd
  norm_num at hodd

theorem primitiveCentered_q_ne_zero (S : PrimitiveCenteredFourSqAP) : S.q ≠ 0 := by
  intro hq0
  have hodd := S.hq_odd
  rw [hq0] at hodd
  norm_num at hodd

theorem primitiveCentered_r_ne_zero (S : PrimitiveCenteredFourSqAP) : S.r ≠ 0 := by
  intro hr0
  have hodd := S.hr_odd
  rw [hr0] at hodd
  norm_num at hodd

theorem primitiveCentered_s_ne_zero (S : PrimitiveCenteredFourSqAP) : S.s ≠ 0 := by
  intro hs0
  have hodd := S.hs_odd
  rw [hs0] at hodd
  norm_num at hodd

theorem primitiveCenteredRootProduct_odd (S : PrimitiveCenteredFourSqAP) :
    Odd (primitiveCenteredRootProduct S) := by
  dsimp [primitiveCenteredRootProduct]
  exact (((primitiveCentered_p_odd S).mul (primitiveCentered_q_odd S)).mul
    (primitiveCentered_r_odd S)).mul (primitiveCentered_s_odd S)

theorem primitiveCenteredRootProduct_mod_two (S : PrimitiveCenteredFourSqAP) :
    primitiveCenteredRootProduct S % 2 = 1 :=
  Int.odd_iff.mp (primitiveCenteredRootProduct_odd S)

theorem primitiveCentered_sixN_lt_X (S : PrimitiveCenteredFourSqAP) :
    6 * S.N < S.X := by
  have hpsq : 0 < S.p ^ 2 := sq_pos_of_ne_zero (primitiveCentered_p_ne_zero S)
  nlinarith [S.hp]

theorem primitiveCentered_big_hyp_pos (S : PrimitiveCenteredFourSqAP) :
    0 < S.X ^ 2 - 20 * S.N ^ 2 := by
  have hX : 6 * S.N < S.X := primitiveCentered_sixN_lt_X S
  have hsq : (6 * S.N) ^ 2 < S.X ^ 2 :=
    pow_lt_pow_left₀ hX (by nlinarith [S.hNpos]) (by norm_num : (2 : ℕ) ≠ 0)
  nlinarith [hsq, sq_pos_of_ne_zero (ne_of_gt S.hNpos)]

theorem primitiveCentered_big_pyth_triple (S : PrimitiveCenteredFourSqAP) :
    PythagoreanTriple
      (primitiveCenteredRootProduct S)
      (16 * S.N ^ 2)
      (S.X ^ 2 - 20 * S.N ^ 2) := by
  dsimp [PythagoreanTriple, primitiveCenteredRootProduct]
  nlinarith [primitiveCentered_big_pyth_identity S]

theorem gcd_left_step_of_adjacent_square_gap {u v N : ℤ}
    (huv : Int.gcd u v = 1)
    (hgap : v ^ 2 - u ^ 2 = 4 * N) : Int.gcd u N = 1 := by
  have huvC : IsCoprime u v := Int.isCoprime_iff_gcd_eq_one.mpr huv
  have huv2 : IsCoprime u (v ^ 2) := by
    exact huvC.pow_right
  have hv2' : v ^ 2 = 4 * N + u ^ 2 := by
    nlinarith [hgap]
  have hv2 : v ^ 2 = 4 * N + u * u := by
    calc
      v ^ 2 = 4 * N + u ^ 2 := hv2'
      _ = 4 * N + u * u := by ring
  have hcop : IsCoprime u (4 * N + u * u) := by
    simpa [hv2] using huv2
  have h4N : IsCoprime u (4 * N) := hcop.of_add_mul_left_right
  have hN : IsCoprime u N := h4N.of_mul_right_right
  exact Int.isCoprime_iff_gcd_eq_one.mp hN

theorem gcd_right_step_of_adjacent_square_gap {u v N : ℤ}
    (huv : Int.gcd u v = 1)
    (hgap : v ^ 2 - u ^ 2 = 4 * N) : Int.gcd v N = 1 := by
  have hvuC : IsCoprime v u := (Int.isCoprime_iff_gcd_eq_one.mpr huv).symm
  have hvu2 : IsCoprime v (u ^ 2) := by
    exact hvuC.pow_right
  have hu2' : u ^ 2 = -4 * N + v ^ 2 := by
    nlinarith [hgap]
  have hu2 : u ^ 2 = -4 * N + v * v := by
    calc
      u ^ 2 = -4 * N + v ^ 2 := hu2'
      _ = -4 * N + v * v := by ring
  have hcop : IsCoprime v (-4 * N + v * v) := by
    simpa [hu2] using hvu2
  have hneg4N : IsCoprime v (-4 * N) := hcop.of_add_mul_left_right
  have h4N : IsCoprime v (4 * N) := by
    rcases hneg4N with ⟨a, b, hab⟩
    refine ⟨a, -b, ?_⟩
    rw [← hab]
    ring
  have hN : IsCoprime v N := h4N.of_mul_right_right
  exact Int.isCoprime_iff_gcd_eq_one.mp hN

theorem primitiveCentered_p_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.p S.N = 1 :=
  gcd_left_step_of_adjacent_square_gap S.hpq (primitiveCentered_gap_pq S)

theorem primitiveCentered_q_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.q S.N = 1 :=
  gcd_right_step_of_adjacent_square_gap S.hpq (primitiveCentered_gap_pq S)

theorem primitiveCentered_r_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.r S.N = 1 :=
  gcd_right_step_of_adjacent_square_gap S.hqr (primitiveCentered_gap_qr S)

theorem primitiveCentered_s_coprime_N (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.s S.N = 1 :=
  gcd_right_step_of_adjacent_square_gap S.hrs (primitiveCentered_gap_rs S)

theorem primitiveCentered_p_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.p S.N :=
  Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_p_coprime_N S)

theorem primitiveCentered_q_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.q S.N :=
  Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_q_coprime_N S)

theorem primitiveCentered_r_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.r S.N :=
  Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_r_coprime_N S)

theorem primitiveCentered_s_isCoprime_N (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.s S.N :=
  Int.isCoprime_iff_gcd_eq_one.mpr (primitiveCentered_s_coprime_N S)

theorem primitiveCenteredRootProduct_isCoprime_N
    (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (primitiveCenteredRootProduct S) S.N := by
  dsimp [primitiveCenteredRootProduct]
  exact ((((primitiveCentered_p_isCoprime_N S).mul_left
    (primitiveCentered_q_isCoprime_N S)).mul_left
      (primitiveCentered_r_isCoprime_N S)).mul_left
        (primitiveCentered_s_isCoprime_N S))

theorem primitiveCenteredRootProduct_isCoprime_sixteen
    (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (primitiveCenteredRootProduct S) (16 : ℤ) := by
  have h2 :
      IsCoprime (primitiveCenteredRootProduct S) (2 : ℤ) :=
    (Int.isCoprime_two_right).mpr (primitiveCenteredRootProduct_odd S)
  have hpow := h2.pow_right (n := 4)
  norm_num at hpow ⊢
  exact hpow

theorem primitiveCentered_big_triple_coprime
    (S : PrimitiveCenteredFourSqAP) :
    Int.gcd (primitiveCenteredRootProduct S) (16 * S.N ^ 2) = 1 := by
  have hN2 :
      IsCoprime (primitiveCenteredRootProduct S) (S.N ^ 2) :=
    (primitiveCenteredRootProduct_isCoprime_N S).pow_right (n := 2)
  have h16 :
      IsCoprime (primitiveCenteredRootProduct S) (16 : ℤ) :=
    primitiveCenteredRootProduct_isCoprime_sixteen S
  have h :
      IsCoprime (primitiveCenteredRootProduct S) (16 * S.N ^ 2) :=
    h16.mul_right hN2
  exact Int.isCoprime_iff_gcd_eq_one.mp h

private theorem primitiveCentered_sq_eq_eight_mul_add_one_of_odd
    {n : ℤ} (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  rcases Int.two_dvd_mul_add_one t with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
    _ = 4 * (2 * u) + 1 := by rw [hu]
    _ = 8 * u + 1 := by ring

private theorem primitiveCentered_eight_dvd_sq_sub_sq_of_odd
    {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    (8 : ℤ) ∣ a ^ 2 - b ^ 2 := by
  rcases primitiveCentered_sq_eq_eight_mul_add_one_of_odd ha with ⟨A, hA⟩
  rcases primitiveCentered_sq_eq_eight_mul_add_one_of_odd hb with ⟨B, hB⟩
  refine ⟨A - B, ?_⟩
  rw [hA, hB]
  ring

theorem primitiveCentered_N_even (S : PrimitiveCenteredFourSqAP) : Even S.N := by
  have h8gap : (8 : ℤ) ∣ S.q ^ 2 - S.p ^ 2 :=
    primitiveCentered_eight_dvd_sq_sub_sq_of_odd
      (primitiveCentered_q_odd S) (primitiveCentered_p_odd S)
  have h8fourN : (8 : ℤ) ∣ 4 * S.N := by
    rw [← primitiveCentered_gap_pq S]
    exact h8gap
  rcases h8fourN with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  nlinarith

private theorem nat_exists_sq_of_coprime_mul_eq_sq_left
    {a b c : ℕ}
    (ha : 0 < a)
    (hcop : Nat.Coprime a b)
    (h : a * b = c ^ 2) :
    ∃ A : ℕ, a = A ^ 2 := by
  have hcopInt : Int.gcd (a : ℤ) (b : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hInt : (a : ℤ) * (b : ℤ) = (c : ℤ) ^ 2 := by
    exact_mod_cast h
  obtain ⟨u, hu | hu⟩ := Int.sq_of_gcd_eq_one hcopInt hInt
  · refine ⟨u.natAbs, ?_⟩
    calc
      a = Int.natAbs (a : ℤ) := by simp
      _ = Int.natAbs (u ^ 2) := by rw [hu]
      _ = u.natAbs ^ 2 := by rw [Int.natAbs_pow]
  · exfalso
    have hapos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
    rw [hu] at hapos
    nlinarith [sq_nonneg u]

private theorem nat_coprime_mul_eq_square_split
    {a b c : ℕ}
    (ha : 0 < a)
    (hb : 0 < b)
    (hcop : Nat.Coprime a b)
    (h : a * b = c ^ 2) :
    ∃ A D : ℕ,
      0 < A ∧ 0 < D ∧
        a = A ^ 2 ∧ b = D ^ 2 ∧ c = A * D := by
  obtain ⟨A, hA⟩ :=
    nat_exists_sq_of_coprime_mul_eq_sq_left
      (a := a) (b := b) (c := c) ha hcop h
  obtain ⟨D, hD⟩ :=
    nat_exists_sq_of_coprime_mul_eq_sq_left
      (a := b) (b := a) (c := c) hb hcop.symm
      (by simpa [mul_comm] using h)
  have hApos : 0 < A := by
    by_contra hAz
    have hA0 : A = 0 := by omega
    have ha0 : a = 0 := by
      rw [hA, hA0]
      norm_num
    exact (ne_of_gt ha) ha0
  have hDpos : 0 < D := by
    by_contra hDz
    have hD0 : D = 0 := by omega
    have hb0 : b = 0 := by
      rw [hD, hD0]
      norm_num
    exact (ne_of_gt hb) hb0
  have hsq : (A * D) ^ 2 = c ^ 2 := by
    calc
      (A * D) ^ 2 = A ^ 2 * D ^ 2 := by ring
      _ = a * b := by rw [← hA, ← hD]
      _ = c ^ 2 := h
  have hAD_eq_c : A * D = c :=
    (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) hsq
  exact ⟨A, D, hApos, hDpos, hA, hD, hAD_eq_c.symm⟩

private theorem nat_coprime_eight_left_of_odd {n : ℕ}
    (hn : Odd n) : Nat.Coprime 8 n := by
  have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  have h23 : Nat.Coprime (2 ^ 3) n := h2.pow_left 3
  simpa using h23

private theorem nat_coprime_product_eq_eight_square_split_even_left
    {N m n : ℕ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m)
    (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Nat.Coprime m n)
    (_hm_even : Even m)
    (hn_odd : Odd n) :
    ∃ A D : ℕ,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ Nat.Coprime A D ∧
        N = A * D ∧
          m = 8 * A ^ 2 ∧ n = D ^ 2 := by
  have h8copn : Nat.Coprime 8 n := nat_coprime_eight_left_of_odd hn_odd
  have h8dvd_mn : 8 ∣ m * n := by
    rw [hmn]
    exact dvd_mul_right 8 (N ^ 2)
  have h8dvd_m : 8 ∣ m := (h8copn.dvd_mul_right).mp h8dvd_mn
  let M : ℕ := m / 8
  have hm_eq : m = 8 * M := by
    dsimp [M]
    rw [mul_comm, Nat.div_mul_cancel h8dvd_m]
  have hquot : M * n = N ^ 2 := by
    have hmul : 8 * (M * n) = 8 * N ^ 2 := by
      calc
        8 * (M * n) = (8 * M) * n := by ring
        _ = m * n := by rw [← hm_eq]
        _ = 8 * N ^ 2 := hmn
    have hmul' : M * n * 8 = N ^ 2 * 8 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact (mul_left_inj' (show (8 : ℕ) ≠ 0 by norm_num)).mp hmul'
  have hMpos : 0 < M := by
    by_contra hMnot
    have hM0 : M = 0 := by omega
    have hN0 : N ^ 2 = 0 := by
      rw [← hquot, hM0]
      norm_num
    exact (pow_ne_zero 2 (ne_of_gt hNpos)) hN0
  have hMdvdm : M ∣ m := by
    refine ⟨8, ?_⟩
    rw [hm_eq]
    ring
  have hcopMn : Nat.Coprime M n := hmn_coprime.of_dvd_left hMdvdm
  obtain ⟨A, D, hApos, hDpos, hM, hDsq, hN⟩ :=
    nat_coprime_mul_eq_square_split hMpos hnpos hcopMn hquot
  have hDodd : Odd D := by
    have hcopD2 : Nat.Coprime D 2 := by
      have hcopDsq2 : Nat.Coprime (D ^ 2) 2 := by
        rw [← hDsq]
        exact Nat.coprime_two_right.mpr hn_odd
      rwa [Nat.coprime_pow_left_iff (by norm_num : (0 : ℕ) < 2)] at hcopDsq2
    exact Nat.coprime_two_right.mp hcopD2
  have hAeven : Even A := by
    have h2dvdAD : 2 ∣ A * D := by
      rw [← hN]
      exact even_iff_two_dvd.mp hNeven
    have hcop2D : Nat.Coprime 2 D := Nat.coprime_two_left.mpr hDodd
    exact even_iff_two_dvd.mpr ((hcop2D.dvd_mul_right).mp h2dvdAD)
  have hcopAD : Nat.Coprime A D := by
    have hcopSquares : Nat.Coprime (A ^ 2) (D ^ 2) := by
      simpa [hM, hDsq] using hcopMn
    rwa [Nat.coprime_pow_left_iff (by norm_num : (0 : ℕ) < 2),
      Nat.coprime_pow_right_iff (by norm_num : (0 : ℕ) < 2)] at hcopSquares
  refine ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, ?_, hDsq⟩
  rw [hm_eq, hM]

theorem nat_coprime_product_eq_eight_square_split
    {N m n : ℕ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m)
    (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Nat.Coprime m n)
    (hparity : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    ∃ A D : ℕ,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ Nat.Coprime A D ∧
        N = A * D ∧
          ((m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
            (m = D ^ 2 ∧ n = 8 * A ^ 2)) := by
  rcases hparity with hleft | hright
  · obtain ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, hm8, hnD⟩ :=
      nat_coprime_product_eq_eight_square_split_even_left
        (hNpos := hNpos) (hNeven := hNeven)
        (hmpos := hmpos) (hnpos := hnpos)
        (hmn := hmn) (hmn_coprime := hmn_coprime)
        hleft.1 hleft.2
    exact ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD,
      hN, Or.inl ⟨hm8, hnD⟩⟩
  · obtain ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, hn8, hmD⟩ :=
      nat_coprime_product_eq_eight_square_split_even_left
        (N := N) (m := n) (n := m)
        (hNpos := hNpos) (hNeven := hNeven)
        (hmpos := hnpos) (hnpos := hmpos)
        (hmn := by simpa [mul_comm] using hmn)
        (hmn_coprime := hmn_coprime.symm)
        hright.2 hright.1
    exact ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD,
      hN, Or.inr ⟨hmD, hn8⟩⟩

private theorem int_even_natCast_of_even {n : ℕ} (hn : Even n) :
    Even (n : ℤ) := by
  rcases hn with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  exact_mod_cast hk

private theorem int_odd_natCast_of_odd {n : ℕ} (hn : Odd n) :
    Odd (n : ℤ) := by
  rcases hn with ⟨k, hk⟩
  refine ⟨(k : ℤ), ?_⟩
  exact_mod_cast hk

theorem coprime_product_eq_eight_square_split_int
    {N m n : ℤ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m)
    (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Int.gcd m n = 1)
    (hparity :
      (m % 2 = 0 ∧ n % 2 = 1) ∨
        (m % 2 = 1 ∧ n % 2 = 0)) :
    ∃ A D : ℤ,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ IsCoprime A D ∧
        N = A * D ∧
          ((m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
            (m = D ^ 2 ∧ n = 8 * A ^ 2)) := by
  let NN : ℕ := N.natAbs
  let mm : ℕ := m.natAbs
  let nn : ℕ := n.natAbs
  have hNNcast : (NN : ℤ) = N := by
    dsimp [NN]
    exact Int.natAbs_of_nonneg (le_of_lt hNpos)
  have hmmcast : (mm : ℤ) = m := by
    dsimp [mm]
    exact Int.natAbs_of_nonneg (le_of_lt hmpos)
  have hnncast : (nn : ℤ) = n := by
    dsimp [nn]
    exact Int.natAbs_of_nonneg (le_of_lt hnpos)
  have hNNpos : 0 < NN := by
    have h : (0 : ℤ) < (NN : ℤ) := by
      simpa [hNNcast] using hNpos
    exact_mod_cast h
  have hmmpos : 0 < mm := by
    have h : (0 : ℤ) < (mm : ℤ) := by
      simpa [hmmcast] using hmpos
    exact_mod_cast h
  have hnnpos : 0 < nn := by
    have h : (0 : ℤ) < (nn : ℤ) := by
      simpa [hnncast] using hnpos
    exact_mod_cast h
  have hNNeven : Even NN := by
    dsimp [NN]
    exact Int.natAbs_even.mpr hNeven
  have hmnNat : mm * nn = 8 * NN ^ 2 := by
    have h := congrArg Int.natAbs hmn
    dsimp [mm, nn, NN]
    simpa [Int.natAbs_mul, Int.natAbs_pow] using h
  have hcopNat : Nat.Coprime mm nn := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd_def, mm, nn] using hmn_coprime
  have hparityNat :
      (Even mm ∧ Odd nn) ∨ (Odd mm ∧ Even nn) := by
    rcases hparity with hleft | hright
    · exact Or.inl
        ⟨Int.natAbs_even.mpr ((Int.even_iff (n := m)).mpr hleft.1),
          Int.natAbs_odd.mpr ((Int.odd_iff (n := n)).mpr hleft.2)⟩
    · exact Or.inr
        ⟨Int.natAbs_odd.mpr ((Int.odd_iff (n := m)).mpr hright.1),
          Int.natAbs_even.mpr ((Int.even_iff (n := n)).mpr hright.2)⟩
  obtain ⟨A, D, hApos, hDpos, hAeven, hDodd, hADcop,
    hNAD, hsplit⟩ :=
    nat_coprime_product_eq_eight_square_split
      hNNpos hNNeven hmmpos hnnpos hmnNat hcopNat hparityNat
  refine ⟨(A : ℤ), (D : ℤ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hApos
  · exact_mod_cast hDpos
  · exact int_even_natCast_of_even hAeven
  · exact int_odd_natCast_of_odd hDodd
  · rw [Int.isCoprime_iff_nat_coprime]
    simpa using hADcop
  · calc
      N = (NN : ℤ) := hNNcast.symm
      _ = (A * D : ℕ) := by exact_mod_cast hNAD
      _ = (A : ℤ) * (D : ℤ) := by norm_num
  · rcases hsplit with hsplit | hsplit
    · exact Or.inl ⟨
        (by
          calc
            m = (mm : ℤ) := hmmcast.symm
            _ = (8 * A ^ 2 : ℕ) := by exact_mod_cast hsplit.1
            _ = 8 * (A : ℤ) ^ 2 := by norm_num),
        (by
          calc
            n = (nn : ℤ) := hnncast.symm
            _ = (D ^ 2 : ℕ) := by exact_mod_cast hsplit.2
            _ = (D : ℤ) ^ 2 := by norm_num)⟩
    · exact Or.inr ⟨
        (by
          calc
            m = (mm : ℤ) := hmmcast.symm
            _ = (D ^ 2 : ℕ) := by exact_mod_cast hsplit.1
            _ = (D : ℤ) ^ 2 := by norm_num),
        (by
          calc
            n = (nn : ℤ) := hnncast.symm
            _ = (8 * A ^ 2 : ℕ) := by exact_mod_cast hsplit.2
            _ = 8 * (A : ℤ) ^ 2 := by norm_num)⟩

/-- Euler square-pair package used by the classical descent on four-square APs. -/
structure EulerSquarePair where
  A : ℤ
  D : ℤ
  B : ℤ
  C : ℤ
  hApos : 0 < A
  hDpos : 0 < D
  hDodd : Odd D
  hAeven : Even A
  hADcop : IsCoprime A D
  hBpos : 0 < B
  hCpos : 0 < C
  hB : B ^ 2 = 16 * A ^ 2 + D ^ 2
  hC : C ^ 2 = 4 * A ^ 2 + D ^ 2

/-- Algebraic balance identity arising after refining two coprime factorizations
in the Euler-pair descent. -/
theorem euler_refinement_balance
    {a b c d D : ℤ}
    (hD1 : D = 4 * a ^ 2 * b ^ 2 - c ^ 2 * d ^ 2)
    (hD2 : D = 16 * a ^ 2 * c ^ 2 - b ^ 2 * d ^ 2) :
    b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2) := by
  nlinarith

/-- Product-square identity used to reconstruct the middle roots from an
Euler square pair. -/
theorem eulerPair_middle_product_square
    {A D B C : ℤ}
    (hB : B ^ 2 = 16 * A ^ 2 + D ^ 2)
    (hC : C ^ 2 = 4 * A ^ 2 + D ^ 2) :
    (B * C) ^ 2 - (2 * (A * D)) ^ 2 =
      (D ^ 2 + 8 * A ^ 2) ^ 2 := by
  nlinarith [hB, hC]

/-- Product-square identity used to reconstruct the endpoint roots from an
Euler square pair. -/
theorem eulerPair_outer_product_square
    {A D B C : ℤ}
    (hB : B ^ 2 = 16 * A ^ 2 + D ^ 2)
    (hC : C ^ 2 = 4 * A ^ 2 + D ^ 2) :
    (B * C) ^ 2 - (6 * (A * D)) ^ 2 =
      (D ^ 2 - 8 * A ^ 2) ^ 2 := by
  nlinarith [hB, hC]

namespace EulerSquarePair

/-- The center used when reconstructing a centered four-square AP from an
Euler square pair. -/
@[simp] def centerX (E : EulerSquarePair) : ℤ := E.B * E.C

/-- The step used when reconstructing a centered four-square AP from an Euler
square pair. -/
@[simp] def stepN (E : EulerSquarePair) : ℤ := E.A * E.D

@[simp] def fm6 (E : EulerSquarePair) : ℤ := E.centerX - 6 * E.stepN

@[simp] def fm2 (E : EulerSquarePair) : ℤ := E.centerX - 2 * E.stepN

@[simp] def fp2 (E : EulerSquarePair) : ℤ := E.centerX + 2 * E.stepN

@[simp] def fp6 (E : EulerSquarePair) : ℤ := E.centerX + 6 * E.stepN

theorem stepN_pos (E : EulerSquarePair) : 0 < E.stepN := by
  dsimp [stepN]
  nlinarith [E.hApos, E.hDpos]

theorem stepN_even (E : EulerSquarePair) : Even E.stepN := by
  rcases E.hAeven with ⟨a, ha⟩
  refine ⟨a * E.D, ?_⟩
  dsimp [stepN]
  rw [ha]
  ring

theorem centerX_pos (E : EulerSquarePair) : 0 < E.centerX := by
  dsimp [centerX]
  nlinarith [E.hBpos, E.hCpos]

theorem B_odd (E : EulerSquarePair) : Odd E.B := by
  have hEven16 : Even (16 : ℤ) := by norm_num
  have hEven : Even (16 * E.A ^ 2) := hEven16.mul_right _
  have hOddRhs : Odd (16 * E.A ^ 2 + E.D ^ 2) :=
    hEven.add_odd E.hDodd.pow
  have hOddSq : Odd (E.B ^ 2) := by
    simpa [E.hB] using hOddRhs
  exact (Int.odd_pow' (m := E.B) (n := 2) (by norm_num)).mp hOddSq

theorem C_odd (E : EulerSquarePair) : Odd E.C := by
  have hEven4 : Even (4 : ℤ) := by norm_num
  have hEven : Even (4 * E.A ^ 2) := hEven4.mul_right _
  have hOddRhs : Odd (4 * E.A ^ 2 + E.D ^ 2) :=
    hEven.add_odd E.hDodd.pow
  have hOddSq : Odd (E.C ^ 2) := by
    simpa [E.hC] using hOddRhs
  exact (Int.odd_pow' (m := E.C) (n := 2) (by norm_num)).mp hOddSq

theorem centerX_odd (E : EulerSquarePair) : Odd E.centerX := by
  dsimp [centerX]
  exact E.B_odd.mul E.C_odd

theorem fp2_pos (E : EulerSquarePair) : 0 < E.fp2 := by
  rw [fp2]
  nlinarith [E.centerX_pos, E.stepN_pos]

theorem fp6_pos (E : EulerSquarePair) : 0 < E.fp6 := by
  rw [fp6]
  nlinarith [E.centerX_pos, E.stepN_pos]

theorem fm2_pos_of_fm6_pos (E : EulerSquarePair) (h : 0 < E.fm6) :
    0 < E.fm2 := by
  rw [fm2, fm6] at *
  nlinarith [h, E.stepN_pos]

private theorem dvd_sq_of_dvd {d x : ℤ} (h : d ∣ x) : d ∣ x ^ 2 := by
  rw [pow_two]
  exact dvd_mul_of_dvd_left h x

theorem D_coprime_16A2 (E : EulerSquarePair) :
    IsCoprime E.D (16 * E.A ^ 2) := by
  have hD2 : IsCoprime E.D (2 : ℤ) :=
    (Int.isCoprime_two_right).mpr E.hDodd
  have hD16 : IsCoprime E.D (16 : ℤ) := by
    have h := hD2.pow_right (n := 4)
    norm_num at h ⊢
    exact h
  have hDA2 : IsCoprime E.D (E.A ^ 2) :=
    E.hADcop.symm.pow_right (n := 2)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hD16.mul_right hDA2

theorem D_coprime_4A2 (E : EulerSquarePair) :
    IsCoprime E.D (4 * E.A ^ 2) := by
  have hD2 : IsCoprime E.D (2 : ℤ) :=
    (Int.isCoprime_two_right).mpr E.hDodd
  have hD4 : IsCoprime E.D (4 : ℤ) := by
    have h := hD2.pow_right (n := 2)
    norm_num at h ⊢
    exact h
  have hDA2 : IsCoprime E.D (E.A ^ 2) :=
    E.hADcop.symm.pow_right (n := 2)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hD4.mul_right hDA2

theorem B_coprime_A (E : EulerSquarePair) : IsCoprime E.B E.A := by
  apply IsRelPrime.isCoprime
  intro d hdB hdA
  have hdB2 : d ∣ E.B ^ 2 := dvd_sq_of_dvd hdB
  have hdA2 : d ∣ E.A ^ 2 := dvd_sq_of_dvd hdA
  have hd16A2 : d ∣ 16 * E.A ^ 2 := dvd_mul_of_dvd_right hdA2 16
  have hsum : d ∣ 16 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hB]
    exact hdB2
  have hdD2 : d ∣ E.D ^ 2 := by
    have hsub : d ∣ (16 * E.A ^ 2 + E.D ^ 2) - 16 * E.A ^ 2 :=
      dvd_sub hsum hd16A2
    convert hsub using 1
    ring
  exact (E.hADcop.pow_right (n := 2)).isUnit_of_dvd' hdA hdD2

theorem C_coprime_A (E : EulerSquarePair) : IsCoprime E.C E.A := by
  apply IsRelPrime.isCoprime
  intro d hdC hdA
  have hdC2 : d ∣ E.C ^ 2 := dvd_sq_of_dvd hdC
  have hdA2 : d ∣ E.A ^ 2 := dvd_sq_of_dvd hdA
  have hd4A2 : d ∣ 4 * E.A ^ 2 := dvd_mul_of_dvd_right hdA2 4
  have hsum : d ∣ 4 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hC]
    exact hdC2
  have hdD2 : d ∣ E.D ^ 2 := by
    have hsub : d ∣ (4 * E.A ^ 2 + E.D ^ 2) - 4 * E.A ^ 2 :=
      dvd_sub hsum hd4A2
    convert hsub using 1
    ring
  exact (E.hADcop.pow_right (n := 2)).isUnit_of_dvd' hdA hdD2

theorem B_coprime_D (E : EulerSquarePair) : IsCoprime E.B E.D := by
  apply IsRelPrime.isCoprime
  intro d hdB hdD
  have hdB2 : d ∣ E.B ^ 2 := dvd_sq_of_dvd hdB
  have hdD2 : d ∣ E.D ^ 2 := dvd_sq_of_dvd hdD
  have hsum : d ∣ 16 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hB]
    exact hdB2
  have hd16A2 : d ∣ 16 * E.A ^ 2 := by
    have hsub : d ∣ (16 * E.A ^ 2 + E.D ^ 2) - E.D ^ 2 :=
      dvd_sub hsum hdD2
    convert hsub using 1
    ring
  exact (E.D_coprime_16A2).isUnit_of_dvd' hdD hd16A2

theorem C_coprime_D (E : EulerSquarePair) : IsCoprime E.C E.D := by
  apply IsRelPrime.isCoprime
  intro d hdC hdD
  have hdC2 : d ∣ E.C ^ 2 := dvd_sq_of_dvd hdC
  have hdD2 : d ∣ E.D ^ 2 := dvd_sq_of_dvd hdD
  have hsum : d ∣ 4 * E.A ^ 2 + E.D ^ 2 := by
    rw [← E.hC]
    exact hdC2
  have hd4A2 : d ∣ 4 * E.A ^ 2 := by
    have hsub : d ∣ (4 * E.A ^ 2 + E.D ^ 2) - E.D ^ 2 :=
      dvd_sub hsum hdD2
    convert hsub using 1
    ring
  exact (E.D_coprime_4A2).isUnit_of_dvd' hdD hd4A2

theorem centerX_coprime_stepN (E : EulerSquarePair) :
    IsCoprime E.centerX E.stepN := by
  rw [centerX, stepN]
  have hB_AD : IsCoprime E.B (E.A * E.D) :=
    (E.B_coprime_A).mul_right E.B_coprime_D
  have hC_AD : IsCoprime E.C (E.A * E.D) :=
    (E.C_coprime_A).mul_right E.C_coprime_D
  exact hB_AD.mul_left hC_AD

theorem middle_factor_product_square (E : EulerSquarePair) :
    E.fm2 * E.fp2 = (E.D ^ 2 + 8 * E.A ^ 2) ^ 2 := by
  dsimp [fm2, fp2, centerX, stepN]
  calc
    (E.B * E.C - 2 * (E.A * E.D)) *
        (E.B * E.C + 2 * (E.A * E.D))
        = (E.B * E.C) ^ 2 - (2 * (E.A * E.D)) ^ 2 := by ring
    _ = (E.D ^ 2 + 8 * E.A ^ 2) ^ 2 :=
      eulerPair_middle_product_square E.hB E.hC

theorem outer_factor_product_square (E : EulerSquarePair) :
    E.fm6 * E.fp6 = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 := by
  dsimp [fm6, fp6, centerX, stepN]
  calc
    (E.B * E.C - 6 * (E.A * E.D)) *
        (E.B * E.C + 6 * (E.A * E.D))
        = (E.B * E.C) ^ 2 - (6 * (E.A * E.D)) ^ 2 := by ring
    _ = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 :=
      eulerPair_outer_product_square E.hB E.hC

private theorem even_eight_mul_sq (a : ℤ) : Even (8 * a ^ 2) := by
  refine ⟨4 * a ^ 2, ?_⟩
  ring

private theorem odd_sub_even_ne_zero {a b : ℤ}
    (ha : Odd a) (hb : Even b) : a - b ≠ 0 := by
  intro hzero
  rcases ha with ⟨u, hu⟩
  rcases hb with ⟨v, hv⟩
  rw [hu, hv] at hzero
  omega

theorem Dsq_sub_8Asq_ne_zero (E : EulerSquarePair) :
    E.D ^ 2 - 8 * E.A ^ 2 ≠ 0 :=
  odd_sub_even_ne_zero E.hDodd.pow (even_eight_mul_sq E.A)

theorem fm6_pos (E : EulerSquarePair) : 0 < E.fm6 := by
  have hprod : E.fm6 * E.fp6 = (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 :=
    E.outer_factor_product_square
  have hsqpos : 0 < (E.D ^ 2 - 8 * E.A ^ 2) ^ 2 :=
    sq_pos_of_ne_zero E.Dsq_sub_8Asq_ne_zero
  have hmulpos : 0 < E.fm6 * E.fp6 := by
    rw [hprod]
    exact hsqpos
  have hfp6 : 0 < E.fp6 := E.fp6_pos
  by_contra hnot
  have hfm6_nonpos : E.fm6 ≤ 0 := le_of_not_gt hnot
  have hfp6_nonneg : 0 ≤ E.fp6 := le_of_lt hfp6
  have hmul_nonpos : E.fm6 * E.fp6 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hfm6_nonpos hfp6_nonneg
  linarith

theorem fm2_pos (E : EulerSquarePair) : 0 < E.fm2 :=
  E.fm2_pos_of_fm6_pos E.fm6_pos

theorem fm2_odd (E : EulerSquarePair) : Odd E.fm2 := by
  rw [fm2]
  exact E.centerX_odd.sub_even (E.stepN_even.mul_left 2)

theorem fp2_odd (E : EulerSquarePair) : Odd E.fp2 := by
  rw [fp2]
  exact E.centerX_odd.add_even (E.stepN_even.mul_left 2)

theorem fm6_odd (E : EulerSquarePair) : Odd E.fm6 := by
  rw [fm6]
  exact E.centerX_odd.sub_even (E.stepN_even.mul_left 6)

theorem fp6_odd (E : EulerSquarePair) : Odd E.fp6 := by
  rw [fp6]
  exact E.centerX_odd.add_even (E.stepN_even.mul_left 6)

private theorem zmod3_sq_add_sq_eq_zero
    {x y : ZMod 3} (h : x ^ 2 + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  have hxy : x ^ 2 = -(y ^ 2) := by
    exact eq_neg_of_add_eq_zero_left h
  by_cases hx : x = 0
  · subst x
    have hy2 : y ^ 2 = 0 := by simpa using h
    exact ⟨rfl, sq_eq_zero_iff.mp hy2⟩
  · have hnot : (3 : ℕ) % 4 ≠ 3 := by
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq
        (p := 3) (x := x) (y := y) hx hxy
    norm_num at hnot

private theorem zmod3_natCast_16_eq_one : (16 : ZMod 3) = (1 : ZMod 3) := by
  change ((16 : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3)
  rw [ZMod.natCast_eq_natCast_iff]
  norm_num

private theorem zmod3_natCast_4_eq_one : (4 : ZMod 3) = (1 : ZMod 3) := by
  change ((4 : ℕ) : ZMod 3) = ((1 : ℕ) : ZMod 3)
  rw [ZMod.natCast_eq_natCast_iff]
  norm_num

theorem not_three_dvd_B (E : EulerSquarePair) : ¬ (3 : ℤ) ∣ E.B := by
  intro h3B
  have hBz :
      (E.B : ZMod 3) ^ 2 =
        (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) E.hB
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow] at h
    simpa [zmod3_natCast_16_eq_one] using h
  have hB0 : (E.B : ZMod 3) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.B 3).2 h3B
  have hsum :
      (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 = 0 := by
    simpa [hB0] using hBz.symm
  obtain ⟨hA0, hD0⟩ := zmod3_sq_add_sq_eq_zero hsum
  have h3A : (3 : ℤ) ∣ E.A := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.A 3).1 hA0
  have h3D : (3 : ℤ) ∣ E.D := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.D 3).1 hD0
  have hunit : IsUnit (3 : ℤ) := E.hADcop.isUnit_of_dvd' h3A h3D
  norm_num [Int.isUnit_iff] at hunit

theorem not_three_dvd_C (E : EulerSquarePair) : ¬ (3 : ℤ) ∣ E.C := by
  intro h3C
  have hCz :
      (E.C : ZMod 3) ^ 2 =
        (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : ZMod 3)) E.hC
    simp only [Int.cast_add, Int.cast_mul, Int.cast_pow] at h
    simpa [zmod3_natCast_4_eq_one] using h
  have hC0 : (E.C : ZMod 3) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.C 3).2 h3C
  have hsum :
      (E.A : ZMod 3) ^ 2 + (E.D : ZMod 3) ^ 2 = 0 := by
    simpa [hC0] using hCz.symm
  obtain ⟨hA0, hD0⟩ := zmod3_sq_add_sq_eq_zero hsum
  have h3A : (3 : ℤ) ∣ E.A := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.A 3).1 hA0
  have h3D : (3 : ℤ) ∣ E.D := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd E.D 3).1 hD0
  have hunit : IsUnit (3 : ℤ) := E.hADcop.isUnit_of_dvd' h3A h3D
  norm_num [Int.isUnit_iff] at hunit

theorem isCoprime_three_int_of_not_dvd {x : ℤ}
    (hx : ¬ (3 : ℤ) ∣ x) : IsCoprime (3 : ℤ) x :=
  Int.prime_three.coprime_iff_not_dvd.mpr hx

theorem three_coprime_B (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.B :=
  isCoprime_three_int_of_not_dvd E.not_three_dvd_B

theorem three_coprime_C (E : EulerSquarePair) : IsCoprime (3 : ℤ) E.C :=
  isCoprime_three_int_of_not_dvd E.not_three_dvd_C

theorem three_coprime_centerX (E : EulerSquarePair) :
    IsCoprime (3 : ℤ) E.centerX := by
  rw [centerX]
  exact E.three_coprime_B.mul_right E.three_coprime_C

private theorem isCoprime_two_of_dvd_odd {d m : ℤ}
    (hm : Odd m) (hdm : d ∣ m) : IsCoprime d (2 : ℤ) :=
  ((Int.isCoprime_two_right).mpr hm).of_isCoprime_of_dvd_left hdm

private theorem dvd_of_dvd_two_mul_of_coprime_two {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ 2 * x) : d ∣ x :=
  hd2.dvd_of_dvd_mul_left h

private theorem dvd_of_dvd_four_mul_of_coprime_two {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ 4 * x) : d ∣ x := by
  have hd4 : IsCoprime d (4 : ℤ) := by
    have hpow := hd2.pow_right (n := 2)
    norm_num at hpow ⊢
    exact hpow
  exact hd4.dvd_of_dvd_mul_left h

private theorem dvd_of_dvd_eight_mul_of_coprime_two {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ 8 * x) : d ∣ x := by
  have hd8 : IsCoprime d (8 : ℤ) := by
    have hpow := hd2.pow_right (n := 3)
    norm_num at hpow ⊢
    exact hpow
  exact hd8.dvd_of_dvd_mul_left h

private theorem isCoprime_three_of_dvd_centerX (E : EulerSquarePair)
    {d : ℤ} (hdX : d ∣ E.centerX) : IsCoprime d (3 : ℤ) :=
  (E.three_coprime_centerX.of_isCoprime_of_dvd_right hdX).symm

private theorem dvd_of_dvd_twelve_mul_of_coprime_two_three {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ)) (hd3 : IsCoprime d (3 : ℤ))
    (h : d ∣ 12 * x) : d ∣ x := by
  have hd4 : IsCoprime d (4 : ℤ) := by
    have hpow := hd2.pow_right (n := 2)
    norm_num at hpow ⊢
    exact hpow
  have hd12 : IsCoprime d (12 : ℤ) := by
    have h43 : IsCoprime d ((4 : ℤ) * 3) := hd4.mul_right hd3
    norm_num at h43 ⊢
    exact h43
  exact hd12.dvd_of_dvd_mul_left h

theorem fm2_coprime_fp2 (E : EulerSquarePair) : IsCoprime E.fm2 E.fp2 := by
  apply IsRelPrime.isCoprime
  intro d hdm hdp
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd E.fm2_odd hdm
  have hsum : d ∣ E.fm2 + E.fp2 := dvd_add hdm hdp
  have hsum_eq : E.fm2 + E.fp2 = 2 * E.centerX := by
    rw [fm2, fp2]
    ring
  have hd2X : d ∣ 2 * E.centerX := by
    rw [← hsum_eq]
    exact hsum
  have hdX : d ∣ E.centerX :=
    dvd_of_dvd_two_mul_of_coprime_two hd2 hd2X
  have hdiff : d ∣ E.fp2 - E.fm2 := dvd_sub hdp hdm
  have hdiff_eq : E.fp2 - E.fm2 = 4 * E.stepN := by
    rw [fm2, fp2]
    ring
  have hd4N : d ∣ 4 * E.stepN := by
    rw [← hdiff_eq]
    exact hdiff
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_four_mul_of_coprime_two hd2 hd4N
  exact E.centerX_coprime_stepN.isUnit_of_dvd' hdX hdN

theorem fm6_coprime_fp6 (E : EulerSquarePair) : IsCoprime E.fm6 E.fp6 := by
  apply IsRelPrime.isCoprime
  intro d hdm hdp
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd E.fm6_odd hdm
  have hsum : d ∣ E.fm6 + E.fp6 := dvd_add hdm hdp
  have hsum_eq : E.fm6 + E.fp6 = 2 * E.centerX := by
    rw [fm6, fp6]
    ring
  have hd2X : d ∣ 2 * E.centerX := by
    rw [← hsum_eq]
    exact hsum
  have hdX : d ∣ E.centerX :=
    dvd_of_dvd_two_mul_of_coprime_two hd2 hd2X
  have hd3 : IsCoprime d (3 : ℤ) :=
    isCoprime_three_of_dvd_centerX E hdX
  have hdiff : d ∣ E.fp6 - E.fm6 := dvd_sub hdp hdm
  have hdiff_eq : E.fp6 - E.fm6 = 12 * E.stepN := by
    rw [fm6, fp6]
    ring
  have hd12N : d ∣ 12 * E.stepN := by
    rw [← hdiff_eq]
    exact hdiff
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_twelve_mul_of_coprime_two_three hd2 hd3 hd12N
  exact E.centerX_coprime_stepN.isUnit_of_dvd' hdX hdN

private theorem square_of_positive_coprime_product_square {x y z : ℤ}
    (hxpos : 0 < x) (hcop : IsCoprime x y) (hprod : x * y = z ^ 2) :
    ∃ u : ℤ, u ^ 2 = x := by
  obtain ⟨u, hu | hu⟩ := Int.sq_of_isCoprime hcop hprod
  · exact ⟨u, hu.symm⟩
  · have hxnonpos : x ≤ 0 := by
      calc
        x = -u ^ 2 := hu
        _ ≤ 0 := neg_nonpos.mpr (sq_nonneg u)
    exact False.elim (not_lt_of_ge hxnonpos hxpos)

theorem fm2_square (E : EulerSquarePair) : ∃ q : ℤ, q ^ 2 = E.fm2 :=
  square_of_positive_coprime_product_square
    E.fm2_pos E.fm2_coprime_fp2 E.middle_factor_product_square

theorem fp2_square (E : EulerSquarePair) : ∃ r : ℤ, r ^ 2 = E.fp2 :=
  square_of_positive_coprime_product_square
    E.fp2_pos E.fm2_coprime_fp2.symm
    (by
      rw [mul_comm]
      exact E.middle_factor_product_square)

theorem fm6_square (E : EulerSquarePair) : ∃ p : ℤ, p ^ 2 = E.fm6 :=
  square_of_positive_coprime_product_square
    E.fm6_pos E.fm6_coprime_fp6 E.outer_factor_product_square

theorem fp6_square (E : EulerSquarePair) : ∃ s : ℤ, s ^ 2 = E.fp6 :=
  square_of_positive_coprime_product_square
    E.fp6_pos E.fm6_coprime_fp6.symm
    (by
      rw [mul_comm]
      exact E.outer_factor_product_square)

theorem fm6_coprime_fm2 (E : EulerSquarePair) : IsCoprime E.fm6 E.fm2 := by
  apply IsRelPrime.isCoprime
  intro d hd6 hd2m
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd E.fm6_odd hd6
  have hdiff : d ∣ E.fm2 - E.fm6 := dvd_sub hd2m hd6
  have hdiff_eq : E.fm2 - E.fm6 = 4 * E.stepN := by
    rw [fm6, fm2]
    ring
  have hd4N : d ∣ 4 * E.stepN := by
    rw [← hdiff_eq]
    exact hdiff
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_four_mul_of_coprime_two hd2 hd4N
  have hX : d ∣ E.centerX := by
    have hsum : d ∣ E.fm6 + 6 * E.stepN :=
      dvd_add hd6 (dvd_mul_of_dvd_right hdN 6)
    have hsum_eq : E.fm6 + 6 * E.stepN = E.centerX := by
      rw [fm6]
      ring
    rw [← hsum_eq]
    exact hsum
  exact E.centerX_coprime_stepN.isUnit_of_dvd' hX hdN

theorem fm6_coprime_fp2 (E : EulerSquarePair) : IsCoprime E.fm6 E.fp2 := by
  apply IsRelPrime.isCoprime
  intro d hd6 hdp2
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd E.fm6_odd hd6
  have hdiff : d ∣ E.fp2 - E.fm6 := dvd_sub hdp2 hd6
  have hdiff_eq : E.fp2 - E.fm6 = 8 * E.stepN := by
    rw [fm6, fp2]
    ring
  have hd8N : d ∣ 8 * E.stepN := by
    rw [← hdiff_eq]
    exact hdiff
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_eight_mul_of_coprime_two hd2 hd8N
  have hX : d ∣ E.centerX := by
    have hsum : d ∣ E.fm6 + 6 * E.stepN :=
      dvd_add hd6 (dvd_mul_of_dvd_right hdN 6)
    have hsum_eq : E.fm6 + 6 * E.stepN = E.centerX := by
      rw [fm6]
      ring
    rw [← hsum_eq]
    exact hsum
  exact E.centerX_coprime_stepN.isUnit_of_dvd' hX hdN

theorem fm2_coprime_fp6 (E : EulerSquarePair) : IsCoprime E.fm2 E.fp6 := by
  apply IsRelPrime.isCoprime
  intro d hdm2 hdp6
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd E.fm2_odd hdm2
  have hdiff : d ∣ E.fp6 - E.fm2 := dvd_sub hdp6 hdm2
  have hdiff_eq : E.fp6 - E.fm2 = 8 * E.stepN := by
    rw [fm2, fp6]
    ring
  have hd8N : d ∣ 8 * E.stepN := by
    rw [← hdiff_eq]
    exact hdiff
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_eight_mul_of_coprime_two hd2 hd8N
  have hX : d ∣ E.centerX := by
    have hsum : d ∣ E.fm2 + 2 * E.stepN :=
      dvd_add hdm2 (dvd_mul_of_dvd_right hdN 2)
    have hsum_eq : E.fm2 + 2 * E.stepN = E.centerX := by
      rw [fm2]
      ring
    rw [← hsum_eq]
    exact hsum
  exact E.centerX_coprime_stepN.isUnit_of_dvd' hX hdN

theorem fp2_coprime_fp6 (E : EulerSquarePair) : IsCoprime E.fp2 E.fp6 := by
  apply IsRelPrime.isCoprime
  intro d hdp2 hdp6
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd E.fp2_odd hdp2
  have hdiff : d ∣ E.fp6 - E.fp2 := dvd_sub hdp6 hdp2
  have hdiff_eq : E.fp6 - E.fp2 = 4 * E.stepN := by
    rw [fp2, fp6]
    ring
  have hd4N : d ∣ 4 * E.stepN := by
    rw [← hdiff_eq]
    exact hdiff
  have hdN : d ∣ E.stepN :=
    dvd_of_dvd_four_mul_of_coprime_two hd2 hd4N
  have hX : d ∣ E.centerX := by
    have hsub : d ∣ E.fp2 - 2 * E.stepN :=
      dvd_sub hdp2 (dvd_mul_of_dvd_right hdN 2)
    have hsub_eq : E.fp2 - 2 * E.stepN = E.centerX := by
      rw [fp2]
      ring
    rw [← hsub_eq]
    exact hsub
  exact E.centerX_coprime_stepN.isUnit_of_dvd' hX hdN

private theorem root_gcd_eq_one_of_sq_eq_of_isCoprime
    {p q x y : ℤ}
    (hp : p ^ 2 = x) (hq : q ^ 2 = y)
    (hxy : IsCoprime x y) :
    Int.gcd p q = 1 := by
  have hpq_sq : IsCoprime (p ^ 2) (q ^ 2) := by
    simpa [hp, hq] using hxy
  have hpq : IsCoprime p q := by
    exact (IsCoprime.pow_iff (R := ℤ) (x := p) (y := q)
      (m := 2) (n := 2) (by norm_num) (by norm_num)).mp hpq_sq
  exact Int.isCoprime_iff_gcd_eq_one.mp hpq

private theorem root_mod_two_eq_one_of_sq_eq_odd {p x : ℤ}
    (hp : p ^ 2 = x) (hxodd : Odd x) :
    p % 2 = 1 := by
  have hp2odd : Odd (p ^ 2) := by
    simpa [hp] using hxodd
  have hpodd : Odd p :=
    (Int.odd_pow' (m := p) (n := 2) (by norm_num)).mp hp2odd
  exact Int.odd_iff.mp hpodd

theorem eulerSquarePairToPrimitiveCentered_constructive
    (E : EulerSquarePair) :
    ∃ T : PrimitiveCenteredFourSqAP, T.N = E.A * E.D := by
  rcases E.fm6_square with ⟨p, hp⟩
  rcases E.fm2_square with ⟨q, hq⟩
  rcases E.fp2_square with ⟨r, hr⟩
  rcases E.fp6_square with ⟨s, hs⟩
  refine ⟨
    { X := E.centerX
      N := E.stepN
      hNpos := E.stepN_pos
      p := p
      q := q
      r := r
      s := s
      hp := by
        simpa [fm6] using hp
      hq := by
        simpa [fm2] using hq
      hr := by
        simpa [fp2] using hr
      hs := by
        simpa [fp6] using hs
      hpq := root_gcd_eq_one_of_sq_eq_of_isCoprime
        hp hq E.fm6_coprime_fm2
      hpr := root_gcd_eq_one_of_sq_eq_of_isCoprime
        hp hr E.fm6_coprime_fp2
      hps := root_gcd_eq_one_of_sq_eq_of_isCoprime
        hp hs E.fm6_coprime_fp6
      hqr := root_gcd_eq_one_of_sq_eq_of_isCoprime
        hq hr E.fm2_coprime_fp2
      hqs := root_gcd_eq_one_of_sq_eq_of_isCoprime
        hq hs E.fm2_coprime_fp6
      hrs := root_gcd_eq_one_of_sq_eq_of_isCoprime
        hr hs E.fp2_coprime_fp6
      hp_odd := root_mod_two_eq_one_of_sq_eq_odd hp E.fm6_odd
      hq_odd := root_mod_two_eq_one_of_sq_eq_odd hq E.fm2_odd
      hr_odd := root_mod_two_eq_one_of_sq_eq_odd hr E.fp2_odd
      hs_odd := root_mod_two_eq_one_of_sq_eq_odd hs E.fp6_odd },
    by
      simp [stepN]⟩

theorem D_mod_two_eq_one (E : EulerSquarePair) : E.D % 2 = 1 :=
  Int.odd_iff.mp E.hDodd

theorem D_coprime_twoA (E : EulerSquarePair) :
    IsCoprime E.D (2 * E.A) := by
  have hD2 : IsCoprime E.D (2 : ℤ) :=
    (Int.isCoprime_two_right).mpr E.hDodd
  exact hD2.mul_right E.hADcop.symm

theorem D_coprime_fourA (E : EulerSquarePair) :
    IsCoprime E.D (4 * E.A) := by
  have hD2 : IsCoprime E.D (2 : ℤ) :=
    (Int.isCoprime_two_right).mpr E.hDodd
  have hD4 : IsCoprime E.D (4 : ℤ) := by
    have hpow := hD2.pow_right (n := 2)
    norm_num at hpow ⊢
    exact hpow
  exact hD4.mul_right E.hADcop.symm

theorem gcd_D_twoA_eq_one (E : EulerSquarePair) :
    Int.gcd E.D (2 * E.A) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp E.D_coprime_twoA

theorem gcd_D_fourA_eq_one (E : EulerSquarePair) :
    Int.gcd E.D (4 * E.A) = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp E.D_coprime_fourA

theorem pythagorean_D_twoA_C (E : EulerSquarePair) :
    PythagoreanTriple E.D (2 * E.A) E.C := by
  dsimp [PythagoreanTriple]
  nlinarith [E.hC]

theorem pythagorean_D_fourA_B (E : EulerSquarePair) :
    PythagoreanTriple E.D (4 * E.A) E.B := by
  dsimp [PythagoreanTriple]
  nlinarith [E.hB]

theorem pythagorean_D_twoA_C_params (E : EulerSquarePair) :
    ∃ m n : ℤ,
      E.D = m ^ 2 - n ^ 2 ∧
        2 * E.A = 2 * m * n ∧
          E.C = m ^ 2 + n ^ 2 ∧
            Int.gcd m n = 1 ∧
              (m % 2 = 0 ∧ n % 2 = 1 ∨
                m % 2 = 1 ∧ n % 2 = 0) ∧
                0 ≤ m :=
  E.pythagorean_D_twoA_C.coprime_classification'
    E.gcd_D_twoA_eq_one E.D_mod_two_eq_one E.hCpos

theorem pythagorean_D_fourA_B_params (E : EulerSquarePair) :
    ∃ m n : ℤ,
      E.D = m ^ 2 - n ^ 2 ∧
        4 * E.A = 2 * m * n ∧
          E.B = m ^ 2 + n ^ 2 ∧
            Int.gcd m n = 1 ∧
              (m % 2 = 0 ∧ n % 2 = 1 ∨
                m % 2 = 1 ∧ n % 2 = 0) ∧
                0 ≤ m :=
  E.pythagorean_D_fourA_B.coprime_classification'
    E.gcd_D_fourA_eq_one E.D_mod_two_eq_one E.hBpos

theorem C_signed_even_odd_params (E : EulerSquarePair) :
    ∃ U V eps : ℤ,
      0 < U ∧ 0 < V ∧
        IsCoprime U V ∧ Even U ∧ Odd V ∧
          (eps = 1 ∨ eps = -1) ∧
            E.A = U * V ∧
              E.D = eps * (U ^ 2 - V ^ 2) ∧
                E.C = U ^ 2 + V ^ 2 := by
  rcases E.pythagorean_D_twoA_C_params with
    ⟨m, n, hD, hA2, hC, hmn_gcd, hparity, hm_nonneg⟩
  have hA : E.A = m * n := by nlinarith
  have hmn_pos : 0 < m * n := by
    rw [← hA]
    exact E.hApos
  have hm_ne : m ≠ 0 := by
    intro hm
    rw [hm] at hmn_pos
    norm_num at hmn_pos
  have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg hm_ne.symm
  have hn_pos : 0 < n := by
    have hnm_pos : 0 < n * m := by
      simpa [mul_comm] using hmn_pos
    exact pos_of_mul_pos_left hnm_pos (le_of_lt hm_pos)
  have hcop_mn : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
  rcases hparity with hmn_even_odd | hmn_odd_even
  · rcases hmn_even_odd with ⟨hm_even, hn_odd⟩
    refine ⟨m, n, 1, hm_pos, hn_pos, hcop_mn,
      Int.even_iff.mpr hm_even, Int.odd_iff.mpr hn_odd,
      Or.inl rfl, hA, ?_, hC⟩
    simpa using hD
  · rcases hmn_odd_even with ⟨hm_odd, hn_even⟩
    refine ⟨n, m, -1, hn_pos, hm_pos, hcop_mn.symm,
      Int.even_iff.mpr hn_even, Int.odd_iff.mpr hm_odd,
      Or.inr rfl, ?_, ?_, ?_⟩
    · simpa [mul_comm] using hA
    · calc
        E.D = m ^ 2 - n ^ 2 := hD
        _ = (-1 : ℤ) * (n ^ 2 - m ^ 2) := by ring
    · calc
        E.C = m ^ 2 + n ^ 2 := hC
        _ = n ^ 2 + m ^ 2 := by ring

private theorem two_mul_left_cancel_int {a b : ℤ}
    (h : (2 : ℤ) * a = 2 * b) : a = b := by
  have h' : a * (2 : ℤ) = b * 2 := by
    simpa [mul_comm] using h
  exact (mul_left_inj' (show (2 : ℤ) ≠ 0 by norm_num)).mp h'

private theorem left_mod_two_eq_zero_of_even_mul_of_right_mod_two_eq_one
    {a b : ℤ} (hab : Even (a * b)) (hb : b % 2 = 1) :
    a % 2 = 0 := by
  have hnot : ¬ Odd a := by
    intro ha
    have hbOdd : Odd b := Int.odd_iff.mpr hb
    have hOdd : Odd (a * b) := Int.odd_mul.mpr ⟨ha, hbOdd⟩
    exact (Int.not_odd_iff_even.mpr hab) hOdd
  exact Int.not_odd_iff.mp hnot

theorem B_signed_even_odd_params (E : EulerSquarePair) :
    ∃ Up Vp eps : ℤ,
      0 < Up ∧ 0 < Vp ∧
        IsCoprime Up Vp ∧ Even Up ∧ Odd Vp ∧
          (eps = 1 ∨ eps = -1) ∧
            E.A = Up * Vp ∧
              E.D = eps * (4 * Up ^ 2 - Vp ^ 2) ∧
                E.B = 4 * Up ^ 2 + Vp ^ 2 := by
  rcases E.pythagorean_D_fourA_B_params with
    ⟨m, n, hD, h4A, hB, hmn_gcd, hparity, hm_nonneg⟩
  have h2A_mn : (2 : ℤ) * E.A = m * n := by
    apply two_mul_left_cancel_int
    calc
      (2 : ℤ) * (2 * E.A) = 4 * E.A := by ring
      _ = 2 * m * n := h4A
      _ = 2 * (m * n) := by ring
  have hmn_coprime : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
  have hmn_pos : 0 < m * n := by
    have h2Apos : 0 < (2 : ℤ) * E.A := by nlinarith [E.hApos]
    rw [h2A_mn] at h2Apos
    exact h2Apos
  have hm_ne : m ≠ 0 := by
    intro hm
    rw [hm] at hmn_pos
    norm_num at hmn_pos
  have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg hm_ne.symm
  have hn_pos : 0 < n := by
    have hnm_pos : 0 < n * m := by
      simpa [mul_comm] using hmn_pos
    exact pos_of_mul_pos_left hnm_pos (le_of_lt hm_pos)
  rcases hparity with hmn_even_odd | hmn_odd_even
  · rcases hmn_even_odd with ⟨hm_even, hn_odd⟩
    rcases Int.dvd_of_emod_eq_zero hm_even with ⟨Up, hUp⟩
    have hUp_pos : 0 < Up := by nlinarith [hm_pos, hUp]
    have hA : E.A = Up * n := by
      apply two_mul_left_cancel_int
      calc
        (2 : ℤ) * E.A = m * n := h2A_mn
        _ = 2 * (Up * n) := by
          rw [hUp]
          ring
    have hB' : E.B = 4 * Up ^ 2 + n ^ 2 := by
      calc
        E.B = m ^ 2 + n ^ 2 := hB
        _ = 4 * Up ^ 2 + n ^ 2 := by
          rw [hUp]
          ring
    have hD' : E.D = 4 * Up ^ 2 - n ^ 2 := by
      calc
        E.D = m ^ 2 - n ^ 2 := hD
        _ = 4 * Up ^ 2 - n ^ 2 := by
          rw [hUp]
          ring
    have hcop : IsCoprime Up n := by
      have hcop2Upn : IsCoprime (2 * Up) n := by
        simpa [hUp] using hmn_coprime
      exact hcop2Upn.of_mul_left_right
    have hUpEven : Even Up :=
      Int.even_iff.mpr <|
        left_mod_two_eq_zero_of_even_mul_of_right_mod_two_eq_one
          (by simpa [hA] using E.hAeven) hn_odd
    refine ⟨Up, n, 1, hUp_pos, hn_pos, hcop, hUpEven,
      Int.odd_iff.mpr hn_odd, Or.inl rfl, hA, ?_, hB'⟩
    simpa using hD'
  · rcases hmn_odd_even with ⟨hm_odd, hn_even⟩
    rcases Int.dvd_of_emod_eq_zero hn_even with ⟨Up, hUp⟩
    have hUp_pos : 0 < Up := by nlinarith [hn_pos, hUp]
    have hA : E.A = Up * m := by
      apply two_mul_left_cancel_int
      calc
        (2 : ℤ) * E.A = m * n := h2A_mn
        _ = 2 * (Up * m) := by
          rw [hUp]
          ring
    have hB' : E.B = 4 * Up ^ 2 + m ^ 2 := by
      calc
        E.B = m ^ 2 + n ^ 2 := hB
        _ = 4 * Up ^ 2 + m ^ 2 := by
          rw [hUp]
          ring
    have hD' : E.D = -(4 * Up ^ 2 - m ^ 2) := by
      calc
        E.D = m ^ 2 - n ^ 2 := hD
        _ = -(4 * Up ^ 2 - m ^ 2) := by
          rw [hUp]
          ring
    have hcop : IsCoprime Up m := by
      have hcopm2Up : IsCoprime m (2 * Up) := by
        simpa [hUp] using hmn_coprime
      exact hcopm2Up.of_mul_right_right.symm
    have hUpEven : Even Up :=
      Int.even_iff.mpr <|
        left_mod_two_eq_zero_of_even_mul_of_right_mod_two_eq_one
          (by simpa [hA] using E.hAeven) hm_odd
    refine ⟨Up, m, -1, hUp_pos, hm_pos, hcop, hUpEven,
      Int.odd_iff.mpr hm_odd, Or.inr rfl, hA, ?_, hB'⟩
    simpa using hD'

/-- An even square minus an odd square is `-1 mod 4`, in integer form. -/
theorem even_sq_sub_odd_sq_eq_four_mul_sub_one
    {U V : ℤ} (hU : Even U) (hV : Odd V) :
    ∃ m : ℤ, U ^ 2 - V ^ 2 = 4 * m - 1 := by
  rcases hU with ⟨u, rfl⟩
  rcases hV with ⟨v, rfl⟩
  refine ⟨u ^ 2 - v ^ 2 - v, ?_⟩
  ring

/-- `4*U^2` minus an odd square is `-1 mod 4`, in integer form. -/
theorem four_mul_sq_sub_odd_sq_eq_four_mul_sub_one
    {U V : ℤ} (hV : Odd V) :
    ∃ m : ℤ, 4 * U ^ 2 - V ^ 2 = 4 * m - 1 := by
  rcases hV with ⟨v, rfl⟩
  refine ⟨U ^ 2 - v ^ 2 - v, ?_⟩
  ring

private theorem same_sign_of_four_mul_sub_one
    {D x y : ℤ}
    (hx4 : ∃ m : ℤ, x = 4 * m - 1)
    (hy4 : ∃ n : ℤ, y = 4 * n - 1)
    (hxD : x = D ∨ x = -D)
    (hyD : y = D ∨ y = -D) :
    (x = D ∧ y = D) ∨ (x = -D ∧ y = -D) := by
  rcases hx4 with ⟨m, hx4⟩
  rcases hy4 with ⟨n, hy4⟩
  rcases hxD with hxD | hxD
  · rcases hyD with hyD | hyD
    · exact Or.inl ⟨hxD, hyD⟩
    · exfalso
      subst x
      subst y
      omega
  · rcases hyD with hyD | hyD
    · exfalso
      subst x
      subst y
      omega
    · exact Or.inr ⟨hxD, hyD⟩

/-- The two signed odd legs in the Euler pair parametrizations have the same
orientation. -/
theorem same_orientation_of_pythagorean_signed_forms
    {D U V Up Vp : ℤ}
    (hUeven : Even U)
    (hVodd : Odd V)
    (hVpodd : Odd Vp)
    (h1 : D = U ^ 2 - V ^ 2 ∨ -D = U ^ 2 - V ^ 2)
    (h2 : D = 4 * Up ^ 2 - Vp ^ 2 ∨
      -D = 4 * Up ^ 2 - Vp ^ 2) :
    (D = U ^ 2 - V ^ 2 ∧ D = 4 * Up ^ 2 - Vp ^ 2) ∨
      (-D = U ^ 2 - V ^ 2 ∧ -D = 4 * Up ^ 2 - Vp ^ 2) := by
  have hx4 :
      ∃ m : ℤ, U ^ 2 - V ^ 2 = 4 * m - 1 :=
    even_sq_sub_odd_sq_eq_four_mul_sub_one hUeven hVodd
  have hy4 :
      ∃ n : ℤ, 4 * Up ^ 2 - Vp ^ 2 = 4 * n - 1 :=
    four_mul_sq_sub_odd_sq_eq_four_mul_sub_one hVpodd
  have hxD : U ^ 2 - V ^ 2 = D ∨ U ^ 2 - V ^ 2 = -D := by
    rcases h1 with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  have hyD :
      4 * Up ^ 2 - Vp ^ 2 = D ∨
        4 * Up ^ 2 - Vp ^ 2 = -D := by
    rcases h2 with h2 | h2
    · exact Or.inl h2.symm
    · exact Or.inr h2.symm
  have hs := same_sign_of_four_mul_sub_one
    (D := D) (x := U ^ 2 - V ^ 2) (y := 4 * Up ^ 2 - Vp ^ 2)
    hx4 hy4 hxD hyD
  rcases hs with hs | hs
  · exact Or.inl ⟨hs.1.symm, hs.2.symm⟩
  · exact Or.inr ⟨hs.1.symm, hs.2.symm⟩

theorem signed_even_odd_params_same_orientation (E : EulerSquarePair) :
    ∃ U V Up Vp : ℤ,
      0 < U ∧ 0 < V ∧ 0 < Up ∧ 0 < Vp ∧
        IsCoprime U V ∧ IsCoprime Up Vp ∧
          Even U ∧ Odd V ∧ Even Up ∧ Odd Vp ∧
            E.A = U * V ∧ E.A = Up * Vp ∧
              E.C = U ^ 2 + V ^ 2 ∧ E.B = 4 * Up ^ 2 + Vp ^ 2 ∧
                ((E.D = U ^ 2 - V ^ 2 ∧
                    E.D = 4 * Up ^ 2 - Vp ^ 2) ∨
                  (-E.D = U ^ 2 - V ^ 2 ∧
                    -E.D = 4 * Up ^ 2 - Vp ^ 2)) := by
  rcases E.C_signed_even_odd_params with
    ⟨U, V, epsC, hUpos, hVpos, hUVcop, hUeven, hVodd,
      hepsC, hAUV, hDC, hC⟩
  rcases E.B_signed_even_odd_params with
    ⟨Up, Vp, epsB, hUppos, hVppos, hUpVpcop, hUpeven, hVpodd,
      hepsB, hAUpVp, hDB, hB⟩
  have hCsign : E.D = U ^ 2 - V ^ 2 ∨ -E.D = U ^ 2 - V ^ 2 := by
    rcases hepsC with rfl | rfl
    · exact Or.inl (by simpa using hDC)
    · exact Or.inr (by nlinarith [hDC])
  have hBsign :
      E.D = 4 * Up ^ 2 - Vp ^ 2 ∨
        -E.D = 4 * Up ^ 2 - Vp ^ 2 := by
    rcases hepsB with rfl | rfl
    · exact Or.inl (by simpa using hDB)
    · exact Or.inr (by nlinarith [hDB])
  have hsame :=
    same_orientation_of_pythagorean_signed_forms
      hUeven hVodd hVpodd hCsign hBsign
  exact ⟨U, V, Up, Vp, hUpos, hVpos, hUppos, hVppos,
    hUVcop, hUpVpcop, hUeven, hVodd, hUpeven, hVpodd,
    hAUV, hAUpVp, hC, hB, hsame⟩

/-- Once the signed odd legs are oriented consistently, a common refinement of
the two factorizations gives the Euler balance equation. -/
theorem refinement_equation_of_same_orientation
    {D U V Up Vp a b c d : ℤ}
    (hU : U = 2 * a * b)
    (hV : V = c * d)
    (hUp : Up = 2 * a * c)
    (hVp : Vp = b * d)
    (hsame :
      (D = U ^ 2 - V ^ 2 ∧ D = 4 * Up ^ 2 - Vp ^ 2) ∨
        (-D = U ^ 2 - V ^ 2 ∧ -D = 4 * Up ^ 2 - Vp ^ 2)) :
    b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2) := by
  have heq : U ^ 2 - V ^ 2 = 4 * Up ^ 2 - Vp ^ 2 := by
    rcases hsame with hsame | hsame
    · rw [← hsame.1, ← hsame.2]
    · rw [← hsame.1, ← hsame.2]
  subst U
  subst V
  subst Up
  subst Vp
  ring_nf at heq ⊢
  nlinarith [heq]

private theorem two_coprime_factorizations_refine_nat
    {U V Up Vp : ℕ}
    (hUpos : 0 < U) (hVpos : 0 < V)
    (hEq : U * V = Up * Vp)
    (hUV : Nat.Coprime U V)
    (hUpVp : Nat.Coprime Up Vp) :
    ∃ a b c d : ℕ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
        U = a * b ∧ V = c * d ∧
          Up = a * c ∧ Vp = b * d ∧
            Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime a d ∧
              Nat.Coprime b c ∧ Nat.Coprime b d ∧ Nat.Coprime c d := by
  let a := Nat.gcd U Up
  let b := Nat.gcd U Vp
  let c := Nat.gcd V Up
  let d := Nat.gcd V Vp
  have hU_dvd : U ∣ Up * Vp := ⟨V, hEq.symm⟩
  have hV_dvd : V ∣ Up * Vp := by
    refine ⟨U, ?_⟩
    simpa [mul_comm] using hEq.symm
  have hUp_dvd : Up ∣ U * V := ⟨Vp, hEq⟩
  have hVp_dvd : Vp ∣ U * V := by
    refine ⟨Up, ?_⟩
    simpa [mul_comm] using hEq
  have hU_corner : Nat.gcd U Up * Nat.gcd U Vp = U :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hUpVp).2 hU_dvd
  have hV_corner : Nat.gcd V Up * Nat.gcd V Vp = V :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hUpVp).2 hV_dvd
  have hUp_corner : Nat.gcd Up U * Nat.gcd Up V = Up :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hUV).2 hUp_dvd
  have hVp_corner : Nat.gcd Vp U * Nat.gcd Vp V = Vp :=
    (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime hUV).2 hVp_dvd
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Nat.gcd_pos_of_pos_left Up hUpos
  have hb_pos : 0 < b := by
    dsimp [b]
    exact Nat.gcd_pos_of_pos_left Vp hUpos
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Nat.gcd_pos_of_pos_left Up hVpos
  have hd_pos : 0 < d := by
    dsimp [d]
    exact Nat.gcd_pos_of_pos_left Vp hVpos
  have hUeq : U = a * b := by
    dsimp [a, b]
    exact hU_corner.symm
  have hVeq : V = c * d := by
    dsimp [c, d]
    exact hV_corner.symm
  have hUpeq : Up = a * c := by
    dsimp [a, c]
    simpa [Nat.gcd_comm] using hUp_corner.symm
  have hVpeq : Vp = b * d := by
    dsimp [b, d]
    simpa [Nat.gcd_comm] using hVp_corner.symm
  have haU : a ∣ U := by
    dsimp [a]
    exact Nat.gcd_dvd_left U Up
  have haUp : a ∣ Up := by
    dsimp [a]
    exact Nat.gcd_dvd_right U Up
  have hbU : b ∣ U := by
    dsimp [b]
    exact Nat.gcd_dvd_left U Vp
  have hbVp : b ∣ Vp := by
    dsimp [b]
    exact Nat.gcd_dvd_right U Vp
  have hcV : c ∣ V := by
    dsimp [c]
    exact Nat.gcd_dvd_left V Up
  have hcUp : c ∣ Up := by
    dsimp [c]
    exact Nat.gcd_dvd_right V Up
  have hdV : d ∣ V := by
    dsimp [d]
    exact Nat.gcd_dvd_left V Vp
  have hdVp : d ∣ Vp := by
    dsimp [d]
    exact Nat.gcd_dvd_right V Vp
  have hab : Nat.Coprime a b := Nat.Coprime.of_dvd haUp hbVp hUpVp
  have hac : Nat.Coprime a c := Nat.Coprime.of_dvd haU hcV hUV
  have had : Nat.Coprime a d := Nat.Coprime.of_dvd haU hdV hUV
  have hbc : Nat.Coprime b c := Nat.Coprime.of_dvd hbU hcV hUV
  have hbd : Nat.Coprime b d := Nat.Coprime.of_dvd hbU hdV hUV
  have hcd : Nat.Coprime c d := Nat.Coprime.of_dvd hcUp hdVp hUpVp
  exact ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos,
    hUeq, hVeq, hUpeq, hVpeq, hab, hac, had, hbc, hbd, hcd⟩

private theorem isCoprime_self_sub_right_int {x z : ℤ}
    (h : IsCoprime x z) : IsCoprime x (x - z) := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u + v, -v, ?_⟩
  calc
    (u + v) * x + (-v) * (x - z) = u * x + v * z := by ring
    _ = 1 := huv

theorem euler_left_cofactor_coprime_A
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) A := by
  apply IsRelPrime.isCoprime
  intro d hdF hdA
  have hdF' : d ∣ 16 * A ^ 2 + D ^ 2 := hdF
  have hdA2 : d ∣ A ^ 2 := dvd_sq_of_dvd hdA
  have hd16A2 : d ∣ 16 * A ^ 2 := dvd_mul_of_dvd_right hdA2 16
  have hdD2 : d ∣ D ^ 2 := by
    have hsub : d ∣ (16 * A ^ 2 + D ^ 2) - 16 * A ^ 2 :=
      dvd_sub hdF' hd16A2
    convert hsub using 1
    ring
  exact (hAD.pow_right (n := 2)).isUnit_of_dvd' hdA hdD2

theorem euler_left_cofactor_coprime_A_sq
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (A ^ 2) :=
  (euler_left_cofactor_coprime_A hAD).pow_right (n := 2)

theorem euler_left_cofactor_odd {A D : ℤ} (hDodd : Odd D) :
    Odd (16 * A ^ 2 + D ^ 2) := by
  have hEven16 : Even (16 : ℤ) := by norm_num
  have hEven : Even (16 * A ^ 2) := hEven16.mul_right _
  exact hEven.add_odd hDodd.pow

theorem euler_left_cofactor_coprime_four
    {A D : ℤ} (hDodd : Odd D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 : ℤ) := by
  have hF2 : IsCoprime (16 * A ^ 2 + D ^ 2) (2 : ℤ) :=
    (Int.isCoprime_two_right).mpr (euler_left_cofactor_odd hDodd)
  have hpow := hF2.pow_right (n := 2)
  norm_num at hpow ⊢
  exact hpow

theorem euler_left_cofactor_coprime_three
    {A D : ℤ} (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (3 : ℤ) := by
  have hnot : ¬ (3 : ℤ) ∣ 16 * A ^ 2 + D ^ 2 := by
    intro h3F
    have hF0 : ((16 * A ^ 2 + D ^ 2 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 h3F
    have hsum :
        (A : ZMod 3) ^ 2 + (D : ZMod 3) ^ 2 = 0 := by
      simpa [zmod3_natCast_16_eq_one] using hF0
    obtain ⟨hA0, hD0⟩ := zmod3_sq_add_sq_eq_zero hsum
    have h3A : (3 : ℤ) ∣ A :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd A 3).1 hA0
    have h3D : (3 : ℤ) ∣ D :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd D 3).1 hD0
    have hunit : IsUnit (3 : ℤ) := hAD.isUnit_of_dvd' h3A h3D
    norm_num [Int.isUnit_iff] at hunit
  exact (isCoprime_three_int_of_not_dvd hnot).symm

theorem euler_left_cofactor_coprime_twelve_mul_A_sq
    {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (12 * A ^ 2) := by
  have hA2 :
      IsCoprime (16 * A ^ 2 + D ^ 2) (A ^ 2) :=
    euler_left_cofactor_coprime_A_sq hAD
  have h4 :
      IsCoprime (16 * A ^ 2 + D ^ 2) (4 : ℤ) :=
    euler_left_cofactor_coprime_four hDodd
  have h3 :
      IsCoprime (16 * A ^ 2 + D ^ 2) (3 : ℤ) :=
    euler_left_cofactor_coprime_three hAD
  have h12 :
      IsCoprime (16 * A ^ 2 + D ^ 2) ((4 : ℤ) * 3) :=
    h4.mul_right h3
  have h12' :
      IsCoprime (16 * A ^ 2 + D ^ 2) (12 : ℤ) := by
    simpa using h12
  have h :
      IsCoprime (16 * A ^ 2 + D ^ 2) ((12 : ℤ) * A ^ 2) :=
    h12'.mul_right hA2
  simpa using h

theorem euler_cofactor_coprime
    {A D : ℤ}
    (hDodd : Odd D)
    (hAD : IsCoprime A D) :
    IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) := by
  have hF12A :
      IsCoprime (16 * A ^ 2 + D ^ 2) (12 * A ^ 2) :=
    euler_left_cofactor_coprime_twelve_mul_A_sq hDodd hAD
  have h := isCoprime_self_sub_right_int hF12A
  convert h using 1
  ring

theorem exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    {x y z : ℤ}
    (hxpos : 0 < x)
    (hypos : 0 < y)
    (hxy : IsCoprime x y)
    (hprod : z ^ 2 = x * y) :
    ∃ r s : ℤ, 0 < r ∧ 0 < s ∧ r ^ 2 = x ∧ s ^ 2 = y := by
  have hx : ∃ r : ℤ, r ^ 2 = x :=
    square_of_positive_coprime_product_square hxpos hxy hprod.symm
  have hy : ∃ s : ℤ, s ^ 2 = y :=
    square_of_positive_coprime_product_square hypos hxy.symm
      (by simpa [mul_comm] using hprod.symm)
  rcases hx with ⟨r, hr⟩
  rcases hy with ⟨s, hs⟩
  refine ⟨|r|, |s|, ?_, ?_, ?_, ?_⟩
  · rw [abs_pos]
    intro hr0
    rw [hr0] at hr
    nlinarith [hr, hxpos]
  · rw [abs_pos]
    intro hs0
    rw [hs0] at hs
    nlinarith [hs, hypos]
  · simpa [sq_abs] using hr
  · simpa [sq_abs] using hs

theorem euler_cofactors_are_squares_of_center_square
    {A D X : ℤ}
    (hApos : 0 < A)
    (hDpos : 0 < D)
    (hDodd : Odd D)
    (hAD : IsCoprime A D)
    (hXsq :
      X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)) :
    ∃ B C : ℤ,
      0 < B ∧ 0 < C ∧
        B ^ 2 = 16 * A ^ 2 + D ^ 2 ∧
          C ^ 2 = 4 * A ^ 2 + D ^ 2 := by
  have hLpos : 0 < 16 * A ^ 2 + D ^ 2 := by
    have hAne : A ≠ 0 := ne_of_gt hApos
    nlinarith [sq_nonneg A, sq_pos_of_ne_zero (ne_of_gt hDpos)]
  have hRpos : 0 < 4 * A ^ 2 + D ^ 2 := by
    nlinarith [sq_nonneg A, sq_pos_of_ne_zero (ne_of_gt hDpos)]
  have hcop :
      IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) :=
    euler_cofactor_coprime hDodd hAD
  exact exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    hLpos hRpos hcop hXsq

end EulerSquarePair

/-- The product of the two Euler cofactors is the centered AP center square
once the large Pythagorean-triple parameters split as `8*A^2` and `D^2`. -/
theorem center_square_eq_euler_cofactor_product_of_big_split
    {X N m n A D : ℤ}
    (hZ : X ^ 2 - 20 * N ^ 2 = m ^ 2 + n ^ 2)
    (hN : N = A * D)
    (hsplit :
      (m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
        (m = D ^ 2 ∧ n = 8 * A ^ 2)) :
    X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) := by
  rcases hsplit with hsplit | hsplit
  · rcases hsplit with ⟨hm, hn⟩
    rw [hN, hm, hn] at hZ
    ring_nf at hZ ⊢
    nlinarith [hZ]
  · rcases hsplit with ⟨hm, hn⟩
    rw [hN, hm, hn] at hZ
    ring_nf at hZ ⊢
    nlinarith [hZ]

/-- First hard Euler-descent interface: convert a primitive centered AP to a
concordant-form square pair with the same positive parameter product. -/
def PrimitiveCenteredToEulerSquarePair : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ E : EulerSquarePair, S.N = E.A * E.D

theorem primitiveCenteredToEulerSquarePair_constructive
    (S : PrimitiveCenteredFourSqAP) :
    ∃ E : EulerSquarePair, S.N = E.A * E.D := by
  obtain ⟨m, n, hroot, hprod, hcenter, hmn_gcd, hparity, hm_nonneg⟩ :=
    (primitiveCentered_big_pyth_triple S).coprime_classification'
      (primitiveCentered_big_triple_coprime S)
      (primitiveCenteredRootProduct_mod_two S)
      (primitiveCentered_big_hyp_pos S)
  have hmn8 : m * n = 8 * S.N ^ 2 := by
    nlinarith [hprod]
  have hmn_pos : 0 < m * n := by
    have hNsq_pos : 0 < S.N ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt S.hNpos)
    nlinarith [hmn8, hNsq_pos]
  have hm_ne : m ≠ 0 := by
    intro hm0
    rw [hm0] at hmn_pos
    norm_num at hmn_pos
  have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg hm_ne.symm
  have hn_pos : 0 < n := by
    have hnm_pos : 0 < n * m := by
      simpa [mul_comm] using hmn_pos
    exact pos_of_mul_pos_left hnm_pos (le_of_lt hm_pos)
  obtain ⟨A, D, hApos, hDpos, hAeven, hDodd, hADcop, hNAD, hsplit⟩ :=
    coprime_product_eq_eight_square_split_int
      (hNpos := S.hNpos)
      (hNeven := primitiveCentered_N_even S)
      (hmpos := hm_pos)
      (hnpos := hn_pos)
      (hmn := hmn8)
      (hmn_coprime := hmn_gcd)
      (hparity := hparity)
  have hXsq :
      S.X ^ 2 =
        (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2) :=
    center_square_eq_euler_cofactor_product_of_big_split
      (X := S.X) (N := S.N) (m := m) (n := n) (A := A) (D := D)
      hcenter hNAD hsplit
  obtain ⟨B, C, hBpos, hCpos, hB, hC⟩ :=
    EulerSquarePair.euler_cofactors_are_squares_of_center_square
      hApos hDpos hDodd hADcop hXsq
  refine ⟨
    { A := A
      D := D
      B := B
      C := C
      hApos := hApos
      hDpos := hDpos
      hDodd := hDodd
      hAeven := hAeven
      hADcop := hADcop
      hBpos := hBpos
      hCpos := hCpos
      hB := hB
      hC := hC },
    hNAD⟩

theorem primitiveCenteredToEulerSquarePair :
    PrimitiveCenteredToEulerSquarePair :=
  primitiveCenteredToEulerSquarePair_constructive

private lemma int_natAbs_mul_eq_of_eq
    {U V Up Vp : ℤ} (hEq : U * V = Up * Vp) :
    U.natAbs * V.natAbs = Up.natAbs * Vp.natAbs := by
  simpa [Int.natAbs_mul] using congrArg Int.natAbs hEq

private lemma natAbs_cast_of_pos {x : ℤ} (hx : 0 < x) :
    (x.natAbs : ℤ) = x :=
  Int.natAbs_of_nonneg (le_of_lt hx)

private lemma natAbs_pos_of_pos {x : ℤ} (hx : 0 < x) :
    0 < x.natAbs := by
  have hx' : (0 : ℤ) < (x.natAbs : ℤ) := by
    rw [natAbs_cast_of_pos hx]
    exact hx
  exact_mod_cast hx'

private lemma odd_left_of_odd_mul_nat {a b : ℕ}
    (h : Odd (a * b)) : Odd a := by
  by_contra ha
  have hae : Even a := Nat.not_odd_iff_even.mp ha
  have he : Even (a * b) := hae.mul_right b
  exact (Nat.not_even_iff_odd.mpr h) he

private lemma odd_right_of_odd_mul_nat {a b : ℕ}
    (h : Odd (a * b)) : Odd b := by
  have h' : Odd (b * a) := by simpa [mul_comm] using h
  exact odd_left_of_odd_mul_nat h'

private lemma even_left_of_even_mul_odd_nat {a b : ℕ}
    (hab : Even (a * b)) (hb : Odd b) : Even a := by
  by_contra ha
  have haodd : Odd a := Nat.not_even_iff_odd.mp ha
  have hodd : Odd (a * b) := haodd.mul hb
  exact (Nat.not_even_iff_odd.mpr hodd) hab

private lemma odd_factors_of_odd_mul_int {x y : ℤ}
    (hxy : Odd (x * y)) : Odd x ∧ Odd y :=
  Int.odd_mul.mp hxy

private lemma even_left_of_even_mul_odd_int {x y : ℤ}
    (hxy : Even (x * y)) (hy : Odd y) : Even x := by
  by_contra hx
  have hxodd : Odd x := Int.not_even_iff_odd.mp hx
  have hodd : Odd (x * y) := hxodd.mul hy
  exact (Int.not_odd_iff_even.mpr hxy) hodd

private lemma even_pos_as_two_mul {k : ℤ}
    (hkpos : 0 < k) (hkeven : Even k) :
    ∃ a : ℤ, 0 < a ∧ k = 2 * a := by
  rcases hkeven with ⟨a, ha⟩
  refine ⟨a, ?_, ?_⟩ <;> nlinarith

private lemma coprime_of_coprime_two_mul_left {a d : ℤ}
    (h : IsCoprime (2 * a) d) : IsCoprime a d :=
  h.of_mul_left_right

private theorem two_coprime_factorizations_refine_int_pos
    {U V Up Vp : ℤ}
    (hUpos : 0 < U)
    (hVpos : 0 < V)
    (hUppos : 0 < Up)
    (hVppos : 0 < Vp)
    (hUV : IsCoprime U V)
    (hUpVp : IsCoprime Up Vp)
    (hprod : U * V = Up * Vp) :
    ∃ k b c d : ℤ,
      0 < k ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
        U = k * b ∧ V = c * d ∧ Up = k * c ∧ Vp = b * d ∧
          IsCoprime k b ∧ IsCoprime k c ∧ IsCoprime k d ∧
            IsCoprime b c ∧ IsCoprime b d ∧ IsCoprime c d := by
  have hEqNat :
      U.natAbs * V.natAbs = Up.natAbs * Vp.natAbs :=
    int_natAbs_mul_eq_of_eq hprod
  have hUVNat : Nat.Coprime U.natAbs V.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hUV
  have hUpVpNat : Nat.Coprime Up.natAbs Vp.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hUpVp
  obtain ⟨k, b, c, d, hkpos, hbpos, hcpos, hdpos,
      hUeq, hVeq, hUpeq, hVpeq, hkb, hkc, hkd, hbc, hbd, hcd⟩ :=
    EulerSquarePair.two_coprime_factorizations_refine_nat
      (natAbs_pos_of_pos hUpos) (natAbs_pos_of_pos hVpos)
      hEqNat hUVNat hUpVpNat
  refine ⟨(k : ℤ), (b : ℤ), (c : ℤ), (d : ℤ),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hkpos
  · exact_mod_cast hbpos
  · exact_mod_cast hcpos
  · exact_mod_cast hdpos
  · calc
      U = (U.natAbs : ℤ) := (natAbs_cast_of_pos hUpos).symm
      _ = ((k * b : ℕ) : ℤ) := by exact_mod_cast hUeq
      _ = (k : ℤ) * (b : ℤ) := by norm_num
  · calc
      V = (V.natAbs : ℤ) := (natAbs_cast_of_pos hVpos).symm
      _ = ((c * d : ℕ) : ℤ) := by exact_mod_cast hVeq
      _ = (c : ℤ) * (d : ℤ) := by norm_num
  · calc
      Up = (Up.natAbs : ℤ) := (natAbs_cast_of_pos hUppos).symm
      _ = ((k * c : ℕ) : ℤ) := by exact_mod_cast hUpeq
      _ = (k : ℤ) * (c : ℤ) := by norm_num
  · calc
      Vp = (Vp.natAbs : ℤ) := (natAbs_cast_of_pos hVppos).symm
      _ = ((b * d : ℕ) : ℤ) := by exact_mod_cast hVpeq
      _ = (b : ℤ) * (d : ℤ) := by norm_num
  · exact Nat.Coprime.isCoprime hkb
  · exact Nat.Coprime.isCoprime hkc
  · exact Nat.Coprime.isCoprime hkd
  · exact Nat.Coprime.isCoprime hbc
  · exact Nat.Coprime.isCoprime hbd
  · exact Nat.Coprime.isCoprime hcd

private lemma cofactor_coprime_for_descent
    {a d : ℤ}
    (hdodd : Odd d)
    (had : IsCoprime a d) :
    IsCoprime (4 * a ^ 2 + d ^ 2) (16 * a ^ 2 + d ^ 2) :=
  (EulerSquarePair.euler_cofactor_coprime hdodd had).symm

private lemma pos_four_sq_add_sq_of_pos_right {a d : ℤ}
    (hdpos : 0 < d) : 0 < 4 * a ^ 2 + d ^ 2 := by
  nlinarith [sq_nonneg a, sq_pos_of_ne_zero (ne_of_gt hdpos)]

private lemma pos_sixteen_sq_add_sq_of_pos_right {a d : ℤ}
    (hdpos : 0 < d) : 0 < 16 * a ^ 2 + d ^ 2 := by
  nlinarith [sq_nonneg a, sq_pos_of_ne_zero (ne_of_gt hdpos)]

private lemma even_of_descent_balance
    {a b c d : ℤ}
    (hb : Odd b) (hc : Odd c) (hd : Odd d)
    (h :
      b ^ 2 * (4 * a ^ 2 + d ^ 2) =
        c ^ 2 * (16 * a ^ 2 + d ^ 2)) :
    Even a := by
  by_contra haNot
  have haOdd : Odd a := Int.not_even_iff_odd.mp haNot
  rcases primitiveCentered_sq_eq_eight_mul_add_one_of_odd haOdd with ⟨A, hA⟩
  rcases primitiveCentered_sq_eq_eight_mul_add_one_of_odd hb with ⟨B, hB⟩
  rcases primitiveCentered_sq_eq_eight_mul_add_one_of_odd hc with ⟨C, hC⟩
  rcases primitiveCentered_sq_eq_eight_mul_add_one_of_odd hd with ⟨D, hD⟩
  rw [hA, hB, hC, hD] at h
  ring_nf at h
  omega

private lemma descent_product_lt
    {EA ED a b c d : ℤ}
    (hapos : 0 < a) (hbpos : 0 < b)
    (hcpos : 0 < c) (hdpos : 0 < d)
    (hEDpos : 0 < ED)
    (hEA : EA = 2 * a * b * c * d) :
    a * d < EA * ED := by
  have hadpos : 0 < a * d := mul_pos hapos hdpos
  have hbcpos : 0 < b * c := mul_pos hbpos hcpos
  have hbcEDpos : 0 < b * c * ED := mul_pos hbcpos hEDpos
  have hfactor : 1 < 2 * (b * c * ED) := by
    have hge : (1 : ℤ) ≤ b * c * ED := by omega
    nlinarith
  calc
    a * d = 1 * (a * d) := by ring
    _ < (2 * (b * c * ED)) * (a * d) :=
      mul_lt_mul_of_pos_right hfactor hadpos
    _ = (2 * a * b * c * d) * ED := by ring
    _ = EA * ED := by rw [hEA]

/-- Second hard Euler-descent interface: descend a concordant-form square pair
to a smaller one. -/
def EulerSquarePairDescent : Prop :=
  ∀ E : EulerSquarePair,
    ∃ F : EulerSquarePair, F.A * F.D < E.A * E.D

theorem eulerSquarePairDescent_constructive :
    EulerSquarePairDescent := by
  intro E
  obtain ⟨U, V, Up, Vp,
      hUpos, hVpos, hUppos, hVppos,
      hUVcop, hUpVpcop,
      hUeven, hVodd, hUpeven, hVpodd,
      hEA_UV, hEA_UpVp,
      _hCparam, _hBparam,
      horient⟩ :=
    EulerSquarePair.signed_even_odd_params_same_orientation E
  have hprod : U * V = Up * Vp :=
    hEA_UV.symm.trans hEA_UpVp
  obtain ⟨k, b, c, d,
      hkpos, hbpos, hcpos, hdpos,
      hUfac, hVfac, hUpfac, hVpfac,
      _hkb, _hkc, hkd, hbc, _hbd, _hcd⟩ :=
    two_coprime_factorizations_refine_int_pos
      hUpos hVpos hUppos hVppos hUVcop hUpVpcop hprod
  have hcdOdd : Odd (c * d) := by
    rw [← hVfac]
    exact hVodd
  obtain ⟨hcOdd, hdOdd⟩ := odd_factors_of_odd_mul_int hcdOdd
  have hbdOdd : Odd (b * d) := by
    rw [← hVpfac]
    exact hVpodd
  obtain ⟨hbOdd, _⟩ := odd_factors_of_odd_mul_int hbdOdd
  have hkEven : Even k := by
    have hkbEven : Even (k * b) := by
      rw [← hUfac]
      exact hUeven
    exact even_left_of_even_mul_odd_int hkbEven hbOdd
  obtain ⟨a, hapos, hk_eq⟩ := even_pos_as_two_mul hkpos hkEven
  have hUfac' : U = 2 * a * b := by
    calc
      U = k * b := hUfac
      _ = (2 * a) * b := by rw [hk_eq]
      _ = 2 * a * b := by ring
  have hUpfac' : Up = 2 * a * c := by
    calc
      Up = k * c := hUpfac
      _ = (2 * a) * c := by rw [hk_eq]
      _ = 2 * a * c := by ring
  have hEA_prod : E.A = 2 * a * b * c * d := by
    calc
      E.A = U * V := hEA_UV
      _ = (2 * a * b) * (c * d) := by rw [hUfac', hVfac]
      _ = 2 * a * b * c * d := by ring
  have had : IsCoprime a d := by
    apply coprime_of_coprime_two_mul_left
    simpa [hk_eq] using hkd
  have hbalance :
      b ^ 2 * (4 * a ^ 2 + d ^ 2) =
        c ^ 2 * (16 * a ^ 2 + d ^ 2) :=
    EulerSquarePair.refinement_equation_of_same_orientation
      hUfac' hVfac hUpfac' hVpfac horient
  have haEven : Even a :=
    even_of_descent_balance hbOdd hcOdd hdOdd hbalance
  let M : ℤ := 4 * a ^ 2 + d ^ 2
  let N : ℤ := 16 * a ^ 2 + d ^ 2
  have hMpos : 0 < M := by
    dsimp [M]
    exact pos_four_sq_add_sq_of_pos_right hdpos
  have hNpos : 0 < N := by
    dsimp [N]
    exact pos_sixteen_sq_add_sq_of_pos_right hdpos
  have hMNcop : IsCoprime M N := by
    dsimp [M, N]
    exact cofactor_coprime_for_descent hdOdd had
  have hbalanceMN : b ^ 2 * M = c ^ 2 * N := by
    dsimp [M, N]
    exact hbalance
  obtain ⟨hM_eq_csq, hN_eq_bsq⟩ :=
    square_factor_balance_int
      hbpos hcpos hMpos hNpos hbc hMNcop hbalanceMN
  have hCsq : c ^ 2 = 4 * a ^ 2 + d ^ 2 := by
    dsimp [M] at hM_eq_csq
    exact hM_eq_csq.symm
  have hBsq : b ^ 2 = 16 * a ^ 2 + d ^ 2 := by
    dsimp [N] at hN_eq_bsq
    exact hN_eq_bsq.symm
  refine ⟨
    { A := a
      D := d
      B := b
      C := c
      hApos := hapos
      hDpos := hdpos
      hDodd := hdOdd
      hAeven := haEven
      hADcop := had
      hBpos := hbpos
      hCpos := hcpos
      hB := hBsq
      hC := hCsq },
    ?_⟩
  exact descent_product_lt hapos hbpos hcpos hdpos E.hDpos hEA_prod

theorem eulerSquarePairDescent :
    EulerSquarePairDescent :=
  eulerSquarePairDescent_constructive

/-- Third hard Euler-descent interface: reconstruct a primitive centered AP
from a concordant-form square pair. -/
def EulerSquarePairToPrimitiveCentered : Prop :=
  ∀ E : EulerSquarePair,
    ∃ T : PrimitiveCenteredFourSqAP, T.N = E.A * E.D

theorem eulerSquarePairToPrimitiveCentered :
    EulerSquarePairToPrimitiveCentered :=
  EulerSquarePair.eulerSquarePairToPrimitiveCentered_constructive

/-- Descent residual on primitive centered APs. -/
def PrimitiveCenteredFourSqAPDescent : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ T : PrimitiveCenteredFourSqAP, T.N.natAbs < S.N.natAbs

private theorem int_natAbs_lt_natAbs_of_pos_lt {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b) (h : a < b) :
    a.natAbs < b.natAbs := by
  have haAbs : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg (le_of_lt ha)
  have hbAbs : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg (le_of_lt hb)
  have hcast : (a.natAbs : ℤ) < (b.natAbs : ℤ) := by
    simpa [haAbs, hbAbs] using h
  exact_mod_cast hcast

/-- The Euler/concordant-form interfaces compose to the primitive-centered AP
descent residual. -/
theorem primitiveCenteredFourSqAPDescent_of_eulerSquarePair_dag
    (hto : PrimitiveCenteredToEulerSquarePair)
    (hstep : EulerSquarePairDescent)
    (hfrom : EulerSquarePairToPrimitiveCentered) :
    PrimitiveCenteredFourSqAPDescent := by
  intro S
  rcases hto S with ⟨E, hSN⟩
  rcases hstep E with ⟨F, hFE⟩
  rcases hfrom F with ⟨T, hTN⟩
  refine ⟨T, ?_⟩
  have hTltS : T.N < S.N := by
    nlinarith [hTN, hSN, hFE]
  exact int_natAbs_lt_natAbs_of_pos_lt T.hNpos S.hNpos hTltS

theorem primitiveCenteredFourSqAPDescent_of_eulerSquarePair_to_descent
    (hto : PrimitiveCenteredToEulerSquarePair)
    (hstep : EulerSquarePairDescent) :
    PrimitiveCenteredFourSqAPDescent :=
  primitiveCenteredFourSqAPDescent_of_eulerSquarePair_dag
    hto hstep eulerSquarePairToPrimitiveCentered

theorem primitiveCenteredFourSqAPDescent_checked :
    PrimitiveCenteredFourSqAPDescent :=
  primitiveCenteredFourSqAPDescent_of_eulerSquarePair_to_descent
    primitiveCenteredToEulerSquarePair
    eulerSquarePairDescent

/-- Residual normalization from an arbitrary nonconstant integer AP to a weak
primitive centered AP. -/
def ArbitraryAPToWeakPrimitiveCentered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
      Nonempty WeakPrimitiveCenteredFourSqAP

/-- Residual normalization from an arbitrary nonconstant integer AP to a
primitive centered AP. -/
def ArbitraryAPToPrimitiveCentered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
      Nonempty PrimitiveCenteredFourSqAP

/-- Residual package turning a weak primitive centered AP into the strong
pairwise-coprime, odd-root package. -/
def WeakPrimitiveCenteredToStrong : Prop :=
  ∀ _ : WeakPrimitiveCenteredFourSqAP, Nonempty PrimitiveCenteredFourSqAP

/-- Divide a positive-difference AP by the common root gcd. -/
def RootGCD4Division : Prop :=
  ∀ {w x y z Δ : ℤ},
    0 < Δ →
    x ^ 2 - w ^ 2 = Δ →
    y ^ 2 - x ^ 2 = Δ →
    z ^ 2 - y ^ 2 = Δ →
      ∃ g p q r s Δ' : ℤ,
        0 < g ∧ 0 < Δ' ∧
        w = g * p ∧ x = g * q ∧ y = g * r ∧ z = g * s ∧
        q ^ 2 - p ^ 2 = Δ' ∧
        r ^ 2 - q ^ 2 = Δ' ∧
        s ^ 2 - r ^ 2 = Δ' ∧
        rootGCD4 p q r s = 1

/-- The root-gcd division residual for a positive-difference four-square AP is
an elementary consequence of dividing the four roots by their common gcd. -/
theorem rootGCD4Division : RootGCD4Division := by
  intro w x y z Δ hΔpos hxw hyx hzy
  let gn : ℕ := rootGCD4 w x y z
  let g : ℤ := (gn : ℤ)
  let p : ℤ := w / g
  let q : ℤ := x / g
  let r : ℤ := y / g
  let s : ℤ := z / g
  let Δ' : ℤ := Δ / (g ^ 2)
  have hgnpos : 0 < gn := by
    dsimp [gn]
    exact rootGCD4_pos_of_first_gap hΔpos hxw
  have hgpos : 0 < g := by
    dsimp [g]
    exact_mod_cast hgnpos
  have hgw : g ∣ w := by
    simpa [g, gn] using rootGCD4_intCast_dvd_left w x y z
  have hgx : g ∣ x := by
    simpa [g, gn] using rootGCD4_intCast_dvd_second w x y z
  have hgy : g ∣ y := by
    simpa [g, gn] using rootGCD4_intCast_dvd_third w x y z
  have hgz : g ∣ z := by
    simpa [g, gn] using rootGCD4_intCast_dvd_fourth w x y z
  have hw : w = g * p := by
    dsimp [p]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgw).symm
  have hx : x = g * q := by
    dsimp [q]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgx).symm
  have hy : y = g * r := by
    dsimp [r]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgy).symm
  have hz : z = g * s := by
    dsimp [s]
    simpa [mul_comm] using (Int.ediv_mul_cancel hgz).symm
  have hΔdvd : g ^ 2 ∣ Δ := by
    simpa [g, gn] using
      rootGCD4_sq_dvd_delta_of_first_gap
        (w := w) (x := x) (y := y) (z := z) hxw
  have hΔscale : Δ = g ^ 2 * Δ' := by
    dsimp [Δ']
    simpa [mul_comm] using (Int.ediv_mul_cancel hΔdvd).symm
  have hΔ'pos : 0 < Δ' := by
    have hprod : 0 < g ^ 2 * Δ' := by
      simpa [hΔscale] using hΔpos
    have hprod' : 0 < Δ' * g ^ 2 := by
      simpa [mul_comm] using hprod
    exact pos_of_mul_pos_left hprod' (sq_nonneg g)
  have hpq : q ^ 2 - p ^ 2 = Δ' := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hgpos))
    calc
      g ^ 2 * (q ^ 2 - p ^ 2) = (g * q) ^ 2 - (g * p) ^ 2 := by ring
      _ = x ^ 2 - w ^ 2 := by rw [← hx, ← hw]
      _ = Δ := hxw
      _ = g ^ 2 * Δ' := hΔscale
  have hrq : r ^ 2 - q ^ 2 = Δ' := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hgpos))
    calc
      g ^ 2 * (r ^ 2 - q ^ 2) = (g * r) ^ 2 - (g * q) ^ 2 := by ring
      _ = y ^ 2 - x ^ 2 := by rw [← hy, ← hx]
      _ = Δ := hyx
      _ = g ^ 2 * Δ' := hΔscale
  have hsr : s ^ 2 - r ^ 2 = Δ' := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hgpos))
    calc
      g ^ 2 * (s ^ 2 - r ^ 2) = (g * s) ^ 2 - (g * r) ^ 2 := by ring
      _ = z ^ 2 - y ^ 2 := by rw [← hz, ← hy]
      _ = Δ := hzy
      _ = g ^ 2 * Δ' := hΔscale
  have hprim : rootGCD4 p q r s = 1 :=
    rootGCD4_eq_one_of_common_factor
      (g := gn) (w := w) (x := x) (y := y) (z := z)
      (p := p) (q := q) (r := r) (s := s)
      hgnpos rfl
      (by simpa [g] using hw)
      (by simpa [g] using hx)
      (by simpa [g] using hy)
      (by simpa [g] using hz)
  exact ⟨g, p, q, r, s, Δ', hgpos, hΔ'pos,
    hw, hx, hy, hz, hpq, hrq, hsr, hprim⟩

/-- Parity residual for weak primitive AP roots. -/
def WeakPrimitiveAPParity : Prop :=
  ∀ {p q r s Δ : ℤ},
    q ^ 2 - p ^ 2 = Δ →
    r ^ 2 - q ^ 2 = Δ →
    s ^ 2 - r ^ 2 = Δ →
    rootGCD4 p q r s = 1 →
      p % 2 = 1 ∧ q % 2 = 1 ∧ r % 2 = 1 ∧ s % 2 = 1 ∧
        (8 : ℤ) ∣ Δ

private theorem n12_sq_eq_four_mul_of_even {n : ℤ} (hn : Even n) :
    ∃ k : ℤ, n ^ 2 = 4 * k := by
  rcases hn with ⟨t, rfl⟩
  refine ⟨t ^ 2, ?_⟩
  ring

private theorem n12_sq_eq_four_mul_add_one_of_odd {n : ℤ} (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 4 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  refine ⟨t ^ 2 + t, ?_⟩
  ring

private theorem n12_sq_eq_eight_mul_add_one_of_odd {n : ℤ} (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  rcases Int.two_dvd_mul_add_one t with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
    _ = 4 * (2 * u) + 1 := by rw [hu]
    _ = 8 * u + 1 := by ring

private theorem n12_eight_dvd_sq_sub_sq_of_odd {a b : ℤ}
    (ha : Odd a) (hb : Odd b) :
    (8 : ℤ) ∣ a ^ 2 - b ^ 2 := by
  rcases n12_sq_eq_eight_mul_add_one_of_odd ha with ⟨A, hA⟩
  rcases n12_sq_eq_eight_mul_add_one_of_odd hb with ⟨B, hB⟩
  refine ⟨A - B, ?_⟩
  rw [hA, hB]
  ring

/-- In a three-square AP, the three roots have uniform parity. -/
private theorem n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq
    {a b c : ℤ}
    (h : a ^ 2 + c ^ 2 = 2 * b ^ 2) :
    (Odd a ∧ Odd b ∧ Odd c) ∨ (Even a ∧ Even b ∧ Even c) := by
  rcases Int.even_or_odd a with haEven | haOdd
  · rcases Int.even_or_odd b with hbEven | hbOdd
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exact Or.inr ⟨haEven, hbEven, hcEven⟩
      · exfalso
        rcases n12_sq_eq_four_mul_of_even haEven with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_of_even hbEven with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hcOdd with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exfalso
        rcases n12_sq_eq_four_mul_of_even haEven with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hbOdd with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_of_even hcEven with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
      · exfalso
        rcases n12_sq_eq_four_mul_of_even haEven with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hbOdd with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hcOdd with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
  · rcases Int.even_or_odd b with hbEven | hbOdd
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exfalso
        rcases n12_sq_eq_four_mul_add_one_of_odd haOdd with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_of_even hbEven with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_of_even hcEven with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
      · exfalso
        rcases n12_sq_eq_four_mul_add_one_of_odd haOdd with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_of_even hbEven with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hcOdd with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exfalso
        rcases n12_sq_eq_four_mul_add_one_of_odd haOdd with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hbOdd with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_of_even hcEven with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
      · exact Or.inl ⟨haOdd, hbOdd, hcOdd⟩

private theorem n12_rootGCD4_ne_one_of_all_even {p q r s : ℤ}
    (hp : Even p) (hq : Even q) (hr : Even r) (hs : Even s) :
    rootGCD4 p q r s ≠ 1 := by
  have h2p : 2 ∣ p.natAbs := by
    have hpAbs : Even p.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hpAbs
  have h2q : 2 ∣ q.natAbs := by
    have hqAbs : Even q.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hqAbs
  have h2r : 2 ∣ r.natAbs := by
    have hrAbs : Even r.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hrAbs
  have h2s : 2 ∣ s.natAbs := by
    have hsAbs : Even s.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hsAbs
  have h2g : 2 ∣ rootGCD4 p q r s :=
    dvd_rootGCD4 h2p h2q h2r h2s
  intro hprim
  have hbad : (2 : ℕ) ∣ 1 := by
    rw [hprim] at h2g
    exact h2g
  norm_num at hbad

/-- Weak primitive four-square APs have odd roots and square gap divisible by
`8`. -/
theorem weakPrimitiveAPParity : WeakPrimitiveAPParity := by
  intro p q r s Δ hpq hrq hsr hprim
  have hpqr : p ^ 2 + r ^ 2 = 2 * q ^ 2 := by
    nlinarith [hpq, hrq]
  have hqrs : q ^ 2 + s ^ 2 = 2 * r ^ 2 := by
    nlinarith [hrq, hsr]
  rcases n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq hpqr with hpqrOdd | hpqrEven
  · rcases hpqrOdd with ⟨hpOdd, hqOdd, hrOdd⟩
    rcases n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq hqrs with hqrsOdd | hqrsEven
    · rcases hqrsOdd with ⟨_hqOdd2, _hrOdd2, hsOdd⟩
      have h8 : (8 : ℤ) ∣ Δ := by
        rw [← hpq]
        exact n12_eight_dvd_sq_sub_sq_of_odd hqOdd hpOdd
      exact ⟨Int.odd_iff.mp hpOdd,
        Int.odd_iff.mp hqOdd,
        Int.odd_iff.mp hrOdd,
        Int.odd_iff.mp hsOdd,
        h8⟩
    · rcases hqrsEven with ⟨hqEven2, _hrEven2, _hsEven⟩
      exfalso
      exact (Int.not_even_iff_odd.mpr hqOdd) hqEven2
  · rcases hpqrEven with ⟨hpEven, hqEven, hrEven⟩
    rcases n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq hqrs with hqrsOdd | hqrsEven
    · rcases hqrsOdd with ⟨hqOdd2, _hrOdd2, _hsOdd⟩
      exfalso
      exact (Int.not_even_iff_odd.mpr hqOdd2) hqEven
    · rcases hqrsEven with ⟨_hqEven2, _hrEven2, hsEven⟩
      exfalso
      exact n12_rootGCD4_ne_one_of_all_even hpEven hqEven hrEven hsEven hprim

/-- A natural divisor of `x.natAbs` is the same as its integer cast dividing
`x`. -/
theorem nat_dvd_natAbs_iff_int_dvd {n : ℕ} {x : ℤ} :
    n ∣ x.natAbs ↔ ((n : ℤ) ∣ x) := by
  exact Int.natCast_dvd.symm

/-- A natural prime dividing all four roots contradicts primitivity. -/
theorem false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
    {p q r s : ℤ} {ℓ : ℕ}
    (hroot : rootGCD4 p q r s = 1)
    (hℓ : ℓ.Prime)
    (hp : ℓ ∣ p.natAbs)
    (hq : ℓ ∣ q.natAbs)
    (hr : ℓ ∣ r.natAbs)
    (hs : ℓ ∣ s.natAbs) :
    False := by
  have hℓroot : ℓ ∣ rootGCD4 p q r s :=
    dvd_rootGCD4 hp hq hr hs
  have hℓone : ℓ ∣ (1 : ℕ) := by
    simpa [hroot] using hℓroot
  have hle : ℓ ≤ 1 := Nat.le_of_dvd (by decide : 0 < (1 : ℕ)) hℓone
  exact (not_lt_of_ge hle) hℓ.one_lt

/-- Adjacent-pair propagation for `(p,q)`: any natural prime dividing `p` and
`q` propagates through the AP equations to all four roots. -/
theorem nat_prime_dvd_all_roots_of_dvd_pq_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hp : ℓ ∣ p.natAbs)
    (hq : ℓ ∣ q.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  have hpZ : ((ℓ : ℤ) ∣ p) := Int.natCast_dvd.mpr hp
  have hqZ : ((ℓ : ℤ) ∣ q) := Int.natCast_dvd.mpr hq
  have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hpZ p
  have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hqZ q
  have hDeltaZ : ((ℓ : ℤ) ∣ Δ) := by
    rw [← hpq]
    exact Int.dvd_sub hq2Z hp2Z
  have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
    have hr_sq : r ^ 2 = q ^ 2 + Δ := by
      nlinarith [hqr]
    rw [hr_sq]
    exact Int.dvd_add hq2Z hDeltaZ
  have hr : ℓ ∣ r.natAbs := Int.Prime.dvd_pow hℓ hr2Z
  have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := by
    have hs_sq : s ^ 2 = r ^ 2 + Δ := by
      nlinarith [hrs]
    rw [hs_sq]
    exact Int.dvd_add hr2Z hDeltaZ
  have hs : ℓ ∣ s.natAbs := Int.Prime.dvd_pow hℓ hs2Z
  exact ⟨hp, hq, hr, hs⟩

/-- The adjacent `(p,q)` gcd is one in a weak primitive AP. -/
theorem int_gcd_pq_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd p q = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hp hq
  rcases nat_prime_dvd_all_roots_of_dvd_pq_weak_ap hℓ hpq hqr hrs hp hq with
    ⟨hp', hq', hr', hs'⟩
  exact False.elim <|
    false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
      hroot hℓ hp' hq' hr' hs'

/-- The local oddness convention `a % 2 = 1` rules out divisibility by `2`. -/
theorem int_odd_mod_two_not_dvd {a : ℤ} (ha : a % 2 = 1) :
    ¬ (2 : ℤ) ∣ a := by
  intro h2a
  have hmodEq : a ≡ 0 [ZMOD (2 : ℤ)] := Int.modEq_zero_iff_dvd.mpr h2a
  have hmod0 : a % 2 = 0 := by
    simpa [Int.ModEq] using hmodEq
  rw [hmod0] at ha
  norm_num at ha

/-- If an odd natural prime divides `2 * Δ`, then it divides `Δ`. -/
theorem natPrime_dvd_of_dvd_two_mul_int_of_ne_two
    {ℓ : ℕ} {Δ : ℤ}
    (hℓprime : Nat.Prime ℓ)
    (hℓne2 : ℓ ≠ 2)
    (hℓtwoΔ : (ℓ : ℤ) ∣ 2 * Δ) :
    (ℓ : ℤ) ∣ Δ := by
  have hcases : (ℓ : ℤ) ∣ (2 : ℤ) ∨ (ℓ : ℤ) ∣ Δ :=
    Int.Prime.dvd_mul' hℓprime hℓtwoΔ
  rcases hcases with hℓtwo | hℓΔ
  · exfalso
    have hℓdvd2Nat : ℓ ∣ (2 : ℕ) := by
      simpa using (Int.natCast_dvd.mp hℓtwo)
    have hℓle2 : ℓ ≤ 2 := Nat.le_of_dvd (by norm_num) hℓdvd2Nat
    have h2leℓ : 2 ≤ ℓ := hℓprime.two_le
    exact hℓne2 (le_antisymm hℓle2 h2leℓ)
  · exact hℓΔ

/-- Distance-two propagation for `(p,r)`: any odd natural prime dividing both
`p` and `r` propagates through the AP equations to all four roots. -/
theorem nat_prime_dvd_all_roots_of_dvd_pr_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hℓne2 : ℓ ≠ 2)
    (hp : ℓ ∣ p.natAbs)
    (hr : ℓ ∣ r.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  have hpZ : ((ℓ : ℤ) ∣ p) := Int.natCast_dvd.mpr hp
  have hrZ : ((ℓ : ℤ) ∣ r) := Int.natCast_dvd.mpr hr
  have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hpZ p
  have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hrZ r
  have hℓ_r2_sub_p2 : (ℓ : ℤ) ∣ r ^ 2 - p ^ 2 :=
    Int.dvd_sub hr2Z hp2Z
  have hrp_twoDelta : r ^ 2 - p ^ 2 = 2 * Δ := by
    nlinarith [hpq, hqr]
  have hℓ_twoDelta : (ℓ : ℤ) ∣ 2 * Δ := by
    rwa [hrp_twoDelta] at hℓ_r2_sub_p2
  have hℓΔ : (ℓ : ℤ) ∣ Δ :=
    natPrime_dvd_of_dvd_two_mul_int_of_ne_two hℓ hℓne2 hℓ_twoDelta
  have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := by
    have hq_sq : q ^ 2 = p ^ 2 + Δ := by
      nlinarith [hpq]
    rw [hq_sq]
    exact Int.dvd_add hp2Z hℓΔ
  have hq : ℓ ∣ q.natAbs := Int.Prime.dvd_pow hℓ hq2Z
  have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := by
    have hs_sq : s ^ 2 = r ^ 2 + Δ := by
      nlinarith [hrs]
    rw [hs_sq]
    exact Int.dvd_add hr2Z hℓΔ
  have hs : ℓ ∣ s.natAbs := Int.Prime.dvd_pow hℓ hs2Z
  exact ⟨hp, hq, hr, hs⟩

/-- The distance-two `(p,r)` gcd is one in a weak primitive AP. -/
theorem int_gcd_pr_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1)
    (hp_odd : p % 2 = 1) :
    Int.gcd p r = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hp hr
  by_cases hℓeq2 : ℓ = 2
  · subst ℓ
    exact False.elim (int_odd_mod_two_not_dvd hp_odd (Int.natCast_dvd.mpr hp))
  · rcases nat_prime_dvd_all_roots_of_dvd_pr_weak_ap
      hℓ hpq hqr hrs hℓeq2 hp hr with
      ⟨hp', hq', hr', hs'⟩
    exact False.elim <|
      false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
        hroot hℓ hp' hq' hr' hs'

/-- If a natural prime divides integer `3`, then it is `3`. -/
theorem nat_prime_eq_three_of_int_dvd_three
    {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ((ℓ : ℤ) ∣ (3 : ℤ))) :
    ℓ = 3 := by
  have hNat : ℓ ∣ (3 : ℕ) := by
    simpa using (Int.natCast_dvd.mp h)
  rcases (Nat.dvd_prime Nat.prime_three).mp hNat with h1 | h3
  · exact False.elim (hℓ.ne_one h1)
  · exact h3

/-- In `ZMod 3`, if endpoint square roots vanish in a four-square AP, the
middle roots vanish too. -/
theorem zmod3_endpoint_square_ap_forces_middle_zero
    (P Q R S Δ : ZMod 3)
    (hp : P = 0) (hs : S = 0)
    (hpq : Q ^ 2 - P ^ 2 = Δ)
    (hqr : R ^ 2 - Q ^ 2 = Δ)
    (hrs : S ^ 2 - R ^ 2 = Δ) :
    Q = 0 ∧ R = 0 := by
  have hq : Q ^ 2 = Δ := by
    rw [hp] at hpq
    simpa using hpq
  have hr : -(R ^ 2) = Δ := by
    rw [hs] at hrs
    simpa using hrs
  have hqr' : Q ^ 2 = -(R ^ 2) := by
    rw [hq, hr]
  by_cases hQ : Q = 0
  · subst Q
    have hR2 : R ^ 2 = 0 := by
      simpa using hqr'
    have hR : R = 0 := sq_eq_zero_iff.mp hR2
    exact ⟨rfl, hR⟩
  · have hnot : (3 : ℕ) % 4 ≠ 3 := by
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq
        (p := 3) (x := Q) (y := R) hQ hqr'
    norm_num at hnot

/-- Endpoint propagation for `(p,s)`: any natural prime dividing both endpoint
roots propagates to all four roots in a four-square AP. -/
theorem nat_prime_dvd_all_roots_of_dvd_ps_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hp : ℓ ∣ p.natAbs)
    (hs : ℓ ∣ s.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  by_cases h3 : ℓ = 3
  · subst ℓ
    have hpZ3 : ((3 : ℤ) ∣ p) := Int.natCast_dvd.mpr hp
    have hsZ3 : ((3 : ℤ) ∣ s) := Int.natCast_dvd.mpr hs
    have hp0 : (p : ZMod 3) = 0 := by
      exact (CharP.intCast_eq_intCast (ZMod 3) 3).mpr
        (Int.modEq_zero_iff_dvd.mpr hpZ3)
    have hs0 : (s : ZMod 3) = 0 := by
      exact (CharP.intCast_eq_intCast (ZMod 3) 3).mpr
        (Int.modEq_zero_iff_dvd.mpr hsZ3)
    have hpq3 : (q : ZMod 3) ^ 2 - (p : ZMod 3) ^ 2 = (Δ : ZMod 3) := by
      have := congrArg (fun z : ℤ => (z : ZMod 3)) hpq
      simpa using this
    have hqr3 : (r : ZMod 3) ^ 2 - (q : ZMod 3) ^ 2 = (Δ : ZMod 3) := by
      have := congrArg (fun z : ℤ => (z : ZMod 3)) hqr
      simpa using this
    have hrs3 : (s : ZMod 3) ^ 2 - (r : ZMod 3) ^ 2 = (Δ : ZMod 3) := by
      have := congrArg (fun z : ℤ => (z : ZMod 3)) hrs
      simpa using this
    rcases zmod3_endpoint_square_ap_forces_middle_zero
        (p : ZMod 3) (q : ZMod 3) (r : ZMod 3) (s : ZMod 3) (Δ : ZMod 3)
        hp0 hs0 hpq3 hqr3 hrs3 with ⟨hq0, hr0⟩
    have hqZ3 : ((3 : ℤ) ∣ q) := by
      exact Int.modEq_zero_iff_dvd.mp <|
        (CharP.intCast_eq_intCast (ZMod 3) 3).mp hq0
    have hrZ3 : ((3 : ℤ) ∣ r) := by
      exact Int.modEq_zero_iff_dvd.mp <|
        (CharP.intCast_eq_intCast (ZMod 3) 3).mp hr0
    have hq : 3 ∣ q.natAbs := Int.natCast_dvd.mp hqZ3
    have hr : 3 ∣ r.natAbs := Int.natCast_dvd.mp hrZ3
    exact ⟨hp, hq, hr, hs⟩
  · have hpZ : ((ℓ : ℤ) ∣ p) := Int.natCast_dvd.mpr hp
    have hsZ : ((ℓ : ℤ) ∣ s) := Int.natCast_dvd.mpr hs
    have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := by
      simpa [pow_two] using dvd_mul_of_dvd_left hpZ p
    have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := by
      simpa [pow_two] using dvd_mul_of_dvd_left hsZ s
    have hdiffZ : ((ℓ : ℤ) ∣ s ^ 2 - p ^ 2) := Int.dvd_sub hs2Z hp2Z
    have hsum : s ^ 2 - p ^ 2 = 3 * Δ := by
      calc
        s ^ 2 - p ^ 2 =
            (q ^ 2 - p ^ 2) + (r ^ 2 - q ^ 2) + (s ^ 2 - r ^ 2) := by
          ring
        _ = Δ + Δ + Δ := by rw [hpq, hqr, hrs]
        _ = 3 * Δ := by ring
    have h3DeltaZ : ((ℓ : ℤ) ∣ 3 * Δ) := by
      rwa [hsum] at hdiffZ
    have hDeltaZ : ((ℓ : ℤ) ∣ Δ) := by
      rcases Int.Prime.dvd_mul' hℓ h3DeltaZ with hℓ3 | hΔ
      · exact False.elim (h3 (nat_prime_eq_three_of_int_dvd_three hℓ hℓ3))
      · exact hΔ
    have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := by
      have hq_sq : q ^ 2 = p ^ 2 + Δ := by
        nlinarith [hpq]
      rw [hq_sq]
      exact Int.dvd_add hp2Z hDeltaZ
    have hq : ℓ ∣ q.natAbs := Int.Prime.dvd_pow hℓ hq2Z
    have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
      have hr_sq : r ^ 2 = q ^ 2 + Δ := by
        nlinarith [hqr]
      rw [hr_sq]
      exact Int.dvd_add hq2Z hDeltaZ
    have hr : ℓ ∣ r.natAbs := Int.Prime.dvd_pow hℓ hr2Z
    exact ⟨hp, hq, hr, hs⟩

/-- The endpoint `(p,s)` gcd is one in a weak primitive AP. -/
theorem int_gcd_ps_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd p s = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hp hs
  rcases nat_prime_dvd_all_roots_of_dvd_ps_weak_ap hℓ hpq hqr hrs hp hs with
    ⟨hp', hq', hr', hs'⟩
  exact False.elim <|
    false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
      hroot hℓ hp' hq' hr' hs'

/-- Middle adjacent-pair propagation for `(q,r)`. -/
theorem nat_prime_dvd_all_roots_of_dvd_qr_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hq : ℓ ∣ q.natAbs)
    (hr : ℓ ∣ r.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  have hqZ : ((ℓ : ℤ) ∣ q) := Int.natCast_dvd.mpr hq
  have hrZ : ((ℓ : ℤ) ∣ r) := Int.natCast_dvd.mpr hr
  have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hqZ q
  have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hrZ r
  have hDeltaZ : ((ℓ : ℤ) ∣ Δ) := by
    rw [← hqr]
    exact Int.dvd_sub hr2Z hq2Z
  have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := by
    have hp_sq : p ^ 2 = q ^ 2 - Δ := by
      nlinarith [hpq]
    rw [hp_sq]
    exact Int.dvd_sub hq2Z hDeltaZ
  have hp : ℓ ∣ p.natAbs := Int.Prime.dvd_pow hℓ hp2Z
  have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := by
    have hs_sq : s ^ 2 = r ^ 2 + Δ := by
      nlinarith [hrs]
    rw [hs_sq]
    exact Int.dvd_add hr2Z hDeltaZ
  have hs : ℓ ∣ s.natAbs := Int.Prime.dvd_pow hℓ hs2Z
  exact ⟨hp, hq, hr, hs⟩

/-- The middle adjacent `(q,r)` gcd is one in a weak primitive AP. -/
theorem int_gcd_qr_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd q r = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hq hr
  rcases nat_prime_dvd_all_roots_of_dvd_qr_weak_ap hℓ hpq hqr hrs hq hr with
    ⟨hp', hq', hr', hs'⟩
  exact False.elim <|
    false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
      hroot hℓ hp' hq' hr' hs'

/-- Distance-two propagation for `(q,s)`: any odd natural prime dividing both
`q` and `s` propagates through the AP equations to all four roots. -/
theorem nat_prime_dvd_all_roots_of_dvd_qs_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hℓne2 : ℓ ≠ 2)
    (hq : ℓ ∣ q.natAbs)
    (hs : ℓ ∣ s.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  have hqZ : ((ℓ : ℤ) ∣ q) := Int.natCast_dvd.mpr hq
  have hsZ : ((ℓ : ℤ) ∣ s) := Int.natCast_dvd.mpr hs
  have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hqZ q
  have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hsZ s
  have hℓ_s2_sub_q2 : (ℓ : ℤ) ∣ s ^ 2 - q ^ 2 :=
    Int.dvd_sub hs2Z hq2Z
  have hsq_twoDelta : s ^ 2 - q ^ 2 = 2 * Δ := by
    nlinarith [hqr, hrs]
  have hℓ_twoDelta : (ℓ : ℤ) ∣ 2 * Δ := by
    rwa [hsq_twoDelta] at hℓ_s2_sub_q2
  have hℓΔ : (ℓ : ℤ) ∣ Δ :=
    natPrime_dvd_of_dvd_two_mul_int_of_ne_two hℓ hℓne2 hℓ_twoDelta
  have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := by
    have hp_sq : p ^ 2 = q ^ 2 - Δ := by
      nlinarith [hpq]
    rw [hp_sq]
    exact Int.dvd_sub hq2Z hℓΔ
  have hp : ℓ ∣ p.natAbs := Int.Prime.dvd_pow hℓ hp2Z
  have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
    have hr_sq : r ^ 2 = q ^ 2 + Δ := by
      nlinarith [hqr]
    rw [hr_sq]
    exact Int.dvd_add hq2Z hℓΔ
  have hr : ℓ ∣ r.natAbs := Int.Prime.dvd_pow hℓ hr2Z
  exact ⟨hp, hq, hr, hs⟩

/-- The distance-two `(q,s)` gcd is one in a weak primitive AP. -/
theorem int_gcd_qs_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1)
    (hq_odd : q % 2 = 1) :
    Int.gcd q s = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hq hs
  by_cases hℓeq2 : ℓ = 2
  · subst ℓ
    exact False.elim (int_odd_mod_two_not_dvd hq_odd (Int.natCast_dvd.mpr hq))
  · rcases nat_prime_dvd_all_roots_of_dvd_qs_weak_ap
      hℓ hpq hqr hrs hℓeq2 hq hs with
      ⟨hp', hq', hr', hs'⟩
    exact False.elim <|
      false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
        hroot hℓ hp' hq' hr' hs'

/-- Right adjacent-pair propagation for `(r,s)`. -/
theorem nat_prime_dvd_all_roots_of_dvd_rs_weak_ap
    {p q r s Δ : ℤ} {ℓ : ℕ}
    (hℓ : ℓ.Prime)
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hr : ℓ ∣ r.natAbs)
    (hs : ℓ ∣ s.natAbs) :
    ℓ ∣ p.natAbs ∧ ℓ ∣ q.natAbs ∧ ℓ ∣ r.natAbs ∧ ℓ ∣ s.natAbs := by
  have hrZ : ((ℓ : ℤ) ∣ r) := Int.natCast_dvd.mpr hr
  have hsZ : ((ℓ : ℤ) ∣ s) := Int.natCast_dvd.mpr hs
  have hr2Z : ((ℓ : ℤ) ∣ r ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hrZ r
  have hs2Z : ((ℓ : ℤ) ∣ s ^ 2) := by
    simpa [pow_two] using dvd_mul_of_dvd_left hsZ s
  have hDeltaZ : ((ℓ : ℤ) ∣ Δ) := by
    rw [← hrs]
    exact Int.dvd_sub hs2Z hr2Z
  have hq2Z : ((ℓ : ℤ) ∣ q ^ 2) := by
    have hq_sq : q ^ 2 = r ^ 2 - Δ := by
      nlinarith [hqr]
    rw [hq_sq]
    exact Int.dvd_sub hr2Z hDeltaZ
  have hq : ℓ ∣ q.natAbs := Int.Prime.dvd_pow hℓ hq2Z
  have hp2Z : ((ℓ : ℤ) ∣ p ^ 2) := by
    have hp_sq : p ^ 2 = q ^ 2 - Δ := by
      nlinarith [hpq]
    rw [hp_sq]
    exact Int.dvd_sub hq2Z hDeltaZ
  have hp : ℓ ∣ p.natAbs := Int.Prime.dvd_pow hℓ hp2Z
  exact ⟨hp, hq, hr, hs⟩

/-- The right adjacent `(r,s)` gcd is one in a weak primitive AP. -/
theorem int_gcd_rs_eq_one_of_weak_ap
    {p q r s Δ : ℤ}
    (hpq : q ^ 2 - p ^ 2 = Δ)
    (hqr : r ^ 2 - q ^ 2 = Δ)
    (hrs : s ^ 2 - r ^ 2 = Δ)
    (hroot : rootGCD4 p q r s = 1) :
    Int.gcd r s = 1 := by
  rw [Int.gcd_def]
  apply Nat.coprime_iff_gcd_eq_one.mp
  refine Nat.coprime_of_dvd' ?_
  intro ℓ hℓ hr hs
  rcases nat_prime_dvd_all_roots_of_dvd_rs_weak_ap hℓ hpq hqr hrs hr hs with
    ⟨hp', hq', hr', hs'⟩
  exact False.elim <|
    false_of_nat_prime_dvd_all_roots_of_rootGCD4_eq_one
      hroot hℓ hp' hq' hr' hs'

/-- Pairwise-coprimality residual for weak primitive AP roots. -/
def WeakPrimitiveAPPairwise : Prop :=
  ∀ {p q r s Δ : ℤ},
    q ^ 2 - p ^ 2 = Δ →
    r ^ 2 - q ^ 2 = Δ →
    s ^ 2 - r ^ 2 = Δ →
    rootGCD4 p q r s = 1 →
    p % 2 = 1 → q % 2 = 1 → r % 2 = 1 → s % 2 = 1 →
      Int.gcd p q = 1 ∧
      Int.gcd p r = 1 ∧
      Int.gcd p s = 1 ∧
      Int.gcd q r = 1 ∧
      Int.gcd q s = 1 ∧
      Int.gcd r s = 1

/-- Weak primitive AP roots are pairwise coprime. -/
theorem weakPrimitiveAPPairwise : WeakPrimitiveAPPairwise := by
  intro p q r s Δ hpq hqr hrs hroot hp_odd hq_odd _hr_odd _hs_odd
  exact ⟨
    int_gcd_pq_eq_one_of_weak_ap hpq hqr hrs hroot,
    int_gcd_pr_eq_one_of_weak_ap hpq hqr hrs hroot hp_odd,
    int_gcd_ps_eq_one_of_weak_ap hpq hqr hrs hroot,
    int_gcd_qr_eq_one_of_weak_ap hpq hqr hrs hroot,
    int_gcd_qs_eq_one_of_weak_ap hpq hqr hrs hroot hq_odd,
    int_gcd_rs_eq_one_of_weak_ap hpq hqr hrs hroot⟩

/-- Center a primitive positive-difference AP once its difference is divisible
by four. -/
def PositivePrimitiveAPToCenteredWeak : Prop :=
  ∀ {p q r s Δ : ℤ},
    0 < Δ →
    q ^ 2 - p ^ 2 = Δ →
    r ^ 2 - q ^ 2 = Δ →
    s ^ 2 - r ^ 2 = Δ →
    rootGCD4 p q r s = 1 →
    (4 : ℤ) ∣ Δ →
      Nonempty WeakPrimitiveCenteredFourSqAP

/-- Centering is a direct algebraic construction after the divisibility by
four has been supplied. -/
theorem positivePrimitiveAP_to_centered_weak :
    PositivePrimitiveAPToCenteredWeak := by
  intro p q r s Δ hΔpos hpq hqr hrs hroot h4
  rcases h4 with ⟨N, hΔ⟩
  have hNpos : 0 < N := by
    nlinarith
  let X : ℤ := p ^ 2 + 6 * N
  refine ⟨{
    X := X
    N := N
    hNpos := hNpos
    p := p
    q := q
    r := r
    s := s
    hp := ?_
    hq := ?_
    hr := ?_
    hs := ?_
    hroot := hroot }⟩
  · dsimp [X]
    ring
  · dsimp [X]
    nlinarith
  · dsimp [X]
    nlinarith
  · dsimp [X]
    nlinarith

/-- Local parity and pairwise-coprimality residuals package a weak primitive
centered AP into the strong structure used by descent. -/
theorem weakPrimitiveCenteredToStrong_of_local_lemmas
    (hparity : WeakPrimitiveAPParity)
    (hpairwise : WeakPrimitiveAPPairwise) :
    WeakPrimitiveCenteredToStrong := by
  intro S
  let Δ : ℤ := 4 * S.N
  have hpq : S.q ^ 2 - S.p ^ 2 = Δ := by
    dsimp [Δ]
    rw [S.hq, S.hp]
    ring
  have hqr : S.r ^ 2 - S.q ^ 2 = Δ := by
    dsimp [Δ]
    rw [S.hr, S.hq]
    ring
  have hrs : S.s ^ 2 - S.r ^ 2 = Δ := by
    dsimp [Δ]
    rw [S.hs, S.hr]
    ring
  rcases hparity hpq hqr hrs S.hroot with
    ⟨hp_odd, hq_odd, hr_odd, hs_odd, _h8⟩
  rcases hpairwise hpq hqr hrs S.hroot hp_odd hq_odd hr_odd hs_odd with
    ⟨hpq_gcd, hpr_gcd, hps_gcd, hqr_gcd, hqs_gcd, hrs_gcd⟩
  exact ⟨{
    X := S.X
    N := S.N
    hNpos := S.hNpos
    p := S.p
    q := S.q
    r := S.r
    s := S.s
    hp := S.hp
    hq := S.hq
    hr := S.hr
    hs := S.hs
    hpq := hpq_gcd
    hpr := hpr_gcd
    hps := hps_gcd
    hqr := hqr_gcd
    hqs := hqs_gcd
    hrs := hrs_gcd
    hp_odd := hp_odd
    hq_odd := hq_odd
    hr_odd := hr_odd
    hs_odd := hs_odd }⟩

/-- Weak normalization plus weak-to-strong packaging gives the strong
normalization residual expected by the descent theorem. -/
theorem arbitraryAPToPrimitiveCentered_of_weak
    (hweak : ArbitraryAPToWeakPrimitiveCentered)
    (hstrong : WeakPrimitiveCenteredToStrong) :
    ArbitraryAPToPrimitiveCentered := by
  intro w x y z hAP hnonconst
  rcases hweak hAP hnonconst with ⟨S⟩
  exact hstrong S

/-- Residual DAG for constructing a weak primitive centered AP from an
arbitrary nonconstant integer AP. -/
def ArbitraryAPToWeakPrimitiveCenteredDAG : Prop :=
  APOrReversedPositiveDiff →
  RootGCD4Division →
  WeakPrimitiveAPParity →
  PositivePrimitiveAPToCenteredWeak →
    ArbitraryAPToWeakPrimitiveCentered

/-- The explicit weak-normalization DAG composes mechanically. -/
theorem arbitraryAPToWeakPrimitiveCentered_of_dag :
    ArbitraryAPToWeakPrimitiveCenteredDAG := by
  intro hpos hdiv hparity hcenter w x y z hAP hnonconst
  rcases hpos hAP hnonconst with
    ⟨a, b, c, d, Δ, hΔpos, hab, hbc, hcd, _horient⟩
  rcases hdiv hΔpos hab hbc hcd with
    ⟨_g, p, q, r, s, Δ', _hgpos, hΔ'pos,
      _ha, _hb, _hc, _hd, hpq, hqr, hrs, hroot⟩
  rcases hparity hpq hqr hrs hroot with
    ⟨_hp_odd, _hq_odd, _hr_odd, _hs_odd, h8⟩
  have h4 : (4 : ℤ) ∣ Δ' :=
    dvd_trans (by norm_num : (4 : ℤ) ∣ 8) h8
  exact hcenter hΔ'pos hpq hqr hrs hroot h4

/-- The checked local normalization lemmas produce a primitive centered AP
from any nonconstant integer four-square AP. -/
theorem arbitraryAPToPrimitiveCentered_checked :
    ArbitraryAPToPrimitiveCentered := by
  exact arbitraryAPToPrimitiveCentered_of_weak
    (arbitraryAPToWeakPrimitiveCentered_of_dag
      ap_or_reversed_positive_diff
      rootGCD4Division
      weakPrimitiveAPParity
      positivePrimitiveAP_to_centered_weak)
    (weakPrimitiveCenteredToStrong_of_local_lemmas
      weakPrimitiveAPParity
      weakPrimitiveAPPairwise)

/-- A strict descent on the positive centered step rules out primitive centered
APs. -/
theorem no_primitiveCenteredFourSqAP_of_descent
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    ¬ Nonempty PrimitiveCenteredFourSqAP := by
  intro hne
  classical
  let P : ℕ → Prop := fun n => ∃ S : PrimitiveCenteredFourSqAP, S.N.natAbs = n
  have hP : ∃ n, P n := by
    rcases hne with ⟨S⟩
    exact ⟨S.N.natAbs, S, rfl⟩
  let m := Nat.find hP
  have hmP : P m := Nat.find_spec hP
  rcases hmP with ⟨S, hS⟩
  rcases hdesc S with ⟨T, hlt⟩
  have hT : P T.N.natAbs := ⟨T, rfl⟩
  have hmin : m ≤ T.N.natAbs := Nat.find_min' hP hT
  have hS_le_T : S.N.natAbs ≤ T.N.natAbs := by
    simpa [← hS] using hmin
  exact not_lt_of_ge hS_le_T hlt

/-- The integer AP theorem follows from normalization plus primitive centered
descent. -/
theorem fourIntSquaresAPConst_of_primitiveCentered_descent
    (hnorm : ArbitraryAPToPrimitiveCentered)
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    FourIntSquaresAPConst := by
  intro w x y z hAP
  by_contra hnot
  exact no_primitiveCenteredFourSqAP_of_descent hdesc (hnorm hAP hnot)

/-- The remaining arithmetic frontier is the descent on primitive centered APs. -/
theorem fourIntSquaresAPConst_of_checked_descent
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    FourIntSquaresAPConst :=
  fourIntSquaresAPConst_of_primitiveCentered_descent
    arbitraryAPToPrimitiveCentered_checked hdesc

theorem fourIntSquaresAPConst_checked :
    FourIntSquaresAPConst :=
  fourIntSquaresAPConst_of_checked_descent
    primitiveCenteredFourSqAPDescent_checked

/-- A common nonzero integer scaling of four rationals to four integers. -/
structure RatIntScale4 (w x y z : ℚ) where
  M : ℤ
  hM : M ≠ 0
  W : ℤ
  X : ℤ
  Y : ℤ
  Z : ℤ
  hW : (W : ℚ) = (M : ℚ) * w
  hX : (X : ℚ) = (M : ℚ) * x
  hY : (Y : ℚ) = (M : ℚ) * y
  hZ : (Z : ℚ) = (M : ℚ) * z

private lemma rat_scale_by_four_den_product
    (q r s t : ℚ) :
    ((q.num * (r.den : ℤ) * (s.den : ℤ) * (t.den : ℤ) : ℤ) : ℚ)
      = ((((q.den * r.den * s.den * t.den : ℕ) : ℤ) : ℚ) * q) := by
  calc
    ((q.num * (r.den : ℤ) * (s.den : ℤ) * (t.den : ℤ) : ℤ) : ℚ)
        = (q.num : ℚ) * (r.den : ℚ) * (s.den : ℚ) * (t.den : ℚ) := by
          norm_cast
    _ = ((q.den : ℚ) * q) * (r.den : ℚ) * (s.den : ℚ) * (t.den : ℚ) := by
          rw [← Rat.den_mul_eq_num q]
    _ = ((((q.den * r.den * s.den * t.den : ℕ) : ℤ) : ℚ) * q) := by
          simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
          ring

/-- Denominator-clearing object for four rationals. -/
theorem rat_int_scale4_nonempty (w x y z : ℚ) :
    Nonempty (RatIntScale4 w x y z) := by
  refine ⟨
    { M := ((w.den * x.den * y.den * z.den : ℕ) : ℤ)
      hM := by
        exact Int.ofNat_ne_zero.2
          (mul_ne_zero
            (mul_ne_zero
              (mul_ne_zero (Rat.den_ne_zero w) (Rat.den_ne_zero x))
              (Rat.den_ne_zero y))
            (Rat.den_ne_zero z))
      W := w.num * (x.den : ℤ) * (y.den : ℤ) * (z.den : ℤ)
      X := x.num * (w.den : ℤ) * (y.den : ℤ) * (z.den : ℤ)
      Y := y.num * (w.den : ℤ) * (x.den : ℤ) * (z.den : ℤ)
      Z := z.num * (w.den : ℤ) * (x.den : ℤ) * (y.den : ℤ)
      hW := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product w x y z
      hX := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product x w y z
      hY := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product y w x z
      hZ := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_four_den_product z w x y }⟩

/-- Existential wrapper for callers that prefer an `Exists` theorem. -/
theorem rat_int_scale4_exists (w x y z : ℚ) :
    ∃ _s : RatIntScale4 w x y z, True := by
  rcases rat_int_scale4_nonempty w x y z with ⟨s⟩
  exact ⟨s, trivial⟩

private lemma ratIntScale4_sq_sub_cast
    {A B M : ℤ} {a b : ℚ}
    (hA : (A : ℚ) = (M : ℚ) * a)
    (hB : (B : ℚ) = (M : ℚ) * b) :
    ((A ^ 2 - B ^ 2 : ℤ) : ℚ) = (M : ℚ) ^ 2 * (a ^ 2 - b ^ 2) := by
  calc
    ((A ^ 2 - B ^ 2 : ℤ) : ℚ) = (A : ℚ) ^ 2 - (B : ℚ) ^ 2 := by
      norm_cast
    _ = ((M : ℚ) * a) ^ 2 - ((M : ℚ) * b) ^ 2 := by
      rw [hA, hB]
    _ = (M : ℚ) ^ 2 * (a ^ 2 - b ^ 2) := by
      ring

/-- Transport rational square-AP equations to the scaled integer quadruple. -/
theorem intFourSqAP_of_ratIntScale4
    {w x y z : ℚ} (s : RatIntScale4 w x y z)
    (h1 : x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2)
    (h2 : y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2) :
    IntFourSqAP s.W s.X s.Y s.Z := by
  constructor
  · exact Rat.intCast_injective (by
      calc
        ((s.X ^ 2 - s.W ^ 2 : ℤ) : ℚ)
            = (s.M : ℚ) ^ 2 * (x ^ 2 - w ^ 2) := by
              exact ratIntScale4_sq_sub_cast s.hX s.hW
        _ = (s.M : ℚ) ^ 2 * (y ^ 2 - x ^ 2) := by
              rw [h1]
        _ = ((s.Y ^ 2 - s.X ^ 2 : ℤ) : ℚ) := by
              exact (ratIntScale4_sq_sub_cast s.hY s.hX).symm)
  · exact Rat.intCast_injective (by
      calc
        ((s.Y ^ 2 - s.X ^ 2 : ℤ) : ℚ)
            = (s.M : ℚ) ^ 2 * (y ^ 2 - x ^ 2) := by
              exact ratIntScale4_sq_sub_cast s.hY s.hX
        _ = (s.M : ℚ) ^ 2 * (z ^ 2 - y ^ 2) := by
              rw [h2]
        _ = ((s.Z ^ 2 - s.Y ^ 2 : ℤ) : ℚ) := by
              exact (ratIntScale4_sq_sub_cast s.hZ s.hY).symm)

private lemma rat_sq_eq_of_scaled_sq_eq
    {M W X : ℤ} {w x : ℚ}
    (hM : M ≠ 0)
    (hW : (W : ℚ) = (M : ℚ) * w)
    (hX : (X : ℚ) = (M : ℚ) * x)
    (hWX : W ^ 2 = X ^ 2) :
    w ^ 2 = x ^ 2 := by
  have hMq : (M : ℚ) ≠ 0 := by
    exact_mod_cast hM
  have hM2 : (M : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hMq
  apply mul_left_cancel₀ hM2
  calc
    (M : ℚ) ^ 2 * w ^ 2 = ((M : ℚ) * w) ^ 2 := by ring
    _ = (W : ℚ) ^ 2 := by rw [← hW]
    _ = ((W ^ 2 : ℤ) : ℚ) := by norm_cast
    _ = ((X ^ 2 : ℤ) : ℚ) := by
          exact congrArg (fun n : ℤ => (n : ℚ)) hWX
    _ = (X : ℚ) ^ 2 := by norm_cast
    _ = ((M : ℚ) * x) ^ 2 := by rw [hX]
    _ = (M : ℚ) ^ 2 * x ^ 2 := by ring

/-- Denominator clearing plus the integer AP theorem gives the rational
four-square AP residual used by the N=12 cover. -/
theorem fourRatSquaresAPConst_of_fourIntSquaresAPConst
    (hInt : FourIntSquaresAPConst) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  rcases rat_int_scale4_nonempty w x y z with ⟨s⟩
  have hsap : IntFourSqAP s.W s.X s.Y s.Z :=
    intFourSqAP_of_ratIntScale4 s h1 h2
  rcases hInt hsap with ⟨hWX, hXY, hYZ⟩
  exact ⟨
    rat_sq_eq_of_scaled_sq_eq s.hM s.hW s.hX hWX,
    rat_sq_eq_of_scaled_sq_eq s.hM s.hX s.hY hXY,
    rat_sq_eq_of_scaled_sq_eq s.hM s.hY s.hZ hYZ⟩

/-- The checked normalization layer reduces the rational AP residual to the
primitive centered descent frontier. -/
theorem fourRatSquaresAPConst_of_checked_descent
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    FourRatSquaresAPConst :=
  fourRatSquaresAPConst_of_fourIntSquaresAPConst
    (fourIntSquaresAPConst_of_checked_descent hdesc)

/-- Public alias for the checked descent-to-rational-AP bridge. -/
theorem fourRatSquaresAPConst_of_primitiveCenteredFourSqAPDescent_checked
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    FourRatSquaresAPConst :=
  fourRatSquaresAPConst_of_checked_descent hdesc

theorem fourRatSquaresAPConst_checked :
    FourRatSquaresAPConst :=
  fourRatSquaresAPConst_of_checked_descent
    primitiveCenteredFourSqAPDescent_checked

/-- The full rational AP residual follows from the three Euler/concordant-form
descent interfaces. -/
theorem fourRatSquaresAPConst_of_eulerSquarePair_dag
    (hto : PrimitiveCenteredToEulerSquarePair)
    (hstep : EulerSquarePairDescent)
    (hfrom : EulerSquarePairToPrimitiveCentered) :
    FourRatSquaresAPConst :=
  fourRatSquaresAPConst_of_checked_descent
    (primitiveCenteredFourSqAPDescent_of_eulerSquarePair_dag
      hto hstep hfrom)

theorem fourRatSquaresAPConst_of_eulerSquarePair_to_descent
    (hto : PrimitiveCenteredToEulerSquarePair)
    (hstep : EulerSquarePairDescent) :
    FourRatSquaresAPConst :=
  fourRatSquaresAPConst_of_checked_descent
    (primitiveCenteredFourSqAPDescent_of_eulerSquarePair_to_descent
      hto hstep)

/-- The optional AP-to-FLT4 bridge residual is enough to discharge the rational
AP residual.  The active non-circular route is expected to use
`fourIntSquaresAPConst_of_primitiveCentered_descent` instead. -/
theorem fourRatSquaresAPConst_from_fermat42_bridge
    (hbridge : FourSquaresAPToFermat42Bridge) :
    FourRatSquaresAPConst := by
  exact fourRatSquaresAPConst_of_fourIntSquaresAPConst
    (fourIntSquaresAPConst_of_fermat42_bridge hbridge)

end MazurProof.RationalPointsN12
