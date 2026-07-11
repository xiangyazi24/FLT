import Mathlib
import FLT.Assumptions.MazurProof.TateOriginDivision

/-!
# Rational points on the level-27 cubic

The relevant genus-one quotient below `X₁(27)` has affine model

`y² + y = x³`.

This is not the Fermat model asserted in the old order-27 exclusion file.
Here we prove directly that its only affine rational points are `(0,0)` and
`(0,-1)`.  The proof clears the reduced denominator of `y`, splits the two
coprime factors `y` and `y+1` into cubes, and invokes the proved exponent-three
case of Fermat's last theorem.

The final section records the algebraic data supplied by an exact order-27
Tate origin.  Constructing the actual quotient coordinates on this cubic is a
separate task; this file deliberately does not package that missing map as a
hypothesis, since such a hypothesis would be equivalent to the desired
order-27 exclusion.
-/

namespace MazurProof.RationalPointsN27CM

open scoped WeierstrassCurve.Affine
open TateOriginDivision

noncomputable section

/-! ## The level-27 cubic -/

def Level27Equation (x y : ℚ) : Prop :=
  y ^ 2 + y = x ^ 3

def Level27Cusp (x y : ℚ) : Prop :=
  x = 0 ∧ (y = 0 ∨ y = -1)

/-- The actual Weierstrass model of the level-27 quotient. -/
def level27Curve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 1
  a₄ := 0
  a₆ := 0

theorem level27Curve_delta : level27Curve.Δ = (-27 : ℚ) := by
  norm_num [level27Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance level27Curve_isElliptic : level27Curve.IsElliptic where
  isUnit := by rw [level27Curve_delta]; norm_num

theorem level27Curve_j : level27Curve.j = 0 := by
  apply WeierstrassCurve.j_eq_zero
  norm_num [level27Curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]

@[simp] theorem level27Curve_equation_iff (x y : ℚ) :
    WeierstrassCurve.Affine.Equation level27Curve x y ↔
      Level27Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [level27Curve, Level27Equation]

abbrev Level27Point := WeierstrassCurve.Affine.Point level27Curve

/-- If a square of a positive natural number is a cube, the number is itself
a cube. -/
private theorem nat_isCube_of_square_eq_cube {n d : ℕ}
    (hn : n ≠ 0) (h : n ^ 2 = d ^ 3) : ∃ t : ℕ, n = t ^ 3 := by
  have hd : d ≠ 0 := by
    intro hd
    have hn2 : n ^ 2 = 0 := by simpa only [hd, zero_pow three_ne_zero] using h
    exact hn ((pow_eq_zero_iff two_ne_zero).mp hn2)
  have hd2 : d ^ 2 ∣ n ^ 2 := ⟨d, by rw [h]; ring⟩
  have hdvd : d ∣ n := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hd2
  obtain ⟨t, rfl⟩ := hdvd
  refine ⟨t, ?_⟩
  have hcancel : d ^ 2 * t ^ 2 = d ^ 2 * d := by
    calc
      d ^ 2 * t ^ 2 = (d * t) ^ 2 := by ring
      _ = d ^ 3 := h
      _ = d ^ 2 * d := by ring
  have ht2 : t ^ 2 = d := mul_left_cancel₀ (pow_ne_zero 2 hd) hcancel
  calc
    d * t = t ^ 2 * t := by rw [ht2]
    _ = t ^ 3 := by ring

/-- Reduced numerator and denominator data extracted from a rational point on
the level-27 cubic. -/
theorem integral_cube_data {x y : ℚ} (hcurve : Level27Equation x y) :
    ∃ m n r s t : ℤ,
      0 < n ∧ 0 < t ∧
      y = (m : ℚ) / (n : ℚ) ∧
      m = r ^ 3 ∧ m + n = s ^ 3 ∧ n = t ^ 3 := by
  let m : ℤ := y.num
  let n : ℤ := (y.den : ℤ)
  have hn : 0 < n := by positivity
  have hnQ : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hn)
  have hred : IsCoprime m n := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [m, n, Int.natAbs_natCast]
    exact y.reduced
  have hsumred : IsCoprime (m + n) n := by
    obtain ⟨a, b, hab⟩ := hred
    exact ⟨a, b - a, by rw [← hab]; ring⟩
  have hfacred : IsCoprime m (m + n) := by
    obtain ⟨a, b, hab⟩ := hred
    exact ⟨a - b, b, by rw [← hab]; ring⟩
  have hprodred : IsCoprime (m * (m + n)) (n ^ 2) :=
    (hred.mul_left hsumred).pow_right
  have hprodredNat :
      Nat.Coprime (m * (m + n)).natAbs (n ^ 2).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hprodred
  have hy : y = (m : ℚ) / (n : ℚ) := by
    simp only [m, n]
    push_cast
    exact (Rat.num_div_den y).symm
  have hrepr : y ^ 2 + y =
      ((m * (m + n) : ℤ) : ℚ) / ((n ^ 2 : ℤ) : ℚ) := by
    rw [hy]
    field_simp [hnQ]
    push_cast
    ring
  have hnum : (y ^ 2 + y).num = m * (m + n) := by
    rw [hrepr]
    exact Rat.num_div_eq_of_coprime (by positivity) hprodredNat
  have hden : (y ^ 2 + y).den = y.den ^ 2 := by
    rw [hrepr]
    have hdenInt :
        ((((m * (m + n) : ℤ) : ℚ) / ((n ^ 2 : ℤ) : ℚ)).den : ℤ) = n ^ 2 := by
      exact Rat.den_div_eq_of_coprime (by positivity) hprodredNat
    have hn2 : n ^ 2 = (y.den : ℤ) ^ 2 := by rfl
    rw [hn2] at hdenInt
    exact_mod_cast hdenInt
  have hmulcube' : m * (m + n) = x.num ^ 3 := by
    have h := congrArg Rat.num hcurve
    rw [hnum, Rat.num_pow] at h
    simpa using h
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd hfacred (show Odd 3 by decide) hmulcube'
  have hdencube : y.den ^ 2 = x.den ^ 3 := by
    calc
      y.den ^ 2 = (y ^ 2 + y).den := hden.symm
      _ = (x ^ 3).den := congrArg Rat.den hcurve
      _ = x.den ^ 3 := Rat.den_pow _ _
  obtain ⟨t, ht⟩ := nat_isCube_of_square_eq_cube y.den_ne_zero hdencube
  refine ⟨m, n, r, s, (t : ℤ), hn, ?_, hy, hr, hs, ?_⟩
  · exact_mod_cast (Nat.pos_of_ne_zero (by
      intro ht0
      apply y.den_ne_zero
      rw [ht, ht0]
      simp))
  · dsimp only [n]
    exact_mod_cast ht

/-- Every affine rational point on `y²+y=x³` is one of the two cusps. -/
theorem level27_rational_points_are_cusps {x y : ℚ}
    (hcurve : Level27Equation x y) : Level27Cusp x y := by
  obtain ⟨m, n, r, s, t, hn, ht, hy, hr, hs, hn3⟩ :=
    integral_cube_data hcurve
  have ht0 : (t : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt ht)
  have hycube : y = ((r : ℚ) / (t : ℚ)) ^ 3 := by
    rw [hy, hr, hn3]
    field_simp [ht0]
    push_cast
    ring
  have hyonecube : y + 1 = ((s : ℚ) / (t : ℚ)) ^ 3 := by
    calc
      y + 1 = ((m + n : ℤ) : ℚ) / (n : ℚ) := by
        rw [hy]
        field_simp [Int.cast_ne_zero.mpr (ne_of_gt hn)]
        push_cast
        ring
      _ = ((s ^ 3 : ℤ) : ℚ) / ((t ^ 3 : ℤ) : ℚ) := by rw [hs, hn3]
      _ = ((s : ℚ) / (t : ℚ)) ^ 3 := by
        field_simp [ht0]
        push_cast
        ring
  by_cases hy0 : y = 0
  · refine ⟨?_, Or.inl hy0⟩
    have : x ^ 3 = 0 := by simpa [Level27Equation, hy0] using hcurve.symm
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  · by_cases hy1 : y = -1
    · refine ⟨?_, Or.inr hy1⟩
      have : x ^ 3 = 0 := by simpa [Level27Equation, hy1] using hcurve.symm
      exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
    · have hr0 : (r : ℚ) / (t : ℚ) ≠ 0 := by
        intro hrt
        apply hy0
        rw [hycube, hrt]
        norm_num
      have hs0 : (s : ℚ) / (t : ℚ) ≠ 0 := by
        intro hst
        apply hy1
        have : y + 1 = 0 := by rw [hyonecube, hst]; norm_num
        linarith
      have hFLTQ : FermatLastTheoremWith ℚ 3 :=
        (fermatLastTheoremFor_iff_rat (n := 3)).mp fermatLastTheoremThree
      exfalso
      exact hFLTQ (r / t) 1 (s / t) hr0 (by norm_num) hs0 (by
        rw [← hycube, ← hyonecube]
        ring)

/-- Exact affine classification, including the easy converse. -/
theorem level27_equation_iff_cusp {x y : ℚ} :
    Level27Equation x y ↔ Level27Cusp x y := by
  constructor
  · exact level27_rational_points_are_cusps
  · rintro ⟨rfl, rfl | rfl⟩ <;> norm_num [Level27Equation]

/-- The two affine cusp points on the level-27 Weierstrass model. -/
def cuspZero : Level27Point :=
  WeierstrassCurve.Affine.Point.mk
    ((level27Curve_equation_iff 0 0).mpr (by norm_num [Level27Equation]))

def cuspNegOne : Level27Point :=
  WeierstrassCurve.Affine.Point.mk
    ((level27Curve_equation_iff 0 (-1)).mpr (by norm_num [Level27Equation]))

/-- Point-level enumeration: infinity and the two affine cusps are all the
rational points of the level-27 curve. -/
theorem level27_point_classification (P : Level27Point) :
    P = 0 ∨ P = cuspZero ∨ P = cuspNegOne := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
      have hcusp : Level27Cusp x y :=
        level27_rational_points_are_cusps
          ((level27Curve_equation_iff x y).mp h.1)
      rcases hcusp with ⟨hx, hy | hy⟩
      · right; left
        subst x
        subst y
        rfl
      · right; right
        subst x
        subst y
        rfl

theorem cuspZero_ne_zero : cuspZero ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

theorem cuspNegOne_ne_zero : cuspNegOne ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

theorem cuspZero_ne_cuspNegOne : cuspZero ≠ cuspNegOne := by
  intro h
  have hy := (WeierstrassCurve.Affine.Point.some.inj h).2
  norm_num at hy

/-- Set-theoretic form of the complete three-point classification. -/
theorem level27_rational_point_set :
    (Set.univ : Set Level27Point) = {0, cuspZero, cuspNegOne} := by
  ext P
  simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
  exact level27_point_classification P

/-! The following explicit polynomial is the denominator displayed by the
LMFDB model in the affine chart `z=1`.  The theorem below is purely algebraic:
this file does not formalize the modular interpretation of that display. -/
def Level27JDenominator (y : ℚ) : ℚ :=
  y ^ 9 * (y + 1) ^ 9 * (y ^ 2 + y + 1) ^ 3 *
    (y ^ 3 - 3 * y ^ 2 - 6 * y - 1) *
    (y ^ 3 + 6 * y ^ 2 + 3 * y - 1)

theorem level27_jDenominator_eq_zero {x y : ℚ}
    (hcurve : Level27Equation x y) : Level27JDenominator y = 0 := by
  rcases level27_rational_points_are_cusps hcurve with ⟨_, rfl | rfl⟩
  · simp [Level27JDenominator]
  · simp [Level27JDenominator]

theorem level27_no_point_with_nonzero_displayed_denominator :
    ¬ ∃ x y : ℚ, Level27Equation x y ∧ Level27JDenominator y ≠ 0 := by
  rintro ⟨x, y, hcurve, hden⟩
  exact hden (level27_jDenominator_eq_zero hcurve)

theorem level27_no_noncuspidal_point :
    ¬ ∃ x y : ℚ, Level27Equation x y ∧ ¬ Level27Cusp x y := by
  rintro ⟨x, y, hcurve, hnoncusp⟩
  exact hnoncusp (level27_rational_points_are_cusps hcurve)

/-! ## Exact order-27 Tate data -/

/-- Exact order 27 supplies all algebraic inputs required by the corrected
level-27 map. -/
theorem exact_order_twenty_seven_tate_data
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h27 : HasRationalPointOfOrder E 27) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = 27 ∧ b ≠ 0 ∧
        ((W b c).preΨ' 27).eval 0 = 0 ∧
        ((W b c).preΨ' 9).eval 0 ≠ 0 := by
  obtain ⟨b, c, hEll, hord, hb, h27eval⟩ :=
    exists_tate_parameters_of_has_rational_point_of_odd_order E
      (by norm_num : 3 < 27) (by decide : ¬ Even 27) h27
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have h9eval : ((W b c).preΨ' 9).eval 0 ≠ 0 :=
    prePsi_eval_ne_zero_of_lt_addOrder b c
      (by norm_num : 0 < 27) (by norm_num : 0 < 9)
      (by norm_num : 9 < 27) (by decide : ¬ Even 9) hord
  exact ⟨b, c, inferInstance, hord, hb, h27eval, h9eval⟩

end

end MazurProof.RationalPointsN27CM
