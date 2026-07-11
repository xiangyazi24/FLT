import FLT.Assumptions.MazurProof.TateNFDivision

/-!
# Rational algebra for the order-18 obstruction

This file eliminates the two Tate parameters from the simultaneous system

`F9(b,c) = 0`, `T2(b,c,X) = 0`, `b != 0`.

The order-nine equation is rational.  Every nondegenerate solution is uniquely
of Kubert's form

`c = t^2 (t - 1)`, `b = t^2 (t - 1) (t^2 - t + 1)`.

After substitution, the order-18 obstruction is the explicit plane curve
`G18(t,X) = 0`.  Thus the remaining arithmetic problem has only two variables;
no elliptic-curve or division-polynomial definitions remain in its statement.
-/

namespace MazurProof.RationalPointsN18

noncomputable section

/-- Kubert's `c` parameter for a marked point of order nine. -/
def kubertC9 (t : ℚ) : ℚ := t ^ 2 * (t - 1)

/-- Kubert's `b` parameter for a marked point of order nine. -/
def kubertB9 (t : ℚ) : ℚ :=
  t ^ 2 * (t - 1) * (t ^ 2 - t + 1)

/-- The plane equation obtained by substituting the Kubert order-nine family
into the Tate two-division cubic. -/
def G18 (t X : ℚ) : ℚ :=
  4 * X ^ 3
    + (t ^ 6 - 6 * t ^ 5 + 9 * t ^ 4 - 10 * t ^ 3 + 6 * t ^ 2 + 1) * X ^ 2
    + (2 * t ^ 8 - 6 * t ^ 7 + 8 * t ^ 6 - 8 * t ^ 5
        + 6 * t ^ 4 - 4 * t ^ 3 + 2 * t ^ 2) * X
    + t ^ 10 - 4 * t ^ 9 + 8 * t ^ 8 - 10 * t ^ 7
        + 8 * t ^ 6 - 4 * t ^ 5 + t ^ 4

/-! ## The order-nine parametrization -/

theorem kubert_F9 (t : ℚ) :
    TateNFDivision.F9 (kubertB9 t) (kubertC9 t) = 0 := by
  simp only [kubertB9, kubertC9, TateNFDivision.F9]
  ring

theorem c_ne_zero_of_F9
    {b c : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0) :
    c ≠ 0 := by
  intro hc
  subst c
  simp only [TateNFDivision.F9, sub_zero, zero_pow (by norm_num : 3 ≠ 0),
    zero_mul, add_zero] at hF9
  exact (pow_ne_zero 3 hb) hF9

theorem b_sub_c_ne_zero_of_F9
    {b c : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0) :
    b - c ≠ 0 := by
  have hc := c_ne_zero_of_F9 hb hF9
  intro hbc
  have hbeq : b = c := sub_eq_zero.mp hbc
  have hpow : c ^ 5 = 0 := by
    rw [hbeq] at hF9
    simp only [TateNFDivision.F9, sub_self, zero_pow (by norm_num : 3 ≠ 0),
      zero_add] at hF9
    nlinarith
  exact (pow_ne_zero 5 hc) hpow

/-- The parameter recovered from a nondegenerate solution of `F9 = 0`. -/
def recoveredT (b c : ℚ) : ℚ := c ^ 2 / (b - c)

theorem recovered_c
    {b c : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0) :
    c = kubertC9 (recoveredT b c) := by
  have hd := b_sub_c_ne_zero_of_F9 hb hF9
  simp only [recoveredT, kubertC9]
  simp only [TateNFDivision.F9] at hF9
  field_simp [hd]
  linear_combination c * hF9

theorem recovered_b
    {b c : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0) :
    b = kubertB9 (recoveredT b c) := by
  have hd := b_sub_c_ne_zero_of_F9 hb hF9
  have hc := recovered_c hb hF9
  change b = kubertC9 (recoveredT b c) *
    (recoveredT b c ^ 2 - recoveredT b c + 1)
  rw [← hc]
  simp only [recoveredT]
  simp only [TateNFDivision.F9] at hF9
  field_simp [hd]
  linear_combination hF9

theorem recoveredT_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0) :
    recoveredT b c ≠ 0 := by
  have hc := c_ne_zero_of_F9 hb hF9
  have hd := b_sub_c_ne_zero_of_F9 hb hF9
  simp only [recoveredT]
  exact div_ne_zero (pow_ne_zero 2 hc) hd

theorem recoveredT_ne_one
    {b c : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0) :
    recoveredT b c ≠ 1 := by
  have hc0 := c_ne_zero_of_F9 hb hF9
  have hc := recovered_c hb hF9
  intro ht
  rw [ht] at hc
  simp only [kubertC9, one_pow, sub_self, mul_zero] at hc
  exact hc0 hc

theorem F9_parametrization
    {b c : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0) :
    ∃ t : ℚ, t ≠ 0 ∧ t ≠ 1 ∧ b = kubertB9 t ∧ c = kubertC9 t := by
  exact ⟨recoveredT b c, recoveredT_ne_zero hb hF9, recoveredT_ne_one hb hF9,
    recovered_b hb hF9, recovered_c hb hF9⟩

/-! ## Substitution into the two-division cubic -/

theorem T2_kubert_eq_G18 (t X : ℚ) :
    TateNFDivision.T2 (kubertB9 t) (kubertC9 t) X = G18 t X := by
  simp only [TateNFDivision.T2, kubertB9, kubertC9, G18]
  ring

theorem kubert_quadratic_pos (t : ℚ) : 0 < t ^ 2 - t + 1 := by
  nlinarith [sq_nonneg (t - (1 / 2 : ℚ))]

theorem kubertB9_ne_zero {t : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    kubertB9 t ≠ 0 := by
  unfold kubertB9
  exact mul_ne_zero
    (mul_ne_zero (pow_ne_zero 2 ht0) (sub_ne_zero.mpr ht1))
    (ne_of_gt (kubert_quadratic_pos t))

/-- The simultaneous Tate obstruction implies a noncuspidal rational point on
the explicit plane model `G18 = 0`. -/
theorem obstruction_to_G18
    {b c X : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0)
    (hT2 : TateNFDivision.T2 b c X = 0) :
    ∃ t : ℚ, t ≠ 0 ∧ t ≠ 1 ∧ G18 t X = 0 := by
  obtain ⟨t, ht0, ht1, hbparam, hcparam⟩ := F9_parametrization hb hF9
  refine ⟨t, ht0, ht1, ?_⟩
  rw [hbparam, hcparam, T2_kubert_eq_G18] at hT2
  exact hT2

/-- Conversely, every noncuspidal rational point on `G18 = 0` gives a
simultaneous nondegenerate solution of the original Tate equations. -/
theorem G18_to_obstruction
    {t X : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hG : G18 t X = 0) :
    kubertB9 t ≠ 0 ∧
      TateNFDivision.F9 (kubertB9 t) (kubertC9 t) = 0 ∧
      TateNFDivision.T2 (kubertB9 t) (kubertC9 t) X = 0 := by
  refine ⟨kubertB9_ne_zero ht0 ht1, kubert_F9 t, ?_⟩
  rw [T2_kubert_eq_G18]
  exact hG

/-- Exact equivalence between the three-variable Tate system and the
two-variable noncuspidal plane curve. -/
theorem obstruction_iff_G18 :
    (∃ b c X : ℚ, b ≠ 0 ∧ TateNFDivision.F9 b c = 0 ∧
      TateNFDivision.T2 b c X = 0) ↔
    ∃ t X : ℚ, t ≠ 0 ∧ t ≠ 1 ∧ G18 t X = 0 := by
  constructor
  · rintro ⟨b, c, X, hb, hF9, hT2⟩
    obtain ⟨t, ht0, ht1, hG⟩ := obstruction_to_G18 hb hF9 hT2
    exact ⟨t, X, ht0, ht1, hG⟩
  · rintro ⟨t, X, ht0, ht1, hG⟩
    obtain ⟨hb, hF9, hT2⟩ := G18_to_obstruction ht0 ht1 hG
    exact ⟨kubertB9 t, kubertC9 t, X, hb, hF9, hT2⟩

/-! ## Birational reduction to the standard `X₁(18)` model

The following cubic is the standard affine model

`(U - 1)² V² - (U³ - U + 1)V + U²(U - 1) = 0`.

Here its second coordinate is the Kubert parameter `t`.  The displayed
numerator and denominator give an explicit rational map from `G18` to this
model.  The Bezout identity below proves that the denominator cannot vanish
on a noncuspidal point of `G18`.
-/

def standardG18 (U V : ℚ) : ℚ :=
  (U - 1) ^ 2 * V ^ 2 - (U ^ 3 - U + 1) * V + U ^ 2 * (U - 1)

private def mapNumerator (t X : ℚ) : ℚ :=
  -(t - 1) * (t ^ 3 - t ^ 2 + 1) * X
    + t ^ 2 * (t - 1) ^ 2 * (t ^ 2 - t + 1)

private def mapDenominator (t X : ℚ) : ℚ :=
  -(t ^ 3 - t ^ 2 + 2 * t - 1) * X
    + t ^ 2 * (t - 1) * (2 * t - 1) * (t ^ 2 - t + 1)

/-- Denominator-cleared evaluation of `standardG18 (N / D) V`. -/
private def standardG18Hom (N D V : ℚ) : ℚ :=
  (N - D) ^ 2 * V ^ 2 * D
    - (N ^ 3 - N * D ^ 2 + D ^ 3) * V
    + N ^ 2 * (N - D)

/-- The quotient in the Bezout identity between `G18` and the linear map
denominator. -/
private def denominatorBezoutQ (t X : ℚ) : ℚ :=
  (-4 * t ^ 6 + 8 * t ^ 5 - 20 * t ^ 4 + 24 * t ^ 3
      - 24 * t ^ 2 + 16 * t - 4) * X ^ 2
    + (-t ^ 12 + 8 * t ^ 11 - 26 * t ^ 10 + 56 * t ^ 9
        - 85 * t ^ 8 + 96 * t ^ 7 - 82 * t ^ 6 + 52 * t ^ 5
        - 30 * t ^ 4 + 16 * t ^ 3 - 8 * t ^ 2 + 4 * t - 1) * X
    - 2 * t ^ 15 + 17 * t ^ 14 - 65 * t ^ 13 + 149 * t ^ 12
        - 225 * t ^ 11 + 231 * t ^ 10 - 154 * t ^ 9 + 49 * t ^ 8
        + 21 * t ^ 7 - 41 * t ^ 6 + 32 * t ^ 5 - 17 * t ^ 4
        + 6 * t ^ 3 - t ^ 2

/-- Polynomial Bezout identity certifying that `G18` and the map denominator
have no common zero away from `t = 0, 1`. -/
private theorem denominator_bezout_identity (t X : ℚ) :
    (t ^ 3 - t ^ 2 + 2 * t - 1) ^ 3 * G18 t X =
      4 * t ^ 8 * (t - 1) ^ 9 * (t ^ 2 - t + 1) ^ 2
        + mapDenominator t X * denominatorBezoutQ t X := by
  simp only [G18, mapDenominator, denominatorBezoutQ]
  ring

private theorem mapDenominator_ne_zero
    {t X : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hG : G18 t X = 0) :
    mapDenominator t X ≠ 0 := by
  intro hden
  have hres :
      4 * t ^ 8 * (t - 1) ^ 9 * (t ^ 2 - t + 1) ^ 2 = 0 := by
    have h := (denominator_bezout_identity t X).symm
    simpa only [hG, hden, mul_zero, zero_mul, add_zero] using h
  have hq : t ^ 2 - t + 1 ≠ 0 := ne_of_gt (kubert_quadratic_pos t)
  have hres_ne :
      4 * t ^ 8 * (t - 1) ^ 9 * (t ^ 2 - t + 1) ^ 2 ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (pow_ne_zero 8 ht0))
        (pow_ne_zero 9 (sub_ne_zero.mpr ht1)))
      (pow_ne_zero 2 hq)
  exact hres_ne hres

/-- Exact substitution identity for the rational map from the Tate plane
model to the standard cubic model of `X₁(18)`. -/
private theorem standardG18_map_cleared (t X : ℚ) :
    standardG18Hom (mapNumerator t X) (mapDenominator t X) t =
      2 * t ^ 4 * (t - 1) ^ 4 * (t ^ 2 - t + 1) * G18 t X := by
  simp only [standardG18Hom, mapNumerator, mapDenominator, G18]
  set_option maxRecDepth 100000 in
    ring

private theorem standardG18_division_identity
    (N D V : ℚ) (hD : D ≠ 0) :
    D ^ 3 * standardG18 (N / D) V = standardG18Hom N D V := by
  simp only [standardG18, standardG18Hom]
  field_simp [hD]

private theorem standardG18_map_identity
    (t X : ℚ) (hden : mapDenominator t X ≠ 0) :
    mapDenominator t X ^ 3 *
        standardG18 (mapNumerator t X / mapDenominator t X) t =
      2 * t ^ 4 * (t - 1) ^ 4 * (t ^ 2 - t + 1) * G18 t X := by
  rw [standardG18_division_identity _ _ _ hden]
  exact standardG18_map_cleared t X

/-- Every noncuspidal point of the Tate plane model maps to the standard
affine model of `X₁(18)`. -/
theorem G18_to_standardG18
    {t X : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hG : G18 t X = 0) :
    ∃ U : ℚ, standardG18 U t = 0 := by
  have hden := mapDenominator_ne_zero ht0 ht1 hG
  refine ⟨mapNumerator t X / mapDenominator t X, ?_⟩
  have hmap := standardG18_map_identity t X hden
  rw [hG, mul_zero] at hmap
  exact (mul_eq_zero.mp hmap).resolve_left (pow_ne_zero 3 hden)

theorem standardG18_U_ne_zero
    {U t : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : standardG18 U t = 0) : U ≠ 0 := by
  intro hU
  subst U
  simp only [standardG18] at h
  apply (mul_ne_zero ht0 (sub_ne_zero.mpr ht1))
  nlinarith

theorem standardG18_U_ne_one
    {U t : ℚ} (ht0 : t ≠ 0) (h : standardG18 U t = 0) : U ≠ 1 := by
  intro hU
  subst U
  simp only [standardG18] at h
  apply ht0
  nlinarith

/-! ## The hyperelliptic model -/

def hyperellipticF18 (U : ℚ) : ℚ :=
  U ^ 6 - 4 * U ^ 5 + 10 * U ^ 4 - 10 * U ^ 3
    + 5 * U ^ 2 - 2 * U + 1

def hyperellipticY18 (U V : ℚ) : ℚ :=
  2 * (U - 1) ^ 2 * V - (U ^ 3 - U + 1)

/-- Completing the square in the second coordinate of the standard cubic
gives the usual genus-two hyperelliptic equation. -/
theorem standardG18_to_hyperelliptic
    {U V : ℚ} (h : standardG18 U V = 0) :
    hyperellipticY18 U V ^ 2 = hyperellipticF18 U := by
  calc
    hyperellipticY18 U V ^ 2 =
        hyperellipticF18 U + 4 * (U - 1) ^ 2 * standardG18 U V := by
      simp only [hyperellipticY18, hyperellipticF18, standardG18]
      ring
    _ = hyperellipticF18 U := by rw [h]; ring

/-- The original simultaneous `F9`/`T2` obstruction produces a noncuspidal
rational point on the standard hyperelliptic model of `X₁(18)`. -/
theorem obstruction_to_hyperelliptic
    {b c X : ℚ} (hb : b ≠ 0) (hF9 : TateNFDivision.F9 b c = 0)
    (hT2 : TateNFDivision.T2 b c X = 0) :
    ∃ U Y : ℚ,
      U ≠ 0 ∧ U ≠ 1 ∧ Y ^ 2 = hyperellipticF18 U := by
  obtain ⟨t, ht0, ht1, hG⟩ := obstruction_to_G18 hb hF9 hT2
  obtain ⟨U, hstandard⟩ := G18_to_standardG18 ht0 ht1 hG
  refine ⟨U, hyperellipticY18 U t,
    standardG18_U_ne_zero ht0 ht1 hstandard,
    standardG18_U_ne_one ht0 hstandard, ?_⟩
  exact standardG18_to_hyperelliptic hstandard

end

end MazurProof.RationalPointsN18
