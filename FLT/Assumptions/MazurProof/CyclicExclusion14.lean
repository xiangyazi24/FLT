import FLT.Assumptions.MazurProof.CyclicOrderReduction
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.TateOrder18
import scratch.DischargeN14

/-!
# Cyclic exclusion for order 14

This file records the cyclic `N = 14` composite exclusion needed by
`CyclicOrderReduction`.

The existing `DescentBridgeN14` file excludes the noncyclic subgroup
`ZMod 2 × ZMod 14`; that is not enough for a cyclic point of order `14`.
Here the cyclic case is routed through its own Tate/Kubert modular-curve
bridge to the same `N = 14` obstruction curve

`w² = u³ + u² - 2u`.

The remaining external computation is isolated as
`cyclic_order_14_kubert_bridge`: a rational point of order `14` gives a
nondegenerate rational point on the `N = 14` obstruction curve.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof

namespace CyclicExclusion14

noncomputable section

open Scratch.TateZ2xZ10Reduction

private abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

/-! ## The order-seven division condition at the Tate origin -/

private theorem tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W]

private def tateOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

private theorem psi_ne_zero_rat (W : WeierstrassCurve ℚ) :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hψ₂_ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
        (Polynomial.C_ne_zero.mpr (two_ne_zero (α := ℚ))),
        Polynomial.natDegree_zero]
      omega)
  have hψ₂_deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsi_ne : ∀ n : ℕ, n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hψ₂_ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsi_deg : ∀ n : ℕ, n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree
            ≤ 0 + 1 := Polynomial.natDegree_mul_le |>.trans
              (Nat.add_le_add (Polynomial.natDegree_C _).le hψ₂_deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hPsi :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hPsi (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne n (by intro h; exact hm (by simp [h])))
      (hPsi_deg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne _ (Nat.succ_ne_zero n))
      (hPsi_deg _ (Nat.succ_ne_zero n))

private theorem nsmul_eq_zero_iff_PsiSq_eval
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n : ℕ} {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    n • (WeierstrassCurve.Affine.Point.some x y h : (W⁄ℚ).Point) = 0 ↔
      (W.ΨSq (n : ℤ)).eval x = 0 := by
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hc3 : W.Ψ₃ ≠ 0 :=
    WeierstrassCurve.Ψ₃_ne_zero W (by norm_num)
  have key := KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval
    W h4 (psi_ne_zero_rat W) hc3 (n := n) h
  convert key using 3
  congr
  exact Subsingleton.elim _ _

private lemma eval_prePsi_five (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_seven (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 =
      ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 3).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 ^ 3 * ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 1)
  simpa using h

private theorem prePsi_seven_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 = b ^ 16 * TateNFDivision.F7 b c := by
  rw [eval_prePsi_seven, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F7]
  ring

private theorem F7_eq_zero_of_tateOrigin_order_seven
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 7) :
    TateNFDivision.F7 b c = 0 := by
  have h7 : (7 : ℕ) • tateOrigin b c = 0 := by
    simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)
  have hPsiSq : ((W b c).ΨSq (7 : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp h7
  have hpre : ((W b c).preΨ' 7).eval 0 = 0 := by
    change ((W b c).ΨSq (7 : ℕ)).eval 0 = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 7] at hPsiSq
    simpa [show ¬ Even (7 : ℕ) by decide] using hPsiSq
  rw [prePsi_seven_eval_tate_origin] at hpre
  exact (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 16 hb)

private lemma tateOrigin_eq_order18_tateOrigin
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    tateOrigin b c = TateOrder18.tateOrigin b c := by
  change WeierstrassCurve.Affine.Point.some 0 0 _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/-! ## Simultaneous order-seven/order-two normalization -/

private lemma addOrderOf_two_nsmul_of_order14
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 14) :
    addOrderOf ((2 : ℕ) • P) = 7 := by
  rw [addOrderOf_nsmul' P (by norm_num), hP]
  norm_num

private lemma addOrderOf_seven_nsmul_of_order14
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 14) :
    addOrderOf ((7 : ℕ) • P) = 2 := by
  rw [addOrderOf_nsmul' P (by norm_num), hP]
  norm_num

/-- An exact order-14 point produces the order-seven division equation and a
rational root of the two-division cubic on one and the same Tate curve. -/
theorem order14_to_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h14 : HasRationalPointOfOrder E 14) :
    ∃ b c X : ℚ,
      b ≠ 0 ∧ TateNFDivision.F7 b c = 0 ∧
        TateNFDivision.T2 b c X = 0 := by
  obtain ⟨P, hP⟩ := h14
  let Q : (E⁄ℚ).Point := (2 : ℕ) • P
  let R : (E⁄ℚ).Point := (7 : ℕ) • P
  have hQord : addOrderOf Q = 7 := addOrderOf_two_nsmul_of_order14 hP
  have hRord : addOrderOf R = 2 := addOrderOf_seven_nsmul_of_order14 hP
  have hR2 : (2 : ℕ) • R = 0 := by
    have h := addOrderOf_nsmul_eq_zero R
    rwa [hRord] at h
  have hRne0 : R ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hRord
    exact absurd hRord (by norm_num)
  obtain ⟨b, c, X, Y, hEll, hT, hord, hb, h2⟩ :=
    TateOrder18.exists_tate_normalized_2torsion_of_addOrder_gt_three
      E Q R 7 (by norm_num) hQord hR2 hRne0
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have hord' : addOrderOf (tateOrigin b c) = 7 := by
    rw [tateOrigin_eq_order18_tateOrigin]
    exact hord
  exact ⟨b, c, X, hb,
    F7_eq_zero_of_tateOrigin_order_seven b c hb hord',
    TateOrder18.T2_eq_zero_of_two_nsmul b c X Y hT h2⟩

/-! ## Elimination of the Tate parameters -/

/-- Kubert's order-seven parameter `b`. -/
def kubertB7 (t : ℚ) : ℚ := t ^ 2 * (t - 1)

/-- Kubert's order-seven parameter `c`. -/
def kubertC7 (t : ℚ) : ℚ := t * (t - 1)

private theorem c_ne_zero_of_F7
    {b c : ℚ} (hb : b ≠ 0) (hF7 : TateNFDivision.F7 b c = 0) :
    c ≠ 0 := by
  intro hc
  subst c
  have hb2 : b ^ 2 = 0 := by
    simp only [TateNFDivision.F7, zero_pow (by norm_num : 3 ≠ 0),
      mul_zero, add_zero] at hF7
    linarith
  exact hb (sq_eq_zero_iff.mp hb2)

private def recoveredT (b c : ℚ) : ℚ := b / c

private theorem recovered_c
    {b c : ℚ} (hb : b ≠ 0) (hF7 : TateNFDivision.F7 b c = 0) :
    c = kubertC7 (recoveredT b c) := by
  have hc := c_ne_zero_of_F7 hb hF7
  simp only [recoveredT, kubertC7]
  simp only [TateNFDivision.F7] at hF7
  field_simp [hc]
  ring_nf at hF7 ⊢
  linarith

private theorem recovered_b
    {b c : ℚ} (hb : b ≠ 0) (hF7 : TateNFDivision.F7 b c = 0) :
    b = kubertB7 (recoveredT b c) := by
  have hc := c_ne_zero_of_F7 hb hF7
  simp only [recoveredT, kubertB7]
  simp only [TateNFDivision.F7] at hF7
  field_simp [hc]
  ring_nf at hF7 ⊢
  linarith

private theorem recoveredT_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hF7 : TateNFDivision.F7 b c = 0) :
    recoveredT b c ≠ 0 :=
  div_ne_zero hb (c_ne_zero_of_F7 hb hF7)

private theorem recoveredT_ne_one
    {b c : ℚ} (hb : b ≠ 0) (hF7 : TateNFDivision.F7 b c = 0) :
    recoveredT b c ≠ 1 := by
  have hc := c_ne_zero_of_F7 hb hF7
  intro ht
  have hbc : b = c := (div_eq_one_iff_eq hc).mp ht
  rw [hbc] at hF7
  have hcub : c ^ 3 = 0 := by
    simp only [TateNFDivision.F7] at hF7
    ring_nf at hF7 ⊢
    exact hF7
  exact (pow_ne_zero 3 hc) hcub

/-- Every nondegenerate solution of `F7 = 0` has Kubert's one-parameter
form, with the two cusp parameters removed. -/
theorem F7_parametrization
    {b c : ℚ} (hb : b ≠ 0) (hF7 : TateNFDivision.F7 b c = 0) :
    ∃ t : ℚ, t ≠ 0 ∧ t ≠ 1 ∧
      b = kubertB7 t ∧ c = kubertC7 t := by
  exact ⟨recoveredT b c, recoveredT_ne_zero hb hF7,
    recoveredT_ne_one hb hF7, recovered_b hb hF7, recovered_c hb hF7⟩

/-- The explicit affine order-14 equation obtained after substituting the
order-seven Kubert family into the rational two-torsion cubic. -/
def rawX14Polynomial (t X : ℚ) : ℚ :=
  4 * X ^ 3
    + (t ^ 4 - 6 * t ^ 3 + 3 * t ^ 2 + 2 * t + 1) * X ^ 2
    + (2 * t ^ 5 - 4 * t ^ 4 + 2 * t ^ 2) * X
    + t ^ 6 - 2 * t ^ 5 + t ^ 4

/-- A noncuspidal rational point on the raw `X₁(14)` model. -/
def RawOrder14Obstruction : Prop :=
  ∃ t X : ℚ, t ≠ 0 ∧ t ≠ 1 ∧ rawX14Polynomial t X = 0

theorem T2_kubert_eq_rawX14Polynomial (t X : ℚ) :
    TateNFDivision.T2 (kubertB7 t) (kubertC7 t) X =
      rawX14Polynomial t X := by
  simp only [TateNFDivision.T2, kubertB7, kubertC7, rawX14Polynomial]
  ring

/-- Fully formal forward reduction from an exact order-14 point to a
noncuspidal rational point on an explicit affine model of `X₁(14)`. -/
theorem order14_to_raw_X1_14
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h14 : HasRationalPointOfOrder E 14) :
    RawOrder14Obstruction := by
  obtain ⟨b, c, X, hb, hF7, hT2⟩ := order14_to_tate_obstruction E h14
  obtain ⟨t, ht0, ht1, hbparam, hcparam⟩ := F7_parametrization hb hF7
  subst b
  subst c
  refine ⟨t, X, ht0, ht1, ?_⟩
  rw [← T2_kubert_eq_rawX14Polynomial]
  exact hT2

/-! ## Birational passage to the standard `X₁(14)` model -/

/-- The denominator in the square-root coordinate on the raw model. -/
def rawAuxDen (t X : ℚ) : ℚ := t ^ 2 - t - X

/-- The numerator in the square-root coordinate on the raw model. -/
def rawAuxNum (t X : ℚ) : ℚ :=
  t ^ 3 + t ^ 2 * X - t ^ 2 - 3 * t * X + X

/-- A rational square root of `-X` on the raw model. -/
def rawAuxZ (t X : ℚ) : ℚ :=
  rawAuxNum t X / (2 * rawAuxDen t X)

/-- The cubic relation satisfied by the square-root coordinate. -/
def rawCubicRelation (t z : ℚ) : ℚ :=
  -t ^ 3 + t ^ 2 * z ^ 2 + 2 * t ^ 2 * z + t ^ 2
    - 3 * t * z ^ 2 - 2 * t * z + 2 * z ^ 3 + z ^ 2

theorem rawX14Polynomial_at_den_zero (t : ℚ) :
    rawX14Polynomial t (t ^ 2 - t) = t ^ 2 * (t - 1) ^ 6 := by
  simp only [rawX14Polynomial]
  ring

theorem rawAuxDen_ne_zero
    {t X : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hraw : rawX14Polynomial t X = 0) :
    rawAuxDen t X ≠ 0 := by
  intro hden
  have hX : X = t ^ 2 - t := by
    dsimp [rawAuxDen] at hden
    linarith
  rw [hX, rawX14Polynomial_at_den_zero] at hraw
  exact (mul_ne_zero (pow_ne_zero 2 ht0)
    (pow_ne_zero 6 (sub_ne_zero.mpr ht1))) hraw

/-- The key polynomial identity exposing `-X` as a square on the raw model. -/
theorem rawAux_square_identity (t X : ℚ) :
    rawAuxNum t X ^ 2 + X * (2 * rawAuxDen t X) ^ 2 =
      rawX14Polynomial t X := by
  simp only [rawAuxNum, rawAuxDen, rawX14Polynomial]
  ring

theorem rawAuxZ_sq
    {t X : ℚ} (hden : rawAuxDen t X ≠ 0)
    (hraw : rawX14Polynomial t X = 0) :
    rawAuxZ t X ^ 2 = -X := by
  have hid := rawAux_square_identity t X
  rw [hraw] at hid
  dsimp [rawAuxZ]
  field_simp [hden]
  ring_nf at hid ⊢
  linarith

theorem rawAuxZ_linear
    {t X : ℚ} (hden : rawAuxDen t X ≠ 0) :
    2 * rawAuxDen t X * rawAuxZ t X = rawAuxNum t X := by
  dsimp [rawAuxZ]
  field_simp [hden]

theorem rawAuxZ_cubic_relation
    {t X : ℚ} (hden : rawAuxDen t X ≠ 0)
    (hraw : rawX14Polynomial t X = 0) :
    rawCubicRelation t (rawAuxZ t X) = 0 := by
  let z := rawAuxZ t X
  have hsq : z ^ 2 + X = 0 := by
    dsimp [z]
    linarith [rawAuxZ_sq hden hraw]
  have hlin : 2 * rawAuxDen t X * z - rawAuxNum t X = 0 := by
    dsimp [z]
    linarith [rawAuxZ_linear hden]
  dsimp [rawCubicRelation, rawAuxDen, rawAuxNum] at hlin ⊢
  linear_combination (t ^ 2 - 3 * t + 2 * z + 1) * hsq + hlin

theorem rawAuxZ_ne_t
    {t X : ℚ} (ht0 : t ≠ 0)
    (hrel : rawCubicRelation t (rawAuxZ t X) = 0) :
    rawAuxZ t X ≠ t := by
  intro hzt
  rw [hzt] at hrel
  have ht4 : t ^ 4 = 0 := by
    dsimp [rawCubicRelation] at hrel
    ring_nf at hrel ⊢
    exact hrel
  exact (pow_ne_zero 4 ht0) ht4

/-- The first coordinate on `X₁(14) : s² + us + s = u³ - u`. -/
def rawToX14U (t X : ℚ) : ℚ :=
  rawAuxZ t X / (rawAuxZ t X - t)

/-- The second coordinate on `X₁(14) : s² + us + s = u³ - u`. -/
def rawToX14S (t X : ℚ) : ℚ :=
  -t * rawToX14U t X ^ 2 * (rawToX14U t X - 1)
    - rawToX14U t X ^ 2 - 1

theorem rawToX14_equation
    {t X : ℚ} (ht0 : t ≠ 0)
    (hrel : rawCubicRelation t (rawAuxZ t X) = 0) :
    Scratch.DischargeN14.X14Equation (rawToX14U t X) (rawToX14S t X) := by
  let z := rawAuxZ t X
  have hzt : z - t ≠ 0 := sub_ne_zero.mpr (rawAuxZ_ne_t ht0 hrel)
  dsimp [Scratch.DischargeN14.X14Equation, rawToX14S, rawToX14U]
  change
    (-t * (z / (z - t)) ^ 2 * (z / (z - t) - 1)
        - (z / (z - t)) ^ 2 - 1) ^ 2
      + (z / (z - t)) *
          (-t * (z / (z - t)) ^ 2 * (z / (z - t) - 1)
            - (z / (z - t)) ^ 2 - 1)
      + (-t * (z / (z - t)) ^ 2 * (z / (z - t) - 1)
          - (z / (z - t)) ^ 2 - 1) =
        (z / (z - t)) ^ 3 - z / (z - t)
  field_simp [hzt]
  dsimp [rawCubicRelation] at hrel
  linear_combination t ^ 2 * z ^ 2 * hrel

theorem rawToX14_nondegenerate
    {t X : ℚ} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hrel : rawCubicRelation t (rawAuxZ t X) = 0) :
    ¬ Scratch.DischargeN14.X14DegenerateParameter (rawToX14U t X) := by
  let z := rawAuxZ t X
  have hzt : z - t ≠ 0 := sub_ne_zero.mpr (rawAuxZ_ne_t ht0 hrel)
  have hrelz : rawCubicRelation t z = 0 := by
    simpa [z] using hrel
  intro hdeg
  rcases hdeg with hu | hu | hu
  · have hz : z = t / 2 := by
      have hmul : z = (-1 : ℚ) * (z - t) := by
        apply (div_eq_iff hzt).mp
        simpa [rawToX14U, z] using hu
      linarith
    have hprod : t ^ 2 * (t - 1) ^ 2 = 0 := by
      dsimp [rawCubicRelation] at hrelz
      rw [hz] at hrelz
      ring_nf at hrelz ⊢
      linarith
    exact (mul_ne_zero (pow_ne_zero 2 ht0)
      (pow_ne_zero 2 (sub_ne_zero.mpr ht1))) hprod
  · have hz : z = 0 := by
      have hdiv : z / (z - t) = 0 := by
        simpa [rawToX14U, z] using hu
      exact (div_eq_zero_iff.mp hdiv).resolve_right hzt
    have hprod : t ^ 2 * (1 - t) = 0 := by
      dsimp [rawCubicRelation] at hrelz
      rw [hz] at hrelz
      ring_nf at hrelz ⊢
      exact hrelz
    exact (mul_ne_zero (pow_ne_zero 2 ht0)
      (sub_ne_zero.mpr (Ne.symm ht1))) hprod
  · have hzt_eq : z = z - t := by
      apply (div_eq_one_iff_eq hzt).mp
      simpa [rawToX14U, z] using hu
    exact ht0 (by linarith)

/-- The raw Tate obstruction maps to a noncuspidal rational point on the
standard cyclic modular curve `X₁(14)`. -/
theorem raw_obstruction_to_X14
    (hraw : RawOrder14Obstruction) :
    ∃ u s : ℚ, Scratch.DischargeN14.X14Equation u s ∧
      ¬ Scratch.DischargeN14.X14DegenerateParameter u := by
  obtain ⟨t, X, ht0, ht1, hpoly⟩ := hraw
  have hden := rawAuxDen_ne_zero ht0 ht1 hpoly
  have hrel := rawAuxZ_cubic_relation hden hpoly
  exact ⟨rawToX14U t X, rawToX14S t X,
    rawToX14_equation ht0 hrel, rawToX14_nondegenerate ht0 ht1 hrel⟩

end

end CyclicExclusion14

/-! ## Order 14 is a composite residual -/

theorem needs_composite_exclusion_14 : NeedsCompositeExclusion 14 := by
  refine needs_composite_exclusion_of_small_prime_factors ?_ ?_ ?_
  · norm_num
  · norm_num [allowedCyclicOrders]
  · intro p hp hpdvd
    have hp_le : p ≤ 14 := Nat.le_of_dvd (by norm_num) hpdvd
    have hp_ge : 2 ≤ p := hp.two_le
    interval_cases p
    all_goals simp [allowedPrimeOrders] at hpdvd ⊢
    all_goals norm_num at hp

/-! ## Elementary prime-order reductions from a point of order 14 -/

theorem order14_gives_order7
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 14) :
    HasRationalPointOfOrder E 7 :=
  exists_point_of_prime_order_of_dvd (E := E) (n := 14) (p := 7)
    (by norm_num) (by norm_num) (by norm_num) h

theorem order14_gives_order2
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 14) :
    HasRationalPointOfOrder E 2 :=
  exists_point_of_prime_order_of_dvd (E := E) (n := 14) (p := 2)
    (by norm_num) (by norm_num) (by norm_num) h

/-! ## Cyclic `N = 14` modular-curve bridge -/

/--
The cyclic `N = 14` Tate/Kubert computation.

Mathematically, one starts from the Tate normal form with a marked point of
order `7`, imposes that the marked lift has order `14`, and obtains a rational
point on `w² = u³ + u² - 2u`.  Nondegeneracy excludes the cuspidal parameters.
-/
def CyclicOrder14KubertBridge : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    HasRationalPointOfOrder E 14 →
      ∃ u w : ℚ, E_N14_AffineEquation u w ∧ ¬ E_N14_DegenerateParameter u

/--
Residual cyclic `N = 14` bridge.

This is the only cyclic-order-specific modular-curve computation in this file;
the contradiction after this point is formal.
-/
theorem cyclic_order_14_kubert_bridge : CyclicOrder14KubertBridge := by
  intro E hEll horder
  sorry

/-! ## Exclusion theorem -/

theorem no_rational_point_of_order_14_of_kubert_bridge
    (hbridge : CyclicOrder14KubertBridge)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 14 := by
  intro horder
  rcases hbridge E horder with ⟨u, w, hcurve, hnondeg⟩
  exact hnondeg (obstruction_curve_N14_points_degenerate u w hcurve)

/-- No elliptic curve over `ℚ` has a rational point of order `14`. -/
theorem no_rational_point_of_order_14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 14 :=
  no_rational_point_of_order_14_of_kubert_bridge cyclic_order_14_kubert_bridge E

theorem no_rational_point_of_order_eq_14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ} (hn : n = 14) :
    ¬ HasRationalPointOfOrder E n := by
  subst hn
  exact no_rational_point_of_order_14 E

end MazurProof
