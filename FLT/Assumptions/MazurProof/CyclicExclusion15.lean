import FLT.Assumptions.MazurProof.CyclicOrderReduction
import FLT.Assumptions.MazurProof.TateNFDivision
import FLT.Assumptions.MazurProof.TateNormalFormBridge
import FLT.Assumptions.MazurProof.RationalPointsX115
import scratch.KeystoneEDS

/-!
# Cyclic order 15 exclusion

A rational point of exact order `15 = 3 * 5` gives rational points of
orders `5` and `3` by taking `3 • P` and `5 • P`.  The remaining arithmetic
input is the rational-points computation on `X₁(15)`: over `ℚ`, the curve has
only cuspidal rational points, equivalently no elliptic curve over `ℚ` has
simultaneously a rational point of order `3` and one of order `5`.
-/

open scoped WeierstrassCurve.Affine
open Polynomial

namespace MazurProof

/-! ## Elementary order extraction from a point of order 15 -/

theorem addOrderOf_three_nsmul_of_order15
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 15) :
    addOrderOf (3 • P) = 5 := by
  rw [addOrderOf_nsmul' P (by norm_num : (3 : ℕ) ≠ 0), hP]
  norm_num

theorem addOrderOf_five_nsmul_of_order15
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {P : (E⁄ℚ).Point} (hP : addOrderOf P = 15) :
    addOrderOf (5 • P) = 3 := by
  rw [addOrderOf_nsmul' P (by norm_num : (5 : ℕ) ≠ 0), hP]
  norm_num

theorem order15_gives_order5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 5 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨3 • P, addOrderOf_three_nsmul_of_order15 hP⟩

theorem order15_gives_order3
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 3 := by
  rcases hord with ⟨P, hP⟩
  exact ⟨5 • P, addOrderOf_five_nsmul_of_order15 hP⟩

theorem order15_gives_orders3_and5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hord : HasRationalPointOfOrder E 15) :
    HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5 :=
  ⟨order15_gives_order3 E hord, order15_gives_order5 E hord⟩

/-! ## Position of `15` in the composite-order reduction framework -/

theorem needs_composite_exclusion_15 : NeedsCompositeExclusion 15 := by
  refine needs_composite_exclusion_of_small_prime_factors ?_ ?_ ?_
  · norm_num
  · norm_num [allowedCyclicOrders]
  · intro p hp hpdvd
    have hp35 : p ∣ 3 * 5 := by
      simpa using hpdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp35 with hp3 | hp5
    · have hp_eq : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp3
      rw [hp_eq]
      norm_num [allowedPrimeOrders]
    · have hp_eq : p = 5 :=
        (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp5
      rw [hp_eq]
      norm_num [allowedPrimeOrders]

theorem no_order15_from_future_composite_exclusions
    (hcomp : FutureCompositeExclusions)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 :=
  hcomp E (n := 15) (by norm_num) needs_composite_exclusion_15

namespace CyclicExclusion15

open Scratch.TateZ2xZ10Reduction

noncomputable section

/-! ## Tate normal form for the `3`-and-`5` obstruction -/

/--
The Tate normal form after imposing that `(0,0)` has order `5`:

`y² + (1-b)xy - by = x³ - bx²`.

For the usual two-parameter Tate normal form, the order-`5` condition is
`c = b`.
-/
def tateOrder5Curve (b : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b b

/-- The explicit `ψ₃` polynomial in the Tate order-`5` parameter. -/
def tateOrder5Psi3 (b x : ℚ) : ℚ :=
  3 * x ^ 4 + (b ^ 2 - 6 * b + 1) * x ^ 3 +
    3 * (b ^ 2 - b) * x ^ 2 + 3 * b ^ 2 * x - b ^ 3

/-- The nonsingularity condition for the Tate order-`5` normal form. -/
def TateOrder5NonsingularParameter (b : ℚ) : Prop :=
  b ^ 5 * (b ^ 2 - 11 * b - 1) ≠ 0

/-- The Tate curve equation with `c = b` (order-5 specialization). -/
def TateOrder5CurveEq (b x y : ℚ) : Prop :=
  y ^ 2 + (1 - b) * x * y - b * y = x ^ 3 - b * x ^ 2

/--
The exact Diophantine obstruction needed for `X₁(15)`: a nonsingular Tate
order-`5` normal form has no rational point `(x,y)` on the curve with
`ψ₃(x) = 0`.

Note: ψ₃ CAN have rational roots (e.g. `b = -2, x = -1`) without producing
a rational 3-torsion point, because the curve equation may have no rational `y`.
-/
def TateOrder5Psi3RootSolution (b x y : ℚ) : Prop :=
  TateOrder5NonsingularParameter b ∧ TateOrder5CurveEq b x y ∧
    tateOrder5Psi3 b x = 0

theorem tateOrder5Curve_discriminant (b : ℚ) :
    (tateOrder5Curve b).Δ = b ^ 5 * (b ^ 2 - 11 * b - 1) := by
  simp [tateOrder5Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem tateOrder5Curve_psi3_eval (b x : ℚ) :
    ((tateOrder5Curve b).Ψ₃).eval x = tateOrder5Psi3 b x := by
  simp [tateOrder5Curve, tateOrder5Psi3, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-! ### Reusable division-polynomial facts over `ℚ` -/

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

private theorem psi3_eval_zero_of_order_three
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y)
    (hord : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y h : (W⁄ℚ).Point) = 3) :
    W.Ψ₃.eval x = 0 := by
  let T : (W⁄ℚ).Point := WeierstrassCurve.Affine.Point.some x y h
  have h3 : (3 : ℕ) • T = 0 := by
    simpa [T, hord] using addOrderOf_nsmul_eq_zero T
  have hPsiSq : (W.ΨSq (3 : ℤ)).eval x = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval W h).mp h3
  change (W.ΨSq (3 : ℕ)).eval x = 0 at hPsiSq
  rw [W.ΨSq_ofNat 3] at hPsiSq
  simpa [show ¬ Even (3 : ℕ) by decide,
    WeierstrassCurve.preΨ'_three] using hPsiSq

/-! ### Order five at the Tate origin forces `c = b` -/

private abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

private lemma normalized_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W, tateNormalFormCurve]

private def normalizedOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0
    (normalized_origin_nonsingular b c)

private lemma eval_prePsi_five (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
  simpa using h

private theorem prePsi_five_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 = b ^ 8 * TateNFDivision.F5 b c := by
  rw [eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, TateNFDivision.F5]
  ring

private theorem c_eq_b_of_normalizedOrigin_order_five
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (normalizedOrigin b c) = 5) :
    c = b := by
  have h5 : (5 : ℕ) • normalizedOrigin b c = 0 := by
    simpa [hord] using addOrderOf_nsmul_eq_zero (normalizedOrigin b c)
  have hPsiSq : ((W b c).ΨSq (5 : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (normalized_origin_nonsingular b c)).mp h5
  have hpre : ((W b c).preΨ' 5).eval 0 = 0 := by
    change ((W b c).ΨSq (5 : ℕ)).eval 0 = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 5] at hPsiSq
    simpa [show ¬ Even (5 : ℕ) by decide] using hPsiSq
  rw [prePsi_five_eval_tate_origin] at hpre
  have hF5 : TateNFDivision.F5 b c = 0 :=
    (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 8 hb)
  exact (sub_eq_zero.mp hF5).symm

/-! ### Simultaneously transporting a second marked point -/

private noncomputable def pointCurveEqAddEquiv
    {W W' : WeierstrassCurve ℚ} (h : W = W') :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point W' := by
  subst h
  exact AddEquiv.refl _

private lemma pointCurveEqAddEquiv_some
    {W W' : WeierstrassCurve ℚ} (h : W = W') {x y : ℚ}
    {hW : WeierstrassCurve.Affine.Nonsingular W x y}
    {hW' : WeierstrassCurve.Affine.Nonsingular W' x y} :
    pointCurveEqAddEquiv h (WeierstrassCurve.Affine.Point.some x y hW) =
      WeierstrassCurve.Affine.Point.some x y hW' := by
  subst h
  change WeierstrassCurve.Affine.Point.some x y hW =
    WeierstrassCurve.Affine.Point.some x y hW'
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

private lemma origin_three_nsmul_eq_zero_of_a2_eq_zero
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {h0 : WeierstrassCurve.Affine.Nonsingular W 0 0}
    (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ ≠ 0)
    (ha₄ : W.a₄ = 0) (ha₆ : W.a₆ = 0) :
    (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some 0 0 h0 :
          WeierstrassCurve.Affine.Point W) = 0 := by
  let O : WeierstrassCurve.Affine.Point W :=
    WeierstrassCurve.Affine.Point.some 0 0 h0
  have hy : (0 : ℚ) ≠ WeierstrassCurve.Affine.negY W 0 0 := by
    intro h
    apply ha₃
    rw [WeierstrassCurve.Affine.negY] at h
    linarith
  have h2 : WeierstrassCurve.Affine.Nonsingular W 0 (-W.a₃) := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [ha₂, ha₄, ha₆]
    ring
  have h2eq :
      (2 : ℕ) • O =
        WeierstrassCurve.Affine.Point.some 0 (-W.a₃) h2 := by
    rw [two_nsmul]
    simp only [O]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
        ha₂, ha₄]
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
        ha₂, ha₄]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl]
  simp [WeierstrassCurve.Affine.negY]

/-- Normalize an exact order-five point to the Tate origin while transporting
an exact order-three point through the same two additive equivalences. -/
private theorem exists_normalized_order5_and_order3
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P5 P3 : (E⁄ℚ).Point)
    (hP5 : addOrderOf P5 = 5) (hP3 : addOrderOf P3 = 3) :
    ∃ b c x3 y3 : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      ∃ h3 : WeierstrassCurve.Affine.Nonsingular (W b c) x3 y3,
        addOrderOf (normalizedOrigin b c) = 5 ∧ b ≠ 0 ∧
          addOrderOf
            (WeierstrassCurve.Affine.Point.some x3 y3 h3 :
              WeierstrassCurve.Affine.Point (W b c)) = 3 := by
  cases P5 with
  | zero =>
      have hzero :
          addOrderOf (WeierstrassCurve.Affine.Point.zero : (E⁄ℚ).Point) = 1 := by
        rw [← WeierstrassCurve.Affine.Point.zero_def]
        simp
      rw [hzero] at hP5
      omega
  | some x₀ y₀ hPaff =>
      let hPaffE : WeierstrassCurve.Affine.Nonsingular E x₀ y₀ := by
        change WeierstrassCurve.Affine.Nonsingular (E⁄ℚ) x₀ y₀
        exact hPaff
      let P₀ : WeierstrassCurve.Affine.Point E :=
        WeierstrassCurve.Affine.Point.some x₀ y₀ hPaffE
      have hP₀_order : addOrderOf P₀ = 5 := by
        dsimp [P₀, hPaffE]
        change addOrderOf
          (WeierstrassCurve.Affine.Point.some x₀ y₀ hPaff) = 5
        exact hP5
      let Psmall₀ :
          ∀ m < 5, 0 < m → (m : ℕ) • P₀ ≠ 0 :=
        ((addOrderOf_eq_iff (x := P₀) (by norm_num : 0 < 5)).mp
          hP₀_order).2
      let T₀ : WeierstrassCurve.Affine.Point E := P3
      have hT₀_order : addOrderOf T₀ = 3 := by
        change addOrderOf (P3 : WeierstrassCurve.Affine.Point E) = 3
        exact hP3
      have hden : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by
        intro hden0
        have hy : y₀ = WeierstrassCurve.Affine.negY E x₀ y₀ := by
          rw [WeierstrassCurve.Affine.negY]
          linarith
        have h2zero : (2 : ℕ) • P₀ = 0 := by
          simpa [P₀, two_nsmul] using
            (WeierstrassCurve.Affine.Point.add_self_of_Y_eq
              (W := E) (h₁ := hPaff) hy)
        exact Psmall₀ 2 (by norm_num) (by norm_num) h2zero
      let C0 := translateToOriginTangent E x₀ y₀
      let W1 : WeierstrassCurve ℚ := C0 • E
      haveI : W1.IsElliptic := by
        dsimp [W1]
        infer_instance
      let φ0 : WeierstrassCurve.Affine.Point E ≃+
          WeierstrassCurve.Affine.Point W1 := by
        dsimp [W1]
        exact variableChangePointAddEquiv E C0
      have hW1a₆ : W1.a₆ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₆_eq_zero E
            (x₀ := x₀) (y₀ := y₀) hPaffE.1
      have hW1a₄ : W1.a₄ = 0 := by
        simpa [W1, C0] using
          translateToOriginTangent_a₄_eq_zero E
            (x₀ := x₀) (y₀ := y₀) hden
      have hW1a₃_formula : W1.a₃ = E.a₃ + E.a₁ * x₀ + 2 * y₀ := by
        simp [W1, C0]
      have hW1a₃_ne : W1.a₃ ≠ 0 := by
        rw [hW1a₃_formula]
        intro h
        apply hden
        linarith
      have hW1origin : WeierstrassCurve.Affine.Nonsingular W1 0 0 := by
        apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        rw [WeierstrassCurve.Affine.equation_iff]
        simp [hW1a₆]
      have hφ0P_origin :
          φ0 P₀ = WeierstrassCurve.Affine.Point.some 0 0 hW1origin := by
        change variableChangePointMap E C0 P₀ =
          WeierstrassCurve.Affine.Point.some 0 0 hW1origin
        dsimp [variableChangePointMap, P₀]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor <;>
          simp [C0, variableChangePointX,
            variableChangePointY, translateToOriginTangent]
      have hW1a₂_ne : W1.a₂ ≠ 0 := by
        intro hW1a₂
        have h3zero_origin :
            (3 : ℕ) •
                (WeierstrassCurve.Affine.Point.some 0 0 hW1origin :
                  WeierstrassCurve.Affine.Point W1) = 0 :=
          origin_three_nsmul_eq_zero_of_a2_eq_zero
            W1 hW1a₂ hW1a₃_ne hW1a₄ hW1a₆
        have h3zero_map : (3 : ℕ) • φ0 P₀ = 0 := by
          simpa [hφ0P_origin] using h3zero_origin
        have h3zero : (3 : ℕ) • P₀ = 0 := by
          apply (EquivLike.injective φ0)
          rw [map_nsmul, h3zero_map, map_zero]
        exact Psmall₀ 3 (by norm_num) (by norm_num) h3zero
      let ρ : ℚ := W1.a₃ / W1.a₂
      have hρ : ρ ≠ 0 := div_ne_zero hW1a₃_ne hW1a₂_ne
      let C1 := scaleByRho ρ hρ
      let b : ℚ := tateBFromCoefficients W1.a₂ W1.a₃
      let c : ℚ := tateCFromCoefficients W1.a₁ W1.a₂ W1.a₃
      have hW2eq : C1 • W1 = W b c := by
        ext <;> dsimp [C1, ρ, b, c, W, tateNormalFormCurve,
          tateBFromCoefficients, tateCFromCoefficients]
        · rw [WeierstrassCurve.variableChange_a₁]
          simp [scaleByRho]
          field_simp [hW1a₂_ne, hW1a₃_ne]
        · rw [scaleByTateRho_a₂ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · rw [scaleByTateRho_a₃ W1 hW1a₂_ne hW1a₃_ne]
          ring
        · simp [WeierstrassCurve.variableChange_a₄, scaleByRho, hW1a₄]
        · simp [WeierstrassCurve.variableChange_a₆, scaleByRho, hW1a₆]
      haveI : WeierstrassCurve.IsElliptic (W b c) := by
        rw [← hW2eq]
        infer_instance
      let φ1raw : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (C1 • W1) :=
        variableChangePointAddEquiv W1 C1
      let φ1 : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (W b c) :=
        φ1raw.trans (pointCurveEqAddEquiv hW2eq)
      have hφ1φ0P_origin : φ1 (φ0 P₀) = normalizedOrigin b c := by
        rw [hφ0P_origin]
        have hRawOrigin :
            WeierstrassCurve.Affine.Nonsingular (C1 • W1) 0 0 := by
          simpa [hW2eq] using normalized_origin_nonsingular b c
        have hφ1raw_origin :
            φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
              WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin := by
          change variableChangePointMap W1 C1
              (WeierstrassCurve.Affine.Point.some 0 0 hW1origin) =
            WeierstrassCurve.Affine.Point.some 0 0 hRawOrigin
          dsimp [variableChangePointMap]
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          constructor <;>
            simp [C1, variableChangePointX, variableChangePointY, scaleByRho]
        change (pointCurveEqAddEquiv hW2eq)
            (φ1raw (WeierstrassCurve.Affine.Point.some 0 0 hW1origin)) =
          normalizedOrigin b c
        rw [hφ1raw_origin]
        exact pointCurveEqAddEquiv_some hW2eq
      have hOriginOrder : addOrderOf (normalizedOrigin b c) = 5 := by
        have hmaporder : addOrderOf (φ1 (φ0 P₀)) = 5 := by
          calc
            addOrderOf (φ1 (φ0 P₀)) = addOrderOf (φ0 P₀) :=
              addOrderOf_injective φ1.toAddMonoidHom
                (EquivLike.injective φ1) (φ0 P₀)
            _ = addOrderOf P₀ :=
              addOrderOf_injective φ0.toAddMonoidHom
                (EquivLike.injective φ0) P₀
            _ = 5 := hP₀_order
        rwa [hφ1φ0P_origin] at hmaporder
      have hb : b ≠ 0 := by
        have hdiv : W1.a₂ ^ 3 / W1.a₃ ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 3 hW1a₂_ne) (pow_ne_zero 2 hW1a₃_ne)
        simpa [b, tateBFromCoefficients] using (neg_ne_zero.mpr hdiv)
      have hTmapOrder : addOrderOf (φ1 (φ0 T₀)) = 3 := by
        calc
          addOrderOf (φ1 (φ0 T₀)) = addOrderOf (φ0 T₀) :=
            addOrderOf_injective φ1.toAddMonoidHom
              (EquivLike.injective φ1) (φ0 T₀)
          _ = addOrderOf T₀ :=
            addOrderOf_injective φ0.toAddMonoidHom
              (EquivLike.injective φ0) T₀
          _ = 3 := hT₀_order
      cases hTpoint : φ1 (φ0 T₀) with
      | zero =>
          have hzeroPoint :
              addOrderOf
                (WeierstrassCurve.Affine.Point.zero :
                  WeierstrassCurve.Affine.Point (W b c)) = 1 := by
            rw [← WeierstrassCurve.Affine.Point.zero_def]
            simp
          have hzero : addOrderOf (φ1 (φ0 T₀)) = 1 := by
            rw [hTpoint]
            exact hzeroPoint
          omega
      | some x3 y3 h3 =>
          refine ⟨b, c, x3, y3, inferInstance, h3, hOriginOrder, hb, ?_⟩
          simpa [hTpoint] using hTmapOrder

set_option maxHeartbeats 1000000 in
-- Dependent transport across the specialized Tate-curve definition is kernel-intensive.
private theorem normalized_data_gives_tate_solution
    {b c x3 y3 : ℚ}
    (hTateEll : WeierstrassCurve.IsElliptic (W b c))
    (h3 : WeierstrassCurve.Affine.Nonsingular (W b c) x3 y3)
    (hOrigin5 : addOrderOf (normalizedOrigin b c) = 5)
    (hb : b ≠ 0)
    (hOrder3 :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some x3 y3 h3 :
          WeierstrassCurve.Affine.Point (W b c)) = 3) :
    ∃ b x y : ℚ, TateOrder5Psi3RootSolution b x y := by
  letI : WeierstrassCurve.IsElliptic (W b c) := hTateEll
  have hcb : c = b :=
    c_eq_b_of_normalizedOrigin_order_five b c hb hOrigin5
  subst c
  letI : WeierstrassCurve.IsElliptic (tateOrder5Curve b) := hTateEll
  have hdisc : TateOrder5NonsingularParameter b := by
    unfold TateOrder5NonsingularParameter
    rw [← tateOrder5Curve_discriminant]
    exact (tateOrder5Curve b).isUnit_Δ.ne_zero
  have heqRaw :
      WeierstrassCurve.Affine.Equation (tateOrder5Curve b) x3 y3 := h3.1
  rw [WeierstrassCurve.Affine.equation_iff] at heqRaw
  simp only [tateOrder5Curve, tateNormalFormCurve_a₁,
    tateNormalFormCurve_a₂, tateNormalFormCurve_a₃,
    tateNormalFormCurve_a₄, tateNormalFormCurve_a₆,
    zero_mul, add_zero] at heqRaw
  have heq : TateOrder5CurveEq b x3 y3 := by
    unfold TateOrder5CurveEq
    linear_combination heqRaw
  have hpsiEval : ((tateOrder5Curve b).Ψ₃).eval x3 = 0 :=
    psi3_eval_zero_of_order_three (tateOrder5Curve b) h3 hOrder3
  have hpsi : tateOrder5Psi3 b x3 = 0 := by
    rwa [tateOrder5Curve_psi3_eval] at hpsiEval
  exact ⟨b, x3, y3, hdisc, heq, hpsi⟩

/--
Moduli and division-polynomial bridge for `X₁(15)`.

From a curve over `ℚ` with rational points of exact orders `3` and `5`, put
the order-`5` point in Tate normal form, use the order-`5` condition `c = b`,
and evaluate the third division polynomial at the rational `x`-coordinate of
the order-`3` point.
-/
def SimultaneousOrder3And5TateBridge : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5 →
      ∃ b x y : ℚ, TateOrder5Psi3RootSolution b x y

/--
Residual bridge from the current torsion predicate to the explicit Tate
normal-form Diophantine problem.
-/
theorem simultaneous_order3_and5_tate_bridge :
    SimultaneousOrder3And5TateBridge := by
  intro E hEll htors
  rcases htors with ⟨⟨P3, hP3⟩, ⟨P5, hP5⟩⟩
  obtain ⟨b, c, x3, y3, hTateEll, h3, hOrigin5, hb, hOrder3⟩ :=
    exists_normalized_order5_and_order3 E P5 P3 hP5 hP3
  exact normalized_data_gives_tate_solution
    hTateEll h3 hOrigin5 hb hOrder3

/-! ## The explicit genus-one reduction -/

/-- The square obtained by completing the Tate order-five curve equation. -/
private def tateOrder5LiftRad (b x : ℚ) : ℚ :=
  4 * x ^ 3 + (b ^ 2 - 6 * b + 1) * x ^ 2 +
    2 * (b ^ 2 - b) * x + b ^ 2

/-- The normalized division-polynomial equation after writing `x = b*u`. -/
private def n15NormalizedPsi3 (b u : ℚ) : ℚ :=
  b ^ 2 * u ^ 3 + 3 * b * u ^ 2 * (u - 1) ^ 2 + (u - 1) ^ 3

/-- The quartic ordinate obtained from the quadratic equation in `b`. -/
private def n15QuarticW (b u : ℚ) : ℚ :=
  (2 * u ^ 3 * b + 3 * u ^ 2 * (u - 1) ^ 2) / (u * (u - 1))

/-- The genus-one quartic forced by a rational root of `ψ₃`. -/
private def N15QuarticEquation (u w : ℚ) : Prop :=
  w ^ 2 = u * (u - 1) * (3 * u + 1) * (3 * u - 4)

/-- The affine cubic used to classify the quartic rational points. -/
private def N15AuxiliaryEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 15) * (X - 16)

private def n15AuxX (u : ℚ) : ℚ :=
  12 + 4 / u

private def n15AuxY (u w : ℚ) : ℚ :=
  4 * w / u ^ 2

/-- The seven affine points in the expected rational-point classification.
The eighth point is the point at infinity. -/
private def N15AuxiliaryAffineCandidate (X Y : ℚ) : Prop :=
  (X = 0 ∧ Y = 0) ∨
    (X = 15 ∧ Y = 0) ∨
    (X = 16 ∧ Y = 0) ∨
    (X = 12 ∧ Y = 12) ∨
    (X = 12 ∧ Y = -12) ∨
    (X = 20 ∧ Y = 20) ∨
    (X = 20 ∧ Y = -20)

/-- The only four `(b,x)` pairs that can survive the non-boundary inverse
map from the quartic. -/
private def N15TateCandidate (b x : ℚ) : Prop :=
  (b = 8 ∧ x = -(8 / 3)) ∨
    (b = -(1 / 8) ∧ x = -(1 / 6)) ∨
    (b = -2 ∧ x = -1) ∨
    (b = 1 / 2 ∧ x = 1 / 4)

/-- Completing the square in the Tate curve equation. -/
private theorem tateOrder5CurveEq_square_completion {b x y : ℚ}
    (hcurve : TateOrder5CurveEq b x y) :
    (2 * y + (1 - b) * x - b) ^ 2 = tateOrder5LiftRad b x := by
  unfold TateOrder5CurveEq at hcurve
  unfold tateOrder5LiftRad
  linear_combination 4 * hcurve

/-- Literal substitution of `x=b*u` in the third division polynomial. -/
private theorem tateOrder5Psi3_substitute (b u : ℚ) :
    tateOrder5Psi3 b (b * u) = b ^ 3 * n15NormalizedPsi3 b u := by
  unfold tateOrder5Psi3 n15NormalizedPsi3
  ring

private theorem n15_normalized_psi3 {b x : ℚ} (hb : b ≠ 0)
    (hpsi : tateOrder5Psi3 b x = 0) :
    n15NormalizedPsi3 b (x / b) = 0 := by
  have hxb : b * (x / b) = x := by field_simp
  have hsub := tateOrder5Psi3_substitute b (x / b)
  rw [hxb, hpsi] at hsub
  exact (mul_eq_zero.mp hsub.symm).resolve_left (pow_ne_zero 3 hb)

private theorem n15_u_ne_zero {b u : ℚ}
    (hnorm : n15NormalizedPsi3 b u = 0) : u ≠ 0 := by
  intro hu
  subst u
  norm_num [n15NormalizedPsi3] at hnorm

private theorem n15_u_ne_one {b u : ℚ} (hb : b ≠ 0)
    (hnorm : n15NormalizedPsi3 b u = 0) : u ≠ 1 := by
  intro hu
  subst u
  norm_num [n15NormalizedPsi3] at hnorm
  exact hb (by nlinarith [sq_nonneg b])

/-- The discriminant-square identity taking the normalized quadratic to the
quartic. -/
private theorem n15_normalized_to_quartic {b u : ℚ}
    (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (hnorm : n15NormalizedPsi3 b u = 0) :
    N15QuarticEquation u (n15QuarticW b u) := by
  unfold n15NormalizedPsi3 at hnorm
  unfold N15QuarticEquation n15QuarticW
  field_simp [hu0, sub_ne_zero.mpr hu1]
  linear_combination 4 * hnorm

/-- Inverse formula recovering `b` from a non-boundary quartic point. -/
private theorem n15_recover_b (b u : ℚ) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    b = (u - 1) * (n15QuarticW b u - 3 * u * (u - 1)) /
      (2 * u ^ 2) := by
  unfold n15QuarticW
  field_simp [hu0, sub_ne_zero.mpr hu1]
  ring

/-- The birational map from the quartic to
`Y² = X(X-15)(X-16)`. -/
private theorem n15_quartic_to_auxiliary {u w : ℚ} (hu0 : u ≠ 0)
    (hquartic : N15QuarticEquation u w) :
    N15AuxiliaryEquation (n15AuxX u) (n15AuxY u w) := by
  unfold N15AuxiliaryEquation n15AuxX n15AuxY
  field_simp [hu0]
  unfold N15QuarticEquation at hquartic
  rw [hquartic]
  ring

private theorem n15_auxX_ne_twelve {u : ℚ} (hu0 : u ≠ 0) :
    n15AuxX u ≠ 12 := by
  intro h
  have hzero : (4 : ℚ) / u = 0 := by
    unfold n15AuxX at h
    linarith
  exact (div_ne_zero (by norm_num) hu0) hzero

/-! ### Kernel-checked finite arithmetic for the two-descent -/

private def n15Reduce16to2 : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_two_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 2 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 120 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_six_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 6 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 40 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_ten_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 10 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 24 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_kummer_thirty_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ 30 * M ^ 4 - 31 * M ^ 2 * N ^ 2 + 8 * N ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction enumerates the `16^3` residue triples.
private theorem n15_no_dual_negative_class_mod16 :
    ∀ M N R : ZMod 16,
      (n15Reduce16to2 M ≠ 0 ∨ n15Reduce16to2 N ≠ 0) →
      R ^ 2 ≠ -(M ^ 4) + 62 * M ^ 2 * N ^ 2 - N ^ 4 := by
  decide

/-- The auxiliary cubic has seven affine points over `𝔽₇`; adding infinity
gives the good-reduction count `#E(𝔽₇)=8`. -/
private theorem n15_auxiliary_affine_mod7_card :
    ((Finset.univ.filter fun P : ZMod 7 × ZMod 7 =>
      P.2 ^ 2 = P.1 * (P.1 - 15) * (P.1 - 16)).card) = 7 := by
  decide

/-! ### The auxiliary two-isogeny as actual elliptic-curve point maps -/

private def n15AuxCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -31
  a₃ := 0
  a₄ := 240
  a₆ := 0

private def n15IsoCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 62
  a₃ := 0
  a₄ := 1
  a₆ := 0

private theorem n15AuxCurve_delta : n15AuxCurve.Δ = (921600 : ℚ) := by
  norm_num [n15AuxCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private theorem n15IsoCurve_delta : n15IsoCurve.Δ = (61440 : ℚ) := by
  norm_num [n15IsoCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private instance n15AuxCurve_isElliptic : n15AuxCurve.IsElliptic where
  isUnit := by rw [n15AuxCurve_delta]; norm_num

private instance n15IsoCurve_isElliptic : n15IsoCurve.IsElliptic where
  isUnit := by rw [n15IsoCurve_delta]; norm_num

private def N15IsogenousEquation (T V : ℚ) : Prop :=
  V ^ 2 = T ^ 3 + 62 * T ^ 2 + T

@[simp] private theorem n15AuxCurve_equation_iff (X Y : ℚ) :
    WeierstrassCurve.Affine.Equation n15AuxCurve X Y ↔
      N15AuxiliaryEquation X Y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold N15AuxiliaryEquation
  simp [n15AuxCurve]
  ring_nf

@[simp] private theorem n15IsoCurve_equation_iff (T V : ℚ) :
    WeierstrassCurve.Affine.Equation n15IsoCurve T V ↔
      N15IsogenousEquation T V := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold N15IsogenousEquation
  simp [n15IsoCurve]

private abbrev N15AuxPoint :=
  WeierstrassCurve.Affine.Point n15AuxCurve

private abbrev N15IsoPoint :=
  WeierstrassCurve.Affine.Point n15IsoCurve

private def n15ForwardX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2

private def n15ForwardY (x y : ℚ) : ℚ :=
  y * (240 - x ^ 2) / x ^ 2

private def n15DualX (x y : ℚ) : ℚ := y ^ 2 / x ^ 2 / 4

private def n15DualY (x y : ℚ) : ℚ :=
  y * (1 - x ^ 2) / x ^ 2 / 8

private theorem n15_forward_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation n15AuxCurve x y) :
    WeierstrassCurve.Affine.Equation n15IsoCurve
      (n15ForwardX x y) (n15ForwardY x y) := by
  rw [n15IsoCurve_equation_iff]
  have hcurve := (n15AuxCurve_equation_iff x y).mp h
  unfold N15AuxiliaryEquation at hcurve
  unfold N15IsogenousEquation n15ForwardX n15ForwardY
  field_simp [hx]
  rw [hcurve]
  ring

private theorem n15_dual_equation {x y : ℚ} (hx : x ≠ 0)
    (h : WeierstrassCurve.Affine.Equation n15IsoCurve x y) :
    WeierstrassCurve.Affine.Equation n15AuxCurve
      (n15DualX x y) (n15DualY x y) := by
  rw [n15AuxCurve_equation_iff]
  have hcurve := (n15IsoCurve_equation_iff x y).mp h
  unfold N15IsogenousEquation at hcurve
  unfold N15AuxiliaryEquation n15DualX n15DualY
  field_simp [hx]
  rw [hcurve]
  ring

private noncomputable def n15ForwardPoint : N15AuxPoint → N15IsoPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (n15_forward_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))

private noncomputable def n15DualPoint : N15IsoPoint → N15AuxPoint
  | .zero => .zero
  | .some x _y h =>
      if hx : x = 0 then .zero
      else WeierstrassCurve.Affine.Point.mk
        (n15_dual_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h))

@[simp] private theorem n15ForwardPoint_zero :
    n15ForwardPoint 0 = 0 := rfl

@[simp] private theorem n15DualPoint_zero :
    n15DualPoint 0 = 0 := rfl

@[simp] private theorem n15ForwardPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x = 0) :
    n15ForwardPoint (.some x y h) = 0 := by
  rw [n15ForwardPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

@[simp] private theorem n15DualPoint_some_of_x_eq_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15IsoCurve x y)
    (hx : x = 0) :
    n15DualPoint (.some x y h) = 0 := by
  rw [n15DualPoint]
  split <;> simp_all [WeierstrassCurve.Affine.Point.zero_def]

private theorem n15ForwardPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x ≠ 0) :
    n15ForwardPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (n15_forward_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [n15ForwardPoint, hx]

private theorem n15DualPoint_some_of_x_ne_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15IsoCurve x y)
    (hx : x ≠ 0) :
    n15DualPoint (.some x y h) =
      WeierstrassCurve.Affine.Point.mk
        (n15_dual_equation hx
          (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)) := by
  simp [n15DualPoint, hx]

private def n15DualPreimageX (r y : ℚ) : ℚ :=
  -31 + 2 * r ^ 2 - 2 * y / r

private def n15DualPreimageY (r y : ℚ) : ℚ :=
  2 * r * n15DualPreimageX r y

private def n15ForwardPreimageX (r y : ℚ) : ℚ :=
  (r ^ 2 + 31 - y / r) / 2

private def n15ForwardPreimageY (r y : ℚ) : ℚ :=
  r * n15ForwardPreimageX r y

/-- A square first coordinate on the auxiliary curve has an explicit
preimage under the dual isogeny. -/
private theorem n15_exists_dual_preimage_of_x_eq_sq {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ Q : N15IsoPoint,
      n15DualPoint Q = WeierstrassCurve.Affine.Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve : y ^ 2 = x ^ 3 - 31 * x ^ 2 + 240 * x := by
    have heq := (n15AuxCurve_equation_iff x y).mp h.1
    unfold N15AuxiliaryEquation at heq
    nlinarith
  have hcurveR : y ^ 2 = r ^ 6 - 31 * r ^ 4 + 240 * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let qx := n15DualPreimageX r y
  let qy := n15DualPreimageY r y
  have hprod :
      qx * (-31 + 2 * r ^ 2 + 2 * y / r) = 1 := by
    dsimp [qx, n15DualPreimageX]
    field_simp [hr0]
    linear_combination -4 * hcurveR
  have hqx : qx ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hprod
    norm_num at hprod
  have hnum : 1 - qx ^ 2 = 4 * qx * y / r := by
    rw [← hprod]
    dsimp [qx, n15DualPreimageX]
    field_simp [hr0]
    ring
  have hqeq : N15IsogenousEquation qx qy := by
    unfold N15IsogenousEquation
    dsimp [qx, qy, n15DualPreimageX, n15DualPreimageY]
    field_simp [hr0]
    linear_combination
      4 * (-2 * r ^ 3 + 31 * r + 2 * y) * hcurveR
  have hqns : WeierstrassCurve.Affine.Nonsingular n15IsoCurve qx qy :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((n15IsoCurve_equation_iff qx qy).mpr hqeq)
  let Q : N15IsoPoint :=
    WeierstrassCurve.Affine.Point.some qx qy hqns
  refine ⟨Q, ?_⟩
  dsimp [Q]
  rw [n15DualPoint_some_of_x_ne_zero hqns hqx]
  change WeierstrassCurve.Affine.Point.some
      (n15DualX qx qy) (n15DualY qx qy) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (2 * r * qx) ^ 2 / qx ^ 2 / 4 = x
    rw [hr]
    field_simp [hqx]
    ring
  · change (2 * r * qx) * (1 - qx ^ 2) / qx ^ 2 / 8 = y
    rw [hnum]
    field_simp [hqx, hr0]
    ring

/-- A square first coordinate on the isogenous curve has an explicit
preimage under the forward isogeny. -/
private theorem n15_exists_forward_preimage_of_x_eq_sq {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15IsoCurve x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ P : N15AuxPoint,
      n15ForwardPoint P = WeierstrassCurve.Affine.Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve : y ^ 2 = x ^ 3 + 62 * x ^ 2 + x :=
    (n15IsoCurve_equation_iff x y).mp h.1
  have hcurveR : y ^ 2 = r ^ 6 + 62 * r ^ 4 + r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := n15ForwardPreimageX r y
  let py := n15ForwardPreimageY r y
  have hprod :
      px * ((r ^ 2 + 31 + y / r) / 2) = 240 := by
    dsimp [px, n15ForwardPreimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    norm_num at hprod
  have hnum : 240 - px ^ 2 = px * y / r := by
    rw [← hprod]
    dsimp [px, n15ForwardPreimageX]
    field_simp [hr0]
    ring
  have hpeq : N15AuxiliaryEquation px py := by
    unfold N15AuxiliaryEquation
    dsimp [px, py, n15ForwardPreimageX, n15ForwardPreimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 - 31 * r + y) * hcurveR
  have hpns : WeierstrassCurve.Affine.Nonsingular n15AuxCurve px py :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((n15AuxCurve_equation_iff px py).mpr hpeq)
  let P : N15AuxPoint :=
    WeierstrassCurve.Affine.Point.some px py hpns
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [n15ForwardPoint_some_of_x_ne_zero hpns hpx]
  change WeierstrassCurve.Affine.Point.some
      (n15ForwardX px py) (n15ForwardY px py) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · change (r * px) ^ 2 / px ^ 2 = x
    rw [hr]
    field_simp [hpx]
  · change (r * px) * (240 - px ^ 2) / px ^ 2 = y
    rw [hnum]
    field_simp [hpx, hr0]

@[simp] private theorem n15AuxCurve_negY (x y : ℚ) :
    WeierstrassCurve.Affine.negY n15AuxCurve x y = -y := by
  simp [WeierstrassCurve.Affine.negY, n15AuxCurve]

private def n15AuxTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 - 62 * x + 240) / (2 * y)

private def n15TangentX (a₂ x m : ℚ) : ℚ :=
  m ^ 2 - a₂ - 2 * x

private def n15TangentY (a₂ x y m : ℚ) : ℚ :=
  -(m * (n15TangentX a₂ x m - x) + y)

private theorem n15_dual_forward_x {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : N15AuxiliaryEquation x y) :
    n15DualX (n15ForwardX x y) (n15ForwardY x y) =
      n15TangentX (-31) x (n15AuxTangent x y) := by
  unfold n15DualX n15ForwardX n15ForwardY n15TangentX n15AuxTangent
  unfold N15AuxiliaryEquation at h
  field_simp [hx, hy]
  rw [h]
  ring

private theorem n15_dual_forward_y {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (h : N15AuxiliaryEquation x y) :
    n15DualY (n15ForwardX x y) (n15ForwardY x y) =
      n15TangentY (-31) x y (n15AuxTangent x y) := by
  unfold n15DualY n15ForwardX n15ForwardY n15TangentY
    n15TangentX n15AuxTangent
  unfold N15AuxiliaryEquation at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x * (x - 15) * (x - 16)) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x * (x - 15) * (x - 16)) ^ 2 := by rw [h]
  rw [hy4, h]
  ring

private theorem n15AuxCurve_slope_self {x y : ℚ} (hy : y ≠ 0) :
    WeierstrassCurve.Affine.slope n15AuxCurve x x y y =
      n15AuxTangent x y := by
  have hyneg : y ≠ WeierstrassCurve.Affine.negY n15AuxCurve x y := by
    intro h
    apply hy
    rw [n15AuxCurve_negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
  simp [n15AuxCurve, n15AuxTangent,
    WeierstrassCurve.Affine.negY]
  ring

private theorem n15AuxCurve_addX_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addX n15AuxCurve x x
      (n15AuxTangent x y) =
        n15TangentX (-31) x (n15AuxTangent x y) := by
  simp [n15AuxCurve, n15TangentX]
  ring

private theorem n15AuxCurve_addY_tangent (x y : ℚ) :
    WeierstrassCurve.Affine.addY n15AuxCurve x x y
      (n15AuxTangent x y) =
        n15TangentY (-31) x y (n15AuxTangent x y) := by
  unfold WeierstrassCurve.Affine.addY
    WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY
    WeierstrassCurve.Affine.addX
    n15TangentY n15TangentX n15AuxCurve
  ring

private theorem n15Aux_y_zero_of_x_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x = 0) : y = 0 := by
  have heq := (n15AuxCurve_equation_iff x y).mp h.1
  unfold N15AuxiliaryEquation at heq
  rw [hx] at heq
  norm_num at heq
  nlinarith

private theorem n15Aux_double_eq_zero_of_y_zero {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hy : y = 0) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : N15AuxPoint) = 0 := by
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    (by simp [hy, n15AuxCurve])

private theorem n15Aux_y_ne_negY {x y : ℚ} (hy : y ≠ 0) :
    y ≠ WeierstrassCurve.Affine.negY n15AuxCurve x y := by
  intro h
  apply hy
  rw [n15AuxCurve_negY] at h
  linarith

/-- The dual isogeny after the forward isogeny is doubling, including all
exceptional affine branches. -/
private theorem n15_dual_comp_forwardPoint (P : N15AuxPoint) :
    n15DualPoint (n15ForwardPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy : y = 0 := n15Aux_y_zero_of_x_zero h hx
        rw [n15ForwardPoint_some_of_x_eq_zero h hx]
        simp only [n15DualPoint_zero]
        exact (n15Aux_double_eq_zero_of_y_zero h hy).symm
      · rw [n15ForwardPoint_some_of_x_ne_zero h hx]
        by_cases hy : y = 0
        · have hfx : n15ForwardX x y = 0 := by
            simp [n15ForwardX, hy]
          change n15DualPoint
              (.some (n15ForwardX x y) (n15ForwardY x y) _) = _
          rw [n15DualPoint_some_of_x_eq_zero _ hfx]
          exact (n15Aux_double_eq_zero_of_y_zero h hy).symm
        · have hfx : n15ForwardX x y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
          change n15DualPoint
              (.some (n15ForwardX x y) (n15ForwardY x y) _) = _
          rw [n15DualPoint_some_of_x_ne_zero _ hfx]
          rw [two_nsmul,
            WeierstrassCurve.Affine.Point.add_self_of_Y_ne
              (n15Aux_y_ne_negY (x := x) (y := y) hy)]
          change WeierstrassCurve.Affine.Point.some
              (n15DualX (n15ForwardX x y) (n15ForwardY x y))
              (n15DualY (n15ForwardX x y) (n15ForwardY x y)) _ =
            WeierstrassCurve.Affine.Point.some
              (WeierstrassCurve.Affine.addX n15AuxCurve x x
                (WeierstrassCurve.Affine.slope n15AuxCurve x x y y))
              (WeierstrassCurve.Affine.addY n15AuxCurve x x y
                (WeierstrassCurve.Affine.slope n15AuxCurve x x y y)) _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          have heq : N15AuxiliaryEquation x y :=
            (n15AuxCurve_equation_iff x y).mp h.1
          constructor
          · rw [n15_dual_forward_x hx hy heq,
              n15AuxCurve_slope_self hy,
              n15AuxCurve_addX_tangent]
          · rw [n15_dual_forward_y hx hy heq,
              n15AuxCurve_slope_self hy,
              n15AuxCurve_addY_tangent]

/-! ### Denominator normalization and the two Kummer images -/

private theorem n15_nat_isSquare_of_isSquare_cube {n : ℕ}
    (hn : n ≠ 0) (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc
        n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

private theorem n15_den_monic_cubic (a b : ℤ) (x : ℚ) :
    ((x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den : ℤ) =
      (x.den : ℤ) ^ 3 := by
  set A : ℤ := x.num
  set D : ℤ := (x.den : ℤ)
  have hDpos : (0 : ℤ) < D := by positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hred : IsCoprime A D := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [A, D, Int.natAbs_natCast]
    exact x.reduced
  set N : ℤ := A ^ 3 + a * A ^ 2 * D + b * A * D ^ 2
  have hND : IsCoprime N D := by
    have h1 : IsCoprime (A ^ 3) D := hred.pow_left
    have h2 : IsCoprime
        (A ^ 3 + D * (a * A ^ 2 + b * A * D)) D :=
      h1.add_mul_left_left _
    convert h2 using 1
    ring
  have hND3 : IsCoprime N (D ^ 3) := hND.pow_right
  have hND3nat : Nat.Coprime N.natAbs (D ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hND3
  have hrepr : x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x =
      (N : ℚ) / (D ^ 3 : ℚ) := by
    have hx : x = (A : ℚ) / (D : ℚ) := by
      simp only [A, D]
      push_cast
      exact (Rat.num_div_den x).symm
    rw [hx]
    field_simp [hDne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hND3nat

private theorem n15_rat_denom_square_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :=
    ⟨y, by rw [← h]; ring⟩
  have hdenSq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hdenEq :
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den =
        x.den ^ 3 := by
    exact_mod_cast n15_den_monic_cubic a b x
  have hden3Sq : IsSquare (x.den ^ 3) := hdenEq ▸ hdenSq
  have hdenSq' : IsSquare x.den :=
    n15_nat_isSquare_of_isSquare_cube x.den_ne_zero hden3Sq
  obtain ⟨B0, hB0⟩ := hdenSq'
  have hB0pos : 0 < B0 := by
    rcases Nat.eq_zero_or_pos B0 with hzero | hpos
    · simp [hzero] at hB0
    · exact hpos
  refine ⟨x.num, (B0 : ℤ), by exact_mod_cast hB0pos, ?_, ?_⟩
  · have hBdvd : B0 ∣ x.den := ⟨B0, hB0⟩
    have := x.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      x = (x.num : ℚ) / (x.den : ℚ) := by
        simpa using (Rat.num_div_den x).symm
      _ = (x.num : ℚ) / ((B0 : ℚ) ^ 2) := by
        rw [hB0]
        push_cast
        ring

private theorem n15_integral_model_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4) := by
  obtain ⟨A, B, hBpos, hcop, hx⟩ :=
    n15_rat_denom_square_monic a b x y h
  have hBne : (B : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  set N : ℤ := A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at h
    push_cast [N] at h ⊢
    field_simp [hBne] at h ⊢
    nlinarith
  have hNsq : IsSquare (N : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hNsq
  obtain ⟨C, hC⟩ := hNsq
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  rw [sq C]
  exact hC.symm

private theorem n15_aux_integral_model {x y : ℚ}
    (h : N15AuxiliaryEquation x y) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A - 15 * B ^ 2) * (A - 16 * B ^ 2) := by
  have hcubic : y ^ 2 = x ^ 3 - 31 * x ^ 2 + 240 * x := by
    unfold N15AuxiliaryEquation at h
    nlinarith
  have hcubic' : y ^ 2 =
      x ^ 3 + ((-31 : ℤ) : ℚ) * x ^ 2 + ((240 : ℤ) : ℚ) * x := by
    norm_num at ⊢
    simpa [sub_eq_add_neg] using hcubic
  obtain ⟨A, B, C, hBpos, hcop, hx, hC⟩ :=
    n15_integral_model_monic (-31) 240 x y hcubic'
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  calc
    C ^ 2 = A * (A ^ 2 - 31 * A * B ^ 2 + 240 * B ^ 4) := by
      simpa [sub_eq_add_neg] using hC
    _ = A * (A - 15 * B ^ 2) * (A - 16 * B ^ 2) := by ring

private theorem n15_iso_integral_model {x y : ℚ}
    (h : N15IsogenousEquation x y) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + 62 * A * B ^ 2 + B ^ 4) := by
  have hcubic : y ^ 2 =
      x ^ 3 + ((62 : ℤ) : ℚ) * x ^ 2 + ((1 : ℤ) : ℚ) * x := by
    unfold N15IsogenousEquation at h
    norm_num at ⊢
    exact h
  obtain ⟨A, B, C, hBpos, hcop, hx, hC⟩ :=
    n15_integral_model_monic 62 1 x y hcubic
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  simpa using hC

private theorem n15_squarefree_core_dvd_other {a q c d r : ℕ}
    (ha0 : a ≠ 0) (hdecomp : r ^ 2 * d = a) (hd : Squarefree d)
    (hsq : c ^ 2 = a * q) : d ∣ q := by
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    simp at hdecomp
    exact ha0 hdecomp.symm
  have hr2dvd : r ^ 2 ∣ c ^ 2 := by
    refine ⟨d * q, ?_⟩
    rw [hsq, ← hdecomp]
    ring
  have hrdvd : r ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hr2dvd
  obtain ⟨k, rfl⟩ := hrdvd
  have hk : k ^ 2 = d * q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hr0)
    calc
      r ^ 2 * k ^ 2 = (r * k) ^ 2 := by ring
      _ = a * q := hsq
      _ = (r ^ 2 * d) * q := by rw [hdecomp]
      _ = r ^ 2 * (d * q) := by ring
  have hdk2 : d ∣ k ^ 2 := ⟨q, hk⟩
  have hdk : d ∣ k := (hd.dvd_pow_iff_dvd two_ne_zero).mp hdk2
  obtain ⟨l, rfl⟩ := hdk
  have hcancel : d * (d * l ^ 2) = d * q := by
    calc
      d * (d * l ^ 2) = (d * l) ^ 2 := by ring
      _ = d * q := hk
  have hq : d * l ^ 2 = q := mul_left_cancel₀ hd.ne_zero hcancel
  exact ⟨l ^ 2, hq.symm⟩

private theorem n15_coprime_of_dvd_left {a b d : ℤ}
    (hab : IsCoprime a b) (hd : d ∣ a) : IsCoprime d b := by
  rcases hab with ⟨u, v, huv⟩
  rcases hd with ⟨k, rfl⟩
  exact ⟨u * k, v, by rw [← huv]; ring⟩

private theorem n15_squarefree_core_dvd_cubic_coefficient
    {a b A B C : ℤ} {d r : ℕ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 =
      A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4))
    (hdecomp : r ^ 2 * d = A.natAbs) (hd : Squarefree d) :
    d ∣ b.natAbs := by
  let Q : ℤ := A ^ 2 + a * A * B ^ 2 + b * B ^ 4
  have hAabs0 : A.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA0
  have habs : C.natAbs ^ 2 = A.natAbs * Q.natAbs := by
    simpa [Q, Int.natAbs_pow, Int.natAbs_mul] using
      congrArg Int.natAbs hmodel
  have hdQ : d ∣ Q.natAbs :=
    n15_squarefree_core_dvd_other hAabs0 hdecomp hd habs
  have hdA : d ∣ A.natAbs := by
    exact hdecomp ▸ dvd_mul_left d (r ^ 2)
  have hdAZ : (d : ℤ) ∣ A := Int.natCast_dvd.mpr hdA
  have hdQZ : (d : ℤ) ∣ Q := Int.natCast_dvd.mpr hdQ
  have hdbB4 : (d : ℤ) ∣ b * B ^ 4 := by
    rw [show b * B ^ 4 = Q - A * (A + a * B ^ 2) by
      simp only [Q]
      ring]
    exact dvd_sub hdQZ (dvd_mul_of_dvd_left hdAZ _)
  have hAB : IsCoprime A B :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hdB4 : IsCoprime (d : ℤ) (B ^ 4) :=
    (n15_coprime_of_dvd_left hAB hdAZ).pow_right
  have hdbZ : (d : ℤ) ∣ b := hdB4.dvd_of_dvd_mul_right hdbB4
  exact Int.natCast_dvd.mp hdbZ

private theorem n15_first_coordinate_squareclass
    {a b A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 =
      A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ d r : ℕ, Squarefree d ∧ d ∣ b.natAbs ∧
      (A = (d : ℤ) * (r : ℤ) ^ 2 ∨
       A = -((d : ℤ) * (r : ℤ) ^ 2)) := by
  obtain ⟨d, r, hdecomp, hd⟩ := Nat.sq_mul_squarefree A.natAbs
  have hdb := n15_squarefree_core_dvd_cubic_coefficient
    hcop hA0 hmodel hdecomp hd
  have habs : (A.natAbs : ℤ) = (d : ℤ) * (r : ℤ) ^ 2 := by
    have hcast : (A.natAbs : ℤ) = ((r ^ 2 * d : ℕ) : ℤ) := by
      exact_mod_cast hdecomp.symm
    rw [hcast]
    push_cast
    ring
  refine ⟨d, r, hd, hdb, ?_⟩
  rcases Int.natAbs_eq A with hpos | hneg
  · left
    rw [hpos, habs]
  · right
    rw [hneg, habs]

private theorem n15_squarefree_dvd_240 {d : ℕ}
    (hd : Squarefree d) (hdiv : d ∣ 240) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨
      d = 6 ∨ d = 10 ∨ d = 15 ∨ d = 30 := by
  have hd30 : d ∣ 30 := by
    have hdPow : d ∣ 30 ^ 4 := hdiv.trans (by norm_num)
    exact (hd.dvd_pow_iff_dvd (by norm_num : 4 ≠ 0)).mp hdPow
  have hdle : d ≤ 30 := Nat.le_of_dvd (by norm_num) hd30
  interval_cases d
  all_goals norm_num at hd30
  all_goals simp

private theorem n15_quartic_cover_of_squareclass
    {a b d e A B C r : ℤ} (hd : d ≠ 0) (hr : r ≠ 0)
    (hb : b = d * e) (hA : A = d * r ^ 2)
    (hmodel : C ^ 2 =
      A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ z : ℤ,
      z ^ 2 = d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4 := by
  let Q : ℤ := d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4
  have hfactor : C ^ 2 = (d * r) ^ 2 * Q := by
    rw [hmodel, hA, hb]
    simp only [Q]
    ring
  have hfactor' : C ^ 2 = d ^ 2 * r ^ 2 * Q := by
    calc
      C ^ 2 = (d * r) ^ 2 * Q := hfactor
      _ = d ^ 2 * r ^ 2 * Q := by ring
  have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hrq : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hrat : ((C : ℚ) / ((d : ℚ) * (r : ℚ))) ^ 2 = (Q : ℚ) := by
    field_simp [hdq, hrq]
    exact_mod_cast hfactor'
  have hsq : IsSquare (Q : ℚ) :=
    ⟨(C : ℚ) / ((d : ℚ) * (r : ℚ)), by
      rw [← sq]
      exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨z, hz⟩ := hsq
  refine ⟨z, ?_⟩
  rw [sq]
  exact hz.symm

private theorem n15_root_coprime_denominator {d r A B : ℤ}
    (hcop : Int.gcd A B = 1) (hA : A = d * r ^ 2) :
    Int.gcd r B = 1 := by
  have hAB : IsCoprime A B :=
    Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hrA : r ∣ A := by
    rw [hA]
    exact ⟨d * r, by ring⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp
    (n15_coprime_of_dvd_left hAB hrA)

private theorem n15_primitive_mod_two {r B : ℤ}
    (hcop : Int.gcd r B = 1) :
    n15Reduce16to2 (r : ZMod 16) ≠ 0 ∨
      n15Reduce16to2 (B : ZMod 16) ≠ 0 := by
  have hnot : ¬ ((2 : ℤ) ∣ r ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h2g : (2 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h2g
    norm_num at h2g
  have hmod2 : (r : ZMod 2) ≠ 0 ∨ (B : ZMod 2) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp h.1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp h.2⟩
  simpa [n15Reduce16to2, ZMod.castHom_apply] using hmod2

private theorem n15_no_primitive_kummer_two (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 2 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 120 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_two_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_kummer_six (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 6 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 40 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_six_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_kummer_ten (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 10 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 24 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_ten_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_kummer_thirty (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = 30 * r ^ 4 - 31 * r ^ 2 * B ^ 2 + 8 * B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_kummer_thirty_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_no_primitive_dual_negative (r B z : ℤ)
    (hcop : Int.gcd r B = 1)
    (h : z ^ 2 = -(r ^ 4) + 62 * r ^ 2 * B ^ 2 - B ^ 4) :
    False := by
  have hmod := congrArg (fun n : ℤ => (n : ZMod 16)) h
  push_cast at hmod
  exact (n15_no_dual_negative_class_mod16 _ _ _
    (n15_primitive_mod_two hcop)) hmod

private theorem n15_aux_x_nonnegative {x y : ℚ}
    (h : N15AuxiliaryEquation x y) : 0 ≤ x := by
  by_contra hx
  have hxneg : x < 0 := lt_of_not_ge hx
  have hx15 : x - 15 < 0 := by linarith
  have hx16 : x - 16 < 0 := by linarith
  have hprod : x * (x - 15) * (x - 16) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hxneg hx15) hx16
  unfold N15AuxiliaryEquation at h
  nlinarith [sq_nonneg y]

private theorem n15_rat_squareclass_of_integral
    {x : ℚ} {A B d r : ℤ} (hB : B ≠ 0)
    (hx : x = (A : ℚ) / (B : ℚ) ^ 2)
    (hA : A = d * r ^ 2) :
    x = (d : ℚ) * ((r : ℚ) / (B : ℚ)) ^ 2 := by
  rw [hx, hA]
  push_cast
  field_simp [Int.cast_ne_zero.mpr hB]

private theorem n15_aux_rational_x_squareclasses {x y : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ,
      x = q ^ 2 ∨ x = 3 * q ^ 2 ∨ x = 5 * q ^ 2 ∨ x = 15 * q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    n15_aux_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hAz
    apply hx0
    rw [hx, hAz]
    norm_num
  have hmodel' : C ^ 2 =
      A * (A ^ 2 + (-31) * A * B ^ 2 + 240 * B ^ 4) := by
    rw [hmodel]
    ring
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    n15_first_coordinate_squareclass hcop hA0 hmodel'
  have hdiv240 : d ∣ 240 := by simpa using hdiv
  have hxpos : 0 < x :=
    lt_of_le_of_ne (n15_aux_x_nonnegative h) (Ne.symm hx0)
  have hApos : 0 < A := by
    have hBq0 : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hB0
    have hmul : (A : ℚ) = x * (B : ℚ) ^ 2 := by
      rw [hx]
      field_simp [hBq0]
    have hAqpos : (0 : ℚ) < (A : ℚ) := by
      rw [hmul]
      exact mul_pos hxpos (sq_pos_of_ne_zero hBq0)
    exact_mod_cast hAqpos
  have hA : A = (d : ℤ) * (r : ℤ) ^ 2 := by
    rcases hsign with hpos | hneg
    · exact hpos
    · exfalso
      rw [hneg] at hApos
      have hd0 : (0 : ℤ) ≤ (d : ℤ) := by positivity
      nlinarith [sq_nonneg (r : ℤ)]
  have hr0 : (r : ℤ) ≠ 0 := by
    intro hr
    apply hA0
    rw [hA, hr]
    norm_num
  have hcopRB : Int.gcd (r : ℤ) B = 1 :=
    n15_root_coprime_denominator hcop hA
  rcases n15_squarefree_dvd_240 hd hdiv240 with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    left
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (2 : ℤ)) (e := 120) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_two (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    right; left
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    right; right; left
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (6 : ℤ)) (e := 40) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_six (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (10 : ℤ)) (e := 24) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_ten (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    right; right; right
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (30 : ℤ)) (e := 8) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) hA hmodel'
    exact (n15_no_primitive_kummer_thirty (r : ℤ) B z hcopRB
      (by simpa [sub_eq_add_neg] using hz)).elim

private theorem n15_iso_rational_x_square {x y : ℚ}
    (h : N15IsogenousEquation x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 := by
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    n15_iso_integral_model h
  have hB0 : B ≠ 0 := ne_of_gt hBpos
  have hA0 : A ≠ 0 := by
    intro hAz
    apply hx0
    rw [hx, hAz]
    norm_num
  have hmodel' : C ^ 2 =
      A * (A ^ 2 + (62 : ℤ) * A * B ^ 2 + (1 : ℤ) * B ^ 4) := by
    simpa using hmodel
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    n15_first_coordinate_squareclass hcop hA0 hmodel'
  have hd1 : d = 1 := by
    have : d ∣ 1 := by simpa using hdiv
    exact Nat.dvd_one.mp this
  subst d
  rcases hsign with hA | hA
  · refine ⟨(r : ℚ) / (B : ℚ), ?_⟩
    simpa using n15_rat_squareclass_of_integral hB0 hx hA
  · have hr0 : (r : ℤ) ≠ 0 := by
      intro hr
      apply hA0
      rw [hA, hr]
      norm_num
    have hcopRB : Int.gcd (r : ℤ) B = 1 := by
      exact n15_root_coprime_denominator (d := (-1 : ℤ)) hcop
        (by simpa using hA)
    obtain ⟨z, hz⟩ := n15_quartic_cover_of_squareclass
      (d := (-1 : ℤ)) (e := -1) (r := (r : ℤ))
      (by norm_num) hr0 (by norm_num) (by simpa using hA) hmodel'
    exact (n15_no_primitive_dual_negative (r : ℤ) B z hcopRB
      (by calc
        z ^ 2 = -1 * (r : ℤ) ^ 4 + 62 * (r : ℤ) ^ 2 * B ^ 2 +
            -1 * B ^ 4 := hz
        _ = -((r : ℤ) ^ 4) + 62 * (r : ℤ) ^ 2 * B ^ 2 - B ^ 4 := by
          ring)).elim

private def n15AuxPointOf (x y : ℚ) (h : N15AuxiliaryEquation x y) :
    N15AuxPoint :=
  WeierstrassCurve.Affine.Point.some x y
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((n15AuxCurve_equation_iff x y).mpr h))

private def n15P00 : N15AuxPoint :=
  n15AuxPointOf 0 0 (by norm_num [N15AuxiliaryEquation])

private def n15P15 : N15AuxPoint :=
  n15AuxPointOf 15 0 (by norm_num [N15AuxiliaryEquation])

private def n15P16 : N15AuxPoint :=
  n15AuxPointOf 16 0 (by norm_num [N15AuxiliaryEquation])

private def n15P12 : N15AuxPoint :=
  n15AuxPointOf 12 12 (by norm_num [N15AuxiliaryEquation])

private def n15P20 : N15AuxPoint :=
  n15AuxPointOf 20 20 (by norm_num [N15AuxiliaryEquation])

private theorem n15_exists_half_of_square_x {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hx : x ≠ 0) (hsq : ∃ q : ℚ, x = q ^ 2) :
    ∃ Q : N15AuxPoint,
      2 • Q = WeierstrassCurve.Affine.Point.some x y h := by
  obtain ⟨q, hq⟩ := hsq
  obtain ⟨S, hS⟩ := n15_exists_dual_preimage_of_x_eq_sq h hx hq
  cases S with
  | zero =>
      change n15DualPoint (0 : N15IsoPoint) = _ at hS
      rw [n15DualPoint_zero] at hS
      cases hS
  | some t v ht =>
      by_cases ht0 : t = 0
      · rw [n15DualPoint_some_of_x_eq_zero ht ht0] at hS
        cases hS
      · have hteq : N15IsogenousEquation t v :=
          (n15IsoCurve_equation_iff t v).mp ht.1
        obtain ⟨r, hr⟩ := n15_iso_rational_x_square hteq ht0
        obtain ⟨Q, hQ⟩ :=
          n15_exists_forward_preimage_of_x_eq_sq ht ht0 hr
        refine ⟨Q, ?_⟩
        rw [← n15_dual_comp_forwardPoint Q, hQ, hS]

private theorem n15P00_two : 2 • n15P00 = 0 := by
  exact n15Aux_double_eq_zero_of_y_zero _ rfl

private theorem n15P15_two : 2 • n15P15 = 0 := by
  exact n15Aux_double_eq_zero_of_y_zero _ rfl

private theorem n15P16_two : 2 • n15P16 = 0 := by
  exact n15Aux_double_eq_zero_of_y_zero _ rfl

private theorem n15P12_two : 2 • n15P12 = n15P16 := by
  change 2 • (WeierstrassCurve.Affine.Point.some 12 12 _ : N15AuxPoint) =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (n15Aux_y_ne_negY (by norm_num : (12 : ℚ) ≠ 0))]
  change WeierstrassCurve.Affine.Point.some
      (WeierstrassCurve.Affine.addX n15AuxCurve 12 12
        (WeierstrassCurve.Affine.slope n15AuxCurve 12 12 12 12))
      (WeierstrassCurve.Affine.addY n15AuxCurve 12 12 12
        (WeierstrassCurve.Affine.slope n15AuxCurve 12 12 12 12)) _ =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [n15P16, n15AuxPointOf, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    n15AuxCurve]

private theorem n15P20_two : 2 • n15P20 = n15P16 := by
  change 2 • (WeierstrassCurve.Affine.Point.some 20 20 _ : N15AuxPoint) =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (n15Aux_y_ne_negY (by norm_num : (20 : ℚ) ≠ 0))]
  change WeierstrassCurve.Affine.Point.some
      (WeierstrassCurve.Affine.addX n15AuxCurve 20 20
        (WeierstrassCurve.Affine.slope n15AuxCurve 20 20 20 20))
      (WeierstrassCurve.Affine.addY n15AuxCurve 20 20 20
        (WeierstrassCurve.Affine.slope n15AuxCurve 20 20 20 20)) _ =
    WeierstrassCurve.Affine.Point.some 16 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [n15P16, n15AuxPointOf, WeierstrassCurve.Affine.slope,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    n15AuxCurve]

private theorem n15P12_four : 4 • n15P12 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P12_two, n15P16_two]

private theorem n15P20_four : 4 • n15P20 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P20_two, n15P16_two]

private theorem n15_secant_x_square
    {x y t s q d r : ℚ}
    (hxy : N15AuxiliaryEquation x y)
    (hts : N15AuxiliaryEquation t s)
    (hx : x = d * q ^ 2) (ht : t = d * r ^ 2)
    (hxt : x ≠ t) (hd : d ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    WeierstrassCurve.Affine.addX n15AuxCurve x t
        (WeierstrassCurve.Affine.slope n15AuxCurve x t y (-s)) =
      ((y * t + s * x) / ((x - t) * d * q * r)) ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hxt]
  unfold WeierstrassCurve.Affine.addX
  simp only [n15AuxCurve, zero_mul, sub_neg_eq_add]
  unfold N15AuxiliaryEquation at hxy hts
  have hxy' : y ^ 2 = x ^ 3 - 31 * x ^ 2 + 240 * x := by
    rw [hxy]
    ring
  have hts' : s ^ 2 = t ^ 3 - 31 * t ^ 2 + 240 * t := by
    rw [hts]
    ring
  field_simp [sub_ne_zero.mpr hxt, hd, hq, hr]
  have hxdt : d ^ 2 * q ^ 2 * r ^ 2 = x * t := by
    rw [hx, ht]
    ring
  calc
    ((y + s) ^ 2 + (x - t) ^ 2 * 0 + (x - t) ^ 2 * 31 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) * d ^ 2 * q ^ 2 * r ^ 2 =
        ((y + s) ^ 2 + (x - t) ^ 2 * 0 + (x - t) ^ 2 * 31 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) *
          (d ^ 2 * q ^ 2 * r ^ 2) := by ring
    _ = ((y + s) ^ 2 + (x - t) ^ 2 * 0 + (x - t) ^ 2 * 31 -
          x * (x - t) ^ 2 - t * (x - t) ^ 2) * (x * t) := by
      rw [hxdt]
    _ = (y * t + s * x) ^ 2 := by
      ring_nf
      rw [hxy', hts']
      ring

private theorem n15_exists_half_after_same_squareclass_secant
    {x y t s q d r : ℚ}
    (hxy : WeierstrassCurve.Affine.Nonsingular n15AuxCurve x y)
    (hts : WeierstrassCurve.Affine.Nonsingular n15AuxCurve t s)
    (hx : x = d * q ^ 2) (ht : t = d * r ^ 2)
    (hxt : x ≠ t) (hd : d ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hz0 : WeierstrassCurve.Affine.addX n15AuxCurve x t
      (WeierstrassCurve.Affine.slope n15AuxCurve x t y (-s)) ≠ 0) :
    ∃ Q : N15AuxPoint,
      2 • Q = WeierstrassCurve.Affine.Point.some x y hxy -
        WeierstrassCurve.Affine.Point.some t s hts := by
  have hcurve : N15AuxiliaryEquation x y :=
    (n15AuxCurve_equation_iff x y).mp hxy.1
  have htcurve : N15AuxiliaryEquation t s :=
    (n15AuxCurve_equation_iff t s).mp hts.1
  have hneg : WeierstrassCurve.Affine.Nonsingular n15AuxCurve t (-s) := by
    have hn := (WeierstrassCurve.Affine.nonsingular_neg t s).mpr hts
    simpa [n15AuxCurve, WeierstrassCurve.Affine.negY] using hn
  let m := WeierstrassCurve.Affine.slope n15AuxCurve x t y (-s)
  let z := WeierstrassCurve.Affine.addX n15AuxCurve x t m
  let w := WeierstrassCurve.Affine.addY n15AuxCurve x t y m
  have hR : WeierstrassCurve.Affine.Nonsingular n15AuxCurve z w :=
    WeierstrassCurve.Affine.nonsingular_add hxy hneg
      (fun hbad => hxt hbad.1)
  have hzsq : z = ((y * t + s * x) / ((x - t) * d * q * r)) ^ 2 := by
    exact n15_secant_x_square hcurve htcurve hx ht hxt hd hq hr
  obtain ⟨Q, hQ⟩ := n15_exists_half_of_square_x hR
    (by simpa [z, m] using hz0)
    ⟨(y * t + s * x) / ((x - t) * d * q * r), hzsq⟩
  refine ⟨Q, ?_⟩
  calc
    2 • Q = WeierstrassCurve.Affine.Point.some z w hR := hQ
    _ = WeierstrassCurve.Affine.Point.some x y hxy +
        WeierstrassCurve.Affine.Point.some t (-s) hneg := by
      symm
      exact WeierstrassCurve.Affine.Point.add_of_X_ne hxt
    _ = WeierstrassCurve.Affine.Point.some x y hxy -
        WeierstrassCurve.Affine.Point.some t s hts := by
      rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some]
      congr 1
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      simp [n15AuxCurve, WeierstrassCurve.Affine.negY]

private theorem n15_x_eq_twelve_or_twenty_of_y_eq_neg_x
    {x y : ℚ} (h : N15AuxiliaryEquation x y)
    (hx0 : x ≠ 0) (hy : y = -x) : x = 12 ∨ x = 20 := by
  unfold N15AuxiliaryEquation at h
  have hcancel : x = (x - 15) * (x - 16) := by
    apply mul_left_cancel₀ hx0
    calc
      x * x = y ^ 2 := by rw [hy]; ring
      _ = x * (x - 15) * (x - 16) := h
      _ = x * ((x - 15) * (x - 16)) := by ring
  have hfactor : (x - 12) * (x - 20) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h12 | h20
  · left; linarith
  · right; linarith

private theorem n15_x_eq_zero_or_fifteen_or_sixteen_of_y_zero
    {x y : ℚ} (h : N15AuxiliaryEquation x y) (hy : y = 0) :
    x = 0 ∨ x = 15 ∨ x = 16 := by
  unfold N15AuxiliaryEquation at h
  rw [hy] at h
  norm_num at h
  rcases h with (hx | h15) | h16
  · exact Or.inl hx
  · right; left; linarith
  · right; right; linarith

private theorem n15_rat_sq_ne_twenty_thirds (q : ℚ) :
    q ^ 2 ≠ 20 / 3 := by
  intro h
  have hs : IsSquare (20 / 3 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

private theorem n15_rat_sq_ne_twelve_fifths (q : ℚ) :
    q ^ 2 ≠ 12 / 5 := by
  intro h
  have hs : IsSquare (12 / 5 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

private theorem n15_rat_sq_ne_sixteen_fifteenths (q : ℚ) :
    q ^ 2 ≠ 16 / 15 := by
  intro h
  have hs : IsSquare (16 / 15 : ℚ) :=
    ⟨q, by simpa [pow_two] using h.symm⟩
  norm_num at hs

private theorem n15_translate_12_x_ne_zero {x y q : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0)
    (hx : x = 3 * q ^ 2) (hx12 : x ≠ 12) :
    WeierstrassCurve.Affine.addX n15AuxCurve x 12
      (WeierstrassCurve.Affine.slope n15AuxCurve x 12 y (-12)) ≠ 0 := by
  have hq0 : q ≠ 0 := by
    intro hq
    apply hx0
    rw [hx, hq]
    norm_num
  have hnum : y * 12 + 12 * x ≠ 0 := by
    intro hnum
    have hy : y = -x := by linarith
    rcases n15_x_eq_twelve_or_twenty_of_y_eq_neg_x h hx0 hy with
      h12 | h20
    · exact hx12 h12
    · apply n15_rat_sq_ne_twenty_thirds q
      rw [h20] at hx
      nlinarith
  have hroot :
      (y * 12 + 12 * x) / ((x - 12) * 3 * q * 2) ≠ 0 :=
    div_ne_zero hnum (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx12) (by norm_num)) hq0)
      (by norm_num))
  rw [n15_secant_x_square (q := q) (d := 3) (r := 2) h
    (by norm_num [N15AuxiliaryEquation]) hx (by norm_num)
    hx12 (by norm_num) hq0 (by norm_num)]
  exact pow_ne_zero 2 hroot

private theorem n15_translate_20_x_ne_zero {x y q : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0)
    (hx : x = 5 * q ^ 2) (hx20 : x ≠ 20) :
    WeierstrassCurve.Affine.addX n15AuxCurve x 20
      (WeierstrassCurve.Affine.slope n15AuxCurve x 20 y (-20)) ≠ 0 := by
  have hq0 : q ≠ 0 := by
    intro hq
    apply hx0
    rw [hx, hq]
    norm_num
  have hnum : y * 20 + 20 * x ≠ 0 := by
    intro hnum
    have hy : y = -x := by linarith
    rcases n15_x_eq_twelve_or_twenty_of_y_eq_neg_x h hx0 hy with
      h12 | h20
    · apply n15_rat_sq_ne_twelve_fifths q
      rw [h12] at hx
      nlinarith
    · exact hx20 h20
  have hroot :
      (y * 20 + 20 * x) / ((x - 20) * 5 * q * 2) ≠ 0 :=
    div_ne_zero hnum (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx20) (by norm_num)) hq0)
      (by norm_num))
  rw [n15_secant_x_square (q := q) (d := 5) (r := 2) h
    (by norm_num [N15AuxiliaryEquation]) hx (by norm_num)
    hx20 (by norm_num) hq0 (by norm_num)]
  exact pow_ne_zero 2 hroot

private theorem n15_translate_15_x_ne_zero {x y q : ℚ}
    (h : N15AuxiliaryEquation x y) (hx0 : x ≠ 0)
    (hx : x = 15 * q ^ 2) (hx15 : x ≠ 15) :
    WeierstrassCurve.Affine.addX n15AuxCurve x 15
      (WeierstrassCurve.Affine.slope n15AuxCurve x 15 y 0) ≠ 0 := by
  have hq0 : q ≠ 0 := by
    intro hq
    apply hx0
    rw [hx, hq]
    norm_num
  have hnum : y * 15 + 0 * x ≠ 0 := by
    intro hnum
    have hy : y = 0 := by linarith
    rcases n15_x_eq_zero_or_fifteen_or_sixteen_of_y_zero h hy with
      hzero | h15 | h16
    · exact hx0 hzero
    · exact hx15 h15
    · apply n15_rat_sq_ne_sixteen_fifteenths q
      rw [h16] at hx
      nlinarith
  have hroot :
      (y * 15 + 0 * x) / ((x - 15) * 15 * q * 1) ≠ 0 :=
    div_ne_zero hnum (mul_ne_zero
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx15) (by norm_num)) hq0)
      (by norm_num))
  have hz := n15_secant_x_square (t := 15) (s := 0)
    (q := q) (d := 15) (r := 1) h
    (by norm_num [N15AuxiliaryEquation]) hx (by norm_num)
    hx15 (by norm_num) hq0 (by norm_num)
  rw [show WeierstrassCurve.Affine.addX n15AuxCurve x 15
      (WeierstrassCurve.Affine.slope n15AuxCurve x 15 y 0) =
        ((y * 15 + 0 * x) / ((x - 15) * 15 * q * 1)) ^ 2 by
    simpa only [neg_zero] using hz]
  exact pow_ne_zero 2 hroot

private theorem n15P00_four : 4 • n15P00 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P00_two]
  simp

private theorem n15P15_four : 4 • n15P15 = 0 := by
  rw [show 4 = 2 * 2 by norm_num, mul_nsmul, n15P15_two]
  simp

private def N15DescentRepresentative (T : N15AuxPoint) : Prop :=
  T = 0 ∨ T = n15P00 ∨ T = n15P12 ∨ T = -n15P12 ∨
    T = n15P20 ∨ T = -n15P20 ∨ T = n15P15

private theorem n15_descent_decomposition (P : N15AuxPoint) :
    ∃ T Q : N15AuxPoint, N15DescentRepresentative T ∧
      4 • T = 0 ∧ P = T + 2 • Q := by
  cases P with
  | zero =>
      refine ⟨0, 0, by simp [N15DescentRepresentative], by simp, ?_⟩
      rfl
  | some x y hxy =>
      have hcurve : N15AuxiliaryEquation x y :=
        (n15AuxCurve_equation_iff x y).mp hxy.1
      by_cases hx0 : x = 0
      · have hy0 : y = 0 := n15Aux_y_zero_of_x_zero hxy hx0
        have hP :
            (WeierstrassCurve.Affine.Point.some x y hxy : N15AuxPoint) =
              n15P00 := by
          change WeierstrassCurve.Affine.Point.some x y hxy =
            WeierstrassCurve.Affine.Point.some 0 0 _
          rw [WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx0, hy0⟩
        refine ⟨n15P00, 0, by simp [N15DescentRepresentative],
          n15P00_four, ?_⟩
        rw [hP]
        simp
      · rcases n15_aux_rational_x_squareclasses hcurve hx0 with
          ⟨q, hsq | hsq | hsq | hsq⟩
        · obtain ⟨Q, hQ⟩ := n15_exists_half_of_square_x hxy hx0 ⟨q, hsq⟩
          refine ⟨0, Q, by simp [N15DescentRepresentative], by simp, ?_⟩
          simpa using hQ.symm
        · have hq0 : q ≠ 0 := by
            intro hq
            apply hx0
            rw [hsq, hq]
            norm_num
          by_cases hx12 : x = 12
          · have hycases : y = 12 ∨ y = -12 := by
              unfold N15AuxiliaryEquation at hcurve
              rw [hx12] at hcurve
              norm_num at hcurve
              have hf : (y - 12) * (y + 12) = 0 := by nlinarith
              rcases mul_eq_zero.mp hf with hp | hn
              · left; linarith
              · right; linarith
            have hrep_four :
                N15DescentRepresentative
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) ∧
                  4 • (WeierstrassCurve.Affine.Point.some x y hxy :
                    N15AuxPoint) = 0 := by
              rcases hycases with hy | hy
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = n15P12 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    WeierstrassCurve.Affine.Point.some 12 12 _
                  rw [WeierstrassCurve.Affine.Point.some.injEq]
                  exact ⟨hx12, hy⟩
                rw [hP]
                exact ⟨by simp [N15DescentRepresentative], n15P12_four⟩
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = -n15P12 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    -(WeierstrassCurve.Affine.Point.some 12 12 _ :
                      N15AuxPoint)
                  rw [WeierstrassCurve.Affine.Point.neg_some,
                    WeierstrassCurve.Affine.Point.some.injEq]
                  simp [n15P12, n15AuxPointOf, n15AuxCurve,
                    WeierstrassCurve.Affine.negY, hx12, hy]
                rw [hP]
                refine ⟨by simp [N15DescentRepresentative], ?_⟩
                simpa using congrArg Neg.neg n15P12_four
            exact ⟨_, 0, hrep_four.1, hrep_four.2, by simp⟩
          · let ht : WeierstrassCurve.Affine.Nonsingular
                n15AuxCurve 12 12 :=
              WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                ((n15AuxCurve_equation_iff 12 12).mpr
                  (by norm_num [N15AuxiliaryEquation]))
            obtain ⟨Q, hQ⟩ :=
              n15_exists_half_after_same_squareclass_secant
                (q := q) (d := 3) (r := 2) hxy ht hsq (by norm_num)
                hx12 (by norm_num) hq0 (by norm_num)
                (n15_translate_12_x_ne_zero hcurve hx0 hsq hx12)
            let T : N15AuxPoint :=
              WeierstrassCurve.Affine.Point.some 12 12 ht
            have hT : T = n15P12 := by
              change WeierstrassCurve.Affine.Point.some 12 12 ht =
                WeierstrassCurve.Affine.Point.some 12 12 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨rfl, rfl⟩
            refine ⟨T, Q, by simp [N15DescentRepresentative, hT], ?_, ?_⟩
            · rw [hT]
              exact n15P12_four
            · change WeierstrassCurve.Affine.Point.some x y hxy =
                T + 2 • Q
              rw [hQ]
              abel
        · have hq0 : q ≠ 0 := by
            intro hq
            apply hx0
            rw [hsq, hq]
            norm_num
          by_cases hx20 : x = 20
          · have hycases : y = 20 ∨ y = -20 := by
              unfold N15AuxiliaryEquation at hcurve
              rw [hx20] at hcurve
              norm_num at hcurve
              have hf : (y - 20) * (y + 20) = 0 := by nlinarith
              rcases mul_eq_zero.mp hf with hp | hn
              · left; linarith
              · right; linarith
            have hrep_four :
                N15DescentRepresentative
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) ∧
                  4 • (WeierstrassCurve.Affine.Point.some x y hxy :
                    N15AuxPoint) = 0 := by
              rcases hycases with hy | hy
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = n15P20 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    WeierstrassCurve.Affine.Point.some 20 20 _
                  rw [WeierstrassCurve.Affine.Point.some.injEq]
                  exact ⟨hx20, hy⟩
                rw [hP]
                exact ⟨by simp [N15DescentRepresentative], n15P20_four⟩
              · have hP :
                    (WeierstrassCurve.Affine.Point.some x y hxy :
                      N15AuxPoint) = -n15P20 := by
                  change WeierstrassCurve.Affine.Point.some x y hxy =
                    -(WeierstrassCurve.Affine.Point.some 20 20 _ :
                      N15AuxPoint)
                  rw [WeierstrassCurve.Affine.Point.neg_some,
                    WeierstrassCurve.Affine.Point.some.injEq]
                  simp [n15P20, n15AuxPointOf, n15AuxCurve,
                    WeierstrassCurve.Affine.negY, hx20, hy]
                rw [hP]
                refine ⟨by simp [N15DescentRepresentative], ?_⟩
                simpa using congrArg Neg.neg n15P20_four
            exact ⟨_, 0, hrep_four.1, hrep_four.2, by simp⟩
          · let ht : WeierstrassCurve.Affine.Nonsingular
                n15AuxCurve 20 20 :=
              WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                ((n15AuxCurve_equation_iff 20 20).mpr
                  (by norm_num [N15AuxiliaryEquation]))
            obtain ⟨Q, hQ⟩ :=
              n15_exists_half_after_same_squareclass_secant
                (q := q) (d := 5) (r := 2) hxy ht hsq (by norm_num)
                hx20 (by norm_num) hq0 (by norm_num)
                (n15_translate_20_x_ne_zero hcurve hx0 hsq hx20)
            let T : N15AuxPoint :=
              WeierstrassCurve.Affine.Point.some 20 20 ht
            have hT : T = n15P20 := by
              change WeierstrassCurve.Affine.Point.some 20 20 ht =
                WeierstrassCurve.Affine.Point.some 20 20 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨rfl, rfl⟩
            refine ⟨T, Q, by simp [N15DescentRepresentative, hT], ?_, ?_⟩
            · rw [hT]
              exact n15P20_four
            · change WeierstrassCurve.Affine.Point.some x y hxy =
                T + 2 • Q
              rw [hQ]
              abel
        · have hq0 : q ≠ 0 := by
            intro hq
            apply hx0
            rw [hsq, hq]
            norm_num
          by_cases hx15 : x = 15
          · have hy0 : y = 0 := by
              unfold N15AuxiliaryEquation at hcurve
              rw [hx15] at hcurve
              norm_num at hcurve
              nlinarith
            have hP :
                (WeierstrassCurve.Affine.Point.some x y hxy :
                  N15AuxPoint) = n15P15 := by
              change WeierstrassCurve.Affine.Point.some x y hxy =
                WeierstrassCurve.Affine.Point.some 15 0 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨hx15, hy0⟩
            refine ⟨n15P15, 0, by simp [N15DescentRepresentative],
              n15P15_four, ?_⟩
            rw [hP]
            simp
          · let ht : WeierstrassCurve.Affine.Nonsingular
                n15AuxCurve 15 0 :=
              WeierstrassCurve.Affine.equation_iff_nonsingular.mp
                ((n15AuxCurve_equation_iff 15 0).mpr
                  (by norm_num [N15AuxiliaryEquation]))
            obtain ⟨Q, hQ⟩ :=
              n15_exists_half_after_same_squareclass_secant
                (q := q) (d := 15) (r := 1) hxy ht hsq (by norm_num)
                hx15 (by norm_num) hq0 (by norm_num)
                (by simpa only [neg_zero] using
                  n15_translate_15_x_ne_zero hcurve hx0 hsq hx15)
            let T : N15AuxPoint :=
              WeierstrassCurve.Affine.Point.some 15 0 ht
            have hT : T = n15P15 := by
              change WeierstrassCurve.Affine.Point.some 15 0 ht =
                WeierstrassCurve.Affine.Point.some 15 0 _
              rw [WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨rfl, rfl⟩
            refine ⟨T, Q, by simp [N15DescentRepresentative, hT], ?_, ?_⟩
            · rw [hT]
              exact n15P15_four
            · change WeierstrassCurve.Affine.Point.some x y hxy =
                T + 2 • Q
              rw [hQ]
              abel

/-- The isolated global arithmetic core: the two-isogeny Kummer computations
give rank zero, and good reduction at `7` bounds the torsion by the eight
displayed points. -/
private theorem n15_auxiliary_rank_zero_and_torsion_exhaustion
    (X Y : ℚ) (hcurve : N15AuxiliaryEquation X Y) :
    N15AuxiliaryAffineCandidate X Y := by
  have hcurve' : RationalPointsX115.OnX115 X Y := by
    simpa [RationalPointsX115.OnX115, N15AuxiliaryEquation] using hcurve
  have hclass := RationalPointsX115.X115_affine_exhaustion hcurve'
  simpa [RationalPointsX115.X115AffineCandidate,
    N15AuxiliaryAffineCandidate] using hclass

/-- Steps 4 and 6: any affine exhaustion of the auxiliary cubic transports
back to exactly the four non-boundary Tate `(b,x)` candidates. -/
private theorem n15_tate_candidates_of_auxiliary_classification
    (hclass : ∀ X Y : ℚ, N15AuxiliaryEquation X Y →
      N15AuxiliaryAffineCandidate X Y)
    {b x : ℚ} (hb : b ≠ 0) (hpsi : tateOrder5Psi3 b x = 0) :
    N15TateCandidate b x := by
  let u : ℚ := x / b
  have hnorm : n15NormalizedPsi3 b u = 0 :=
    n15_normalized_psi3 hb hpsi
  have hu0 : u ≠ 0 := n15_u_ne_zero hnorm
  have hu1 : u ≠ 1 := n15_u_ne_one hb hnorm
  let w : ℚ := n15QuarticW b u
  have hquartic : N15QuarticEquation u w :=
    n15_normalized_to_quartic hu0 hu1 hnorm
  have haux : N15AuxiliaryEquation (n15AuxX u) (n15AuxY u w) :=
    n15_quartic_to_auxiliary hu0 hquartic
  have hrecover :
      b = (u - 1) * (w - 3 * u * (u - 1)) / (2 * u ^ 2) := by
    simpa [w] using n15_recover_b b u hu0 hu1
  have hxu : x = b * u := by
    dsimp [u]
    field_simp
  rcases hclass _ _ haux with
      h00 | h150 | h160 | h1212 | h12n12 | h2020 | h20n20
  · rcases h00 with ⟨hX, hY⟩
    have hu : u = -(1 / 3) := by
      unfold n15AuxX at hX
      field_simp [hu0] at hX
      linarith
    have hw : w = 0 := by
      unfold n15AuxY at hY
      rw [hu] at hY
      norm_num at hY ⊢
      linarith
    have hbval : b = 8 := by
      rw [hu, hw] at hrecover
      norm_num at hrecover ⊢
      exact hrecover
    left
    refine ⟨hbval, ?_⟩
    rw [hxu, hbval, hu]
    norm_num
  · rcases h150 with ⟨hX, hY⟩
    have hu : u = 4 / 3 := by
      unfold n15AuxX at hX
      field_simp [hu0] at hX
      linarith
    have hw : w = 0 := by
      unfold n15AuxY at hY
      rw [hu] at hY
      norm_num at hY ⊢
      linarith
    have hbval : b = -(1 / 8) := by
      rw [hu, hw] at hrecover
      norm_num at hrecover ⊢
      exact hrecover
    right; left
    refine ⟨hbval, ?_⟩
    rw [hxu, hbval, hu]
    norm_num
  · rcases h160 with ⟨hX, _⟩
    have hu : u = 1 := by
      unfold n15AuxX at hX
      field_simp [hu0] at hX
      linarith
    exact (hu1 hu).elim
  · exact (n15_auxX_ne_twelve hu0 h1212.1).elim
  · exact (n15_auxX_ne_twelve hu0 h12n12.1).elim
  · rcases h2020 with ⟨hX, hY⟩
    have hu : u = 1 / 2 := by
      unfold n15AuxX at hX
      field_simp [hu0] at hX
      linarith
    have hw : w = 5 / 4 := by
      unfold n15AuxY at hY
      rw [hu] at hY
      norm_num at hY ⊢
      linarith
    have hbval : b = -2 := by
      rw [hu, hw] at hrecover
      norm_num at hrecover ⊢
      exact hrecover
    right; right; left
    refine ⟨hbval, ?_⟩
    rw [hxu, hbval, hu]
    norm_num
  · rcases h20n20 with ⟨hX, hY⟩
    have hu : u = 1 / 2 := by
      unfold n15AuxX at hX
      field_simp [hu0] at hX
      linarith
    have hw : w = -(5 / 4) := by
      unfold n15AuxY at hY
      rw [hu] at hY
      norm_num at hY ⊢
      linarith
    have hbval : b = 1 / 2 := by
      rw [hu, hw] at hrecover
      norm_num at hrecover ⊢
      exact hrecover
    right; right; right
    refine ⟨hbval, ?_⟩
    rw [hxu, hbval, hu]
    norm_num

private theorem n15_rat_sq_ne_five (r : ℚ) : r ^ 2 ≠ 5 := by
  intro h
  have hsq : IsSquare (5 : ℚ) := ⟨r, by simpa [pow_two] using h.symm⟩
  have hnot : ¬ IsSquare (5 : ℚ) := by norm_num
  exact hnot hsq

private theorem n15_liftRad_eight :
    tateOrder5LiftRad 8 (-(8 / 3)) = -(5120 / 27) := by
  norm_num [tateOrder5LiftRad]

private theorem n15_liftRad_neg_eighth :
    tateOrder5LiftRad (-(1 / 8)) (-(1 / 6)) = -(5 / 6912) := by
  norm_num [tateOrder5LiftRad]

private theorem n15_liftRad_neg_two :
    tateOrder5LiftRad (-2) (-1) = 5 := by
  norm_num [tateOrder5LiftRad]

private theorem n15_liftRad_half :
    tateOrder5LiftRad (1 / 2) (1 / 4) = 5 / 64 := by
  norm_num [tateOrder5LiftRad]

/-- Step 7: none of the four non-boundary division-polynomial roots lifts to
a rational point on the Tate curve. -/
private theorem n15_candidate_lift_false {b x y : ℚ}
    (hcurve : TateOrder5CurveEq b x y)
    (hcandidate : N15TateCandidate b x) : False := by
  have hsquare := tateOrder5CurveEq_square_completion hcurve
  rcases hcandidate with h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    rw [n15_liftRad_eight] at hsquare
    nlinarith [sq_nonneg (2 * y + (1 - 8) * (-(8 / 3)) - 8)]
  · rcases h with ⟨rfl, rfl⟩
    rw [n15_liftRad_neg_eighth] at hsquare
    nlinarith [sq_nonneg
      (2 * y + (1 - (-(1 / 8))) * (-(1 / 6)) - (-(1 / 8)))]
  · rcases h with ⟨rfl, rfl⟩
    rw [n15_liftRad_neg_two] at hsquare
    exact n15_rat_sq_ne_five _ hsquare
  · rcases h with ⟨rfl, rfl⟩
    rw [n15_liftRad_half] at hsquare
    apply n15_rat_sq_ne_five
      (8 * (2 * y + (1 - (1 / 2)) * (1 / 4) - (1 / 2)))
    calc
      (8 * (2 * y + (1 - (1 / 2)) * (1 / 4) - (1 / 2))) ^ 2 =
          64 * (2 * y + (1 - (1 / 2)) * (1 / 4) - (1 / 2)) ^ 2 := by ring
      _ = 5 := by rw [hsquare]; norm_num

/--
Final Diophantine input.

There are no rational `(b,x,y)` with `b^5(b^2-11b-1) ≠ 0`,
`y² + (1-b)xy - by = x³ - bx²`, and `ψ₃(b,x) = 0`.

This is the rational-points computation on `X₁(15)` in Tate-normal-form
coordinates; the rational points are cusps, and the nonsingularity condition
excludes them.

Note: ψ₃ alone CAN have rational roots without the curve equation constraint
(e.g. `b = -2, x = -1` gives ψ₃ = 0 but the curve has no rational `y`).
-/
theorem no_tate_order5_psi3_root_solution :
    ¬ ∃ b x y : ℚ, TateOrder5Psi3RootSolution b x y := by
  rintro ⟨b, x, y, hdisc, hcurve, hpsi⟩
  have hb : b ≠ 0 := by
    intro hb
    apply hdisc
    simp [hb]
  have hcandidates : N15TateCandidate b x :=
    n15_tate_candidates_of_auxiliary_classification
      n15_auxiliary_rank_zero_and_torsion_exhaustion hb hpsi
  exact n15_candidate_lift_false hcurve hcandidates

end

end CyclicExclusion15

/-! ## The remaining `X₁(15)` arithmetic input -/

/--
The `X₁(15)` rational-points input.

Mathematically, `X₁(15)` is an elliptic curve of rank `0` over `ℚ`; its
rational points are cusps.  In the present torsion language this says that no
elliptic curve over `ℚ` has both a rational point of order `3` and a rational
point of order `5`.
-/
theorem x1_15_no_simultaneous_rational_3_and_5_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ (HasRationalPointOfOrder E 3 ∧ HasRationalPointOfOrder E 5) := by
  intro htors
  obtain ⟨b, x, y, hbxy⟩ :=
    CyclicExclusion15.simultaneous_order3_and5_tate_bridge E htors
  exact CyclicExclusion15.no_tate_order5_psi3_root_solution ⟨b, x, y, hbxy⟩

/-- No elliptic curve over `ℚ` has a rational point of exact order `15`. -/
theorem no_rational_point_of_order_15
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 := by
  intro hord
  exact x1_15_no_simultaneous_rational_3_and_5_torsion E
    (order15_gives_orders3_and5 E hord)

namespace CyclicExclusion15

/-- Namespaced form matching the other cyclic-exclusion modules. -/
theorem no_rational_point_of_order_15
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 :=
  MazurProof.no_rational_point_of_order_15 E

end CyclicExclusion15

end MazurProof
