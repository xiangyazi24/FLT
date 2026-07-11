import FLT.Assumptions.MazurProof.CyclicOrderReduction
import FLT.Assumptions.MazurProof.TateNFDivision
import FLT.Assumptions.MazurProof.TateNormalFormBridge
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
  sorry

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

end MazurProof
