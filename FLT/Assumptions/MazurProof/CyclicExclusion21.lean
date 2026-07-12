import FLT.Assumptions.MazurProof.TateOrder18
import FLT.Assumptions.MazurProof.RationalPointsX121

/-!
# Cyclic order 21 exclusion

Order 21 = 3 · 7: put the order-7 point at the Tate origin (F7 = 0),
then show the 3-division polynomial Psi3X has no rational root (with
rational Y satisfying the curve equation) compatible with the Kubert
order-7 parametrization.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.CyclicExclusion21

noncomputable section

open Scratch.TateZ2xZ10Reduction

private abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

def F7 (b c : ℚ) : ℚ := c ^ 3 - b ^ 2 + b * c

def TateEq (b c X Y : ℚ) : Prop :=
  Y ^ 2 + (1 - c) * X * Y - b * Y = X ^ 3 - b * X ^ 2

def Psi3X (b c X : ℚ) : ℚ :=
  3 * X ^ 4 + ((1 - c) ^ 2 - 4 * b) * X ^ 3 +
    3 * b * (c - 1) * X ^ 2 + 3 * b ^ 2 * X - b ^ 3

def Obstruction21 (b c X Y : ℚ) : Prop :=
  b ≠ 0 ∧ F7 b c = 0 ∧ TateEq b c X Y ∧ Psi3X b c X = 0

/-! ## Division-polynomial conditions on the Tate curve -/

private theorem tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W]

private def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
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

private theorem Psi3X_eq_zero_of_three_nsmul
    (b c X Y : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (h : WeierstrassCurve.Affine.Nonsingular (W b c) X Y)
    (h3 : (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some X Y h :
          WeierstrassCurve.Affine.Point (W b c)) = 0) :
    TateNFDivision.Psi3X b c X = 0 := by
  have hPsiSq : ((W b c).ΨSq (3 : ℤ)).eval X = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c) h).mp h3
  have hpre : ((W b c).preΨ' 3).eval X = 0 := by
    change ((W b c).ΨSq (3 : ℕ)).eval X = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 3] at hPsiSq
    simpa [show ¬ Even (3 : ℕ) by decide] using hPsiSq
  rw [WeierstrassCurve.preΨ'_three] at hpre
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    TateNFDivision.Psi3X] at hpre ⊢
  ring_nf at hpre ⊢
  exact hpre

/-! ## Simultaneous normalization and transport -/

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
      simp [WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.negY, ha₂, ha₄]
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY, ha₂, ha₄]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl]
  simp [WeierstrassCurve.Affine.negY]

private theorem exists_tate_normalized_3torsion_of_addOrder_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P T : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n)
    (hT3 : (3 : ℕ) • T = 0) (hTne0 : T ≠ 0) :
    ∃ b c xT yT : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      ∃ hT : WeierstrassCurve.Affine.Nonsingular (W b c) xT yT,
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          (3 : ℕ) •
              (WeierstrassCurve.Affine.Point.some xT yT hT :
                WeierstrassCurve.Affine.Point (W b c)) = 0 := by
  cases P with
  | zero =>
      have hzero :
          addOrderOf (WeierstrassCurve.Affine.Point.zero : (E⁄ℚ).Point) = 1 := by
        rw [← WeierstrassCurve.Affine.Point.zero_def]
        simp
      rw [hzero] at hP
      omega
  | some x₀ y₀ hPaff =>
      let hPaffE : WeierstrassCurve.Affine.Nonsingular E x₀ y₀ := by
        change WeierstrassCurve.Affine.Nonsingular (E⁄ℚ) x₀ y₀
        exact hPaff
      let P₀ : WeierstrassCurve.Affine.Point E :=
        WeierstrassCurve.Affine.Point.some x₀ y₀ hPaffE
      have hP₀_order : addOrderOf P₀ = n := by
        dsimp [P₀, hPaffE]
        change addOrderOf
          (WeierstrassCurve.Affine.Point.some x₀ y₀ hPaff) = n
        exact hP
      let Psmall₀ : ∀ m < n, 0 < m → (m : ℕ) • P₀ ≠ 0 :=
        ((addOrderOf_eq_iff (x := P₀) (by omega)).mp hP₀_order).2
      let T₀ : WeierstrassCurve.Affine.Point E := T
      have hT3₀ : (3 : ℕ) • T₀ = 0 := by
        change (3 : ℕ) • (T : WeierstrassCurve.Affine.Point E) = 0
        simpa using hT3
      have hden : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by
        intro hden0
        have hy : y₀ = WeierstrassCurve.Affine.negY E x₀ y₀ := by
          rw [WeierstrassCurve.Affine.negY]
          linarith
        have h2zero : (2 : ℕ) • P₀ = 0 := by
          simpa [P₀, two_nsmul] using
            (WeierstrassCurve.Affine.Point.add_self_of_Y_eq
              (W := E) (h₁ := hPaff) hy)
        exact Psmall₀ 2 (by omega) (by norm_num) h2zero
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
        exact Psmall₀ 3 hn (by norm_num) h3zero
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
      have hφ1φ0P_origin : φ1 (φ0 P₀) = tateOrigin b c := by
        rw [hφ0P_origin]
        have hRawOrigin :
            WeierstrassCurve.Affine.Nonsingular (C1 • W1) 0 0 := by
          simpa [hW2eq] using tate_origin_nonsingular b c
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
          tateOrigin b c
        rw [hφ1raw_origin]
        exact pointCurveEqAddEquiv_some hW2eq
      have hOriginOrder : addOrderOf (tateOrigin b c) = n := by
        have hmaporder : addOrderOf (φ1 (φ0 P₀)) = n := by
          calc
            addOrderOf (φ1 (φ0 P₀)) = addOrderOf (φ0 P₀) :=
              addOrderOf_injective φ1.toAddMonoidHom
                (EquivLike.injective φ1) (φ0 P₀)
            _ = addOrderOf P₀ :=
              addOrderOf_injective φ0.toAddMonoidHom
                (EquivLike.injective φ0) P₀
            _ = n := hP₀_order
        rwa [hφ1φ0P_origin] at hmaporder
      have hb : b ≠ 0 := by
        have hdiv : W1.a₂ ^ 3 / W1.a₃ ^ 2 ≠ 0 :=
          div_ne_zero (pow_ne_zero 3 hW1a₂_ne) (pow_ne_zero 2 hW1a₃_ne)
        simpa [b, tateBFromCoefficients] using (neg_ne_zero.mpr hdiv)
      have hT3map : (3 : ℕ) • φ1 (φ0 T₀) = 0 := by
        calc
          (3 : ℕ) • φ1 (φ0 T₀) = φ1 ((3 : ℕ) • φ0 T₀) :=
            (map_nsmul φ1 3 (φ0 T₀)).symm
          _ = φ1 (φ0 ((3 : ℕ) • T₀)) := by
            rw [← map_nsmul φ0 3 T₀]
          _ = 0 := by
            rw [hT3₀, map_zero, map_zero]
      have hTmap_ne0 : φ1 (φ0 T₀) ≠ 0 := by
        intro hT0
        have hφ0T0 : φ0 T₀ = 0 := by
          apply (EquivLike.injective φ1)
          simpa [map_zero] using hT0
        have hT₀0 : T₀ = 0 := by
          apply (EquivLike.injective φ0)
          simpa [map_zero] using hφ0T0
        exact hTne0 hT₀0
      cases hTpoint : φ1 (φ0 T₀) with
      | zero =>
          exact False.elim (hTmap_ne0 hTpoint)
      | some xT yT hT =>
          refine ⟨b, c, xT, yT, inferInstance, hT, hOriginOrder, hb, ?_⟩
          simpa [hTpoint] using hT3map

private lemma addOrderOf_three_nsmul_of_order21
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 21) :
    addOrderOf ((3 : ℕ) • P) = 7 := by
  rw [addOrderOf_nsmul' P (by norm_num), hP]
  norm_num

private lemma addOrderOf_seven_nsmul_of_order21
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 21) :
    addOrderOf ((7 : ℕ) • P) = 3 := by
  rw [addOrderOf_nsmul' P (by norm_num), hP]
  norm_num

theorem order21_to_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h21 : HasRationalPointOfOrder E 21) :
    ∃ b c X Y : ℚ, Obstruction21 b c X Y := by
  obtain ⟨P, hP⟩ := h21
  let Q : (E⁄ℚ).Point := (3 : ℕ) • P
  let R : (E⁄ℚ).Point := (7 : ℕ) • P
  have hQord : addOrderOf Q = 7 := addOrderOf_three_nsmul_of_order21 hP
  have hRord : addOrderOf R = 3 := addOrderOf_seven_nsmul_of_order21 hP
  have hR3 : (3 : ℕ) • R = 0 := by
    have h := addOrderOf_nsmul_eq_zero R
    rwa [hRord] at h
  have hRne0 : R ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hRord
    exact absurd hRord (by norm_num)
  obtain ⟨b, c, X, Y, hEll, hT, hord, hb, h3⟩ :=
    exists_tate_normalized_3torsion_of_addOrder_gt_three
      E Q R 7 (by norm_num) hQord hR3 hRne0
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  refine ⟨b, c, X, Y, hb, ?_, ?_, ?_⟩
  · simpa [F7, TateNFDivision.F7] using
      F7_eq_zero_of_tateOrigin_order_seven b c hb hord
  · have heq : WeierstrassCurve.Affine.Equation (W b c) X Y := hT.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp [W, tateNormalFormCurve] at heq
    dsimp [TateEq]
    ring_nf at heq ⊢
    exact heq
  · have hpsi := Psi3X_eq_zero_of_three_nsmul b c X Y hT h3
    dsimp [Psi3X, TateNFDivision.Psi3X] at hpsi ⊢
    ring_nf at hpsi ⊢
    exact hpsi

theorem no_obstruction21 : ¬ ∃ b c X Y : ℚ, Obstruction21 b c X Y := by
  rintro ⟨b, c, X, Y, hb, hF7, _hTate, hPsi⟩
  have hc : c ≠ 0 := by
    intro hc0
    subst c
    simp only [F7] at hF7
    apply hb
    nlinarith [sq_nonneg b]
  let t : ℚ := b / c
  have ht0 : t ≠ 0 := div_ne_zero hb hc
  have ht1 : t ≠ 1 := by
    intro ht
    have hbc : b = c := (div_eq_one_iff_eq hc).mp ht
    rw [hbc] at hF7
    simp only [F7] at hF7
    ring_nf at hF7
    exact (pow_ne_zero 3 hc) hF7
  have hcparam : c = t * (t - 1) := by
    dsimp only [t]
    simp only [F7] at hF7
    field_simp [hc]
    nlinarith [hF7]
  have hbparam : b = t ^ 2 * (t - 1) := by
    calc
      b = t * c := by
        dsimp only [t]
        exact (div_mul_cancel₀ b hc).symm
      _ = t * (t * (t - 1)) := by rw [hcparam]
      _ = t ^ 2 * (t - 1) := by ring
  have hG : RationalPointsX121.G21 t X = 0 := by
    rw [← hPsi]
    rw [hbparam, hcparam]
    unfold Psi3X RationalPointsX121.G21
    ring
  exact RationalPointsX121.G21_ne_zero_of_t_ne_zero_one t X ht0 ht1 hG

theorem no_rational_point_of_order_21
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 21 := by
  intro h21
  exact no_obstruction21 (order21_to_tate_obstruction E h21)

end
end MazurProof.CyclicExclusion21
