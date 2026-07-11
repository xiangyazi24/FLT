import FLT.Assumptions.MazurProof.TateNFDivision
import FLT.Assumptions.MazurProof.TateNormalFormBridge
import FLT.Assumptions.MazurProof.TorsionDefs
import scratch.KeystoneEDS

/-!
# The reusable order-18 Tate-normal-form bridge

`18 = 2 · 9`.  A rational point `P` of exact order `18` yields two derived
rational points:

* `2 • P`, of exact order `9`;
* `9 • P`, of exact order `2`.

This file bridges from such a `P` to the Tate normal form `E(b,c)` with the
order-`9` point placed at the marked origin `(0,0)`.  Two independently checked
conditions on the *same* parameters `(b,c)` result:

* the **order-9 division condition** `F₉(b,c) = 0`, obtained from the
  division-polynomial identity `ψ₉(0,0) = b²⁷ · F₉(b,c)`;
* the **rational 2-torsion constraint** `∃ X, T₂(b,c,X) = 0`, obtained by
  transporting the order-2 point `9 • P` through the Weierstrass variable
  changes and reading off the `x`-coordinate of the resulting rational
  2-torsion point of `E(b,c)`.

Together these are exactly `MazurProof.TateNFDivision.Obstruction18 b c`, the
system consumed by `CyclicExclusion18`.

The point-transport reuses the variable-change group isomorphism
`Scratch.TateZ2xZ10Reduction.variableChangePointAddEquiv` (the same machinery
underpinning `TateNormalFormBridge`); the division-polynomial half reuses the
`KeystoneLadder` `n • P = 0 ↔ ΨSqₙ` ladder.  No final rank claim is made.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder18

open Scratch.TateZ2xZ10Reduction

noncomputable section

private abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

/-! ## The marked origin on Tate normal form -/

private theorem tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W]

/-- The marked point `(0,0)` on the order-`n` Tate curve. -/
def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

/-! ## Division-polynomial nonvanishing (reused from the order-11 development)

These two lemmas are the local specialization of the `KeystoneLadder`
`n • P = 0 ↔ ΨSqₙ(x) = 0` criterion to rational curves: over `ℚ` all division
polynomials `ψₘ` are nonzero, so the criterion applies unconditionally. -/

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

/-! ## The order-9 division condition `F₉(b,c) = 0`

The origin evaluations of the auxiliary polynomials `preΨ'ₖ` are read off from
Mathlib's elliptic-divisibility recurrence, exactly as in the order-11 file. -/

private lemma eval_prePsi_five (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_six (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 =
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 0)
  simpa using h

private lemma eval_prePsi_nine (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 =
      ((W b c).preΨ' 6).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 2)
  simpa [show Even (2 : ℕ) by decide] using h

/-- The order-9 division-polynomial identity at the Tate origin. -/
theorem prePsi_nine_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 =
      b ^ 27 * TateNFDivision.F9 b c := by
  rw [eval_prePsi_nine, eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, TateNFDivision.F9]
  ring

/-- If the marked origin has additive order 9 then `F₉(b,c) = 0`. -/
theorem F9_eq_zero_of_tateOrigin_order_nine
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 9) :
    TateNFDivision.F9 b c = 0 := by
  have h9 : (9 : ℕ) • tateOrigin b c = 0 := by
    simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)
  have hPsiSq : ((W b c).ΨSq (9 : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp h9
  have hpre : ((W b c).preΨ' 9).eval 0 = 0 := by
    change ((W b c).ΨSq (9 : ℕ)).eval 0 = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 9] at hPsiSq
    simpa [show ¬ Even (9 : ℕ) by decide] using hPsiSq
  rw [prePsi_nine_eval_tate_origin] at hpre
  exact (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 27 hb)

/-! ## The rational 2-torsion constraint `T₂(b,c,X) = 0`

Any rational affine point of order dividing `2` on `E(b,c)` supplies a rational
root of the Tate 2-division cubic `T₂`.  Its `x`-coordinate satisfies `T₂ = 0`
because the two-torsion condition `2Y + (1-c)X - b = 0` together with the curve
equation forces `T₂(b,c,X) = (2Y + (1-c)X - b)² - 4·(curve) = 0`. -/

private lemma two_torsion_Y_eq_negY
    (b c X Y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular (W b c) X Y)
    (h2 : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some X Y h :
          WeierstrassCurve.Affine.Point (W b c)) = 0) :
    Y = WeierstrassCurve.Affine.negY (W b c) X Y := by
  by_contra hne
  have hself := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := h) hne
  rw [← two_nsmul] at hself
  rw [h2] at hself
  exact (WeierstrassCurve.Affine.Point.some_ne_zero _) hself.symm

/-- A rational point of order dividing 2 on `E(b,c)` has an `x`-coordinate that
is a root of the Tate two-division cubic `T₂`. -/
theorem T2_eq_zero_of_two_nsmul
    (b c X Y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular (W b c) X Y)
    (h2 : (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some X Y h :
          WeierstrassCurve.Affine.Point (W b c)) = 0) :
    TateNFDivision.T2 b c X = 0 := by
  have hYeq : Y = WeierstrassCurve.Affine.negY (W b c) X Y :=
    two_torsion_Y_eq_negY b c X Y h h2
  have hy : 2 * Y + (1 - c) * X - b = 0 := by
    rw [WeierstrassCurve.Affine.negY] at hYeq
    simp only [W, tateNormalFormCurve_a₁, tateNormalFormCurve_a₃] at hYeq
    linarith
  have heq : WeierstrassCurve.Affine.Equation (W b c) X Y := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [W, tateNormalFormCurve_a₁, tateNormalFormCurve_a₂,
    tateNormalFormCurve_a₃, tateNormalFormCurve_a₄,
    tateNormalFormCurve_a₆] at heq
  rw [TateNFDivision.T2]
  linear_combination (2 * Y + (1 - c) * X - b) * hy - 4 * heq

/-! ## Transport helpers for the enhanced bridge

Local copies of the (private) `TateNormalFormBridge` helper lemmas, needed to
build the group isomorphism `E ≃+ E(b,c)` that transports the 2-torsion point. -/

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
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, ha₂, ha₄]
    · rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
      simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY, ha₂, ha₄]
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
  rw [h2eq]
  rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl]
  simp [WeierstrassCurve.Affine.negY]

/-! ## The enhanced Tate-normal-form bridge

Like `TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three`, but it
additionally *transports* a chosen rational 2-torsion point `T` along the same
variable changes, returning the coordinates of its image on `E(b,c)`. -/

/--
Any rational point `P` of additive order `n > 3` can be moved to the marked
origin of a nonsingular Tate normal form, and simultaneously any rational
2-torsion point `T ≠ 0` is transported to an explicit rational affine 2-torsion
point of the same Tate curve.
-/
theorem exists_tate_normalized_2torsion_of_addOrder_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P T : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n)
    (hT2 : (2 : ℕ) • T = 0) (hTne0 : T ≠ 0) :
    ∃ b c xT yT : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
      ∃ hT : WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) xT yT,
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          (2 : ℕ) •
              (WeierstrassCurve.Affine.Point.some xT yT hT :
                WeierstrassCurve.Affine.Point (tateNormalFormCurve b c)) = 0 := by
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
      let Psmall₀ :
          ∀ m < n, 0 < m → (m : ℕ) • P₀ ≠ 0 :=
        ((addOrderOf_eq_iff (x := P₀) (by omega)).mp hP₀_order).2
      let T₀ : WeierstrassCurve.Affine.Point E := T
      have hT2₀ : (2 : ℕ) • T₀ = 0 := by
        change (2 : ℕ) • (T : WeierstrassCurve.Affine.Point E) = 0
        simpa using hT2
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
      have hW2eq : C1 • W1 = tateNormalFormCurve b c := by
        ext <;> dsimp [C1, ρ, b, c, tateNormalFormCurve,
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
      haveI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := by
        rw [← hW2eq]
        infer_instance
      let φ1raw : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (C1 • W1) :=
        variableChangePointAddEquiv W1 C1
      let φ1 : WeierstrassCurve.Affine.Point W1 ≃+
          WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
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
      have hT2map : (2 : ℕ) • φ1 (φ0 T₀) = 0 := by
        calc
          (2 : ℕ) • φ1 (φ0 T₀) = φ1 ((2 : ℕ) • φ0 T₀) :=
            (map_nsmul φ1 2 (φ0 T₀)).symm
          _ = φ1 (φ0 ((2 : ℕ) • T₀)) := by
            rw [← map_nsmul φ0 2 T₀]
          _ = 0 := by
            rw [hT2₀, map_zero, map_zero]
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
          simpa [hTpoint] using hT2map

/-! ## Order arithmetic for `18 = 2 · 9` -/

private lemma addOrderOf_two_nsmul_of_order18
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 18) :
    addOrderOf ((2 : ℕ) • P) = 9 := by
  rw [addOrderOf_nsmul' P (by norm_num), hP]
  norm_num

private lemma addOrderOf_nine_nsmul_of_order18
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 18) :
    addOrderOf ((9 : ℕ) • P) = 2 := by
  rw [addOrderOf_nsmul' P (by norm_num), hP]
  norm_num

/-! ## Assembly: order 18 gives the Tate `Obstruction18` system -/

/--
The reusable order-18 bridge.  An elliptic curve over `ℚ` with a rational point
of exact order `18` yields Tate parameters `(b,c)` simultaneously solving the
order-9 division condition `F₉(b,c) = 0` and carrying a rational 2-torsion
point, i.e. satisfying `MazurProof.TateNFDivision.Obstruction18`.
-/
theorem order18_gives_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h18 : HasRationalPointOfOrder E 18) :
    ∃ b c : ℚ, TateNFDivision.Obstruction18 b c := by
  obtain ⟨P, hP⟩ := h18
  set Q : (E⁄ℚ).Point := (2 : ℕ) • P with hQ
  set R : (E⁄ℚ).Point := (9 : ℕ) • P with hR
  have hQord : addOrderOf Q = 9 := addOrderOf_two_nsmul_of_order18 hP
  have hRord : addOrderOf R = 2 := addOrderOf_nine_nsmul_of_order18 hP
  have hR2 : (2 : ℕ) • R = 0 := by
    have := addOrderOf_nsmul_eq_zero R
    rwa [hRord] at this
  have hRne0 : R ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hRord
    exact absurd hRord (by norm_num)
  obtain ⟨b, c, xT, yT, hEll, hT, hord, hb, h2t⟩ :=
    exists_tate_normalized_2torsion_of_addOrder_gt_three
      E Q R 9 (by norm_num) hQord hR2 hRne0
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  refine ⟨b, c, ⟨hb, ?_⟩, ⟨xT, ?_⟩⟩
  · exact F9_eq_zero_of_tateOrigin_order_nine b c hb hord
  · exact T2_eq_zero_of_two_nsmul b c xT yT hT h2t

/-- Flat form matching the `Obstruction18 b c X` predicate of
`CyclicExclusion18`. -/
theorem order18_to_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h18 : HasRationalPointOfOrder E 18) :
    ∃ b c X : ℚ,
      b ≠ 0 ∧ TateNFDivision.F9 b c = 0 ∧ TateNFDivision.T2 b c X = 0 := by
  obtain ⟨b, c, ⟨hb, hF9⟩, X, hT2⟩ := order18_gives_tate_obstruction E h18
  exact ⟨b, c, X, hb, hF9, hT2⟩

end

end MazurProof.TateOrder18
