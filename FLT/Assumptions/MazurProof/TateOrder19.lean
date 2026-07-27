import FLT.Assumptions.MazurProof.TateNFDivision
import FLT.Assumptions.MazurProof.TateNormalFormBridge
import scratch.KeystoneEDS

/-!
# The concrete order-19 Tate-normal-form condition

Parallels `TateOrder13` and `TateOrder17`: connects the Tate-normal-form
bridge, the division-polynomial recurrence, and the explicit identity
`ψ₁₉(0,0) = -(b¹²⁰ F₁₉(b,c))`.

A rational point of exact order 19 yields concrete Tate parameters
with `b ≠ 0` and `F19 b c = 0`.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder19

open Scratch.TateZ2xZ10Reduction

noncomputable section

private abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

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

/-! ## Division polynomial recurrence evaluated at X=0

For preΨ'(19) we need intermediate values up to preΨ'(11):
  preΨ'(19) = preΨ'_odd 7, m = 7 (odd)
  preΨ'(19) = preΨ'(11) * preΨ'(9)³ - preΨ'(8) * preΨ'(10)³ * Ψ₂Sq²
-/

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

private lemma eval_prePsi_seven (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 =
      ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 3).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 ^ 3 * ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 1)
  simpa using h

private lemma eval_prePsi_eight (b c : ℚ) :
    ((W b c).preΨ' 8).eval 0 =
      (((W b c).preΨ' 3).eval 0) ^ 2 * ((W b c).preΨ' 4).eval 0 *
        ((W b c).preΨ' 6).eval 0 -
      ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 1)
  simpa using h

private lemma eval_prePsi_nine (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 =
      ((W b c).preΨ' 6).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 -
      ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 2)
  simpa [show Even (2 : ℕ) by decide] using h

private lemma eval_prePsi_ten (b c : ℚ) :
    ((W b c).preΨ' 10).eval 0 =
      (((W b c).preΨ' 4).eval 0) ^ 2 * ((W b c).preΨ' 5).eval 0 *
        ((W b c).preΨ' 7).eval 0 -
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 *
        (((W b c).preΨ' 6).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 2)
  simpa using h

private lemma eval_prePsi_eleven (b c : ℚ) :
    ((W b c).preΨ' 11).eval 0 =
      ((W b c).preΨ' 7).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 -
      ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 6).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 3)
  simpa [show ¬ Even (3 : ℕ) by decide] using h

private lemma eval_prePsi_nineteen (b c : ℚ) :
    ((W b c).preΨ' 19).eval 0 =
      ((W b c).preΨ' 11).eval 0 * (((W b c).preΨ' 9).eval 0) ^ 3 -
      ((W b c).preΨ' 8).eval 0 * (((W b c).preΨ' 10).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 7)
  simpa [show ¬ Even (7 : ℕ) by decide] using h

set_option maxHeartbeats 0 in
theorem prePsi_nineteen_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 19).eval 0 =
      -(b ^ 120 * TateNFDivision.F19 b c) := by
  rw [eval_prePsi_nineteen, eval_prePsi_eleven, eval_prePsi_ten,
    eval_prePsi_nine, eval_prePsi_eight, eval_prePsi_seven,
    eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, TateNFDivision.F19]
  ring

/-! ## Connection to torsion order -/

private lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W]

def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

private lemma tateOrigin_eq_normalized_origin
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    tateOrigin b c = TateNormalFormBridge.tateOrigin b c := by
  change WeierstrassCurve.Affine.Point.some 0 0 _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

theorem F19_eq_zero_of_tateOrigin_order_nineteen
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 19) :
    TateNFDivision.F19 b c = 0 := by
  have h19 : (19 : ℕ) • tateOrigin b c = 0 := by
    simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)
  have hPsiSq : ((W b c).ΨSq (19 : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp h19
  have hpre : ((W b c).preΨ' 19).eval 0 = 0 := by
    change ((W b c).ΨSq (19 : ℕ)).eval 0 = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 19] at hPsiSq
    simpa [show ¬ Even (19 : ℕ) by decide] using hPsiSq
  rw [prePsi_nineteen_eval_tate_origin] at hpre
  have hpre' : b ^ 120 * TateNFDivision.F19 b c = 0 := neg_eq_zero.mp hpre
  exact (mul_eq_zero.mp hpre').resolve_left (pow_ne_zero 120 hb)

theorem tateOrigin_order_nineteen_of_F19_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (_hb : b ≠ 0) (hF19 : TateNFDivision.F19 b c = 0) :
    addOrderOf (tateOrigin b c) = 19 := by
  have hpre : ((W b c).preΨ' 19).eval 0 = 0 := by
    rw [prePsi_nineteen_eval_tate_origin, hF19, mul_zero, neg_zero]
  have hPsiSq : ((W b c).ΨSq (19 : ℤ)).eval 0 = 0 := by
    change ((W b c).ΨSq (19 : ℕ)).eval 0 = 0
    rw [(W b c).ΨSq_ofNat 19]
    simp [show ¬ Even (19 : ℕ) by decide, hpre]
  have h19 : (19 : ℕ) • tateOrigin b c = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mpr hPsiSq
  have hne : tateOrigin b c ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero _
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime h19 hne

theorem exists_tate_parameters_of_order_nineteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 19) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = 19 ∧
          b ≠ 0 ∧ TateNFDivision.F19 b c = 0 := by
  obtain ⟨b, c, hEll, hord, hb⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three
      E P 19 (by norm_num) hP
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have horigin : addOrderOf (tateOrigin b c) = 19 := by
    rw [tateOrigin_eq_normalized_origin]
    exact hord
  exact ⟨b, c, inferInstance, horigin, hb,
    F19_eq_zero_of_tateOrigin_order_nineteen b c hb horigin⟩

end

end MazurProof.TateOrder19
