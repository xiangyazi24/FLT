import FLT.Assumptions.MazurProof.TateNFDivision
import FLT.Assumptions.MazurProof.TateNormalFormBridge
import FLT.Assumptions.MazurProof.TorsionDefs
import scratch.KeystoneEDS

/-!
# Generic odd-order division condition at the Tate origin

This file factors out the kernel-checked division-polynomial argument shared by
the order-11 and order-18 developments.  If the marked origin on a Tate normal
form has odd additive order `n`, then `preΨ'_n(0) = 0`.  Conversely, a proper
odd multiple below the exact order has nonzero evaluation.

The final theorem combines this with `TateNormalFormBridge`: every rational
point of odd order greater than three produces nonsingular Tate parameters
with a nonzero `b` parameter and the corresponding raw division condition.
No explicit factorization of `preΨ'_n(0)` is asserted here.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOriginDivision

open Scratch.TateZ2xZ10Reduction

noncomputable section

abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

theorem psi_ne_zero_rat (W : WeierstrassCurve ℚ) :
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

theorem nsmul_eq_zero_iff_PsiSq_eval
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

theorem tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W, tateNormalFormCurve]

/-- The marked point `(0,0)` on a Tate normal form. -/
def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

theorem tateOrigin_eq_normalized_origin
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    tateOrigin b c = TateNormalFormBridge.tateOrigin b c := by
  change WeierstrassCurve.Affine.Point.some 0 0 _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

/-- For odd `n`, vanishing of the `n`-multiple of the Tate origin implies the
raw division condition `preΨ'_n(0) = 0`. -/
theorem prePsi_eval_zero_of_odd_nsmul_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {n : ℕ} (hnodd : ¬ Even n)
    (hn : n • tateOrigin b c = 0) :
    ((W b c).preΨ' n).eval 0 = 0 := by
  have hPsiSq : ((W b c).ΨSq (n : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp hn
  change ((W b c).ΨSq n).eval 0 = 0 at hPsiSq
  rw [(W b c).ΨSq_ofNat n] at hPsiSq
  simpa [hnodd] using hPsiSq

/-- For odd `n`, a nonzero `n`-multiple forces the raw division evaluation to
be nonzero. -/
theorem prePsi_eval_ne_zero_of_odd_nsmul_ne_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {n : ℕ} (hnodd : ¬ Even n)
    (hn : n • tateOrigin b c ≠ 0) :
    ((W b c).preΨ' n).eval 0 ≠ 0 := by
  intro hpre
  apply hn
  apply (nsmul_eq_zero_iff_PsiSq_eval (W b c)
    (tate_origin_nonsingular b c)).mpr
  rw [(W b c).ΨSq_ofNat n]
  simp [hnodd, hpre]

/-- The raw odd division polynomial vanishes at a Tate origin of exact order
`n`. -/
theorem prePsi_eval_zero_of_odd_addOrder
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {n : ℕ} (hnodd : ¬ Even n)
    (hord : addOrderOf (tateOrigin b c) = n) :
    ((W b c).preΨ' n).eval 0 = 0 := by
  apply prePsi_eval_zero_of_odd_nsmul_eq_zero b c hnodd
  simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)

/-- Every positive proper odd multiple below an exact order has nonzero raw
division evaluation. -/
theorem prePsi_eval_ne_zero_of_lt_addOrder
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    {m n : ℕ} (hnpos : 0 < n) (hmpos : 0 < m) (hmn : m < n)
    (hmodd : ¬ Even m) (hord : addOrderOf (tateOrigin b c) = n) :
    ((W b c).preΨ' m).eval 0 ≠ 0 := by
  have hm : m • tateOrigin b c ≠ 0 :=
    ((addOrderOf_eq_iff (x := tateOrigin b c) hnpos).mp hord).2 m hmn hmpos
  exact prePsi_eval_ne_zero_of_odd_nsmul_ne_zero b c hmodd hm

/-- Generic Tate reduction for an odd exact order greater than three. -/
theorem exists_tate_parameters_of_odd_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (P : (E⁄ℚ).Point) (hn3 : 3 < n) (hnodd : ¬ Even n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          ((W b c).preΨ' n).eval 0 = 0 := by
  obtain ⟨b, c, hEll, hord, hb⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three
      E P n hn3 hP
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have horigin : addOrderOf (tateOrigin b c) = n := by
    rw [tateOrigin_eq_normalized_origin]
    exact hord
  exact ⟨b, c, inferInstance, horigin, hb,
    prePsi_eval_zero_of_odd_addOrder b c hnodd horigin⟩

/-- Predicate-level wrapper of `exists_tate_parameters_of_odd_order`. -/
theorem exists_tate_parameters_of_has_rational_point_of_odd_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {n : ℕ} (hn3 : 3 < n) (hnodd : ¬ Even n)
    (hP : HasRationalPointOfOrder E n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 ∧
          ((W b c).preΨ' n).eval 0 = 0 := by
  obtain ⟨P, hP⟩ := hP
  exact exists_tate_parameters_of_odd_order E P hn3 hnodd hP

end

end MazurProof.TateOriginDivision
