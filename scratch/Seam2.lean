/-
SEAM 2 build: the x-coordinate formula for [n]P, avoiding omega_n via x-only
differential addition.  Standalone scratch file; do not edit NTorsionCard.lean or
Torsion.lean.
-/
import Mathlib

set_option warn.sorry false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine

namespace Seam2

variable {k : Type*} [Field k] [DecidableEq k]

/-- Projective equality on P^1 representatives, oriented as `v = c • u`
for a nonzero scalar `c`. -/
def SameP1 (u v : Fin 2 → k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ v = c • u

namespace SameP1

lemma refl (u : Fin 2 → k) : SameP1 u u := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp

lemma symm {u v : Fin 2 → k} (h : SameP1 u v) : SameP1 v u := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  ext i
  simp [Pi.smul_apply, hc]

lemma trans {u v w : Fin 2 → k} (huv : SameP1 u v) (hvw : SameP1 v w) : SameP1 u w := by
  rcases huv with ⟨c, hc, rfl⟩
  rcases hvw with ⟨d, hd, rfl⟩
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  ext i
  simp [Pi.smul_apply, mul_assoc]

lemma second_eq_zero_of_same_infty {v : Fin 2 → k}
    (h : SameP1 (![1, 0] : Fin 2 → k) v) : v 1 = 0 := by
  rcases h with ⟨c, _hc, rfl⟩
  simp

lemma second_ne_zero_of_same_affine {x : k} {v : Fin 2 → k}
    (h : SameP1 (![x, 1] : Fin 2 → k) v) : v 1 ≠ 0 := by
  rcases h with ⟨c, hc, rfl⟩
  simpa using hc

end SameP1

abbrev EPoint (W : WeierstrassCurve k) := W.toAffine.Point

/-- The intended x-coordinate representative `[Phi_n(x), PsiSq_n(x)]`. -/
noncomputable def xPair (W : WeierstrassCurve k) (n : ℤ) (x : k) : Fin 2 → k :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

namespace XOnly

@[simp] def X (v : Fin 2 → k) : k := v 0
@[simp] def Z (v : Fin 2 → k) : k := v 1

def Δ (A B : Fin 2 → k) : k :=
  X A * Z B - X B * Z A

def diffAddNum (W : WeierstrassCurve k) (A B D : Fin 2 → k) : k :=
  let XA := X A
  let ZA := Z A
  let XB := X B
  let ZB := Z B
  let XD := X D
  let ZD := Z D
  let d := Δ A B
  let s := XA * ZB + XB * ZA
  let n :=
      2 * XA * XB * s
    + W.b₂ * XA * XB * ZA * ZB
    + W.b₄ * s * ZA * ZB
    + W.b₆ * (ZA * ZB) ^ 2
  n * ZD - XD * d ^ 2

def diffAddDen (_W : WeierstrassCurve k) (A B D : Fin 2 → k) : k :=
  (Δ A B) ^ 2 * Z D

def diffAddRep (W : WeierstrassCurve k) (A B D : Fin 2 → k) : Fin 2 → k :=
  ![diffAddNum W A B D, diffAddDen W A B D]

lemma diffAddNum_smul_smul_smul (W : WeierstrassCurve k) (A B D : Fin 2 → k) (a b d : k) :
    diffAddNum W (a • A) (b • B) (d • D) =
      a ^ 2 * b ^ 2 * d * diffAddNum W A B D := by
  simp [diffAddNum, Δ, X, Z, Pi.smul_apply]
  ring

lemma diffAddDen_smul_smul_smul (W : WeierstrassCurve k) (A B D : Fin 2 → k) (a b d : k) :
    diffAddDen W (a • A) (b • B) (d • D) =
      a ^ 2 * b ^ 2 * d * diffAddDen W A B D := by
  simp [diffAddDen, Δ, X, Z, Pi.smul_apply]
  ring

lemma Ψ₂Sq_eval_eq_sub_negY_sq (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Equation x y) :
    W.Ψ₂Sq.eval x = (y - W.toAffine.negY x y) ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  linear_combination (norm := ring1) -4 * h

lemma diffAddNum_affine_of_X_ne (W : WeierstrassCurve k) {x₁ x₂ y₁ y₂ : k}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hx : x₁ ≠ x₂) :
    (2 * x₁ * x₂ * (x₁ + x₂) + W.b₂ * x₁ * x₂ + W.b₄ * (x₁ + x₂) + W.b₆) -
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) *
          (x₁ - x₂) ^ 2 =
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) * (x₁ - x₂) ^ 2 := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at *
  rw [WeierstrassCurve.Affine.equation_iff] at h₁ h₂
  field_simp [sub_ne_zero.mpr hx]
  linear_combination (norm := ring1) -2 * h₁ - 2 * h₂

theorem diffAddRep_congr
    (W : WeierstrassCurve k)
    {A A' B B' D D' : Fin 2 → k}
    (hA : SameP1 A A') (hB : SameP1 B B') (hD : SameP1 D D') :
    SameP1 (diffAddRep W A B D) (diffAddRep W A' B' D') := by
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  rcases hD with ⟨d, hd, rfl⟩
  refine ⟨a ^ 2 * b ^ 2 * d, mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hb)) hd, ?_⟩
  ext i <;> fin_cases i
  · simp [diffAddRep, diffAddNum_smul_smul_smul, Pi.smul_apply]
  · simp [diffAddRep, diffAddDen_smul_smul_smul, Pi.smul_apply]

/-- HARD GEOMETRIC PRIMITIVE: x-only differential addition for general Weierstrass curves. -/
theorem xRep_add_of_xRep_sub
    (W : WeierstrassCurve k)
    [W.IsElliptic]
    (A B : W.toAffine.Point)
    (hsub : A - B ≠ 0) :
    SameP1 ((A + B).xRep) (diffAddRep W A.xRep B.xRep (A - B).xRep) := by
  classical
  cases A with
  | zero =>
      cases B with
      | zero =>
          exact False.elim (hsub (by simp [sub_eq_add_neg]))
      | some x₂ y₂ h₂ =>
          refine ⟨1, one_ne_zero, ?_⟩
          ext i <;> fin_cases i <;> simp [diffAddRep, diffAddNum, diffAddDen, Δ, X, Z,
            sub_eq_add_neg, ← Point.zero_def] <;> ring
  | some x₁ y₁ h₁ =>
      cases B with
      | zero =>
          refine ⟨1, one_ne_zero, ?_⟩
          ext i <;> fin_cases i <;> simp [diffAddRep, diffAddNum, diffAddDen, Δ, X, Z,
            sub_eq_add_neg, ← Point.zero_def] <;> ring
      | some x₂ y₂ h₂ =>
          by_cases hx : x₁ = x₂
          · have hpoint_or :
                Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ ∨
                  Point.some x₁ y₁ h₁ = -Point.some x₂ y₂ h₂ :=
              (Point.X_eq_iff (W := W.toAffine)).mp hx
            have hneg : Point.some x₁ y₁ h₁ = -Point.some x₂ y₂ h₂ := by
              rcases hpoint_or with hsame | hneg
              · exfalso
                apply hsub
                simp [sub_eq_add_neg, hsame]
              · exact hneg
            have hy : y₁ = W.toAffine.negY x₂ y₂ := by
              have hneg' := hneg
              simp [Point.neg_some] at hneg'
              exact hneg'.2
            have hsum :
                Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0 :=
              Point.add_of_Y_eq hx hy
            have hself_ne : y₁ ≠ W.toAffine.negY x₁ y₁ := by
              intro hself
              apply hsub
              have hdouble :
                  Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ = 0 :=
                Point.add_self_of_Y_eq hself
              simpa [sub_eq_add_neg, hneg.symm] using hdouble
            have hψ₂_ne : W.Ψ₂Sq.eval x₁ ≠ 0 := by
              rw [Ψ₂Sq_eval_eq_sub_negY_sq W h₁.1]
              exact pow_ne_zero 2 (sub_ne_zero.mpr hself_ne)
            cases hD : (Point.some x₁ y₁ h₁ : W.toAffine.Point) -
                Point.some x₂ y₂ h₂ with
            | zero =>
                exact False.elim (hsub hD)
            | some xD yD hDsing =>
                refine ⟨W.Ψ₂Sq.eval x₁, hψ₂_ne, ?_⟩
                ext i <;> fin_cases i
                · simp only [hsum, Point.xRep_zero, Pi.smul_apply, Matrix.cons_val_zero]
                  simp [diffAddRep, diffAddNum, diffAddDen, Δ, X, Z, hD, hx, hy,
                    WeierstrassCurve.Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul,
                    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
                  ring
                · rw [hsum]
                  simp [diffAddRep, diffAddNum, diffAddDen, Δ, X, Z, hx]
          · have hsub_rep :
                ((Point.some x₁ y₁ h₁ : W.toAffine.Point) -
                    Point.some x₂ y₂ h₂).xRep =
                  ![W.toAffine.addX x₁ x₂
                      (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)), 1] := by
              simp [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hx]
            refine ⟨(x₁ - x₂) ^ 2, pow_ne_zero 2 (sub_ne_zero.mpr hx), ?_⟩
            ext i <;> fin_cases i
            · simp only [Point.add_of_X_ne hx, Point.xRep_some, hsub_rep, diffAddRep,
                Matrix.cons_val_zero, Pi.smul_apply]
              simp [diffAddNum, Δ, X, Z]
              simpa [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
                mul_comm, mul_left_comm, mul_assoc] using
                diffAddNum_affine_of_X_ne W h₁.1 h₂.1 hx
            · simp [Point.add_of_X_ne hx, Point.xRep_some, hsub_rep, diffAddRep,
                diffAddDen, Δ, X, Z]

end XOnly

variable (W : WeierstrassCurve k)

/-- Odd EDS compatibility for the x-only differential-addition representative. -/
theorem xPair_diffAdd_odd
    (m : ℕ) (x : k) :
    SameP1
      (XOnly.diffAddRep W
        (xPair W ((m + 3 : ℕ) : ℤ) x)
        (xPair W ((m + 2 : ℕ) : ℤ) x)
        (xPair W (1 : ℤ) x))
      (xPair W ((2 * (m + 2) + 1 : ℕ) : ℤ) x) := by
  sorry

/-- Even EDS compatibility for the x-only differential-addition representative. -/
theorem xPair_diffAdd_even
    (m : ℕ) (x : k) :
    SameP1
      (XOnly.diffAddRep W
        (xPair W ((m + 4 : ℕ) : ℤ) x)
        (xPair W ((m + 2 : ℕ) : ℤ) x)
        (xPair W (2 : ℤ) x))
      (xPair W ((2 * (m + 3) : ℕ) : ℤ) x) := by
  sorry

theorem xRep_nsmul_zero
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((0 • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
      (xPair W (0 : ℤ) x) := by
  simpa [xPair] using SameP1.refl (![1, 0] : Fin 2 → k)

theorem xRep_nsmul_one
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((1 • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
      (xPair W (1 : ℤ) x) := by
  simpa [xPair] using SameP1.refl (![x, 1] : Fin 2 → k)

/-- Base case `n = 2`; this is where `Psi_2^2` first enters. -/
theorem xRep_two_nsmul
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((2 • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
      (xPair W (2 : ℤ) x) := by
  sorry

theorem xRep_three_nsmul
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((3 • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
      (xPair W (3 : ℤ) x) := by
  sorry

theorem xRep_four_nsmul
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    SameP1
      ((4 • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
      (xPair W (4 : ℤ) x) := by
  sorry

/-- Strong-induction step for all `n > 4`.

This is the EDS bookkeeping step: split by parity, use differential addition with
differences `P` and `2P`, and dispatch the even 2-torsion specialization. -/
theorem xRep_nsmul_same_xPair_step
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    {n : ℕ} (hnlarge : ¬ n ≤ 4)
    (IH : ∀ m < n,
      SameP1
        ((m • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
        (xPair W (m : ℤ) x)) :
    SameP1
      ((n • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
      (xPair W (n : ℤ) x) := by
  sorry

/-- The projective x-coordinate formula for `[n]P`. -/
theorem xRep_nsmul_same_xPair
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (n : ℕ) :
    SameP1
      ((n • (WeierstrassCurve.Affine.Point.some x y h : EPoint W)).xRep)
      (xPair W (n : ℤ) x) := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
      by_cases hnsmall : n ≤ 4
      · interval_cases n
        · simpa using xRep_nsmul_zero (W := W) h
        · simpa using xRep_nsmul_one (W := W) h
        · simpa using xRep_two_nsmul (W := W) h
        · simpa using xRep_three_nsmul (W := W) h
        · simpa using xRep_four_nsmul (W := W) h
      · exact xRep_nsmul_same_xPair_step (W := W) h hnsmall IH

/-- SEAM 2 target: `[n]P = 0` iff the squared division polynomial vanishes at `x(P)`. -/
theorem nsmul_eq_zero_iff_ΨSq_eval
    [W.IsElliptic]
    {x y : k} (h : W.toAffine.Nonsingular x y)
    (n : ℕ) :
    n • (WeierstrassCurve.Affine.Point.some x y h : EPoint W) = 0
      ↔
    (W.ΨSq (n : ℤ)).eval x = 0 := by
  classical
  let P : EPoint W := WeierstrassCurve.Affine.Point.some x y h
  constructor
  · intro hn
    have hsame :
        SameP1 ((n • P).xRep) (xPair W (n : ℤ) x) :=
      xRep_nsmul_same_xPair (W := W) h n
    have hsecond := SameP1.second_eq_zero_of_same_infty (v := xPair W (n : ℤ) x) (by
      simpa [P, hn] using hsame)
    simpa [xPair] using hsecond
  · intro hψ
    by_contra hn
    cases hnp : n • P with
    | zero =>
        exact hn hnp
    | some xn yn hnonsing =>
        have hsame :
            SameP1 ((n • P).xRep) (xPair W (n : ℤ) x) :=
          xRep_nsmul_same_xPair (W := W) h n
        have hsecond_ne :
            (xPair W (n : ℤ) x) 1 ≠ 0 :=
          SameP1.second_ne_zero_of_same_affine (x := xn) (v := xPair W (n : ℤ) x) (by
            simpa [hnp] using hsame)
        exact hsecond_ne (by simpa [xPair] using hψ)

end Seam2
