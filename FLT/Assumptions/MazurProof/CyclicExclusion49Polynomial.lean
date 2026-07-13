import FLT.Assumptions.MazurProof.TateOrder25Factor

/-!
# The compact order-49 Tate polynomial

This file isolates the direct polynomial form of the order-49 obstruction.
It deliberately does not import `CyclicExclusion49`, so the axiom in that file
cannot be used in any proof below.

Writing

`((W b c).preΨ' n).eval 0 = b ^ eₙ * Gₙ(b,c)`,

the division-polynomial recurrence gives compact factors `G₂₃`, ..., `G₂₆`
and

`((W b c).preΨ' 49).eval 0 = b ^ 800 * G49(b,c)`.

The lower-order value is

`((W b c).preΨ' 7).eval 0 = b ^ 16 * F7(b,c)`.

Consequently the raw Tate obstruction is equivalent to the purely polynomial
system

* `b ≠ 0`;
* the explicit Tate discriminant is nonzero;
* `F7(b,c) ≠ 0`;
* `G49(b,c) = 0`.

All recurrence and reduction statements are proved below.  The final
rational-solubility assertion is stated separately at the end.
-/

open Polynomial

namespace MazurProof.CyclicExclusion49Polynomial

open TateNFDivision
open TateOriginDivision
open TateOrder25Factor
open Scratch.TateZ2xZ10Reduction

noncomputable section

private abbrev W49 (b c : ℚ) : WeierstrassCurve ℚ :=
  TateOriginDivision.W b c

/-! ## Low-order origin evaluations -/

private lemma eval_prePsi_five (b c : ℚ) :
    ((W49 b c).preΨ' 5).eval 0 =
      ((W49 b c).preΨ₄).eval 0 * ((W49 b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W49 b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_six (b c : ℚ) :
    ((W49 b c).preΨ' 6).eval 0 =
      ((W49 b c).preΨ' 3).eval 0 * ((W49 b c).preΨ' 5).eval 0 -
        ((W49 b c).preΨ' 3).eval 0 * (((W49 b c).preΨ' 4).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_even 0)
  simpa using h

private lemma eval_prePsi_seven (b c : ℚ) :
    ((W49 b c).preΨ' 7).eval 0 =
      ((W49 b c).preΨ' 5).eval 0 * (((W49 b c).preΨ' 3).eval 0) ^ 3 -
        ((W49 b c).preΨ' 4).eval 0 ^ 3 * ((W49 b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 1)
  simpa using h

private lemma eval_prePsi_eight (b c : ℚ) :
    ((W49 b c).preΨ' 8).eval 0 =
      (((W49 b c).preΨ' 3).eval 0) ^ 2 * ((W49 b c).preΨ' 4).eval 0 *
          ((W49 b c).preΨ' 6).eval 0 -
        ((W49 b c).preΨ' 4).eval 0 * (((W49 b c).preΨ' 5).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_even 1)
  simpa using h

private lemma eval_prePsi_nine (b c : ℚ) :
    ((W49 b c).preΨ' 9).eval 0 =
      ((W49 b c).preΨ' 6).eval 0 * (((W49 b c).preΨ' 4).eval 0) ^ 3 *
          ((W49 b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W49 b c).preΨ' 3).eval 0 * (((W49 b c).preΨ' 5).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 2)
  simpa [show Even (2 : ℕ) by decide] using h

private lemma eval_prePsi_ten (b c : ℚ) :
    ((W49 b c).preΨ' 10).eval 0 =
      ((W49 b c).preΨ' 4).eval 0 ^ 2 * ((W49 b c).preΨ' 5).eval 0 *
          ((W49 b c).preΨ' 7).eval 0 -
        ((W49 b c).preΨ' 3).eval 0 * ((W49 b c).preΨ' 5).eval 0 *
          ((W49 b c).preΨ' 6).eval 0 ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_even 2)
  simpa using h

private lemma eval_prePsi_eleven (b c : ℚ) :
    ((W49 b c).preΨ' 11).eval 0 =
      ((W49 b c).preΨ' 7).eval 0 * (((W49 b c).preΨ' 5).eval 0) ^ 3 -
        ((W49 b c).preΨ' 4).eval 0 * (((W49 b c).preΨ' 6).eval 0) ^ 3 *
          ((W49 b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 3)
  simpa [show ¬ Even (3 : ℕ) by decide] using h

private lemma eval_prePsi_twelve (b c : ℚ) :
    ((W49 b c).preΨ' 12).eval 0 =
      (((W49 b c).preΨ' 5).eval 0) ^ 2 * ((W49 b c).preΨ' 6).eval 0 *
          ((W49 b c).preΨ' 8).eval 0 -
        ((W49 b c).preΨ' 4).eval 0 * ((W49 b c).preΨ' 6).eval 0 *
          (((W49 b c).preΨ' 7).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_even 3)
  simpa using h

private lemma eval_prePsi_thirteen (b c : ℚ) :
    ((W49 b c).preΨ' 13).eval 0 =
      ((W49 b c).preΨ' 8).eval 0 * (((W49 b c).preΨ' 6).eval 0) ^ 3 *
          ((W49 b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W49 b c).preΨ' 5).eval 0 * (((W49 b c).preΨ' 7).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 4)
  simpa [show Even (4 : ℕ) by decide] using h

private lemma eval_prePsi_fourteen (b c : ℚ) :
    ((W49 b c).preΨ' 14).eval 0 =
      (((W49 b c).preΨ' 6).eval 0) ^ 2 * ((W49 b c).preΨ' 7).eval 0 *
          ((W49 b c).preΨ' 9).eval 0 -
        ((W49 b c).preΨ' 5).eval 0 * ((W49 b c).preΨ' 7).eval 0 *
          (((W49 b c).preΨ' 8).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_even 4)
  simpa using h

private lemma eval_prePsi_fifteen (b c : ℚ) :
    ((W49 b c).preΨ' 15).eval 0 =
      ((W49 b c).preΨ' 9).eval 0 * (((W49 b c).preΨ' 7).eval 0) ^ 3 -
        ((W49 b c).preΨ' 6).eval 0 * (((W49 b c).preΨ' 8).eval 0) ^ 3 *
          ((W49 b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 5)
  simpa [show ¬ Even (5 : ℕ) by decide] using h

private lemma Psi2Sq_eval (b c : ℚ) : ((W49 b c).Ψ₂Sq).eval 0 = b ^ 2 := by
  simp [W49, TateOriginDivision.W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

private lemma prePsi_3_eval (b c : ℚ) : ((W49 b c).preΨ' 3).eval 0 = -b ^ 3 := by
  simp [W49, TateOriginDivision.W, tateNormalFormCurve,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private lemma prePsi_4_eval (b c : ℚ) :
    ((W49 b c).preΨ' 4).eval 0 = -(b ^ 4 * c) := by
  simp [W49, TateOriginDivision.W, tateNormalFormCurve,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private lemma prePsi_5_eval (b c : ℚ) :
    ((W49 b c).preΨ' 5).eval 0 = b ^ 8 * F5 b c := by
  rw [eval_prePsi_five]
  simp [W49, TateOriginDivision.W, tateNormalFormCurve,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, F5]
  ring

private lemma prePsi_6_eval (b c : ℚ) :
    ((W49 b c).preΨ' 6).eval 0 = -(b ^ 11 * F6 b c) := by
  rw [eval_prePsi_six, eval_prePsi_five]
  simp [W49, TateOriginDivision.W, tateNormalFormCurve,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, F6]
  ring

/-- The proper order-seven factor at the Tate origin. -/
theorem prePsi_seven_eval_tate_origin (b c : ℚ) :
    ((W49 b c).preΨ' 7).eval 0 = b ^ 16 * F7 b c := by
  rw [eval_prePsi_seven, eval_prePsi_five]
  simp [W49, TateOriginDivision.W, tateNormalFormCurve,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.preΨ'_four,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, F7]
  ring

private lemma prePsi_8_eval (b c : ℚ) :
    ((W49 b c).preΨ' 8).eval 0 = b ^ 20 * c * F8 b c := by
  rw [eval_prePsi_eight, prePsi_3_eval, prePsi_4_eval,
    prePsi_6_eval, prePsi_5_eval]
  simp only [F5, F6, F8]
  ring

private lemma prePsi_9_eval (b c : ℚ) :
    ((W49 b c).preΨ' 9).eval 0 = b ^ 27 * F9 b c := by
  rw [eval_prePsi_nine, prePsi_6_eval, prePsi_4_eval,
    Psi2Sq_eval, prePsi_3_eval, prePsi_5_eval]
  simp only [F5, F6, F9]
  ring

/-! ## Compact factors through order 26 -/

/-- Compact factor with `preΨ'₁₀(0) = b³² · G10 b c`. -/
def G10 (b c : ℚ) : ℚ :=
  F5 b c * (c ^ 2 * F7 b c + b * F6 b c ^ 2)

private lemma prePsi_10_eval (b c : ℚ) :
    ((W49 b c).preΨ' 10).eval 0 = b ^ 32 * G10 b c := by
  rw [eval_prePsi_ten, prePsi_4_eval, prePsi_5_eval,
    prePsi_seven_eval_tate_origin, prePsi_3_eval, prePsi_6_eval]
  simp only [G10]
  ring

private lemma prePsi_11_eval (b c : ℚ) :
    ((W49 b c).preΨ' 11).eval 0 = b ^ 40 * G11 b c := by
  rw [eval_prePsi_eleven, prePsi_seven_eval_tate_origin, prePsi_5_eval,
    prePsi_4_eval, prePsi_6_eval, Psi2Sq_eval]
  simp only [G11]
  ring

private lemma prePsi_12_eval (b c : ℚ) :
    ((W49 b c).preΨ' 12).eval 0 = -(b ^ 47 * G12 b c) := by
  rw [eval_prePsi_twelve, prePsi_5_eval, prePsi_6_eval,
    prePsi_8_eval, prePsi_4_eval, prePsi_seven_eval_tate_origin]
  simp only [G12]
  ring

private lemma prePsi_13_eval (b c : ℚ) :
    ((W49 b c).preΨ' 13).eval 0 = -(b ^ 56 * G13 b c) := by
  rw [eval_prePsi_thirteen, prePsi_8_eval, prePsi_6_eval,
    Psi2Sq_eval, prePsi_5_eval, prePsi_seven_eval_tate_origin]
  simp only [G13]
  ring

private lemma prePsi_14_eval (b c : ℚ) :
    ((W49 b c).preΨ' 14).eval 0 = b ^ 64 * G14 b c := by
  rw [eval_prePsi_fourteen, prePsi_6_eval, prePsi_seven_eval_tate_origin,
    prePsi_9_eval, prePsi_5_eval, prePsi_8_eval]
  simp only [G14]
  ring

private lemma prePsi_15_eval (b c : ℚ) :
    ((W49 b c).preΨ' 15).eval 0 = b ^ 75 * F15 b c := by
  rw [eval_prePsi_fifteen, prePsi_9_eval, prePsi_seven_eval_tate_origin,
    prePsi_6_eval, prePsi_8_eval, Psi2Sq_eval]
  simp only [F6, F15]
  ring

/-- Compact factor with `preΨ'₂₃(0) = b¹⁷⁶ · G23 b c`. -/
def G23 (b c : ℚ) : ℚ :=
  b * G10 b c * G12 b c ^ 3 - G13 b c * G11 b c ^ 3

/-- Compact factor with `preΨ'₂₄(0) = b¹⁹¹ · G24 b c`. -/
def G24 (b c : ℚ) : ℚ :=
  G12 b c * (G10 b c * G13 b c ^ 2 - G11 b c ^ 2 * G14 b c)

/-- Compact factor with `preΨ'₂₅(0) = b²⁰⁸ · G25 b c`.

This still contains the proper order-five factor; no division is performed.
-/
def G25 (b c : ℚ) : ℚ :=
  G11 b c * G13 b c ^ 3 - b * G14 b c * G12 b c ^ 3

/-- Compact factor with `preΨ'₂₆(0) = b²²⁴ · G26 b c`. -/
def G26 (b c : ℚ) : ℚ :=
  G13 b c * (G11 b c * G14 b c ^ 2 - b * G12 b c ^ 2 * F15 b c)

private lemma eval_prePsi_twentythree (b c : ℚ) :
    ((W49 b c).preΨ' 23).eval 0 =
      ((W49 b c).preΨ' 13).eval 0 * (((W49 b c).preΨ' 11).eval 0) ^ 3 -
        ((W49 b c).preΨ' 10).eval 0 * (((W49 b c).preΨ' 12).eval 0) ^ 3 *
          ((W49 b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 9)
  simpa [show ¬ Even (9 : ℕ) by decide] using h

private lemma eval_prePsi_twentyfour (b c : ℚ) :
    ((W49 b c).preΨ' 24).eval 0 =
      ((W49 b c).preΨ' 11).eval 0 ^ 2 * ((W49 b c).preΨ' 12).eval 0 *
          ((W49 b c).preΨ' 14).eval 0 -
        ((W49 b c).preΨ' 10).eval 0 * ((W49 b c).preΨ' 12).eval 0 *
          ((W49 b c).preΨ' 13).eval 0 ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_even 9)
  simpa using h

private lemma eval_prePsi_twentyfive (b c : ℚ) :
    ((W49 b c).preΨ' 25).eval 0 =
      ((W49 b c).preΨ' 14).eval 0 * (((W49 b c).preΨ' 12).eval 0) ^ 3 *
          ((W49 b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W49 b c).preΨ' 11).eval 0 * (((W49 b c).preΨ' 13).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 10)
  simpa [show Even (10 : ℕ) by decide] using h

private lemma eval_prePsi_twentysix (b c : ℚ) :
    ((W49 b c).preΨ' 26).eval 0 =
      ((W49 b c).preΨ' 12).eval 0 ^ 2 * ((W49 b c).preΨ' 13).eval 0 *
          ((W49 b c).preΨ' 15).eval 0 -
        ((W49 b c).preΨ' 11).eval 0 * ((W49 b c).preΨ' 13).eval 0 *
          ((W49 b c).preΨ' 14).eval 0 ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_even 10)
  simpa using h

private lemma prePsi_23_eval (b c : ℚ) :
    ((W49 b c).preΨ' 23).eval 0 = b ^ 176 * G23 b c := by
  rw [eval_prePsi_twentythree, prePsi_13_eval, prePsi_11_eval,
    prePsi_10_eval, prePsi_12_eval, Psi2Sq_eval]
  simp only [G23]
  ring

private lemma prePsi_24_eval (b c : ℚ) :
    ((W49 b c).preΨ' 24).eval 0 = b ^ 191 * G24 b c := by
  rw [eval_prePsi_twentyfour, prePsi_11_eval, prePsi_12_eval,
    prePsi_14_eval, prePsi_10_eval, prePsi_13_eval]
  simp only [G24]
  ring

private lemma prePsi_25_eval (b c : ℚ) :
    ((W49 b c).preΨ' 25).eval 0 = b ^ 208 * G25 b c := by
  rw [eval_prePsi_twentyfive, prePsi_14_eval, prePsi_12_eval,
    Psi2Sq_eval, prePsi_11_eval, prePsi_13_eval]
  simp only [G25]
  ring

private lemma prePsi_26_eval (b c : ℚ) :
    ((W49 b c).preΨ' 26).eval 0 = b ^ 224 * G26 b c := by
  rw [eval_prePsi_twentysix, prePsi_12_eval, prePsi_13_eval,
    prePsi_15_eval, prePsi_11_eval, prePsi_14_eval]
  simp only [G26]
  ring

/-! ## The compact order-49 factor -/

/-- The compact degree-160 order-49 factor.

Its full expansion has about 3500 monomials.  Keeping the lower factors named
is both faster for Lean and substantially more readable.
-/
def G49 (b c : ℚ) : ℚ :=
  b * G26 b c * G24 b c ^ 3 - G23 b c * G25 b c ^ 3

private lemma eval_prePsi_fortynine (b c : ℚ) :
    ((W49 b c).preΨ' 49).eval 0 =
      ((W49 b c).preΨ' 26).eval 0 * (((W49 b c).preΨ' 24).eval 0) ^ 3 *
          ((W49 b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W49 b c).preΨ' 23).eval 0 * (((W49 b c).preΨ' 25).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W49 b c).preΨ'_odd 22)
  simpa [show Even (22 : ℕ) by decide] using h

/-- Compact order-49 division identity at the Tate origin. -/
theorem prePsi_fortynine_eval_tate_origin (b c : ℚ) :
    ((W49 b c).preΨ' 49).eval 0 = b ^ 800 * G49 b c := by
  rw [eval_prePsi_fortynine, prePsi_26_eval, prePsi_24_eval,
    Psi2Sq_eval, prePsi_23_eval, prePsi_25_eval]
  simp only [G49]
  ring

/-! ## Removal of the elliptic-curve and division-polynomial wrappers -/

/-- The Tate discriminant with all Weierstrass definitions expanded. -/
def tateDiscriminant49 (b c : ℚ) : ℚ :=
  b ^ 3 * (16 * b ^ 2 - 8 * b * c ^ 2 - 20 * b * c + b + c * (c - 1) ^ 3)

theorem tate_delta (b c : ℚ) :
    (W49 b c).Δ = tateDiscriminant49 b c := by
  simp [W49, TateOriginDivision.W, tateNormalFormCurve, tateDiscriminant49,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- A local copy of the raw obstruction, used so this file need not import the
file containing the axiom that is to be replaced. -/
def RawOrder49TateObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W49 b c),
      b ≠ 0 ∧
        ((W49 b c).preΨ' 49).eval 0 = 0 ∧
        ((W49 b c).preΨ' 7).eval 0 ≠ 0

/-- The same obstruction after the two division-polynomial evaluations have
been replaced by compact polynomials. -/
def CompactOrder49PolynomialObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W49 b c),
      b ≠ 0 ∧ F7 b c ≠ 0 ∧ G49 b c = 0

/-- The final, purely rational-polynomial system. -/
def PureOrder49PolynomialObstruction : Prop :=
  ∃ b c : ℚ,
    b ≠ 0 ∧
      tateDiscriminant49 b c ≠ 0 ∧
      F7 b c ≠ 0 ∧
      G49 b c = 0

theorem raw_order49_obstruction_iff_compact :
    RawOrder49TateObstruction ↔ CompactOrder49PolynomialObstruction := by
  constructor
  · rintro ⟨b, c, hEll, hb, h49, h7⟩
    have hF7 : F7 b c ≠ 0 := by
      intro hF7
      apply h7
      rw [prePsi_seven_eval_tate_origin, hF7, mul_zero]
    have hG49 : G49 b c = 0 := by
      rw [prePsi_fortynine_eval_tate_origin] at h49
      exact (mul_eq_zero.mp h49).resolve_left (pow_ne_zero 800 hb)
    exact ⟨b, c, hEll, hb, hF7, hG49⟩
  · rintro ⟨b, c, hEll, hb, hF7, hG49⟩
    refine ⟨b, c, hEll, hb, ?_, ?_⟩
    · rw [prePsi_fortynine_eval_tate_origin, hG49, mul_zero]
    · rw [prePsi_seven_eval_tate_origin]
      exact mul_ne_zero (pow_ne_zero 16 hb) hF7

theorem compact_order49_obstruction_iff_pure :
    CompactOrder49PolynomialObstruction ↔ PureOrder49PolynomialObstruction := by
  constructor
  · rintro ⟨b, c, hEll, hb, hF7, hG49⟩
    letI : WeierstrassCurve.IsElliptic (W49 b c) := hEll
    have hdisc : tateDiscriminant49 b c ≠ 0 := by
      intro hzero
      have hDelta : (W49 b c).Δ ≠ 0 := (W49 b c).isUnit_Δ.ne_zero
      apply hDelta
      rw [tate_delta, hzero]
    exact ⟨b, c, hb, hdisc, hF7, hG49⟩
  · rintro ⟨b, c, hb, hdisc, hF7, hG49⟩
    let hEll : WeierstrassCurve.IsElliptic (W49 b c) := ⟨by
      rw [tate_delta, isUnit_iff_ne_zero]
      exact hdisc⟩
    exact ⟨b, c, hEll, hb, hF7, hG49⟩

theorem raw_order49_obstruction_iff_pure :
    RawOrder49TateObstruction ↔ PureOrder49PolynomialObstruction :=
  raw_order49_obstruction_iff_compact.trans compact_order49_obstruction_iff_pure

/-!
## Remaining arithmetic theorem

`G49` is explicit: unfolding `G49`, `G23`, ..., `G10` and the imported
`F5`, ..., `F15`, `G11`, ..., `G14` produces an integer polynomial in `b,c`.
The only missing result is the following exact Diophantine assertion.

A direct completion must supply a checkable certificate proving that every
rational zero of `G49` lies on at least one of these excluded loci:

* `b = 0`;
* `tateDiscriminant49 b c = 0`;
* `F7 b c = 0`.

Equivalently, a generated diamond-quotient certificate may map this open
piece to a noncuspidal rational point of
`y² + xy = x³ - x² - 2x - 1`, followed by a proof that the latter curve's
rational points are only `O` and `(2,-1)`.  Merely assuming either the quotient
map or the rational-point classification would move, rather than close, the
axiom.
-/

/-- `SORRY[N49-POLY]`: the explicit order-49 polynomial has no rational zero
off the singular and proper-order-seven loci. -/
theorem no_pure_order49_polynomial_solution :
    ¬ PureOrder49PolynomialObstruction := by
  sorry

/-- Polynomial-form replacement for the raw Tate obstruction axiom. -/
theorem no_raw_order49_tate_obstruction :
    ¬ RawOrder49TateObstruction := by
  rw [raw_order49_obstruction_iff_pure]
  exact no_pure_order49_polynomial_solution

end

end MazurProof.CyclicExclusion49Polynomial
