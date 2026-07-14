import FLT.Assumptions.MazurProof.TateOrder25Factor
import FLT.Assumptions.MazurProof.RationalPointsX049

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

/-! ### Removal of the proper order-seven factor

The primitive order-`49` factor is much too large to expand: it has `3526`
monomials.  The definitions below instead record a straight-line division by
`F7`.  If `r + F7 * q` and `s + F7 * t` are two split expressions, the three
small quotient combinators give corresponding splits for products, squares,
and cubes. -/

private def splitMulQuotient (f r q s t : ℚ) : ℚ :=
  q * s + r * t + f * q * t

private def splitSquareQuotient (f r q : ℚ) : ℚ :=
  2 * r * q + f * q ^ 2

private def splitCubeQuotient (f r q : ℚ) : ℚ :=
  3 * r ^ 2 * q + 3 * f * r * q ^ 2 + f ^ 2 * q ^ 3

private def G10R (b c : ℚ) : ℚ :=
  b * TateNFDivision.F5 b c * TateNFDivision.F6 b c ^ 2

private def G10Q (b c : ℚ) : ℚ :=
  c ^ 2 * TateNFDivision.F5 b c

private def G11R (b c : ℚ) : ℚ :=
  -(b * c * TateNFDivision.F6 b c ^ 3)

private def G11Q (b c : ℚ) : ℚ :=
  TateNFDivision.F5 b c ^ 3

private def G12R (b c : ℚ) : ℚ :=
  c * TateNFDivision.F6 b c * TateNFDivision.F5 b c ^ 2 * TateNFDivision.F8 b c

private def G12Q (b c : ℚ) : ℚ :=
  c * TateNFDivision.F6 b c * TateNFDivision.F7 b c

private def G13R (b c : ℚ) : ℚ :=
  b * c * TateNFDivision.F6 b c ^ 3 * TateNFDivision.F8 b c

private def G13Q (b c : ℚ) : ℚ :=
  TateNFDivision.F5 b c * TateNFDivision.F7 b c ^ 2

private def G14Q (b c : ℚ) : ℚ :=
  b * TateNFDivision.F6 b c ^ 2 * TateNFDivision.F9 b c -
    c ^ 2 * TateNFDivision.F5 b c * TateNFDivision.F8 b c ^ 2

private def F15R (b c : ℚ) : ℚ :=
  TateNFDivision.F6 b c * c ^ 3 * TateNFDivision.F8 b c ^ 3

private def F15Q (b c : ℚ) : ℚ :=
  TateNFDivision.F9 b c * TateNFDivision.F7 b c ^ 2

private def G23R (b c : ℚ) : ℚ :=
  b * G10R b c * G12R b c ^ 3 - G13R b c * G11R b c ^ 3

private def G23Q (b c : ℚ) : ℚ :=
  let f := TateNFDivision.F7 b c
  b * splitMulQuotient f (G10R b c) (G10Q b c)
      (G12R b c ^ 3) (splitCubeQuotient f (G12R b c) (G12Q b c)) -
    splitMulQuotient f (G13R b c) (G13Q b c)
      (G11R b c ^ 3) (splitCubeQuotient f (G11R b c) (G11Q b c))

private def G24InnerR (b c : ℚ) : ℚ :=
  G10R b c * G13R b c ^ 2

private def G24InnerQ (b c : ℚ) : ℚ :=
  let f := TateNFDivision.F7 b c
  splitMulQuotient f (G10R b c) (G10Q b c)
      (G13R b c ^ 2) (splitSquareQuotient f (G13R b c) (G13Q b c)) -
    splitMulQuotient f (G11R b c ^ 2)
      (splitSquareQuotient f (G11R b c) (G11Q b c)) 0 (G14Q b c)

private def G24R (b c : ℚ) : ℚ :=
  G12R b c * G24InnerR b c

private def G24Q (b c : ℚ) : ℚ :=
  let f := TateNFDivision.F7 b c
  splitMulQuotient f (G12R b c) (G12Q b c) (G24InnerR b c) (G24InnerQ b c)

private def G25R (b c : ℚ) : ℚ :=
  G11R b c * G13R b c ^ 3

private def G25Q (b c : ℚ) : ℚ :=
  let f := TateNFDivision.F7 b c
  splitMulQuotient f (G11R b c) (G11Q b c)
      (G13R b c ^ 3) (splitCubeQuotient f (G13R b c) (G13Q b c)) -
    b * splitMulQuotient f 0 (G14Q b c)
      (G12R b c ^ 3) (splitCubeQuotient f (G12R b c) (G12Q b c))

private def G26InnerR (b c : ℚ) : ℚ :=
  -(b * G12R b c ^ 2 * F15R b c)

private def G26InnerQ (b c : ℚ) : ℚ :=
  let f := TateNFDivision.F7 b c
  splitMulQuotient f (G11R b c) (G11Q b c) 0
      (splitSquareQuotient f 0 (G14Q b c)) -
    b * splitMulQuotient f (G12R b c ^ 2)
      (splitSquareQuotient f (G12R b c) (G12Q b c)) (F15R b c) (F15Q b c)

private def G26R (b c : ℚ) : ℚ :=
  G13R b c * G26InnerR b c

private def G26Q (b c : ℚ) : ℚ :=
  let f := TateNFDivision.F7 b c
  splitMulQuotient f (G13R b c) (G13Q b c) (G26InnerR b c) (G26InnerQ b c)

private def G49R (b c : ℚ) : ℚ :=
  b * G26R b c * G24R b c ^ 3 - G23R b c * G25R b c ^ 3

private def G49Q (b c : ℚ) : ℚ :=
  let f := TateNFDivision.F7 b c
  b * splitMulQuotient f (G26R b c) (G26Q b c)
      (G24R b c ^ 3) (splitCubeQuotient f (G24R b c) (G24Q b c)) -
    splitMulQuotient f (G23R b c) (G23Q b c)
      (G25R b c ^ 3) (splitCubeQuotient f (G25R b c) (G25Q b c))

private lemma G10_split (b c : ℚ) :
    G10 b c = G10R b c + TateNFDivision.F7 b c * G10Q b c := by
  simp only [G10, G10R, G10Q]
  ring

private lemma G11_split (b c : ℚ) :
    TateOrder25Factor.G11 b c =
      G11R b c + TateNFDivision.F7 b c * G11Q b c := by
  simp only [TateOrder25Factor.G11, G11R, G11Q]
  ring

private lemma G12_split (b c : ℚ) :
    TateOrder25Factor.G12 b c =
      G12R b c + TateNFDivision.F7 b c * G12Q b c := by
  simp only [TateOrder25Factor.G12, G12R, G12Q]
  ring

private lemma G13_split (b c : ℚ) :
    TateOrder25Factor.G13 b c =
      G13R b c + TateNFDivision.F7 b c * G13Q b c := by
  simp only [TateOrder25Factor.G13, G13R, G13Q]
  ring

private lemma G14_split (b c : ℚ) :
    TateOrder25Factor.G14 b c = TateNFDivision.F7 b c * G14Q b c := by
  rfl

private lemma F15_split (b c : ℚ) :
    TateNFDivision.F15 b c =
      F15R b c + TateNFDivision.F7 b c * F15Q b c := by
  simp only [TateNFDivision.F15, TateNFDivision.F6, F15R, F15Q]
  ring

private lemma G23_split (b c : ℚ) :
    G23 b c = G23R b c + TateNFDivision.F7 b c * G23Q b c := by
  simp only [G23]
  rw [G10_split, G12_split, G13_split, G11_split]
  simp only [G23R, G23Q, splitMulQuotient, splitCubeQuotient]
  ring

private lemma G24_split (b c : ℚ) :
    G24 b c = G24R b c + TateNFDivision.F7 b c * G24Q b c := by
  simp only [G24]
  rw [G12_split, G10_split, G13_split, G11_split, G14_split]
  simp only [G24R, G24Q, G24InnerR, G24InnerQ, splitMulQuotient,
    splitSquareQuotient]
  ring

private lemma G25_split (b c : ℚ) :
    G25 b c = G25R b c + TateNFDivision.F7 b c * G25Q b c := by
  simp only [G25]
  rw [G11_split, G13_split, G14_split, G12_split]
  simp only [G25R, G25Q, splitMulQuotient, splitCubeQuotient]
  ring

private lemma G26_split (b c : ℚ) :
    G26 b c = G26R b c + TateNFDivision.F7 b c * G26Q b c := by
  simp only [G26]
  rw [G13_split, G11_split, G14_split, G12_split, F15_split]
  simp only [G26R, G26Q, G26InnerR, G26InnerQ, splitMulQuotient,
    splitSquareQuotient]
  ring

private lemma G49_split (b c : ℚ) :
    G49 b c = G49R b c + TateNFDivision.F7 b c * G49Q b c := by
  simp only [G49]
  rw [G26_split, G24_split, G23_split, G25_split]
  simp only [G49R, G49Q, splitMulQuotient, splitCubeQuotient]
  ring

set_option maxHeartbeats 2000000 in
/-- The only expanded table needed by the straight-line division of `G49` by
`F7`.  It has `129` monomials in `a = b - c` and `c`, rather than the `3526`
monomials of the full primitive factor. -/
private def G49RemainderQuotient (a c : ℚ) : ℚ :=
  32*a ^ 21 - 80*a ^ 20*c ^ 2 + 48*a ^ 20*c + 80*a ^ 19*c ^ 4 -
    128*a ^ 19*c ^ 3 + 32*a ^ 19*c ^ 2 - 4*a ^ 19 - 40*a ^ 18*c ^ 6 +
    120*a ^ 18*c ^ 5 - 104*a ^ 18*c ^ 4 + 8*a ^ 18*c ^ 3 +
    36*a ^ 18*c ^ 2 - 8*a ^ 18*c + 10*a ^ 17*c ^ 8 - 40*a ^ 17*c ^ 7 +
    132*a ^ 17*c ^ 6 - 24*a ^ 17*c ^ 5 - 143*a ^ 17*c ^ 4 +
    70*a ^ 17*c ^ 3 - 5*a ^ 17*c ^ 2 - a ^ 17*c - a ^ 16*c ^ 10 -
    5*a ^ 16*c ^ 9 - 90*a ^ 16*c ^ 8 + 14*a ^ 16*c ^ 7 +
    331*a ^ 16*c ^ 6 - 272*a ^ 16*c ^ 5 + 44*a ^ 16*c ^ 4 +
    14*a ^ 16*c ^ 3 - 3*a ^ 16*c ^ 2 + 6*a ^ 15*c ^ 11 +
    45*a ^ 15*c ^ 10 + 32*a ^ 15*c ^ 9 - 490*a ^ 15*c ^ 8 +
    617*a ^ 15*c ^ 7 - 172*a ^ 15*c ^ 6 - 96*a ^ 15*c ^ 5 +
    44*a ^ 15*c ^ 4 - 3*a ^ 15*c ^ 3 - a ^ 14*c ^ 13 -
    21*a ^ 14*c ^ 12 - 65*a ^ 14*c ^ 11 + 472*a ^ 14*c ^ 10 -
    905*a ^ 14*c ^ 9 + 391*a ^ 14*c ^ 8 + 419*a ^ 14*c ^ 7 -
    300*a ^ 14*c ^ 6 + 43*a ^ 14*c ^ 5 - a ^ 14*c ^ 4 +
    7*a ^ 13*c ^ 14 + 56*a ^ 13*c ^ 13 - 279*a ^ 13*c ^ 12 +
    904*a ^ 13*c ^ 11 - 564*a ^ 13*c ^ 10 - 1280*a ^ 13*c ^ 9 +
    1260*a ^ 13*c ^ 8 - 286*a ^ 13*c ^ 7 + 14*a ^ 13*c ^ 6 -
    a ^ 12*c ^ 16 - 28*a ^ 12*c ^ 15 + 74*a ^ 12*c ^ 14 -
    644*a ^ 12*c ^ 13 + 515*a ^ 12*c ^ 12 + 2866*a ^ 12*c ^ 11 -
    3641*a ^ 12*c ^ 10 + 1170*a ^ 12*c ^ 9 - 91*a ^ 12*c ^ 8 +
    8*a ^ 11*c ^ 17 + 20*a ^ 11*c ^ 16 + 358*a ^ 11*c ^ 15 -
    244*a ^ 11*c ^ 14 - 4824*a ^ 11*c ^ 13 + 7656*a ^ 11*c ^ 12 -
    3289*a ^ 11*c ^ 11 + 364*a ^ 11*c ^ 10 - a ^ 10*c ^ 19 -
    24*a ^ 10*c ^ 18 - 182*a ^ 10*c ^ 17 - 58*a ^ 10*c ^ 16 +
    6186*a ^ 10*c ^ 15 - 12078*a ^ 10*c ^ 14 + 6721*a ^ 10*c ^ 13 -
    1001*a ^ 10*c ^ 12 + 8*a ^ 9*c ^ 20 + 90*a ^ 9*c ^ 19 +
    215*a ^ 9*c ^ 18 - 6069*a ^ 9*c ^ 17 + 14520*a ^ 9*c ^ 16 -
    10296*a ^ 9*c ^ 15 + 2002*a ^ 9*c ^ 14 - a ^ 8*c ^ 22 -
    36*a ^ 8*c ^ 21 - 206*a ^ 8*c ^ 20 + 4534*a ^ 8*c ^ 19 -
    13365*a ^ 8*c ^ 18 + 12012*a ^ 8*c ^ 17 - 3003*a ^ 8*c ^ 16 +
    9*a ^ 7*c ^ 23 + 120*a ^ 7*c ^ 22 - 2540*a ^ 7*c ^ 21 +
    9372*a ^ 7*c ^ 20 - 10725*a ^ 7*c ^ 19 + 3432*a ^ 7*c ^ 18 -
    a ^ 6*c ^ 25 - 45*a ^ 6*c ^ 24 + 1035*a ^ 6*c ^ 23 -
    4928*a ^ 6*c ^ 22 + 7293*a ^ 6*c ^ 21 - 3003*a ^ 6*c ^ 20 +
    10*a ^ 5*c ^ 26 - 290*a ^ 5*c ^ 25 + 1884*a ^ 5*c ^ 24 -
    3718*a ^ 5*c ^ 23 + 2002*a ^ 5*c ^ 22 - a ^ 4*c ^ 28 +
    50*a ^ 4*c ^ 27 - 495*a ^ 4*c ^ 26 + 1378*a ^ 4*c ^ 25 -
    1001*a ^ 4*c ^ 24 - 4*a ^ 3*c ^ 29 + 80*a ^ 3*c ^ 28 -
    351*a ^ 3*c ^ 27 + 364*a ^ 3*c ^ 26 - 6*a ^ 2*c ^ 30 +
    55*a ^ 2*c ^ 29 - 91*a ^ 2*c ^ 28 - 4*a*c ^ 31 + 14*a*c ^ 30 - c ^ 32

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
private lemma G49_remainder_bracket_factor (b c : ℚ) :
    -(TateNFDivision.F5 b c ^ 13 * TateNFDivision.F8 b c ^ 5) +
        b ^ 2 * TateNFDivision.F6 b c ^ 8 *
          (TateNFDivision.F5 b c ^ 7 * TateNFDivision.F8 b c ^ 2 +
            b ^ 2 * c * TateNFDivision.F6 b c ^ 7) =
      TateNFDivision.F7 b c *
        G49RemainderQuotient (TateNFDivision.F5 b c) c := by
  simp only [G49RemainderQuotient, TateNFDivision.F5, TateNFDivision.F6,
    TateNFDivision.F7, TateNFDivision.F8]
  ring

set_option maxHeartbeats 2000000 in
private lemma G49R_factor (b c : ℚ) :
    G49R b c =
      TateNFDivision.F7 b c *
        (b ^ 12 * c ^ 15 * TateNFDivision.F6 b c ^ 33 *
          TateNFDivision.F8 b c ^ 10 *
          G49RemainderQuotient (TateNFDivision.F5 b c) c) := by
  have hshape :
      G49R b c =
        b ^ 12 * c ^ 15 * TateNFDivision.F6 b c ^ 33 *
          TateNFDivision.F8 b c ^ 10 *
          (-(TateNFDivision.F5 b c ^ 13 * TateNFDivision.F8 b c ^ 5) +
            b ^ 2 * TateNFDivision.F6 b c ^ 8 *
              (TateNFDivision.F5 b c ^ 7 * TateNFDivision.F8 b c ^ 2 +
                b ^ 2 * c * TateNFDivision.F6 b c ^ 7)) := by
    simp only [G49R, G26R, G26InnerR, G24R, G24InnerR, G23R, G25R,
      G10R, G11R, G12R, G13R, F15R]
    ring
  rw [hshape, G49_remainder_bracket_factor]
  ring

/-- The primitive order-`49` factor, represented by a straight-line program.
Polynomial normalization gives a degree-`157`, `3526`-monomial irreducible
polynomial, but no such expansion is materialized here. -/
def H49 (b c : ℚ) : ℚ :=
  -(G49Q b c +
    b ^ 12 * c ^ 15 * TateNFDivision.F6 b c ^ 33 *
      TateNFDivision.F8 b c ^ 10 *
      G49RemainderQuotient (TateNFDivision.F5 b c) c)

/-- Exact separation of the proper order-seven factor from `G49`. -/
theorem G49_eq_neg_F7_mul_H49 (b c : ℚ) :
    G49 b c = -(TateNFDivision.F7 b c * H49 b c) := by
  rw [G49_split, G49R_factor]
  simp only [H49]
  ring

theorem H49_eq_zero_of_G49_eq_zero
    {b c : ℚ} (hF7 : TateNFDivision.F7 b c ≠ 0) (hG49 : G49 b c = 0) :
    H49 b c = 0 := by
  rw [G49_eq_neg_F7_mul_H49] at hG49
  exact (mul_eq_zero.mp (neg_eq_zero.mp hG49)).resolve_left hF7

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
## Remaining arithmetic theorems

The theorem `G49_eq_neg_F7_mul_H49` above removes the proper order-seven
factor without expanding the degree-`157` primitive factor.  Thus `hF7` and
`hG49` reduce the source equation to `H49 b c = 0`.

The remaining Diophantine argument is split at the standard modular-curve
boundary.  This makes the two certificates that still have to be generated
and checked explicit:

1. the diamond quotient from the open order-`49` Tate locus to the
   noncuspidal affine locus of `X₀(49)`;
2. the rank-zero calculation for the minimal model of `X₀(49)`.

The first certificate is now stated on the primitive equation `H49 = 0`, so it
cannot discharge the goal by returning to the already-removed `F7` component.
The elementary final step from the rank-zero statement to the affine-point
classification is proved below.
-/

/-- The affine minimal model of `X₀(49)` (Cremona `49a1`). -/
def X049Equation (x y : ℚ) : Prop :=
  y ^ 2 + x * y = x ^ 3 - x ^ 2 - 2 * x - 1

/-- `SORRY[N49-PRIMITIVE-QUOTIENT]`: a generated certificate for the diamond
quotient `X₁(49) → X₀(49)` on the primitive Tate chart.

The certificate must give explicit rational functions `x(b,c), y(b,c)`, prove
their denominators nonzero from `hb`, `hdisc`, and `hF7`, verify
`X049Equation x y` from `hH49`, and prove that the image is not the affine cusp
`(2,-1)`.  Here `H49` is the explicit straight-line primitive factor above;
the proper-order-seven component has already been removed.  The point at
infinity is excluded by producing affine coordinates. -/
theorem primitive_order49_to_noncuspidal_X049
    {b c : ℚ}
    (hb : b ≠ 0)
    (hdisc : tateDiscriminant49 b c ≠ 0)
    (hF7 : F7 b c ≠ 0)
    (hH49 : H49 b c = 0) :
    ∃ x y : ℚ, X049Equation x y ∧ ¬ (x = 2 ∧ y = -1) := by
  sorry

/-- The compact order-`49` equation reduces to the primitive quotient
certificate after the proved removal of its proper order-seven factor. -/
theorem pure_order49_to_noncuspidal_X049
    {b c : ℚ}
    (hb : b ≠ 0)
    (hdisc : tateDiscriminant49 b c ≠ 0)
    (hF7 : F7 b c ≠ 0)
    (hG49 : G49 b c = 0) :
    ∃ x y : ℚ, X049Equation x y ∧ ¬ (x = 2 ∧ y = -1) := by
  apply primitive_order49_to_noncuspidal_X049 hb hdisc hF7
  exact H49_eq_zero_of_G49_eq_zero hF7 hG49

/-- `SORRY[N49-RANK-ZERO]`: the Mordell--Weil calculation for `49a1`.

For a concrete `2`-isogeny descent, set `X = 4*(x-2)` and
`Y = 8*y+4*x`.  The resulting model and its `2`-isogenous curve are

* `Y² = X³ + 21*X² + 112*X`;
* `Y² = X³ - 42*X² - 7*X`.

The two square-class images are respectively `{1, 7}` and `{1, -7}`.
Their other candidate classes are excluded by real-sign, parity, and
`7`-adic arguments.  This proves rank zero; good reduction at `2` and `3`
then bounds the torsion order by `gcd(2,4)=2`.  In the original affine
coordinates the conclusion that every rational point is two-torsion is
exactly `2*y+x=0`.
-/
theorem X049_affine_is_two_torsion
    {x y : ℚ} (hcurve : X049Equation x y) :
    2 * y + x = 0 := by
  exact RationalPointsX049.affine_is_two_torsion hcurve

/-- The only affine rational point on `X₀(49)` is its non-infinite cusp. -/
theorem X049_affine_rational_point
    {x y : ℚ} (hcurve : X049Equation x y) :
    x = 2 ∧ y = -1 := by
  have htwo := X049_affine_is_two_torsion hcurve
  have hy : y = -x / 2 := by linarith
  rw [hy] at hcurve
  have hfactor : (x - 2) * (4 * x ^ 2 + 5 * x + 2) = 0 := by
    dsimp [X049Equation] at hcurve
    nlinarith
  rcases mul_eq_zero.mp hfactor with hx | hquad
  · constructor <;> nlinarith
  · have hsquare : (8 * x + 5) ^ 2 + 7 = 0 := by nlinarith
    nlinarith [sq_nonneg (8 * x + 5)]

/-- The explicit order-49 polynomial has no rational zero off the singular and
proper-order-seven loci, modulo the two isolated certificates above. -/
theorem no_pure_order49_polynomial_solution :
    ¬ PureOrder49PolynomialObstruction := by
  rintro ⟨b, c, hb, hdisc, hF7, hG49⟩
  obtain ⟨x, y, hcurve, hnoncusp⟩ :=
    pure_order49_to_noncuspidal_X049 hb hdisc hF7 hG49
  exact hnoncusp (X049_affine_rational_point hcurve)

/-- Polynomial-form replacement for the raw Tate obstruction axiom. -/
theorem no_raw_order49_tate_obstruction :
    ¬ RawOrder49TateObstruction := by
  rw [raw_order49_obstruction_iff_pure]
  exact no_pure_order49_polynomial_solution

end

end MazurProof.CyclicExclusion49Polynomial
