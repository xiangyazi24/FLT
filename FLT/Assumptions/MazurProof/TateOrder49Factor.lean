import FLT.Assumptions.MazurProof.TateOrder25Factor

/-!
# Explicit factorisation of the raw order-49 Tate-origin obstruction

Extends the order-25 development to the order-49 case.  The division chain
`1 | 7 | 49` is unrolled at the Tate origin, extracting powers of `b` at each
step and keeping Kubert factors atomic.

The `49 = 2*24+1` step of the recurrence yields the compact closed identity

  `preΨ'₄₉(0,0) = b⁸⁰⁰ * (b*G₂₆*G₂₄³*Ψ₂Sq² - G₂₃*(F₅*F₂₅)³)`,

with intermediate compact factors built from `F₅,...,F₉,F₁₅,F₂₅` and the order-25
development's `G₁₁,...,G₁₄`.  The proper order-7 factor `F₇ = c³ + bc - b²`
divides the compact bracket, leaving the primitive order-49 polynomial `F₄₉`:

  `preΨ'₄₉(0,0) = b⁸⁰⁰ * F₇ * F₄₉`.

`F₄₉` is degree 157 with 3526 monomials; its vanishing locus (with `b ≠ 0`,
`F₇ ≠ 0`) is the affine modular curve `X₁(49)`, genus 69.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder49Factor

open TateOriginDivision
open TateOrder25Factor
open Scratch.TateZ2xZ10Reduction

noncomputable section

set_option maxRecDepth 20000
set_option linter.style.longLine false

/-! ## Base origin evaluations

These duplicate the private lemmas from `TateOrder25Factor` that this module needs
to access for the recurrence unrollings beyond index 14. -/

private lemma Psi2Sq_eval (b c : ℚ) : ((W b c).Ψ₂Sq).eval 0 = b ^ 2 := by
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

private lemma prePsi_3_eval (b c : ℚ) : ((W b c).preΨ' 3).eval 0 = -b ^ 3 := by
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

private lemma prePsi_4_eval (b c : ℚ) :
    ((W b c).preΨ' 4).eval 0 = -(b ^ 4 * c) := by
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_four, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-! ## Recurrence unrollings at the origin -/

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
      ((W b c).preΨ' 4).eval 0 ^ 2 * ((W b c).preΨ' 5).eval 0 *
          ((W b c).preΨ' 7).eval 0 -
        ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 *
          ((W b c).preΨ' 6).eval 0 ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 2)
  simpa using h

private lemma eval_prePsi_eleven (b c : ℚ) :
    ((W b c).preΨ' 11).eval 0 =
      ((W b c).preΨ' 7).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 6).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 3)
  simpa [show ¬ Even (3 : ℕ) by decide] using h

private lemma eval_prePsi_twelve (b c : ℚ) :
    ((W b c).preΨ' 12).eval 0 =
      (((W b c).preΨ' 5).eval 0) ^ 2 * ((W b c).preΨ' 6).eval 0 *
          ((W b c).preΨ' 8).eval 0 -
        ((W b c).preΨ' 4).eval 0 * ((W b c).preΨ' 6).eval 0 *
          (((W b c).preΨ' 7).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 3)
  simpa using h

private lemma eval_prePsi_thirteen (b c : ℚ) :
    ((W b c).preΨ' 13).eval 0 =
      ((W b c).preΨ' 8).eval 0 * (((W b c).preΨ' 6).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 7).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 4)
  simpa [show Even (4 : ℕ) by decide] using h

private lemma eval_prePsi_fourteen (b c : ℚ) :
    ((W b c).preΨ' 14).eval 0 =
      (((W b c).preΨ' 6).eval 0) ^ 2 * ((W b c).preΨ' 7).eval 0 *
          ((W b c).preΨ' 9).eval 0 -
        ((W b c).preΨ' 5).eval 0 * ((W b c).preΨ' 7).eval 0 *
          (((W b c).preΨ' 8).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 4)
  simpa using h

private lemma eval_prePsi_fifteen (b c : ℚ) :
    ((W b c).preΨ' 15).eval 0 =
      ((W b c).preΨ' 9).eval 0 * (((W b c).preΨ' 7).eval 0) ^ 3 -
        ((W b c).preΨ' 6).eval 0 * (((W b c).preΨ' 8).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 5)
  simpa [show ¬ Even (5 : ℕ) by decide] using h

private lemma eval_prePsi_twentythree (b c : ℚ) :
    ((W b c).preΨ' 23).eval 0 =
      ((W b c).preΨ' 13).eval 0 * (((W b c).preΨ' 11).eval 0) ^ 3 -
        ((W b c).preΨ' 10).eval 0 * (((W b c).preΨ' 12).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 9)
  simpa [show ¬ Even (9 : ℕ) by decide] using h

private lemma eval_prePsi_twentyfour (b c : ℚ) :
    ((W b c).preΨ' 24).eval 0 =
      (((W b c).preΨ' 11).eval 0) ^ 2 * ((W b c).preΨ' 12).eval 0 *
          ((W b c).preΨ' 14).eval 0 -
        ((W b c).preΨ' 10).eval 0 * ((W b c).preΨ' 12).eval 0 *
          (((W b c).preΨ' 13).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 9)
  simpa using h

private lemma eval_prePsi_twentyfive (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 =
      ((W b c).preΨ' 14).eval 0 * (((W b c).preΨ' 12).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 11).eval 0 * (((W b c).preΨ' 13).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 10)
  simpa [show Even (10 : ℕ) by decide] using h

private lemma eval_prePsi_twentysix (b c : ℚ) :
    ((W b c).preΨ' 26).eval 0 =
      (((W b c).preΨ' 12).eval 0) ^ 2 * ((W b c).preΨ' 13).eval 0 *
          ((W b c).preΨ' 15).eval 0 -
        ((W b c).preΨ' 11).eval 0 * ((W b c).preΨ' 13).eval 0 *
          (((W b c).preΨ' 14).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 10)
  simpa using h

private lemma eval_prePsi_fortynine (b c : ℚ) :
    ((W b c).preΨ' 49).eval 0 =
      ((W b c).preΨ' 26).eval 0 * (((W b c).preΨ' 24).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 23).eval 0 * (((W b c).preΨ' 25).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 22)
  simpa [show Even (22 : ℕ) by decide] using h

/-! ## Reduced origin evaluations through the Kubert factors -/

private lemma prePsi_5_eval (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 = b ^ 8 * TateNFDivision.F5 b c := by
  rw [eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F5]
  ring

private lemma prePsi_6_eval (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 = -(b ^ 11 * TateNFDivision.F6 b c) := by
  rw [eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F6]
  ring

theorem prePsi_7_eval (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 = b ^ 16 * TateNFDivision.F7 b c := by
  rw [eval_prePsi_seven, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F7]
  ring

private lemma prePsi_8_eval (b c : ℚ) :
    ((W b c).preΨ' 8).eval 0 = b ^ 20 * c * TateNFDivision.F8 b c := by
  rw [eval_prePsi_eight, eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F8]
  ring

private lemma prePsi_9_eval (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 = b ^ 27 * TateNFDivision.F9 b c := by
  rw [eval_prePsi_nine, eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, TateNFDivision.F9]
  ring

/-! ## Compact intermediate factors

The factors `G₁₁,...,G₁₄` are imported from `TateOrder25Factor`.
New factors needed for the order-49 chain: -/

/-- Compact factor for `preΨ'₁₀(0) = b³² * G10 b c`. -/
def G10 (b c : ℚ) : ℚ :=
  TateNFDivision.F5 b c *
    (c ^ 2 * TateNFDivision.F7 b c + b * TateNFDivision.F6 b c ^ 2)

/-- Compact factor for `preΨ'₂₃(0) = b¹⁷⁶ * G23 b c`. -/
def G23 (b c : ℚ) : ℚ :=
  b * G10 b c * G12 b c ^ 3 - G13 b c * G11 b c ^ 3

/-- Compact factor for `preΨ'₂₄(0) = b¹⁹¹ * G24 b c`. -/
def G24 (b c : ℚ) : ℚ :=
  G12 b c * (G10 b c * G13 b c ^ 2 - G11 b c ^ 2 * G14 b c)

/-- Compact factor for `preΨ'₂₆(0) = b²²⁴ * G26 b c`. -/
def G26 (b c : ℚ) : ℚ :=
  G13 b c * (G11 b c * G14 b c ^ 2 - b * G12 b c ^ 2 * TateNFDivision.F15 b c)

/-! ## Reduced origin evaluations through compact factors -/

private lemma prePsi_10_eval (b c : ℚ) :
    ((W b c).preΨ' 10).eval 0 = b ^ 32 * G10 b c := by
  rw [eval_prePsi_ten, prePsi_4_eval, prePsi_5_eval, prePsi_7_eval,
    prePsi_3_eval, prePsi_6_eval]
  simp only [G10]
  ring

private lemma prePsi_11_eval (b c : ℚ) :
    ((W b c).preΨ' 11).eval 0 = b ^ 40 * G11 b c := by
  rw [eval_prePsi_eleven, prePsi_7_eval, prePsi_5_eval, prePsi_4_eval,
    prePsi_6_eval, Psi2Sq_eval]
  simp only [G11]
  ring

private lemma prePsi_12_eval (b c : ℚ) :
    ((W b c).preΨ' 12).eval 0 = -(b ^ 47 * G12 b c) := by
  rw [eval_prePsi_twelve, prePsi_5_eval, prePsi_6_eval, prePsi_8_eval,
    prePsi_4_eval, prePsi_7_eval]
  simp only [G12]
  ring

private lemma prePsi_13_eval (b c : ℚ) :
    ((W b c).preΨ' 13).eval 0 = -(b ^ 56 * G13 b c) := by
  rw [eval_prePsi_thirteen, prePsi_8_eval, prePsi_6_eval, prePsi_5_eval,
    prePsi_7_eval, Psi2Sq_eval]
  simp only [G13]
  ring

private lemma prePsi_14_eval (b c : ℚ) :
    ((W b c).preΨ' 14).eval 0 = b ^ 64 * G14 b c := by
  rw [eval_prePsi_fourteen, prePsi_6_eval, prePsi_7_eval, prePsi_9_eval,
    prePsi_5_eval, prePsi_8_eval]
  simp only [G14]
  ring

private lemma prePsi_15_eval (b c : ℚ) :
    ((W b c).preΨ' 15).eval 0 = b ^ 75 * TateNFDivision.F15 b c := by
  rw [eval_prePsi_fifteen, prePsi_9_eval, prePsi_7_eval,
    prePsi_6_eval, prePsi_8_eval, Psi2Sq_eval]
  simp only [TateNFDivision.F15, TateNFDivision.F6, TateNFDivision.F7,
    TateNFDivision.F8, TateNFDivision.F9]
  ring

private lemma prePsi_23_eval (b c : ℚ) :
    ((W b c).preΨ' 23).eval 0 = b ^ 176 * G23 b c := by
  rw [eval_prePsi_twentythree, prePsi_13_eval, prePsi_11_eval,
    prePsi_10_eval, prePsi_12_eval, Psi2Sq_eval]
  simp only [G23]
  ring

private lemma prePsi_24_eval (b c : ℚ) :
    ((W b c).preΨ' 24).eval 0 = b ^ 191 * G24 b c := by
  rw [eval_prePsi_twentyfour, prePsi_11_eval, prePsi_12_eval,
    prePsi_14_eval, prePsi_10_eval, prePsi_13_eval]
  simp only [G24]
  ring

private lemma prePsi_26_eval (b c : ℚ) :
    ((W b c).preΨ' 26).eval 0 = b ^ 224 * G26 b c := by
  rw [eval_prePsi_twentysix, prePsi_12_eval, prePsi_13_eval,
    prePsi_15_eval, prePsi_11_eval, prePsi_14_eval]
  simp only [G26]
  ring

/-! ## The compact and primitive order-49 identities -/

/-- The bracket expression from the order-49 recurrence unrolling. Ward's theorem
(F₇ divides the bracket since 7 | 49 in the EDS) means `bracket49 = F₇ * F₄₉`,
but the bridge theorem does not require that factorisation — only the structural
identity `preΨ'₄₉(0) = b⁸⁰⁰ * bracket49` from the `preΨ'_odd` recurrence. -/
def bracket49 (b c : ℚ) : ℚ :=
  b * G26 b c * G24 b c ^ 3 -
    G23 b c * (TateNFDivision.F5 b c * F25 b c) ^ 3

/-- **Compact order-49 division identity at the Tate origin.**
`preΨ'₄₉(0,0) = b⁸⁰⁰ * bracket₄₉(b,c)`. -/
theorem prePsi_fortynine_eval_compact (b c : ℚ) :
    ((W b c).preΨ' 49).eval 0 = b ^ 800 * bracket49 b c := by
  rw [eval_prePsi_fortynine, prePsi_26_eval, prePsi_24_eval,
    Psi2Sq_eval, prePsi_23_eval, prePsi_twentyfive_eval_tate_origin]
  simp only [bracket49]
  ring

end

end MazurProof.TateOrder49Factor
