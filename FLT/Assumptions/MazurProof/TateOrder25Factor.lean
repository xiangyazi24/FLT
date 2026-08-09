import FLT.Assumptions.MazurProof.TateOriginDivision

/-!
# Explicit factorisation of the raw order-25 Tate-origin obstruction

`TateOriginDivision` reduces a rational point of order `25` on a Tate normal form
`E(b,c)` to the raw division-polynomial system defined in this module:

* `preΨ'₂₅(0,0) = 0`,
* `preΨ'₅(0,0) ≠ 0`   (excluding the proper order-`5` divisor),
* `b ≠ 0`             (nonsingular Tate normal form).

`25 = 5·5`, so the divisor chain is `1 ∣ 5 ∣ 25`.  This file unrolls Mathlib's
elliptic-divisibility recurrence at the Tate origin `X = 0`, extracting the power
of `b` at every step and keeping the low Kubert factors `F₅,…,F₉` of
`TateNFDivision` **atomic**, exactly as in the sibling order-`27` development.
The `25 = 2·12+1` step of the recurrence gives the compact closed identity

`preΨ'₂₅(0,0) = b²⁰⁸ · (G₁₁·G₁₃³ − b·G₁₄·G₁₂³)`,

with the intermediate factors written through `F₅,…,F₉`:

* `G₁₁ = F₇·F₅³ − b·c·F₆³`             (`= F₁₁`),
* `G₁₂ = c·F₆·(F₅²·F₈ + F₇²)`,
* `G₁₃ = F₅·F₇³ + b·c·F₆³·F₈`          (`= F₁₃`),
* `G₁₄ = F₇·(b·F₆²·F₉ − c²·F₅·F₈²)`.

The proper order-`5` factor `F₅ = b - c` — whose nonvanishing is exactly the
hypothesis `preΨ'₅(0,0) ≠ 0`, since `preΨ'₅(0,0) = b⁸·F₅` — divides the compact
bracket, and dividing it out leaves the **primitive** order-`25` division
polynomial `F₂₅` (degree `40`, `234` monomials, irreducible over `ℚ`):

`G₁₁·G₁₃³ − b·G₁₄·G₁₂³ = F₅ · F₂₅`,   hence   `preΨ'₂₅(0,0) = b²⁰⁸ · F₅ · F₂₅`.

The main result `raw_order25_obstruction_iff` shows the raw system is
**equivalent** to the single explicit polynomial equation `F₂₅(b,c) = 0` on the
locus `b ≠ 0`, `F₅(b,c) ≠ 0` — an affine rational point on the modular curve
`X₁(25)`.  No power of `b` above the compact factors is ever materialised.
No rank or rational-point classification is asserted here: this module is the
lower-level algebraic input for a separate arithmetic exclusion of the displayed
`X₁(25)` locus.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder25Factor

open TateOriginDivision
open Scratch.TateZ2xZ10Reduction

noncomputable section

set_option maxRecDepth 20000
set_option linter.style.longLine false

/-! ## The exact-order raw Tate obstruction -/

/-- The exact raw Tate-division system left by a rational point of order 25.
The nonvanishing order-five evaluation removes the only nontrivial proper
divisor of 25. -/
def RawOrder25TateObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      b ≠ 0 ∧
        ((W b c).preΨ' 25).eval 0 = 0 ∧
        ((W b c).preΨ' 5).eval 0 ≠ 0

/-- Exact order 25 produces the raw Tate-division obstruction. -/
theorem order25_to_raw_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) :
    RawOrder25TateObstruction := by
  obtain ⟨b, c, hEll, hord, hb, h25eval⟩ :=
    exists_tate_parameters_of_has_rational_point_of_odd_order
      E (n := 25) (by norm_num) (by decide) h25
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have h5eval : ((W b c).preΨ' 5).eval 0 ≠ 0 :=
    prePsi_eval_ne_zero_of_lt_addOrder b c
      (n := 25) (m := 5) (by norm_num) (by norm_num) (by norm_num)
      (by decide) hord
  exact ⟨b, c, inferInstance, hb, h25eval, h5eval⟩

/-! ## Recurrence unrollings at the origin

The origin evaluations of the auxiliary polynomials `preΨ'ₖ` follow Mathlib's
elliptic-divisibility recurrence, read off exactly as in the order-`11`,
order-`18` and order-`27` developments.  Each step extracts a power of `b`,
keeping the compact factor symbolic. -/

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

private lemma eval_prePsi_twentyfive (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 =
      ((W b c).preΨ' 14).eval 0 * (((W b c).preΨ' 12).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 11).eval 0 * (((W b c).preΨ' 13).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 10)
  simpa [show Even (10 : ℕ) by decide] using h

/-! ## Base origin evaluations (fully expanded, low degree) -/

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

/-! ## Reduced origin evaluations through the Kubert factors `F₅,…,F₉` -/

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

private lemma prePsi_7_eval (b c : ℚ) :
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

/-! ## Compact intermediate factors (written through `F₅,…,F₉`) -/

/-- Compact factor with `preΨ'₁₁(0) = b⁴⁰ · G11 b c`; agrees with `F11`. -/
def G11 (b c : ℚ) : ℚ :=
  TateNFDivision.F7 b c * TateNFDivision.F5 b c ^ 3 -
    b * c * TateNFDivision.F6 b c ^ 3

/-- Compact factor with `preΨ'₁₂(0) = -(b⁴⁷ · G12 b c)`. -/
def G12 (b c : ℚ) : ℚ :=
  c * TateNFDivision.F6 b c *
    (TateNFDivision.F5 b c ^ 2 * TateNFDivision.F8 b c + TateNFDivision.F7 b c ^ 2)

/-- Compact factor with `preΨ'₁₃(0) = -(b⁵⁶ · G13 b c)`; agrees with `F13`. -/
def G13 (b c : ℚ) : ℚ :=
  TateNFDivision.F5 b c * TateNFDivision.F7 b c ^ 3 +
    b * c * TateNFDivision.F6 b c ^ 3 * TateNFDivision.F8 b c

/-- Compact factor with `preΨ'₁₄(0) = b⁶⁴ · G14 b c`. -/
def G14 (b c : ℚ) : ℚ :=
  TateNFDivision.F7 b c *
    (b * TateNFDivision.F6 b c ^ 2 * TateNFDivision.F9 b c -
      c ^ 2 * TateNFDivision.F5 b c * TateNFDivision.F8 b c ^ 2)

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

/-- Public order-fourteen origin evaluation used to certify that the tangent
denominator at `7P` is nonzero on the exact order-25 locus. -/
theorem prePsi_fourteen_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 14).eval 0 = b ^ 64 * G14 b c :=
  prePsi_14_eval b c

/-! ## The compact and primitive order-25 identities -/

/-- **Compact order-25 division identity at the Tate origin.**  The `25 = 2·12+1`
recurrence step, with every power of `b` extracted and the Kubert factors kept
atomic:
`preΨ'₂₅(0,0) = b²⁰⁸ · (G₁₁·G₁₃³ − b·G₁₄·G₁₂³)`. -/
theorem prePsi_twentyfive_eval_compact (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 =
      b ^ 208 * (G11 b c * G13 b c ^ 3 - b * G14 b c * G12 b c ^ 3) := by
  rw [eval_prePsi_twentyfive, prePsi_14_eval, prePsi_12_eval,
    prePsi_11_eval, prePsi_13_eval, Psi2Sq_eval]
  ring

set_option maxHeartbeats 2000000 in
-- `F₂₅` is an irreducible degree-`40`, `234`-monomial polynomial; elaborating this
-- large literal needs a heartbeat limit above the default.
/-- The primitive order-25 division polynomial `F₂₅`: the compact bracket with the
proper order-`5` factor `F₅ = b - c` divided out.  Degree `40`, `234` monomials,
irreducible over `ℚ`; its vanishing locus is the affine modular curve `X₁(25)`. -/
def F25 (b c : ℚ) : ℚ :=
  b^6*c^34 + b^5*c^35 + b^4*c^36 + b^3*c^37 + b^2*c^38 - 18*b^7*c^32 + 3*b^6*c^33 + 3*b^5*c^34 + 3*b^4*c^35 + 3*b^3*c^36 + 6*b^2*c^37 + 151*b^8*c^30 - 212*b^7*c^31 + 19*b^6*c^32 + 19*b^5*c^33 + 19*b^4*c^34 - 17*b^3*c^35 + 21*b^2*c^36 - 770*b^9*c^28 + 2065*b^8*c^29 - 1624*b^7*c^30 + 147*b^6*c^31 + 147*b^5*c^32 + 112*b^4*c^33 - 133*b^3*c^34 + 56*b^2*c^35 + 2655*b^10*c^26 - 10530*b^9*c^27 + 15405*b^8*c^28 - 9375*b^7*c^29 + 1251*b^6*c^30 + 516*b^5*c^31 + 411*b^4*c^32 - 459*b^3*c^33 + 126*b^2*c^34 - b^14*c^21 - b^13*c^22 - b^12*c^23 - 6503*b^11*c^24 + 34222*b^10*c^25 - 72725*b^9*c^26 + 78125*b^8*c^27 - 41875*b^7*c^28 + 7754*b^6*c^29 + 929*b^5*c^30 + 851*b^4*c^31 - 1024*b^3*c^32 + 251*b^2*c^33 - b*c^34 - c^35 + 17*b^15*c^19 - 28*b^14*c^20 - 28*b^13*c^21 + 11638*b^12*c^22 - 75959*b^11*c^23 + 211735*b^10*c^24 - 323700*b^9*c^25 + 289875*b^8*c^26 - 147447*b^7*c^27 + 34987*b^6*c^28 - 752*b^5*c^29 + 703*b^4*c^30 - 1447*b^3*c^31 + 434*b^2*c^32 - 28*b*c^33 - 123*b^16*c^17 + 516*b^15*c^18 - 519*b^14*c^19 - 15891*b^13*c^20 + 120525*b^12*c^21 - 408288*b^11*c^22 + 801705*b^10*c^23 - 992925*b^9*c^24 + 793809*b^8*c^25 - 400098*b^7*c^26 + 115557*b^6*c^27 - 13971*b^5*c^28 + 69*b^4*c^29 - 618*b^3*c^30 + 273*b^2*c^31 - 21*b*c^32 + 494*b^17*c^15 - 3262*b^16*c^16 + 8168*b^15*c^17 + 7438*b^14*c^18 - 140192*b^13*c^19 + 563119*b^12*c^20 - 1310235*b^11*c^21 + 2011320*b^10*c^22 - 2123925*b^9*c^23 + 1558300*b^8*c^24 - 785054*b^7*c^25 + 262762*b^6*c^26 - 55738*b^5*c^27 + 7787*b^4*c^28 - 1183*b^3*c^29 + 216*b^2*c^30 - 15*b*c^31 - 1205*b^18*c^13 + 10660*b^17*c^14 - 40426*b^16*c^15 + 71764*b^15*c^16 + 23389*b^14*c^17 - 500071*b^13*c^18 + 1517609*b^12*c^19 - 2767285*b^11*c^20 + 3497590*b^10*c^21 - 3189100*b^9*c^22 + 2115200*b^8*c^23 - 1011950*b^7*c^24 + 342221*b^6*c^25 - 79879*b^5*c^26 + 12961*b^4*c^27 - 1649*b^3*c^28 + 181*b^2*c^29 - 10*b*c^30 + 1836*b^19*c^11 - 20019*b^18*c^12 + 98421*b^17*c^13 - 279858*b^16*c^14 + 468651*b^15*c^15 - 305592*b^14*c^16 - 633822*b^13*c^17 + 2293518*b^12*c^18 - 3867390*b^11*c^19 + 4378848*b^10*c^20 - 3597549*b^9*c^21 + 2191026*b^8*c^22 - 988449*b^7*c^23 + 326004*b^6*c^24 - 77124*b^5*c^25 + 12930*b^4*c^26 - 1560*b^3*c^27 + 135*b^2*c^28 - 6*b*c^29 - 1732*b^20*c^9 + 22103*b^19*c^10 - 130372*b^18*c^11 + 468205*b^17*c^12 - 1129769*b^16*c^13 + 1886674*b^15*c^14 - 2098031*b^14*c^15 + 1188769*b^13*c^16 + 632668*b^12*c^17 - 2340965*b^11*c^18 + 2977348*b^10*c^19 - 2466272*b^9*c^20 + 1471103*b^8*c^21 - 648076*b^7*c^22 + 210737*b^6*c^23 - 49915*b^5*c^24 + 8450*b^4*c^25 - 1000*b^3*c^26 + 78*b^2*c^27 - 3*b*c^28 + 968*b^21*c^7 - 13936*b^20*c^8 + 93894*b^19*c^9 - 392460*b^18*c^10 + 1136487*b^17*c^11 - 2408509*b^16*c^12 + 3838627*b^15*c^13 - 4635863*b^14*c^14 + 4178994*b^13*c^15 - 2643497*b^12*c^16 + 905113*b^11*c^17 + 220429*b^10*c^18 - 551706*b^9*c^19 + 419817*b^8*c^20 - 203267*b^7*c^21 + 69179*b^6*c^22 - 16870*b^5*c^23 + 2925*b^4*c^24 - 351*b^3*c^25 + 27*b^2*c^26 - b*c^27 - 294*b^22*c^5 + 4662*b^21*c^6 - 34848*b^20*c^7 + 163107*b^19*c^8 - 535473*b^18*c^9 + 1308684*b^17*c^10 - 2465814*b^16*c^11 + 3658941*b^15*c^12 - 4329039*b^14*c^13 + 4107246*b^13*c^14 - 3124836*b^12*c^15 + 1895517*b^11*c^16 - 905463*b^10*c^17 + 333432*b^9*c^18 - 91398*b^8*c^19 + 17571*b^7*c^20 - 2115*b^6*c^21 + 120*b^5*c^22 + 35*b^23*c^3 - 595*b^22*c^4 + 4781*b^21*c^5 - 24129*b^20*c^6 + 85716*b^19*c^7 - 227619*b^18*c^8 + 468286*b^17*c^9 - 763217*b^16*c^10 + 998998*b^15*c^11 - 1058057*b^14*c^12 + 908908*b^13*c^13 - 631787*b^12*c^14 + 352716*b^11*c^15 - 156009*b^10*c^16 + 53466*b^9*c^17 - 13699*b^8*c^18 + 2471*b^7*c^19 - 280*b^6*c^20 + 15*b^5*c^21 + b^25 - 20*b^24*c + 190*b^23*c^2 - 1140*b^22*c^3 + 4845*b^21*c^4 - 15504*b^20*c^5 + 38760*b^19*c^6 - 77520*b^18*c^7 + 125970*b^17*c^8 - 167960*b^16*c^9 + 184756*b^15*c^10 - 167960*b^14*c^11 + 125970*b^13*c^12 - 77520*b^12*c^13 + 38760*b^11*c^14 - 15504*b^10*c^15 + 4845*b^9*c^16 - 1140*b^8*c^17 + 190*b^7*c^18 - 20*b^6*c^19 + b^5*c^20

set_option maxHeartbeats 2000000 in
-- Unfolding `F₂₅` (234 monomials) and `ring`-normalising this degree-`40` identity
-- exceeds the default heartbeat budget.
/-- **Separation of the order-`5` factor.**  `F₅ = b - c` divides the compact
order-25 bracket, and the quotient is the primitive polynomial `F₂₅`:
`G₁₁·G₁₃³ − b·G₁₄·G₁₂³ = F₅ · F₂₅`. -/
theorem compact_bracket_factor (b c : ℚ) :
    G11 b c * G13 b c ^ 3 - b * G14 b c * G12 b c ^ 3 =
      TateNFDivision.F5 b c * F25 b c := by
  simp only [G11, G12, G13, G14, F25, TateNFDivision.F5, TateNFDivision.F6,
    TateNFDivision.F7, TateNFDivision.F8, TateNFDivision.F9]
  ring

/-- **Order-25 division-polynomial identity at the Tate origin, primitive form.**
`preΨ'₂₅(0,0) = b²⁰⁸ · F₅ · F₂₅`, i.e. the order-`5` factor `F₅` and the unit
power `b²⁰⁸` are fully separated from the primitive `F₂₅`. -/
theorem prePsi_twentyfive_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 = b ^ 208 * TateNFDivision.F5 b c * F25 b c := by
  rw [prePsi_twentyfive_eval_compact, compact_bracket_factor]
  ring

/-- **Order-5 division-polynomial identity at the Tate origin.**
`preΨ'₅(0,0) = b⁸ · F₅`; its nonvanishing is `b ≠ 0 ∧ F₅ b c ≠ 0`. -/
theorem prePsi_five_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 = b ^ 8 * TateNFDivision.F5 b c :=
  prePsi_5_eval b c

/-- The proper order-`5` factor is literally separated: `preΨ'₂₅(0,0)` is
`preΨ'₅(0,0)` times an explicit cofactor. -/
theorem prePsi_twentyfive_eq_prePsi_five_mul (b c : ℚ) :
    ((W b c).preΨ' 25).eval 0 =
      ((W b c).preΨ' 5).eval 0 * (b ^ 200 * F25 b c) := by
  rw [prePsi_twentyfive_eval_tate_origin, prePsi_five_eval_tate_origin]
  ring

/-! ## Reduction of the raw obstruction to the single equation `F₂₅ = 0` -/

/-- The explicit primitive order-25 obstruction: a rational point on the affine
modular curve `X₁(25)`, off the excluded order-`5` locus `F₅ = 0` (i.e. `b = c`)
and the singular locus `b = 0`. -/
def ExplicitOrder25Obstruction : Prop :=
  ∃ b c : ℚ, ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
    b ≠ 0 ∧ TateNFDivision.F5 b c ≠ 0 ∧ F25 b c = 0

/-- **Main theorem.**  The raw order-25 Tate-division system is equivalent to the
single explicit polynomial equation `F₂₅(b,c) = 0` on the locus `b ≠ 0`,
`F₅(b,c) ≠ 0`.  The `b²⁰⁸` unit power and the proper order-`5` factor `F₅`
(whose nonvanishing is exactly `preΨ'₅(0,0) ≠ 0`) are fully separated. -/
theorem raw_order25_obstruction_iff :
    RawOrder25TateObstruction ↔
      ExplicitOrder25Obstruction := by
  constructor
  · rintro ⟨b, c, hEll, hb, h25, h5⟩
    rw [prePsi_five_eval_tate_origin] at h5
    have hF5 : TateNFDivision.F5 b c ≠ 0 := by
      intro hF5; apply h5; rw [hF5, mul_zero]
    refine ⟨b, c, hEll, hb, hF5, ?_⟩
    rw [prePsi_twentyfive_eval_tate_origin] at h25
    have hb208 : b ^ 208 ≠ 0 := pow_ne_zero _ hb
    rcases mul_eq_zero.mp h25 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hb208
      · exact absurd h' hF5
    · exact h
  · rintro ⟨b, c, hEll, hb, hF5, hF25⟩
    refine ⟨b, c, hEll, hb, ?_, ?_⟩
    · rw [prePsi_twentyfive_eval_tate_origin, hF25, mul_zero]
    · rw [prePsi_five_eval_tate_origin]
      exact mul_ne_zero (pow_ne_zero _ hb) hF5

/-- Forward reduction: a rational point of exact order `25` forces a rational
solution of `F₂₅(b,c) = 0` with `b ≠ 0` and `F₅ b c ≠ 0` (equivalently `b ≠ c`),
i.e. a non-cuspidal rational point on `X₁(25)`. -/
theorem raw_order25_reduces_to_F25 :
    RawOrder25TateObstruction →
      ∃ b c : ℚ, WeierstrassCurve.IsElliptic (W b c) ∧
        b ≠ 0 ∧ TateNFDivision.F5 b c ≠ 0 ∧ F25 b c = 0 := by
  intro h
  obtain ⟨b, c, hEll, hb, hF5, hF25⟩ := raw_order25_obstruction_iff.mp h
  exact ⟨b, c, hEll, hb, hF5, hF25⟩

/-- A rational point of exact order 25 produces the explicit primitive
order-25 obstruction. -/
theorem order25_to_explicit_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h25 : HasRationalPointOfOrder E 25) :
    ExplicitOrder25Obstruction :=
  raw_order25_obstruction_iff.mp (order25_to_raw_tate_obstruction E h25)

end

end MazurProof.TateOrder25Factor
