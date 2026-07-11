import FLT.Assumptions.MazurProof.TateOriginDivision

/-!
# Cyclic order 27: reduction to an explicit Tate-division factor

`27 = 3³`.  A rational point of exact order `27` placed at the marked origin of a
nonsingular Tate normal form satisfies, by the generic odd-order division bridge
(`TateOriginDivision`):

* `preΨ'₂₇(0) = 0`;
* `preΨ'₃(0) ≠ 0` and `preΨ'₉(0) ≠ 0`, excluding the two proper divisors `3` and
  `9` of `27`.

This file records that raw reduction and then factors the order-27 division
condition at the origin.  Unrolling the elliptic-divisibility recurrence and
extracting the power of `b` at every step gives the closed identity

`preΨ'₂₇(0) = -(b²⁴³ · F27 b c)`,

with `F27` written compactly through the lower Kubert factors `F5,…,F9`:

* `G13 = F5·F7³ + b·c·F6³·F8`   (`= F13`),
* `G15 = F9·F7³ + F6·c³·F8³`    (`= F15`),
* `G12 = c·F6·(F5²·F8 + F7²)`,
* `G14 = F7·(b·F6²·F9 − c²·F5·F8²)`,
* `F27 = G15·G13³ − G12·G14³`.

The factor called `F27` here is the full factor left after removing `b²⁴³`, not
the primitive order-27 factor.  Expanding the displayed definitions gives

`F27 = F9 · F27prim`.

This is forced by the old-order component `9 ∣ 27`: every order-9 origin also
annihilates the order-27 division polynomial.  The exact-order reduction below
therefore retains `F9 b c ≠ 0`; this removes that component and leaves precisely
the primitive order-27 locus.  The expanded primitive factor has 261 monomials,
so it is deliberately not materialised here.

Thus this file is a nonterminal algebraic reduction.  It does not construct the
degree-three map from `X₁(27)` to the genus-one quotient `27C1`; that map, not a
map from `X₀(27)`, is the remaining geometric step used by
`CyclicExclusion27`.  Every `ring` call below keeps the compact lower factors
atomic.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder27

open TateOriginDivision
open Scratch.TateZ2xZ10Reduction

noncomputable section

/-! ## Tier 1 — the raw exact-order-27 Tate division system

Mirrors `CyclicExclusion25`/`CyclicExclusion49`, but records **both** proper
divisor conditions because the divisor chain of `27` is `1 ∣ 3 ∣ 9 ∣ 27`. -/

/-- The exact raw Tate-division system left by a rational point of order 27.
The two nonvanishing evaluations remove the proper divisors `3` and `9`. -/
def RawOrder27TateObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      b ≠ 0 ∧
        ((W b c).preΨ' 27).eval 0 = 0 ∧
        ((W b c).preΨ' 3).eval 0 ≠ 0 ∧
        ((W b c).preΨ' 9).eval 0 ≠ 0

/-- Exact order 27 produces the explicit raw Tate-division obstruction. -/
theorem order27_to_raw_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h27 : HasRationalPointOfOrder E 27) :
    RawOrder27TateObstruction := by
  obtain ⟨b, c, hEll, hord, hb, h27eval⟩ :=
    exists_tate_parameters_of_has_rational_point_of_odd_order
      E (n := 27) (by norm_num) (by decide) h27
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have h3eval : ((W b c).preΨ' 3).eval 0 ≠ 0 :=
    prePsi_eval_ne_zero_of_lt_addOrder b c
      (n := 27) (m := 3) (by norm_num) (by norm_num) (by norm_num)
      (by decide) hord
  have h9eval : ((W b c).preΨ' 9).eval 0 ≠ 0 :=
    prePsi_eval_ne_zero_of_lt_addOrder b c
      (n := 27) (m := 9) (by norm_num) (by norm_num) (by norm_num)
      (by decide) hord
  exact ⟨b, c, inferInstance, hb, h27eval, h3eval, h9eval⟩

/-! ## Tier 2 — factoring the order-27 division condition at the origin

The origin evaluations of the auxiliary polynomials `preΨ'ₖ` follow Mathlib's
elliptic-divisibility recurrence, read off exactly as in the order-9 and order-11
developments.  Each step extracts a power of `b`, keeping the compact factor
symbolic. -/

/-! ### Recurrence unrollings at the origin -/

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

private lemma eval_prePsi_twentyseven (b c : ℚ) :
    ((W b c).preΨ' 27).eval 0 =
      ((W b c).preΨ' 15).eval 0 * (((W b c).preΨ' 13).eval 0) ^ 3 -
        ((W b c).preΨ' 12).eval 0 * (((W b c).preΨ' 14).eval 0) ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 11)
  simpa [show ¬ Even (11 : ℕ) by decide] using h

/-! ### Base origin evaluations (fully expanded, low degree) -/

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

/-! ### Compact intermediate factors -/

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

/-- Compact factor with `preΨ'₁₅(0) = b⁷⁵ · G15 b c`; agrees with `F15`. -/
def G15 (b c : ℚ) : ℚ :=
  TateNFDivision.F9 b c * TateNFDivision.F7 b c ^ 3 +
    TateNFDivision.F6 b c * c ^ 3 * TateNFDivision.F8 b c ^ 3

/-- The compact order-27 origin factor: `preΨ'₂₇(0) = -(b²⁴³ · F27 b c)`. -/
def F27 (b c : ℚ) : ℚ :=
  G15 b c * G13 b c ^ 3 - G12 b c * G14 b c ^ 3

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
    ((W b c).preΨ' 15).eval 0 = b ^ 75 * G15 b c := by
  rw [eval_prePsi_fifteen, prePsi_9_eval, prePsi_7_eval, prePsi_6_eval,
    prePsi_8_eval, Psi2Sq_eval]
  simp only [G15]
  ring

/-! ### The compact order-27 identity -/

/-- The order-27 division-polynomial identity at the Tate origin. -/
theorem prePsi_27_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 27).eval 0 = -(b ^ 243 * F27 b c) := by
  rw [eval_prePsi_twentyseven, prePsi_15_eval, prePsi_13_eval, prePsi_12_eval,
    prePsi_14_eval, Psi2Sq_eval]
  simp only [F27]
  ring

/-! ## Tier 2 assembly — the exact-order component of the `F27` obstruction

`preΨ'₂₇(0) = 0` and `b ≠ 0` force `F27 b c = 0`; `preΨ'₉(0) ≠ 0` forces
`F9 b c ≠ 0`.  Since `F27 = F9 · F27prim`, the nonvanishing condition removes
the entire old order-9 component.  This is the explicit algebraic system left by
a rational point of exact order 27.  It is a reduction to the primitive
two-variable locus, not yet the construction of its quotient map to `27C1`. -/

/-- The explicit exact-order-27 system: a nonsingular Tate normal form with
`b ≠ 0` whose full origin factor `F27` vanishes away from its old-order factor
`F9`.  The condition `F9 b c ≠ 0` is essential: without it, every order-9
solution would be a spurious solution of `F27 b c = 0`. -/
def F27Order27Obstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      b ≠ 0 ∧ F27 b c = 0 ∧ TateNFDivision.F9 b c ≠ 0

/-- Exact order 27 produces the explicit compact `F27` obstruction. -/
theorem order27_to_F27_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h27 : HasRationalPointOfOrder E 27) :
    F27Order27Obstruction := by
  obtain ⟨b, c, hEll, hb, h27eval, _h3eval, h9eval⟩ :=
    order27_to_raw_tate_obstruction E h27
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  refine ⟨b, c, inferInstance, hb, ?_, ?_⟩
  · -- `F27 b c = 0`
    have h := prePsi_27_eval_tate_origin b c
    rw [h27eval] at h
    have hz : b ^ 243 * F27 b c = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 243 hb)
  · -- `F9 b c ≠ 0`
    intro hF9
    apply h9eval
    rw [prePsi_9_eval, hF9, mul_zero]

end

end MazurProof.TateOrder27
