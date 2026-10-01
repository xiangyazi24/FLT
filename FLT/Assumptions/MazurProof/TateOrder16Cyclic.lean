import FLT.Assumptions.MazurProof.TateOriginDivision
import FLT.Assumptions.MazurProof.KubertBridgeN16

/-!
# The cyclic order-16 forward bridge to `X₁(16)`

`16 = 2⁴`.  A rational point `P` of exact order `16` on an elliptic curve
`E / ℚ` is placed at the marked origin `(0,0)` of a Tate normal form
`E(b,c) : y² + (1-c)xy - by = x³ - bx²` using
`TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three`.  The exact
order-`16` condition at the origin is then *computed* from the elliptic
divisibility sequence, using the same `KeystoneLadder` criterion
`n • P = 0 ↔ (ΨSqₙ).eval x = 0` reused throughout this development
(`TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval`).

## The landed algebra

Evaluating Mathlib's division-polynomial recurrences `preΨ'_even`/`preΨ'_odd`
at the Tate origin `x = 0` gives closed forms as ring-homomorphic images
`(preΨ' n).eval 0 ∈ ℚ[b,c]`.  The two we need factor exactly:

* `(preΨ' 8).eval 0  = b²⁰ · c · M(b,c)`,
* `(preΨ' 16).eval 0 = b⁸⁴ · c · M(b,c) · Φ₁₆(b,c)`,

where `M = tateM16` (equal to the Kubert factor `F₈`) and `Φ₁₆ = Phi16` are the
already-recorded polynomials of `KubertBridgeN16`.  Since `ΨSqₙ = preΨ'ₙ² · Ψ₂Sq`
for even `n` and `Ψ₂Sq.eval 0 = b₆ = b²`, with `b ≠ 0` the group conditions
`16 • P = 0` and `8 • P ≠ 0` become respectively

* `(preΨ' 16).eval 0 = 0`  ⟹ `c · M · Φ₁₆ = 0`,
* `(preΨ' 8).eval 0  ≠ 0`  ⟹ `c ≠ 0 ∧ M ≠ 0`,

and together they force **`Phi16 b c = 0`** — the genuine affine modular
equation of `X₁(16)` in the Tate coordinates — together with the exact-order
nondegeneracy `c ≠ 0`, `tateM16 b c ≠ 0`.  This is the content of
`order16_forward_bridge` / `order16_gives_X1_16_modular_point` below.

## The genus-2 seam (why this does *not* discharge `CyclicExclusion16`)

`{Φ₁₆ = 0}` is (the affine model of) `X₁(16)`, a curve of **genus 2**.  The
obstruction curve consumed by `CyclicExclusion16`,
`E_N16_AffineEquation : w² = u³ - u² - u`, is an elliptic curve of
**conductor 20** (discriminant `80 = 2⁴·5`, so it has bad reduction at the
prime `5`).  The level of `X₁(16)` is `16 = 2⁴`, supported only at `2`; hence
`J₁(16)` has no isogeny factor of conductor divisible by `5`, and there is no
nonconstant rational map `X₁(16) → {w² = u³ - u² - u}`.  Consequently
`cyclic_order_16_kubert_bridge` (which asks for a *nondegenerate* rational
point on `w² = u³ - u² - u` produced from a point of order `16`) is only
*vacuously* true — via Mazur's theorem the hypothesis never holds — and it
**cannot** be discharged through the conductor-`20` curve.  The honest
completion of the order-`16` exclusion requires the genus-`2`, rank-`0`
analysis of `X₁(16)` (Chabauty/Jacobian), not a genus-`1` obstruction.

This file therefore builds the real forward bridge as far as it genuinely
goes — landing exactly on `Phi16 b c = 0` with its exact-order nonvanishing —
and stops at that seam rather than fabricating the mis-modeled final map.
No `axiom`, `sorry`, `admit`, `native_decide`, or `opaque` is used.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder16Cyclic

open Scratch.TateZ2xZ10Reduction
open MazurProof.TateOriginDivision

noncomputable section

/-! ## Origin evaluations of the division polynomials `preΨ'ₙ`

Each lemma reads the value `(preΨ' n).eval 0` off Mathlib's elliptic
divisibility recurrence.  Because `Polynomial.eval 0` is a ring homomorphism
these are honest polynomial identities in `b, c`, verified by `ring` after
unfolding the Tate normal-form Weierstrass invariants. -/

theorem prePsi_5 (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 = b ^ 8 * (b - c) := by
  have h : ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 - ((W b c).Ψ₃.eval 0) ^ 3 := by
    have h0 := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
    simpa using h0
  rw [h]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem prePsi_6 (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 = -b ^ 11 * (b - c - c ^ 2) := by
  have h : ((W b c).preΨ' 6).eval 0 =
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 2 := by
    have h0 := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 0)
    simpa using h0
  rw [h, prePsi_5]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem prePsi_7 (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 = -b ^ 16 * (b ^ 2 - b * c - c ^ 3) := by
  have h : ((W b c).preΨ' 7).eval 0 =
      ((W b c).preΨ' 5).eval 0 * ((W b c).preΨ' 3).eval 0 ^ 3 -
        ((W b c).preΨ' 2).eval 0 * ((W b c).preΨ' 4).eval 0 ^ 3 *
          ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
    have h0 := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 1)
    simpa [show ¬ Even (1 : ℕ) by decide] using h0
  rw [h, prePsi_5]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem prePsi_8 (b c : ℚ) :
    ((W b c).preΨ' 8).eval 0 = b ^ 20 * c * KubertBridgeN16.tateM16 b c := by
  have h : ((W b c).preΨ' 8).eval 0 =
      ((W b c).preΨ' 3).eval 0 ^ 2 * ((W b c).preΨ' 4).eval 0 * ((W b c).preΨ' 6).eval 0 -
        ((W b c).preΨ' 2).eval 0 * ((W b c).preΨ' 4).eval 0 * ((W b c).preΨ' 5).eval 0 ^ 2 := by
    have h0 := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 1)
    simpa using h0
  rw [h, prePsi_6, prePsi_5]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    KubertBridgeN16.tateM16]
  ring

theorem prePsi_9 (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 =
      b ^ 27 * (b ^ 3 - 3 * b ^ 2 * c + 3 * b * c ^ 2 + b * c ^ 3 - c ^ 3 - c ^ 4 - c ^ 5) := by
  have h : ((W b c).preΨ' 9).eval 0 =
      ((W b c).preΨ' 6).eval 0 * ((W b c).preΨ' 4).eval 0 ^ 3 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 ^ 3 := by
    have h0 := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 2)
    simpa [show Even (2 : ℕ) by decide] using h0
  rw [h, prePsi_6, prePsi_5]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.preΨ₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem prePsi_10 (b c : ℚ) :
    ((W b c).preΨ' 10).eval 0 =
      b ^ 32 * (b - c) *
        (b ^ 3 - 3 * b ^ 2 * c ^ 2 - 2 * b ^ 2 * c + b * c ^ 4 + 3 * b * c ^ 3
          + b * c ^ 2 + c ^ 5) := by
  have h : ((W b c).preΨ' 10).eval 0 =
      ((W b c).preΨ' 4).eval 0 ^ 2 * ((W b c).preΨ' 5).eval 0 * ((W b c).preΨ' 7).eval 0 -
        ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 * ((W b c).preΨ' 6).eval 0 ^ 2 := by
    have h0 := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 2)
    simpa using h0
  rw [h, prePsi_7, prePsi_6, prePsi_5]
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- The order-`16` primitive factor, isolated after dividing out the order-`8`
factor `(preΨ' 8).eval 0`.  This is where `Phi16` is produced. -/
theorem bracket16 (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 ^ 2 * ((W b c).preΨ' 10).eval 0 -
        ((W b c).preΨ' 6).eval 0 * ((W b c).preΨ' 9).eval 0 ^ 2 =
      b ^ 64 * KubertBridgeN16.Phi16 b c := by
  rw [prePsi_7, prePsi_10, prePsi_6, prePsi_9]
  simp only [KubertBridgeN16.Phi16]
  ring

/-- The order-`16` division-polynomial identity at the Tate origin: the value
`(preΨ' 16).eval 0` factors as `b⁸⁴ · c · tateM16 · Phi16`. -/
theorem prePsi_16 (b c : ℚ) :
    ((W b c).preΨ' 16).eval 0 =
      b ^ 84 * c * KubertBridgeN16.tateM16 b c * KubertBridgeN16.Phi16 b c := by
  have h : ((W b c).preΨ' 16).eval 0 =
      ((W b c).preΨ' 7).eval 0 ^ 2 * ((W b c).preΨ' 8).eval 0 * ((W b c).preΨ' 10).eval 0 -
        ((W b c).preΨ' 6).eval 0 * ((W b c).preΨ' 8).eval 0 * ((W b c).preΨ' 9).eval 0 ^ 2 := by
    have h0 := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 5)
    simpa using h0
  have key :
      ((W b c).preΨ' 7).eval 0 ^ 2 * ((W b c).preΨ' 8).eval 0 * ((W b c).preΨ' 10).eval 0 -
          ((W b c).preΨ' 6).eval 0 * ((W b c).preΨ' 8).eval 0 * ((W b c).preΨ' 9).eval 0 ^ 2 =
        ((W b c).preΨ' 8).eval 0 *
          (((W b c).preΨ' 7).eval 0 ^ 2 * ((W b c).preΨ' 10).eval 0 -
            ((W b c).preΨ' 6).eval 0 * ((W b c).preΨ' 9).eval 0 ^ 2) := by
    ring
  rw [h, key, bracket16, prePsi_8]
  ring

/-! ## The `Ψ₂Sq` origin value -/

theorem Psi2Sq_eval_zero (b c : ℚ) : ((W b c).Ψ₂Sq).eval 0 = b ^ 2 := by
  simp [W, tateNormalFormCurve, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]

/-! ## From the group law to the division-polynomial conditions -/

/-- If the Tate origin is killed by `16` then `(preΨ' 16).eval 0 = 0`. -/
theorem prePsi16_eval_zero_of_16_nsmul
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] (hb : b ≠ 0)
    (h16 : (16 : ℕ) • tateOrigin b c = 0) :
    ((W b c).preΨ' 16).eval 0 = 0 := by
  have hΨ : ((W b c).ΨSq (16 : ℕ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c) (tate_origin_nonsingular b c)).mp h16
  rw [(W b c).ΨSq_ofNat 16] at hΨ
  simp only [show Even (16 : ℕ) by decide, if_true, Polynomial.eval_mul,
    Polynomial.eval_pow, Psi2Sq_eval_zero] at hΨ
  rcases mul_eq_zero.mp hΨ with h1 | h2
  · exact (pow_eq_zero_iff two_ne_zero).mp h1
  · exact absurd h2 (pow_ne_zero 2 hb)

/-- If the Tate origin is *not* killed by `8` then `(preΨ' 8).eval 0 ≠ 0`. -/
theorem prePsi8_eval_ne_zero_of_8_nsmul_ne
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (h8 : (8 : ℕ) • tateOrigin b c ≠ 0) :
    ((W b c).preΨ' 8).eval 0 ≠ 0 := by
  intro hpre
  apply h8
  apply (nsmul_eq_zero_iff_PsiSq_eval (W b c) (tate_origin_nonsingular b c)).mpr
  rw [(W b c).ΨSq_ofNat 8]
  simp [show Even (8 : ℕ) by decide, hpre]

/-! ## The genuine `X₁(16)` modular datum -/

/-- The nondegenerate Tate/Kubert datum for `X₁(16)`: parameters `(b,c)`
solving the modular equation `Phi16 = 0` with the exact-order-`16` nonvanishing
conditions `b ≠ 0`, `c ≠ 0`, `tateM16 ≠ 0` (the last excludes proper divisor
orders `8 ∣ 16`). -/
def X116Datum (b c : ℚ) : Prop :=
  b ≠ 0 ∧ c ≠ 0 ∧ KubertBridgeN16.tateM16 b c ≠ 0 ∧ KubertBridgeN16.Phi16 b c = 0

/-- **Forward bridge (exact-order form).**  A Tate normal form whose marked
origin has exact additive order `16` (with `b ≠ 0`) satisfies the `X₁(16)`
modular datum: `Phi16 b c = 0`, together with `c ≠ 0` and `tateM16 b c ≠ 0`. -/
theorem X116Datum_of_tateOrigin_order16
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 16) :
    X116Datum b c := by
  have h16z : (16 : ℕ) • tateOrigin b c = 0 := by
    have := addOrderOf_nsmul_eq_zero (tateOrigin b c)
    rwa [hord] at this
  have h8ne : (8 : ℕ) • tateOrigin b c ≠ 0 :=
    ((addOrderOf_eq_iff (x := tateOrigin b c) (by norm_num)).mp hord).2 8 (by norm_num)
      (by norm_num)
  -- order-16 side: `Phi16 = 0` after removing the lower-order factors
  have he16 : ((W b c).preΨ' 16).eval 0 = 0 :=
    prePsi16_eval_zero_of_16_nsmul b c hb h16z
  rw [prePsi_16] at he16
  -- exact-order side: `c ≠ 0` and `tateM16 ≠ 0`
  have he8 : ((W b c).preΨ' 8).eval 0 ≠ 0 :=
    prePsi8_eval_ne_zero_of_8_nsmul_ne b c h8ne
  rw [prePsi_8] at he8
  have hc : c ≠ 0 := by
    rintro rfl; exact he8 (by ring)
  have hM : KubertBridgeN16.tateM16 b c ≠ 0 := by
    intro hM0; exact he8 (by rw [hM0]; ring)
  have hPhi : KubertBridgeN16.Phi16 b c = 0 := by
    have hprod : b ^ 84 * c * KubertBridgeN16.tateM16 b c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 84 hb) hc) hM
    exact (mul_eq_zero.mp he16).resolve_left hprod
  exact ⟨hb, hc, hM, hPhi⟩

/-- **Forward bridge (curve/point form).**  An elliptic curve `E / ℚ` carrying a
rational point of exact order `16` yields Tate parameters `(b,c)` whose marked
origin has additive order `16` and which satisfy the `X₁(16)` modular datum. -/
theorem order16_forward_bridge
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h16 : HasRationalPointOfOrder E 16) :
    ∃ b c : ℚ, ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      addOrderOf (tateOrigin b c) = 16 ∧ X116Datum b c := by
  obtain ⟨P, hP⟩ := h16
  obtain ⟨b, c, hEll, hordN, hb⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three E P 16 (by norm_num) hP
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have hord : addOrderOf (tateOrigin b c) = 16 := by
    rw [tateOrigin_eq_normalized_origin]; exact hordN
  exact ⟨b, c, inferInstance, hord, X116Datum_of_tateOrigin_order16 b c hb hord⟩

/-- **Forward bridge (existence form).**  From a rational point of exact order
`16` one obtains a rational point on the affine model `Phi16 b c = 0` of
`X₁(16)` that avoids the degenerate (proper-divisor-order) locus. -/
theorem order16_gives_X1_16_modular_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h16 : HasRationalPointOfOrder E 16) :
    ∃ b c : ℚ, X116Datum b c := by
  obtain ⟨b, c, _, _, hdatum⟩ := order16_forward_bridge E h16
  exact ⟨b, c, hdatum⟩

/-! ## Reconciliation with the `TateNFDivision` order predicates

The order-`16` nonvanishing factor `tateM16` is exactly the Kubert order-`8`
factor `F₈`; the datum therefore certifies that the marked origin has exact
order `16` and *not* the proper divisor order `8`. -/

theorem tateM16_eq_F8 (b c : ℚ) :
    KubertBridgeN16.tateM16 b c = TateNFDivision.F8 b c := by
  simp only [KubertBridgeN16.tateM16, TateNFDivision.F8]; ring

/-- Exact-order witness: the `X₁(16)` datum certifies the marked origin does not
have the proper divisor order `8`, i.e. `TateNFDivision.ExactOrder8` fails. -/
theorem not_exactOrder8_of_X116Datum
    {b c : ℚ} (h : X116Datum b c) : ¬ TateNFDivision.ExactOrder8 b c := by
  obtain ⟨_, _, hM, _⟩ := h
  rintro ⟨_, _, hF8⟩
  exact hM (by rw [tateM16_eq_F8]; exact hF8)

end

end MazurProof.TateOrder16Cyclic
