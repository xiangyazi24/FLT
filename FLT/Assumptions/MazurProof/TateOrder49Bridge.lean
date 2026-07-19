import FLT.Assumptions.MazurProof.TateOrder49Factor
import FLT.Assumptions.MazurProof.CyclicExclusion49

/-!
# Bridge: Reduction of the raw order-49 obstruction to `bracket₄₉ = 0`

This file connects the structural recurrence identity
  `preΨ'₄₉(0) = b⁸⁰⁰ * bracket₄₉`
with the geometric front end in `CyclicExclusion49`, proving that the raw
Tate-division system is equivalent to the vanishing of the bracket expression
on the non-degenerate locus.

The approach is purely structural: the `preΨ'_odd` recurrence gives the compact
form; Ward's theorem guarantees `F₇ | bracket₄₉` (since 7 | 49 in the EDS),
but the bridge does not require that factorisation — it works directly with
the unfactored bracket.  The primitive polynomial `F₄₉ = bracket₄₉ / F₇`
(degree 157, genus 69) remains available for future rational-point analysis.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder49Factor

open TateOriginDivision
open TateOrder25Factor

/-- The explicit primitive order-49 obstruction: the bracket expression vanishes
on the non-degenerate locus (b ≠ 0, F₇ ≠ 0, W elliptic). -/
def ExplicitOrder49Obstruction : Prop :=
  ∃ b c : ℚ, ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
    b ≠ 0 ∧ TateNFDivision.F7 b c ≠ 0 ∧ bracket49 b c = 0

/-- **Main theorem.** The raw order-49 Tate-division system is equivalent to the
vanishing of `bracket₄₉` on the non-degenerate locus. -/
theorem raw_order49_obstruction_iff :
    CyclicExclusion49.RawOrder49TateObstruction ↔
      ExplicitOrder49Obstruction := by
  constructor
  · rintro ⟨b, c, hEll, hb, h49, h7⟩
    rw [prePsi_7_eval] at h7
    have hF7 : TateNFDivision.F7 b c ≠ 0 := by
      intro hF7; apply h7; rw [hF7, mul_zero]
    refine ⟨b, c, hEll, hb, hF7, ?_⟩
    have heq := prePsi_fortynine_eval_compact b c
    rw [heq] at h49
    exact (mul_eq_zero.mp h49).resolve_left (pow_ne_zero _ hb)
  · rintro ⟨b, c, hEll, hb, hF7, hBr⟩
    refine ⟨b, c, hEll, hb, ?_, ?_⟩
    · rw [prePsi_fortynine_eval_compact, hBr, mul_zero]
    · rw [prePsi_7_eval]
      exact mul_ne_zero (pow_ne_zero _ hb) hF7

/-- Forward reduction: a rational point of exact order 49 forces
`bracket₄₉(b,c) = 0` with `b ≠ 0` and `F₇ b c ≠ 0`. -/
theorem order49_to_explicit_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h49 : HasRationalPointOfOrder E 49) :
    ExplicitOrder49Obstruction :=
  raw_order49_obstruction_iff.mp (CyclicExclusion49.order49_to_raw_tate_obstruction E h49)

end MazurProof.TateOrder49Factor
