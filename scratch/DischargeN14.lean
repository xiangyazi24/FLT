import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.ObstructionQ14
import scratch.TateZ2xZ10Reduction

/-!
# Discharge layer for the `ZMod 2 × ZMod 14` bridge

The repo's `E_N14` curve is not the cyclic modular curve `X_1(14)`.
The forward bridge is therefore discharged ex falso: an injection
`ZMod 2 × ZMod 14 → E(ℚ)` already gives a rational point of exact order `14`,
and the cyclic `X_1(14)` obstruction rules that out.
-/

open scoped WeierstrassCurve.Affine

namespace Scratch.DischargeN14

open Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The cyclic modular curve model `X_1(14) = 14a4`. -/
def X14Equation (t s : ℚ) : Prop :=
  s ^ 2 + t * s + s = t ^ 3 - t

def X14DegenerateParameter (t : ℚ) : Prop :=
  t = -1 ∨ t = 0 ∨ t = 1

private lemma mem_triple_m1_0_1 {t : ℚ} :
    t ∈ ({-1, 0, 1} : Finset ℚ) ↔ X14DegenerateParameter t := by
  norm_num [Finset.mem_insert, Finset.mem_singleton, X14DegenerateParameter]

private lemma mem_triple_m7_0_1 {v : ℚ} :
    v ∈ ({-7, 0, 1} : Finset ℚ) ↔ v = -7 ∨ v = 0 ∨ v = 1 := by
  norm_num [Finset.mem_insert, Finset.mem_singleton]

private lemma C14_affine_x_mem
    {u w : ℚ}
    (hC : w ^ 2 = u ^ 3 - 11 * u ^ 2 + 32 * u) :
    u ∈ ({0, 4, 8} : Finset ℚ) := by
  classical
  by_cases hu : u = 0
  · subst hu
    norm_num
  let v : ℚ := w ^ 2 / u ^ 2
  let z : ℚ := w * (32 - u ^ 2) / u ^ 2
  have hQ : z ^ 2 = v ^ 3 + 22 * v ^ 2 - 7 * v := by
    dsimp [v, z]
    field_simp [hu]
    rw [hC]
    ring
  have hv := ObstructionQ14.obstruction_Q14 v z hQ
  rw [mem_triple_m7_0_1] at hv
  rcases hv with hv | hv | hv
  · exfalso
    have hw : w ^ 2 = -7 * u ^ 2 := by
      dsimp [v] at hv
      field_simp [hu] at hv
      nlinarith
    have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
    have hw0 : 0 ≤ w ^ 2 := sq_nonneg w
    nlinarith
  · exfalso
    have hw2 : w ^ 2 = 0 := by
      dsimp [v] at hv
      field_simp [hu] at hv
      nlinarith
    have hw : w = 0 := sq_eq_zero_iff.mp hw2
    have hquad : u ^ 2 - 11 * u + 32 = 0 := by
      have h0 : u ^ 3 - 11 * u ^ 2 + 32 * u = 0 := by
        simpa [hw] using hC.symm
      have hmul : u * (u ^ 2 - 11 * u + 32) = 0 := by
        ring_nf
        ring_nf at h0
        exact h0
      exact (mul_eq_zero.mp hmul).resolve_left hu
    have hsq : (2 * u - 11) ^ 2 + 7 = 0 := by
      nlinarith
    nlinarith [sq_nonneg (2 * u - 11)]
  · have hw2 : w ^ 2 = u ^ 2 := by
      dsimp [v] at hv
      field_simp [hu] at hv
      nlinarith
    have hquad : u ^ 2 - 12 * u + 32 = 0 := by
      have h0 : u ^ 2 = u ^ 3 - 11 * u ^ 2 + 32 * u := by
        simpa [hw2] using hC
      have hmul : u * (u ^ 2 - 12 * u + 32) = 0 := by
        ring_nf
        nlinarith
      exact (mul_eq_zero.mp hmul).resolve_left hu
    have hfac : (u - 4) * (u - 8) = 0 := by
      ring_nf
      nlinarith
    rcases mul_eq_zero.mp hfac with h4 | h8
    · rw [sub_eq_zero.mp h4]
      norm_num
    · rw [sub_eq_zero.mp h8]
      norm_num

theorem X14_rational_points_degenerate
    {t s : ℚ}
    (hX : X14Equation t s) :
    X14DegenerateParameter t := by
  classical
  let u : ℚ := 4 * (t + 1)
  let w : ℚ := 4 * (2 * s + t + 1)
  have hC : w ^ 2 = u ^ 3 - 11 * u ^ 2 + 32 * u := by
    dsimp [u, w]
    ring_nf
    unfold X14Equation at hX
    nlinarith [hX]
  have hu := C14_affine_x_mem hC
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with hu | hu | hu
  · left
    nlinarith
  · right; left
    nlinarith
  · right; right
    nlinarith

/-- Denominator in Kubert's `X_1(14)` parametrization. -/
def D14 (t : ℚ) : ℚ :=
  (t + 1) * (t ^ 3 - 2 * t ^ 2 - t + 1)

/-- Kubert/Morain `a`-coefficient on `X_1(14)`. -/
def kubertA14 (t s : ℚ) : ℚ :=
  (t ^ 4 - s * t ^ 3 + (2 * s - 4) * t ^ 2 - s * t + 1) / D14 t

/-- Kubert/Morain `b`-coefficient on `X_1(14)`. -/
def kubertB14 (t s : ℚ) : ℚ :=
  (-t ^ 7 + 2 * t ^ 6 + (2 * s - 1) * t ^ 5 - (2 * s + 1) * t ^ 4
      - 2 * (s - 1) * t ^ 3 + (3 * s - 1) * t ^ 2 - s * t) / (D14 t) ^ 2

/-- Repo Tate convention: `Y^2 + (1-c)XY - bY = X^3 - bX^2`. -/
def tateB14 (t s : ℚ) : ℚ :=
  -kubertB14 t s

/-- Repo Tate convention: `Y^2 + (1-c)XY - bY = X^3 - bX^2`. -/
def tateC14 (t s : ℚ) : ℚ :=
  1 - kubertA14 t s

private lemma tate_origin_nonsingular14
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

private def tateOriginPoint14 (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular14 b c)

/-- Exact order `14` for the origin on repo Tate normal form. -/
def tateOrder14Condition (b c : ℚ) : Prop :=
  ∃ hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
    letI : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c) := hEll
    addOrderOf (tateOriginPoint14 b c) = 14

/--
The pure group-theory extraction from an injective `ZMod 2 × ZMod 14`.
-/
theorem order14_of_injective_Z2xZ14
    {G : Type*} [AddMonoid G]
    (f : (ZMod 2 × ZMod 14) →+ G) (hf : Function.Injective f) :
    addOrderOf (f ((0 : ZMod 2), (1 : ZMod 14))) = 14 := by
  classical
  let p0 : ZMod 2 × ZMod 14 := ((0 : ZMod 2), (1 : ZMod 14))
  have hp0_order : addOrderOf p0 = 14 := by
    simp [p0, Prod.addOrderOf_mk]
  simpa [p0] using addOrderOf_injective f hf p0 |>.trans hp0_order

/--
Tate/Kubert forward bridge for an exact order-14 rational point.

This is the remaining explicit normalization/elimination step: move `(E,R)` to
Tate normal form with `R ↦ (0,0)`, use the order-14 multiple relations, and
map the resulting Tate parameters to the cyclic model
`X_1(14) : s^2 + ts + s = t^3 - t`.
-/
theorem order14_gives_X14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : (E⁄ℚ).Point)
    (hR : addOrderOf R = 14) :
    ∃ t s : ℚ, X14Equation t s ∧ ¬ X14DegenerateParameter t := by
  -- TODO: port the N10/N12 Tate-normal-form calculation and Kubert's
  -- order-14 elimination into this named bridge.
  sorry

/--
The cyclic `X_1(14)` obstruction.

Mathematically this is the standard route:
an exact order-14 rational point gives a non-cuspidal rational point on
`X_1(14) : s^2 + ts + s = t^3 - t`; the curve is Cremona `14a4`, rank zero,
and all rational points are cuspidal, i.e. `t ∈ {-1,0,1}`.
-/
theorem order14_point_obstructed_by_X14_rank_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : (E⁄ℚ).Point)
    (hR : addOrderOf R = 14) :
    False := by
  rcases order14_gives_X14_point E R hR with ⟨t, s, hX, hnondeg⟩
  exact hnondeg (X14_rational_points_degenerate hX)

theorem no_order14_point_over_Q
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : (E⁄ℚ).Point)
    (hR : addOrderOf R = 14) :
    False :=
  order14_point_obstructed_by_X14_rank_zero E R hR

/--
Existing bridge target, discharged ex falso.  No point on the repo curve is
constructed; the `ZMod 2 × ZMod 14` hypothesis is contradictory.
-/
theorem Z2xZ14_gives_non_degenerate_N14_point
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hE : ∃ f : ZMod 2 × ZMod 14 →+ (E⁄ℚ).Point, Function.Injective f) :
    ∃ u w : ℚ,
      w ^ 2 = u ^ 3 + u ^ 2 - 2 * u ∧
        ¬ (u = -2 ∨ u = 0 ∨ u = 1) := by
  rcases hE with ⟨f, hf⟩
  have hR : addOrderOf (f ((0 : ZMod 2), (1 : ZMod 14))) = 14 :=
    order14_of_injective_Z2xZ14 f hf
  exact False.elim (no_order14_point_over_Q E (f ((0 : ZMod 2), (1 : ZMod 14))) hR)

end

end Scratch.DischargeN14
