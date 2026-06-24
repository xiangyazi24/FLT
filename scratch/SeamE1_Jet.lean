module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-! # SEAM1 / E1 — dual-number jet scaffolding (notation + tangent-at-O)

The verifiable scaffolding for the rootwise tangent core: the `D K` dual-number notation and the
`TangentO` first-order chart at `O`, whose `n`-fold sum is scalar `n` (the `d[n]|_O = n·id` fact at
the tangent-coordinate level). The deep raw-coordinate bridge is isolated separately. -/

open scoped DualNumber

namespace WeierstrassCurve.SEAM1

variable {K : Type*} [Field K]

abbrev D (K : Type*) [Field K] := DualNumber K

namespace Dual
abbrev c (x : K) : D K := TrivSqZeroExt.inl x
abbrev e (v : K) : D K := TrivSqZeroExt.inr v
@[simp] lemma fst_c (x : K) : TrivSqZeroExt.fst (c x : D K) = x := rfl
@[simp] lemma snd_c (x : K) : TrivSqZeroExt.snd (c x : D K) = 0 := rfl
@[simp] lemma fst_e (v : K) : TrivSqZeroExt.fst (e v : D K) = 0 := rfl
@[simp] lemma snd_e (v : K) : TrivSqZeroExt.snd (e v : D K) = v := rfl
end Dual

namespace TangentO

/-- First-order `n`-fold sum in the tangent coordinate at `O`. -/
def nsmul₁ : ℕ → K → K
  | 0, _ => 0
  | n + 1, u => nsmul₁ n u + u

@[simp] lemma nsmul₁_zero (u : K) : nsmul₁ 0 u = 0 := rfl
@[simp] lemma nsmul₁_succ (n : ℕ) (u : K) : nsmul₁ (n + 1) u = nsmul₁ n u + u := rfl

/-- The first-order tangent of `[n]` at `O` is scalar multiplication by `(n : K)`. -/
lemma nsmul₁_eq_natCast_mul (n : ℕ) (u : K) : nsmul₁ n u = (n : K) * u := by
  induction n with
  | zero => simp
  | succ n ih => rw [nsmul₁_succ, ih, Nat.cast_succ, add_mul, one_mul]

end TangentO

namespace AffineJet
open Dual
variable (W : WeierstrassCurve K)

@[simp] lemma bc_a₁ : (W.toAffine.baseChange (D K)).a₁ = c W.a₁ := rfl
@[simp] lemma bc_a₂ : (W.toAffine.baseChange (D K)).a₂ = c W.a₂ := rfl
@[simp] lemma bc_a₃ : (W.toAffine.baseChange (D K)).a₃ = c W.a₃ := rfl
@[simp] lemma bc_a₄ : (W.toAffine.baseChange (D K)).a₄ = c W.a₄ := rfl
@[simp] lemma bc_a₆ : (W.toAffine.baseChange (D K)).a₆ = c W.a₆ := rfl

/-- Dual-number product (first-order). -/
lemma dual_mul (a b a2 d : K) :
    (c a + e b) * (c a2 + e d : D K) = c (a * a2) + e (a * d + b * a2) := by
  apply TrivSqZeroExt.ext <;> simp [Dual.c, Dual.e, op_smul_eq_mul] <;> ring

/-- Left scalar times a dual number. -/
@[simp] lemma c_mul_dual (a p q : K) : (c a) * (c p + e q : D K) = c (a * p) + e (a * q) := by
  apply TrivSqZeroExt.ext <;> simp [Dual.c, Dual.e, op_smul_eq_mul]

/-- Dual-number square. -/
@[simp] lemma dual_sq (a b : K) : (c a + e b : D K) ^ 2 = c (a ^ 2) + e (2 * a * b) := by
  rw [sq, dual_mul]; ring_nf

/-- Dual-number cube. -/
@[simp] lemma dual_cube (a b : K) : (c a + e b : D K) ^ 3 = c (a ^ 3) + e (3 * a ^ 2 * b) := by
  rw [pow_succ, dual_sq, dual_mul]; ring_nf

/-- First-order Taylor expansion of the Weierstrass equation over the dual numbers. -/
lemma equation_dual_iff (x y u v : K) :
    (W.toAffine.baseChange (D K)).Equation (c x + e u) (c y + e v) ↔
      W.toAffine.Equation x y ∧
        W.toAffine.polynomialX.evalEval x y * u +
          W.toAffine.polynomialY.evalEval x y * v = 0 := by
  rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial,
      WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial,
      WeierstrassCurve.Affine.evalEval_polynomialX, WeierstrassCurve.Affine.evalEval_polynomialY]
  simp only [bc_a₁, bc_a₂, bc_a₃, bc_a₄, bc_a₆, dual_sq, dual_cube, dual_mul, c_mul_dual]
  rw [TrivSqZeroExt.ext_iff]
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.snd_sub, fst_c, snd_c, fst_e, snd_e, TrivSqZeroExt.fst_zero,
    TrivSqZeroExt.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linear_combination h1, by linear_combination h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linear_combination h1, by linear_combination h2⟩

/-- The slope `v/u` forced by the curve equation when `W_Y(x,y) ≠ 0`. -/
noncomputable def ySlope (x y : K) : K :=
  - W.toAffine.polynomialX.evalEval x y / W.toAffine.polynomialY.evalEval x y

/-- When `W_Y(x,y) ≠ 0`, the x-direction `u` lifts to a first-order curve point. -/
lemma equation_dual_lift_of_polynomialY_ne_zero {x y u : K}
    (hxy : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    (W.toAffine.baseChange (D K)).Equation (c x + e u) (c y + e (ySlope W x y * u)) := by
  rw [equation_dual_iff]
  refine ⟨hxy, ?_⟩
  rw [ySlope]
  field_simp
  ring

/-- Uniqueness of the first-order `y` lift when `W_Y(x,y) ≠ 0`. -/
lemma equation_dual_lift_unique {x y u v : K}
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (h : (W.toAffine.baseChange (D K)).Equation (c x + e u) (c y + e v)) :
    v = ySlope W x y * u := by
  rw [equation_dual_iff] at h
  rcases h with ⟨_, hlin⟩
  rw [ySlope]
  field_simp
  linear_combination hlin

end AffineJet

end WeierstrassCurve.SEAM1

