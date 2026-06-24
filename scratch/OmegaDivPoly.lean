/-
  scratch/OmegaDivPoly.lean
  Three atoms toward the ω-division-polynomial bridge.

  ATOM 0: Bivariate evaluation helpers (already in Mathlib as Polynomial.evalEval)
  ATOM 1: ψ_{2n}/ψ_n quotient via complEDS₂
  ATOM 2: ω_n definition and normalization identity (char ≠ 2)
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Mathlib.Tactic

@[expose] public section

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate

/-! ## ATOM 0: Bivariate evaluation

Mathlib already provides `Polynomial.evalEval : R → R → R[X][Y] → R`
with `evalEval x y p = eval x (eval (C y) p)`.  We re-export nothing here;
downstream files should `open Polynomial` and use `p.evalEval x y` directly.
-/

-- Confirm Mathlib's evalEval is accessible.
#check @Polynomial.evalEval  -- R → R → R[X][Y] → R

/-! ## ATOM 1: ψ_{2n} / ψ_n quotient -/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The complement factor witnessing `ψ_n ∣ ψ_{2n}` in `R[X][Y]`.
Defined as `complEDS₂ ψ₂ (C Ψ₃) (C preΨ₄) n`, so that
`W.ψ n * W.ψTwoMulQuot n = W.ψ (2 * n)`. -/
noncomputable def ψTwoMulQuot (n : ℤ) : R[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

/-- `ψ_n` times its 2-complement equals `ψ_{2n}`. -/
theorem ψ_mul_ψTwoMulQuot (n : ℤ) :
    W.ψ n * W.ψTwoMulQuot n = W.ψ (2 * n) := by
  simp only [WeierstrassCurve.ψ, ψTwoMulQuot]
  exact normEDS_mul_complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

@[simp]
theorem ψTwoMulQuot_zero : W.ψTwoMulQuot 0 = 2 := by
  simp [ψTwoMulQuot]

@[simp]
theorem ψTwoMulQuot_one : W.ψTwoMulQuot 1 = W.ψ₂ := by
  simp [ψTwoMulQuot]

@[simp]
theorem ψTwoMulQuot_neg (n : ℤ) : W.ψTwoMulQuot (-n) = W.ψTwoMulQuot n := by
  simp [ψTwoMulQuot]

/-! ## ATOM 2: ω_n definition (char ≠ 2 prototype) -/

/-- The division polynomial `ω_n ∈ R[X][Y]`, defined with `Invertible (2 : R)`. -/
noncomputable def ωProto [Invertible (2 : R)] (n : ℤ) : R[X][Y] :=
  C (C (⅟(2 : R))) * (W.ψTwoMulQuot n -
    W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2))

/-- The "cleared" normalization identity:
`C(C 2) * ψ_n * ω_n = ψ_{2n} - ψ_n² * (C(C a₁) * φ_n + C(C a₃) * ψ_n²)`. -/
theorem two_mul_ψ_mul_ωProto [Invertible (2 : R)] (n : ℤ) :
    C (C (2 : R)) * W.ψ n * W.ωProto n =
      W.ψ (2 * n) - W.ψ n ^ 2 * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2) := by
  unfold ωProto
  rw [← ψ_mul_ψTwoMulQuot]
  -- After ring_nf, each term has a factor C(C 2) * C(C ⅟2) that we can cancel.
  -- Strategy: use `mul_comm` + `mul_assoc` to isolate, then use the cancellation.
  have hcancel : C (C (2 : R)) * C (C (⅟(2 : R))) = (1 : R[X][Y]) := by
    rw [← map_mul, ← map_mul, mul_invOf_self, map_one, map_one]
  -- Pull out the common CC-factor using linear_combination or direct manipulation.
  -- We want:
  --   CC 2 * ψ * (CC ⅟2 * (Q - ψ * stuff))
  -- = CC 2 * CC ⅟2 * ψ * (Q - ψ * stuff)
  -- = 1 * ψ * (Q - ψ * stuff)
  -- = ψ * Q - ψ² * stuff
  calc C (C (2 : R)) * W.ψ n * (C (C (⅟(2 : R))) *
      (W.ψTwoMulQuot n - W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2)))
      = C (C (2 : R)) * C (C (⅟(2 : R))) * W.ψ n *
        (W.ψTwoMulQuot n - W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2)) := by ring
    _ = 1 * W.ψ n *
        (W.ψTwoMulQuot n - W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2)) := by
        rw [hcancel]
    _ = W.ψ n * W.ψTwoMulQuot n -
        W.ψ n ^ 2 * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2) := by ring

end WeierstrassCurve
