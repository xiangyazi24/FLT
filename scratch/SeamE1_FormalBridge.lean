module

public import scratch.SeamE1_Core
public import scratch.SeamE1_FormalNsmul

/-! # SEAM1 / E1 — Formal Bridge: dual root → tangent zero

The bridge from `hrootε` (preΨ' vanishes at dual x) to `TangentO.nsmul₁ n 1 = 0`.

## Proven in this file (0 sorry, 0 custom axiom)

* `preΨ'_dual_root_extract` — dual root → value root + derivative root
* `preΨ'_eval_zero_of_dual_root` / `preΨ'_deriv_eval_zero_of_dual_root` — projections
* `Φ_eval_at_preΨ'_root` — Φ_n simplification at a root of preΨ'_{m+1}
* `Ψ₂Sq_ne_zero_of_polynomialY_ne_zero` — Ψ₂Sq(x) ≠ 0 from non-2-torsion
* `dual_root_implies_tangent_zero_of_deriv_ne_zero` — assembly conditional on
  the derivative being nonzero at the root (the remaining gap)

## The single remaining sorry

`preΨ'_deriv_ne_zero_at_nontorsion_root` — at a root of preΨ'_n on a non-2-torsion
curve point with (n:K) ≠ 0, the derivative (preΨ'_n)'(x) ≠ 0.

This is the irreducible mathematical content of Bridge 2. It encodes the formal-group
tangent fact [n]'(0) = n. Three known proof routes:

1. **Invariant differential** [n]*ω = n·ω gives, at an n-torsion point, a relationship
   between the total derivative of ψ_n on the curve and the scalar n. The total derivative
   equals (preΨ'_n)' for odd n, and (preΨ'_n)' · polY for even n. This requires building
   the pullback formula from the Φ_n/ψ_n² x-coordinate formula.

2. **Formal group**: construct `W.formalGroup : FormalGroup K`, prove the formal [n]
   map corresponds to the division polynomial multiplication, and apply
   `formalNsmul_coeff_one` (already proven in SeamE1_FormalNsmul.lean).

3. **Direct separability**: prove `IsCoprime (preΨ'_n) (derivative (preΨ'_n))` by EDS
   recurrence induction, extending the n=3 Bezout certificate (already proven in
   KeystoneSeparability.lean, commit 7a383c3). -/

@[expose] public section

open Polynomial

namespace WeierstrassCurve.SEAM1

variable {K : Type*} [Field K]

/-! ## Step 1: Extract root conditions from dual root -/

/-- A dual root of `preΨ' n` at `xε x = x + ε` gives both a value root and a derivative root. -/
theorem preΨ'_dual_root_extract {W : WeierstrassCurve K} {n : ℕ} {x : K}
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    (W.preΨ' n).eval x = 0 ∧ (derivative (W.preΨ' n)).eval x = 0 := by
  have h := SeamE1.eval_dualNumber (W.preΨ' n) x 1
  simp only [MultipleRootBridge.xε, Dual.c, Dual.e] at hrootε
  rw [hrootε] at h
  rw [TrivSqZeroExt.ext_iff] at h
  simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, add_zero, zero_add] at h
  constructor
  · exact h.1.symm
  · have h2 := h.2.symm
    rwa [one_mul] at h2

/-- The value-root half of the extraction. -/
theorem preΨ'_eval_zero_of_dual_root {W : WeierstrassCurve K} {n : ℕ} {x : K}
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    (W.preΨ' n).eval x = 0 :=
  (preΨ'_dual_root_extract hrootε).1

/-- The derivative-root half of the extraction. -/
theorem preΨ'_deriv_eval_zero_of_dual_root {W : WeierstrassCurve K} {n : ℕ} {x : K}
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    (derivative (W.preΨ' n)).eval x = 0 :=
  (preΨ'_dual_root_extract hrootε).2

/-! ## Step 2: Φ_n at a root of preΨ'_n -/

/-- At a root of `preΨ'(m+1)`, the Φ-formula simplifies: the `X · preΨ'^2` term drops. -/
theorem Φ_eval_at_preΨ'_root (W : WeierstrassCurve K) {m : ℕ} {x : K}
    (hroot : (W.preΨ' (m + 1)).eval x = 0) :
    (W.Φ (↑m + 1 : ℤ)).eval x =
      - (W.preΨ' (m + 2)).eval x * (W.preΨ' m).eval x *
        (if Even m then (W.Ψ₂Sq).eval x else 1) := by
  have h := congr_arg (Polynomial.eval x) (W.Φ_ofNat m)
  simp only [eval_sub, eval_mul, eval_pow, eval_X] at h
  rw [hroot, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_sub] at h
  rw [h]
  simp only [apply_ite (Polynomial.eval x), eval_one]
  ring

/-! ## Step 3: Ψ₂Sq from non-2-torsion -/

/-- `Ψ₂Sq(x) ≠ 0` from the non-2-torsion condition. On the curve,
`(polynomialY.evalEval x y)² = Ψ₂Sq(x)`, so `Ψ₂Sq(x) = 0` forces `polY = 0`. -/
theorem Ψ₂Sq_ne_zero_of_polynomialY_ne_zero (W : WeierstrassCurve K) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  intro h0
  apply hY
  have hsq : (W.toAffine.polynomialY.evalEval x y) ^ 2 = W.Ψ₂Sq.eval x := by
    rw [WeierstrassCurve.Affine.evalEval_polynomialY, WeierstrassCurve.Ψ₂Sq]
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    have hEq := hcurve
    rw [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial] at hEq
    linear_combination 4 * hEq
  rw [h0] at hsq
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hsq

/-! ## Step 4: The remaining sorry — derivative nonvanishing

This is the irreducible mathematical content: at a root of `preΨ'_n` on a non-2-torsion
curve point, the derivative is nonzero when `(n:K) ≠ 0`.

This encodes the formal group fact `[n]'(0) = n ≠ 0`. -/

/-- **The derivative nonvanishing**: at a root of `preΨ'_n` on a non-2-torsion curve point
with `(n:K) ≠ 0`, the polynomial derivative `(preΨ'_n)'(x)` is nonzero.

This is the content of `[n]*ω = n·ω` for the invariant differential, restricted to
n-torsion points. Equivalently, it says `IsCoprime (preΨ'_n) (derivative (preΨ'_n))`.

STATUS:
- n=3: PROVEN via Bezout certificate in KeystoneSeparability.Psi3_separable (0 axiom)
- n=4: cofactors computed (commit 66dea94, Res = 2⁹·Δ⁵)
- General n: requires EDS induction or invariant differential infrastructure -/
theorem preΨ'_deriv_ne_zero_at_nontorsion_root [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hroot : (W.preΨ' n).eval x = 0) :
    (derivative (W.preΨ' n)).eval x ≠ 0 := sorry

/-! ## Step 5: Assembly — conditional proof of dual_root_implies_tangent_zero

The assembly is clean: extract both root conditions from `hrootε`, then get a
contradiction from `hroot ∧ hderiv = 0` vs the derivative nonvanishing. -/

/-- The proof of `dual_root_implies_tangent_zero` conditional on
`preΨ'_deriv_ne_zero_at_nontorsion_root`. The conclusion `nsmul₁ n 1 = 0`
equals `(n:K) = 0` (by `nsmul₁_eq_natCast_mul`), which contradicts `hn`. -/
theorem dual_root_implies_tangent_zero_assembled [IsAlgClosed K] (W : WeierstrassCurve K)
    [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y) (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ n (1 : K) = 0 := by
  -- Extract the value root and derivative root from the dual root
  have hroot := preΨ'_eval_zero_of_dual_root hrootε
  have hderiv := preΨ'_deriv_eval_zero_of_dual_root hrootε
  -- The derivative should be nonzero (the content of the sorry)
  have hne := preΨ'_deriv_ne_zero_at_nontorsion_root W hn hcurve hY hroot
  -- Contradiction: hderiv says it's zero, hne says it's nonzero
  exact absurd hderiv hne

end WeierstrassCurve.SEAM1
