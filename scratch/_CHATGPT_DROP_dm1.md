# Q674 (dm1): coefficient of `negAddY` at `(3,0)`

```lean
import scratch.FormalGroupW

open MvPowerSeries Finsupp WeierstrassCurve

variable {R : Type*} [CommRing R]

set_option maxHeartbeats 0 in
theorem coeff_e30_negAddY (W : WeierstrassCurve R) :
    coeff (single (0 : Fin 2) 3)
      ((W.map (C (σ := Fin 2))).toProjective.negAddY
        (W.formalPointMv 0) (W.formalPointMv 1)) = -1 := by
  classical
  -- Expose Mathlib's 18-term projective formula, then substitute the two formal
  -- points `P = [X₀,-1,w(X₀)]` and `Q = [X₁,-1,w(X₁)]`.
  unfold WeierstrassCurve.Projective.negAddY
  simp only [
    WeierstrassCurve.formalPointMv_x,
    WeierstrassCurve.formalPointMv_y,
    WeierstrassCurve.formalPointMv_z,
    WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆,
    one_pow,
    neg_mul,
    mul_neg,
    neg_neg,
    one_mul,
    mul_one]
  -- Normalize the resulting polynomial in the commutative power-series ring.  The
  -- surviving summand is `-(w(X₀))`; all other summands are normalized so that
  -- either an `X₁`-power is visible, or a left monomial of `X₀`-degree at least `4`
  -- is visible.
  ring_nf
  -- The two project-local coefficient lemmas now do the computation:
  -- * every visible positive `X₁`-power has `(3,0)` coefficient zero;
  -- * `[X₀^3] w(X₀) = 1`.
  -- The remaining degree reasons are closed by `coeff_monomial_mul`, `coeff_C_mul`,
  -- and the normal form of `X^n` as a monomial.
  simp [
    coeff_single0_X1_pow_mul,
    coeff_e30_w0,
    MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_mul_C,
    mul_assoc,
    mul_left_comm,
    mul_comm]
```
