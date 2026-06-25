import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic

open WeierstrassCurve.Jacobian

theorem omega_ne_zero_of_phi_ne_zero_at_Z_zero
    {K : Type*} [Field K] (W : WeierstrassCurve K)
    {φ_val ω_val : K}
    (hEq : W.toJacobian.Equation ![φ_val, ω_val, 0])
    (hφ : φ_val ≠ 0) :
    ω_val ≠ 0 := by
  rw [equation_of_Z_eq_zero (show (![φ_val, ω_val, 0] : Fin 3 → K) 2 = 0 from rfl)] at hEq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hEq
  -- hEq : ω_val ^ 2 = φ_val ^ 3
  intro h
  rw [h, zero_pow (by norm_num : 2 ≠ 0), eq_comm, pow_eq_zero_iff (by norm_num : 3 ≠ 0)] at hEq
  exact hφ hEq
