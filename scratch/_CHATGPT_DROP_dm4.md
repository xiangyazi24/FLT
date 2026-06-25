# Q260 (dm4): proving `ωₙ(P) ≠ 0` from the Jacobian equation at `Z = 0`

## Exact Mathlib API

The Jacobian-coordinate equation lives in

```lean
WeierstrassCurve.Jacobian.Equation
```

and is a predicate on a `Fin 3 → R` representative:

```lean
W'.Equation P
```

where `W' : WeierstrassCurve.Jacobian R` and `P : Fin 3 → R`.

If your original curve is `W : WeierstrassCurve k`, use the Jacobian-coordinate conversion:

```lean
W.toJacobian.Equation (![φ, ω, 0] : Fin 3 → k)
```

The exact lemma for reducing the equation at `Z = 0` is:

```lean
WeierstrassCurve.Jacobian.equation_of_Z_eq_zero
```

with shape:

```lean
W'.Equation P ↔ P 1 ^ 2 = P 0 ^ 3
```

under the hypothesis `P 2 = 0`.  So yes: at `Z = 0`, Mathlib’s Jacobian equation reduces to `Y² = X³`.

There is also a direct Mathlib lemma if you have nonsingularity of the Jacobian representative, not just the equation:

```lean
WeierstrassCurve.Jacobian.Y_ne_zero_of_Z_eq_zero
```

It proves `P 1 ≠ 0` from `W'.Nonsingular P` and `P 2 = 0`.  In your stated use, you only mentioned the equation plus `φ ≠ 0`, so the first lemma below is the equation-only proof.

## Reusable equation-only proof

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic
import Mathlib.Tactic

noncomputable section

open Matrix

namespace WeierstrassCurve

variable {k : Type*} [Field k]

/-- If a Jacobian representative lies on the curve, has `Z = 0`, and has nonzero
`X`, then its `Y` coordinate is nonzero.  This uses only the equation at infinity,
not nonsingularity. -/
lemma Jacobian.Y_ne_zero_of_equation_of_Z_eq_zero_of_X_ne_zero
    (W' : WeierstrassCurve.Jacobian k) {P : Fin 3 → k}
    (hEq : W'.Equation P) (hZ : P 2 = 0) (hX : P 0 ≠ 0) :
    P 1 ≠ 0 := by
  have hY2X3 : P 1 ^ 2 = P 0 ^ 3 :=
    (WeierstrassCurve.Jacobian.equation_of_Z_eq_zero
      (W' := W') (P := P) hZ).mp hEq
  intro hY
  have hX3_zero : P 0 ^ 3 = 0 := by
    rw [← hY2X3]
    simp [hY]
  exact (pow_ne_zero 3 hX) hX3_zero

/-- Specialized `[φ : ω : 0]` form for an ordinary Weierstrass curve converted to
Jacobian coordinates. -/
lemma omega_ne_zero_of_phi_ne_zero_of_jacobian_equation_at_infinity
    (W : WeierstrassCurve k) {φ ω : k}
    (hEq : W.toJacobian.Equation (![φ, ω, 0] : Fin 3 → k))
    (hφ : φ ≠ 0) :
    ω ≠ 0 := by
  simpa using
    (Jacobian.Y_ne_zero_of_equation_of_Z_eq_zero_of_X_ne_zero
      (W' := W.toJacobian)
      (P := (![φ, ω, 0] : Fin 3 → k))
      hEq
      (by simp)
      (by simpa using hφ))

end WeierstrassCurve
```

This is the proof you want for the ATOM 5 step once you have:

```lean
hφ : φ ≠ 0
hEq : W.toJacobian.Equation (![φ, ω, 0] : Fin 3 → k)
```

Then simply write:

```lean
have hω : ω ≠ 0 := by
  exact WeierstrassCurve.omega_ne_zero_of_phi_ne_zero_of_jacobian_equation_at_infinity
    (W := W) (φ := φ) (ω := ω) hEq hφ
```

## If you prefer to see the explicit `Y² = X³` step

The core reduction can also be written inline:

```lean
have hY2X3 : ω ^ 2 = φ ^ 3 := by
  have h :=
    (WeierstrassCurve.Jacobian.equation_of_Z_eq_zero
      (W' := W.toJacobian)
      (P := (![φ, ω, 0] : Fin 3 → k))
      (by simp)).mp hEq
  simpa using h

have hω : ω ≠ 0 := by
  intro hω0
  have hφ3_zero : φ ^ 3 = 0 := by
    rw [← hY2X3]
    simp [hω0]
  exact (pow_ne_zero 3 hφ) hφ3_zero
```

This avoids `pow_eq_zero_iff`; `pow_ne_zero 3 hφ` is usually the most robust way to close the final field-domain contradiction.

## Direct proof if you have `Nonsingular`

If your projective representative is already packaged as a nonsingular Jacobian representative, Mathlib has the exact lemma:

```lean
lemma omega_ne_zero_of_jacobian_nonsingular_at_infinity
    (W : WeierstrassCurve k) {φ ω : k}
    (hP : W.toJacobian.Nonsingular (![φ, ω, 0] : Fin 3 → k)) :
    ω ≠ 0 := by
  simpa using
    (WeierstrassCurve.Jacobian.Y_ne_zero_of_Z_eq_zero
      (W' := W.toJacobian)
      (P := (![φ, ω, 0] : Fin 3 → k))
      hP
      (by simp))
```

This version does not need `φ ≠ 0` as a separate hypothesis because nonsingularity at `Z = 0` already forces both `X` and `Y` nonzero in Mathlib.

## How this plugs into the division-polynomial setting

For your torsion point, instantiate:

```lean
φ := (W.Φ n).eval x
ω := omegaEval   -- whatever name you use for the evaluated ωₙ(P)
```

and use your already-proved ATOM 4 statement:

```lean
have hφ : (W.Φ n).eval x ≠ 0 := by
  -- from `ψₙ(P)=0`, `Ψ₂Sq(x)≠0`, no-adjacent-preΨ-zero, and the definition of `Φ`
  exact hphi
```

Then get the Jacobian equation from the theorem saying the projective division-polynomial representative lies on the Jacobian curve:

```lean
have hEq :
    W.toJacobian.Equation
      (![(W.Φ n).eval x, omegaEval, (W.ψ n).evalXY x y] : Fin 3 → k) := by
  -- your projective-representative-on-curve theorem
  exact hJac
```

At an `n`-torsion point, rewrite the third coordinate to zero:

```lean
have hEq0 :
    W.toJacobian.Equation
      (![(W.Φ n).eval x, omegaEval, 0] : Fin 3 → k) := by
  simpa [hψ] using hEq
```

and conclude:

```lean
have hω : omegaEval ≠ 0 := by
  exact WeierstrassCurve.omega_ne_zero_of_phi_ne_zero_of_jacobian_equation_at_infinity
    (W := W)
    (φ := (W.Φ n).eval x)
    (ω := omegaEval)
    hEq0
    hφ
```

The important API answers are therefore:

* equation predicate: `W.toJacobian.Equation (![φ, ω, 0] : Fin 3 → k)`;
* reduction at infinity: `WeierstrassCurve.Jacobian.equation_of_Z_eq_zero`;
* nonzero conclusion from a nonsingular representative, if available: `WeierstrassCurve.Jacobian.Y_ne_zero_of_Z_eq_zero`;
* final field-domain contradiction: `pow_ne_zero 3 hφ` applied to `φ ^ 3 = 0`.
