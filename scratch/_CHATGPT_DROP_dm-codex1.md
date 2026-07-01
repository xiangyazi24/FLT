# Q3006 (dm-codex1): C10 Tate row to `shortW (A10 T) (B10 T)`

The exact same-parameter statement is **false**.  The `t` in the Tate row

```lean
tateC10_b t = t^3*(t-1)*(2*t-1)/(t^2-3*t+1)^2
tateC10_c t = -t*(t-1)*(2*t-1)/(t^2-3*t+1)
```

is not the `t` used by the short family `A10/B10`.  The required reparameterization is

```lean
p = (T - 1) / (2*T)     -- Tate-row parameter
T = 1 / (1 - 2*p)       -- short-family parameter
```

With this change, there is a clean rational variable change.

## 1. Counterexample to the same-parameter theorem

At the same parameter value `t = 2`:

```text
Tate row parameter p=2:
  tateC10_b 2 = 24
  tateC10_c 2 = 6
  after completing square and shifting the 5P root:
    A0 = 25/4
    B0 = -32
    Δ_tate = 16*B0^2*(A0^2 - 4*B0) = 2^10 * 3^5 * 11

Short family parameter T=2:
  Δ_short = Delta10 2 = 2^17 * 3^10 * 5^3
```

A rational variable change satisfies a discriminant scaling by a twelfth power of the `u`-coordinate.  The ratio

```text
Δ_short / Δ_tate = 2^7 * 3^5 * 5^3 / 11
```

is not a twelfth power in `ℚ` (nor is its reciprocal).  So

```lean
∃ C, C • tateW (tateC10_b t) (tateC10_c t) = shortW (A10 t) (B10 t)
```

is false for same `t`.

## 2. Corrected definitions

Use `T` for the short-family parameter and `p` for the Tate-row parameter.

```lean
def tateC10_shortQ (T : ℚ) : ℚ :=
  T ^ 2 - 4*T - 1

/-- Convert the short-family parameter to the Tate-row parameter. -/
def tateC10_shortToTateParam (T : ℚ) : ℚ :=
  (T - 1) / (2*T)
```

Useful closed forms:

```lean
theorem tateC10_den_shortToTateParam
    {T : ℚ} (hT : T ≠ 0) :
    tateC10_den (tateC10_shortToTateParam T) =
      - tateC10_shortQ T / (4*T^2) := by
  dsimp [tateC10_den, tateC10_shortToTateParam, tateC10_shortQ]
  field_simp [hT]
  ring

theorem tateC10_b_shortToTateParam
    {T : ℚ} (hT : T ≠ 0) (hQ : tateC10_shortQ T ≠ 0) :
    tateC10_b (tateC10_shortToTateParam T) =
      (T - 1)^3 * (T + 1) / (T * (tateC10_shortQ T)^2) := by
  have hden : tateC10_den (tateC10_shortToTateParam T) ≠ 0 := by
    rw [tateC10_den_shortToTateParam (T := T) hT]
    exact div_ne_zero (neg_ne_zero.mpr hQ)
      (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (pow_ne_zero 2 hT))
  dsimp [tateC10_b, tateC10_shortToTateParam, tateC10_shortQ]
  field_simp [hT, hQ, hden]
  ring

theorem tateC10_c_shortToTateParam
    {T : ℚ} (hT : T ≠ 0) (hQ : tateC10_shortQ T ≠ 0) :
    tateC10_c (tateC10_shortToTateParam T) =
      (T^2 - 1) / (T * tateC10_shortQ T) := by
  have hden : tateC10_den (tateC10_shortToTateParam T) ≠ 0 := by
    rw [tateC10_den_shortToTateParam (T := T) hT]
    exact div_ne_zero (neg_ne_zero.mpr hQ)
      (mul_ne_zero (by norm_num : (4 : ℚ) ≠ 0) (pow_ne_zero 2 hT))
  dsimp [tateC10_c, tateC10_shortToTateParam, tateC10_shortQ]
  field_simp [hT, hQ, hden]
  ring
```

## 3. Explicit variable change

Use the standard Mathlib convention already used in `KubertTateCommon` / N12:

```text
x_old = u^2*x_new + r
y_old = u^3*y_new + u^2*s*x_new + tau
```

Let `p = (T-1)/(2T)`, `b = tateC10_b p`, `c = tateC10_c p`, and

```lean
u   = 1 / (2*T*(T^2 - 4*T - 1))
r   = - (T - 1)^3 * (T + 1) / (4*T^2*(T^2 - 4*T - 1))
s   = (c - 1) / 2
tau = (b - r*(1 - c)) / 2
```

Equivalently, in the Tate parameter `p`:

```lean
u   = (2*p - 1)^3 / (8 * tateC10_den p)
r   = -p^3 * (p - 1) / tateC10_den p
s   = (c - 1) / 2
tau = (b - r*(1 - c)) / 2
```

Lean definition using the short parameter:

```lean
noncomputable def tateC10_paramToShortVC (T : ℚ) :
    WeierstrassCurve.VariableChange ℚ :=
  let p : ℚ := tateC10_shortToTateParam T
  let b : ℚ := tateC10_b p
  let c : ℚ := tateC10_c p
  let r0 : ℚ :=
    - (T - 1)^3 * (T + 1) / (4*T^2*tateC10_shortQ T)
  { u := 1 / (2*T*tateC10_shortQ T)
    r := r0
    s := (c - 1) / 2
    t := (b - r0 * (1 - c)) / 2 }
```

If your local `VariableChange` field is named `t` (as in N12 snippets), the definition above is correct.  If it is named `t₁`/`tau` locally, only rename that field.

## 4. Corrected theorem statement

This is the corrected version of the residual.  The old theorem with same `t` should be replaced by this.

```lean
theorem tateC10_param_to_shortW_of_tate_delta
    (T : ℚ)
    (hT : T ≠ 0)
    (hQ : tateC10_shortQ T ≠ 0)
    (hDeltaTate :
      (tateW
        (tateC10_b (tateC10_shortToTateParam T))
        (tateC10_c (tateC10_shortToTateParam T))).Δ ≠ 0) :
    Delta10 T ≠ 0 ∧
      ∃ C : WeierstrassCurve.VariableChange ℚ,
        C • tateW
          (tateC10_b (tateC10_shortToTateParam T))
          (tateC10_c (tateC10_shortToTateParam T)) =
        shortW (A10 T) (B10 T) := by
  let C := tateC10_paramToShortVC T
  have hCurve :
      C • tateW
          (tateC10_b (tateC10_shortToTateParam T))
          (tateC10_c (tateC10_shortToTateParam T)) =
        shortW (A10 T) (B10 T) := by
    -- If `ext` gives the five Weierstrass coefficients, this closes directly.
    ext <;>
      dsimp [C, tateC10_paramToShortVC, tateC10_shortToTateParam,
        tateC10_shortQ, tateC10_b, tateC10_c, tateC10_den,
        tateW, shortW, A10, B10, F10] <;>
      field_simp [hT, hQ] <;>
      ring
  refine ⟨?_, ⟨C, hCurve⟩⟩
  have hShortDelta : (shortW (A10 T) (B10 T)).Δ ≠ 0 := by
    -- Use the common/N12 variable-change discriminant wrapper if available.
    -- Typical local name from N12/common:
    --   delta_ne_zero_of_variableChange_eq
    --   tateW_delta_ne_zero_of_variableChange_eq
    --   variableChange_delta_ne_zero_of_curve_eq
    exact delta_ne_zero_of_variableChange_eq
      (W := tateW
          (tateC10_b (tateC10_shortToTateParam T))
          (tateC10_c (tateC10_shortToTateParam T)))
      (V := shortW (A10 T) (B10 T))
      (C := C) hDeltaTate hCurve
  have hDeltaEq : (shortW (A10 T) (B10 T)).Δ = Delta10 T := by
    dsimp [shortW, A10, B10, F10, Delta10]
    ring
  simpa [hDeltaEq] using hShortDelta
```

If the discriminant wrapper takes the equality in the opposite direction or requires `C.u ≠ 0`, use:

```lean
  have hCu : C.u ≠ 0 := by
    dsimp [C, tateC10_paramToShortVC, tateC10_shortQ]
    exact div_ne_zero (by norm_num : (1 : ℚ) ≠ 0)
      (mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) hT) hQ)
```

Then call your local wrapper with `hCu`.

## 5. Coefficient identities behind the proof

With `p=(T-1)/(2T)`, `Q=T^2-4T-1`, and `D=p^2-3p+1`, the key identities are:

```text
D = -Q/(4*T^2)
2*p - 1 = -1/T
b = tateC10_b p = (T-1)^3*(T+1)/(T*Q^2)
c = tateC10_c p = (T^2-1)/(T*Q)
r = -p^3*(p-1)/D = -(T-1)^3*(T+1)/(4*T^2*Q)
u = (2*p-1)^3/(8*D) = 1/(2*T*Q)
```

After completing square and shifting by the `5P` root `r`, the unscaled short coefficients are:

```text
A0 = 3*r + ((1-c)^2 - 4*b)/4
B0 = 3*r^2 + ((1-c)^2 - 4*b)*r/2 + b*(c-1)/2
```

and the scaling identities are:

```text
A0 / u^2 = A10(T)
B0 / u^4 = B10(T)
```

Those are exactly what `field_simp [hT,hQ]; ring` proves in Lean.

## 6. Sympy verification script

This is an exact rational check of the coefficient formulas and discriminant identity.

```python
import sympy as sp
T = sp.symbols('T')
Q = T**2 - 4*T - 1
p = (T - 1)/(2*T)
D = p**2 - 3*p + 1

F10 = 1 + 2*T - 5*T**2 - 5*T**4 - 2*T**5 + T**6
A10 = -2*F10
B10 = (T**2 - 1)**5 * (T**2 - 4*T - 1)
Delta10 = 4096*T**5*(T**2 + T - 1)*(T**2 - 1)**10*(T**2 - 4*T - 1)**2

b = p**3*(p - 1)*(2*p - 1)/D**2
c = -p*(p - 1)*(2*p - 1)/D

a1 = 1 - c
a2 = -b
a3 = -b
a4 = 0
a6 = 0

u = 1/(2*T*Q)
r = - (T - 1)**3 * (T + 1)/(4*T**2*Q)
s = (c - 1)/2
tau = (b - r*(1 - c))/2

# Mathlib/standard generalized Weierstrass change:
# x_old = u^2*x_new + r
# y_old = u^3*y_new + u^2*s*x_new + tau
a1p = (a1 + 2*s)/u
a2p = (a2 - s*a1 + 3*r - s**2)/u**2
a3p = (a3 + r*a1 + 2*tau)/u**3
a4p = (a4 - s*a3 + 2*r*a2 - (tau + r*s)*a1 + 3*r**2 - 2*s*tau)/u**4
a6p = (a6 + r*a4 + r**2*a2 + r**3 - tau*a3 - tau**2 - r*tau*a1)/u**6

assert sp.factor(D + Q/(4*T**2)) == 0
assert sp.factor(2*p - 1 + 1/T) == 0
assert sp.factor(b - (T-1)**3*(T+1)/(T*Q**2)) == 0
assert sp.factor(c - (T**2-1)/(T*Q)) == 0
assert sp.factor(a1p) == 0
assert sp.factor(a2p - A10) == 0
assert sp.factor(a3p) == 0
assert sp.factor(a4p - B10) == 0
assert sp.factor(a6p) == 0

Delta_short = 16*B10**2*(A10**2 - 4*B10)
assert sp.factor(Delta_short - Delta10) == 0

# Same-parameter counterexample at t=2
p2 = sp.Rational(2)
D2 = p2**2 - 3*p2 + 1
b2 = p2**3*(p2-1)*(2*p2-1)/D2**2
c2 = -p2*(p2-1)*(2*p2-1)/D2
r2 = -p2**3*(p2-1)/D2
A0_2 = 3*r2 + ((1-c2)**2 - 4*b2)/4
B0_2 = 3*r2**2 + ((1-c2)**2 - 4*b2)*r2/2 + b2*(c2-1)/2
Delta_tate_2 = sp.factor(16*B0_2**2*(A0_2**2 - 4*B0_2))
Delta_short_2 = sp.factor(Delta10.subs(T, 2))
print(b2, c2, A0_2, B0_2)
print(sp.factor(Delta_tate_2), sp.factor(Delta_short_2), sp.factor(Delta_short_2/Delta_tate_2))
# Output ratio: 2^7 * 3^5 * 5^3 / 11, not a 12th power.
```

## 7. Denominators/exclusions

For the corrected theorem, add these hypotheses explicitly:

```lean
hT : T ≠ 0
hQ : T^2 - 4*T - 1 ≠ 0
```

They imply the Tate denominator for `p=(T-1)/(2T)` is nonzero.  The remaining short discriminant factors

```text
T^2 - 1
T^2 + T - 1
```

should not be assumed from `hT,hQ`; they follow from `hDeltaTate` via the variable-change/discriminant equality.  This is why the honest theorem should keep `hDeltaTate` as an input and derive `Delta10 T ≠ 0` after proving the curve equality.
