# Q511 (dm1): final divisibility strategy for `(X₀-X₁)^3 ∣ formalAddXYZ`

## Executive answer

Do **not** make the final proof depend on UFD/coprimality in `MvPowerSeries`, and do **not** use global truncation/universality as the main Lean route.  The cleaner route is:

1. Split off the forced zero of the formal parameter solution
   ```lean
   w(T) = T^3 * u(T),       u(0) = 1.
   ```
   Thus `u`, and hence `u₀*u₁`, is a unit after substitution into the two-variable power-series ring.

2. Replace the bad numerator
   ```lean
   delta = X₀*w₁ - X₁*w₀
   ```
   by the better primitive diagonal-difference factor
   ```lean
   beta = X₁^2*u₁ - X₀^2*u₀.
   ```
   Then
   ```lean
   delta = X₀ * X₁ * beta.
   ```
   The factor `X₀^3*X₁^3` that appears in `delta^3` is therefore exactly the same forced monomial factor coming from `w₀*w₁`; it should be cancelled/removed **before** the final divisibility argument, not by proving `(X₀-X₁)` coprime to `X₀X₁` inside `MvPowerSeries`.

3. Prove the diagonal factor of `beta` by applying the already-proved diagonal-difference lemma to
   ```lean
   g(T) = T^2 * u(T).
   ```
   If `d = X₀ - X₁`, then
   ```lean
   g(X₀) - g(X₁) = d * dividedDiff g,
   beta = g(X₁) - g(X₀) = d * (-dividedDiff g).
   ```
   So define
   ```lean
   betaQuot := - dividedDiff (T^2 * u)
   ```
   and prove
   ```lean
   beta = d * betaQuot.
   ```

4. For the three add coordinates, prove finite **normalized algebraic certificates** after the substitution
   ```lean
   wᵢ = Xᵢ^3 * uᵢ
   beta = d * betaQuot
   ```
   and after using the `u`-form of the curve equation.  This gives explicit identities
   ```lean
   formalAddX = d^3 * QX
   formalAddY = d^3 * QY
   formalAddZ = d^3 * QZ
   ```
   in `MvPowerSeries (Fin 2) K`.  The quotients `QX QY QZ` should be finite expressions in the substituted series `X₀`, `X₁`, `u₀`, `u₁`, `betaQuot`, and unit inverses of `u₀*u₁` where needed.

This route uses coefficientwise constructions only for two small generic atoms: `w = T^3*u` and the diagonal-difference quotient.  The final `formalAddXYZ` divisibility should be proved by finite `ring_nf` certificates, not coefficient-by-coefficient construction of the whole quotient.

---

## Why the proposed cancellation route is the wrong center of gravity

The chain

```lean
formalAddZ * (w₀*w₁) = delta^3
(X₀-X₁)^3 ∣ delta^3
```

only gives

```lean
(X₀-X₁)^3 ∣ formalAddZ * w₀*w₁.
```

To conclude divisibility of `formalAddZ`, one would need to remove

```lean
w₀*w₁ = X₀^3 * X₁^3 * u₀ * u₁.
```

Removing `u₀*u₁` is fine because it is a unit.  Removing `X₀^3*X₁^3` by coprimality with `(X₀-X₁)^3` is mathematically true over a field, but it is the wrong Lean problem:

* it drags in UFD/GCD/coprime infrastructure for `MvPowerSeries`, which is likely incomplete or painful;
* it is overkill for a local formal-group construction;
* it may force stronger assumptions such as domain/field when the surrounding code wants `CommRing`-level polynomial identities.

Instead, remove the monomial factor structurally:

```lean
w₀ = X₀^3*u₀,
w₁ = X₁^3*u₁,
delta = X₀*X₁*beta.
```

Then the `Z` coordinate should be normalized to the unit-denominator identity

```lean
(formalAddZ) * (u₀*u₁) = beta^3
```

or equivalently

```lean
formalAddZ = beta^3 * (u₀*u₁)⁻¹.
```

After `beta = d*betaQuot`, divisibility is immediate:

```lean
formalAddZ = d^3 * (betaQuot^3 * (u₀*u₁)⁻¹).
```

If the current lemma is only named/proved as

```lean
formalAddZ_mul_ww : formalAddZ * (w₀*w₁) = delta^3
```

then upgrade it to the normalized lemma above.  The upgrade should be proved by unfolding `formalAddZ` and doing a finite polynomial/ring proof after substituting `wᵢ = Xᵢ^3*uᵢ`; do not try to perform nonunit cancellation inside `MvPowerSeries`.

---

## The key finite abstraction: use `u`, not truncations of `w`

The raw `Projective.addXYZ` formulas are finite polynomials in the coordinates of the two points.  The only infinite object is the solution `w(T)`.  Therefore do not truncate `w(T)` to degree `N` and then try to pass to the limit.  Instead, abstract the infinite tail by a single power series `u`:

```lean
w(T) = T^3 * u(T).
```

The Weierstrass equation for

```lean
P(T) = [T : -1 : w(T)]
```

is

```lean
w = T^3 + a₁*T*w + a₂*T^2*w + a₃*w^2 + a₄*T*w^2 + a₆*w^3.
```

After `w = T^3*u`, this becomes the unit-tail equation

```lean
u = 1
    + a₁*T*u
    + a₂*T^2*u
    + a₃*T^3*u^2
    + a₄*T^4*u^2
    + a₆*T^6*u^3.
```

So in the two-variable ring define

```lean
u₀ := u(X₀)
u₁ := u(X₁)
H₀ := u₀ - (1 + a₁*X₀*u₀ + a₂*X₀^2*u₀
              + a₃*X₀^3*u₀^2 + a₄*X₀^4*u₀^2 + a₆*X₀^6*u₀^3)
H₁ := u₁ - (1 + a₁*X₁*u₁ + a₂*X₁^2*u₁
              + a₃*X₁^3*u₁^2 + a₄*X₁^4*u₁^2 + a₆*X₁^6*u₁^3).
```

In the actual power-series instantiation, `H₀ = 0` and `H₁ = 0`.

For each coordinate, ask CAS/Sage to produce a finite polynomial certificate of the following form:

```lean
rawCoord_after_w_eq_X3u
  = d^3 * Q
    + A * (beta - d*betaQuot)
    + B₀ * H₀
    + B₁ * H₁
```

where

```lean
d     = X₀ - X₁
beta  = X₁^2*u₁ - X₀^2*u₀.
```

Then Lean proves the certificate by `ring_nf` in an arbitrary `CommRing`.  After instantiating the actual power series, the last three terms vanish, giving

```lean
rawCoord_after_w_eq_X3u = d^3 * Q.
```

This is the right form of “universality”: a finite polynomial certificate in abstract variables, reflected by `ring_nf`.  It is **not** a truncation-to-degree-`N` argument.

---

## Minimal Lean atoms

### Atom A: split `w = T^3*u`

Define the tail by coefficients:

```lean
noncomputable def wTail3 (w : K⟦T⟧) : K⟦T⟧ :=
  fun n => PowerSeries.coeff (n + 3) w
```

Prove coefficientwise:

```lean
lemma w_eq_X_pow_three_mul_tail3
    (h0 : coeff 0 w = 0)
    (h1 : coeff 1 w = 0)
    (h2 : coeff 2 w = 0) :
    w = PowerSeries.X ^ 3 * wTail3 w := by
  ext n
  -- split `n < 3` / `n = k+3`; use coefficient formula for `X^3 * _`.
```

For the formal Weierstrass solution, prove

```lean
lemma coeff_zero_tail3 : coeff 0 (wTail3 w) = 1 := ...
lemma isUnit_tail3 : IsUnit (wTail3 w) := ...
```

and after substitution:

```lean
lemma isUnit_u0 : IsUnit u₀ := ...
lemma isUnit_u1 : IsUnit u₁ := ...
lemma isUnit_u0_mul_u1 : IsUnit (u₀*u₁) := ...
```

### Atom B: diagonal-difference quotient

Use the already-established quotient:

```lean
def dividedDiff (f : K⟦T⟧) : MvPowerSeries (Fin 2) K :=
  fun e => PowerSeries.coeff (e 0 + e 1 + 1) f
```

with theorem

```lean
lemma subst_X0_subst_X1_eq_d_mul_dividedDiff (f : K⟦T⟧) :
    subst0 f - subst1 f = (X₀ - X₁) * dividedDiff f := ...
```

Apply this to

```lean
g = PowerSeries.X^2 * u.
```

Then

```lean
beta = subst1 g - subst0 g
     = (X₀ - X₁) * (-(dividedDiff g)).
```

Set

```lean
def betaQuot : MvPowerSeries (Fin 2) K :=
  - dividedDiff (PowerSeries.X^2 * u)
```

and prove

```lean
lemma beta_eq_d_mul_betaQuot :
    beta = (X₀ - X₁) * betaQuot := by
  unfold beta betaQuot
  have h := subst_X0_subst_X1_eq_d_mul_dividedDiff (PowerSeries.X^2 * u)
  -- rearrange signs.
```

### Atom C: normalized `Z` coordinate

Do not stop at

```lean
formalAddZ * (w₀*w₁) = delta^3.
```

Prove the stronger normalized form:

```lean
lemma formalAddZ_mul_u0u1_eq_beta_cube :
    formalAddZ * (u₀*u₁) = beta^3 := by
  -- unfold `formalAddZ`, `w₀`, `w₁`, `u₀`, `u₁`, `beta`;
  -- use the finite polynomial certificate / `ring_nf`.
```

Then define the quotient using the unit inverse:

```lean
noncomputable def QZ : MvPowerSeries (Fin 2) K :=
  betaQuot^3 * ↑((isUnit_u0_mul_u1.unit)⁻¹)
```

and prove

```lean
lemma formalAddZ_eq_d_cube_mul_QZ :
    formalAddZ = (X₀ - X₁)^3 * QZ := by
  have hbeta := beta_eq_d_mul_betaQuot
  have hZ := formalAddZ_mul_u0u1_eq_beta_cube
  -- multiply/cancel only by the unit `u₀*u₁`; rewrite `beta = d*betaQuot`; ring.
```

No coprimality with `X₀` or `X₁` appears.

### Atom D: normalized `X` and `Y` coordinates

For `X` and `Y`, use the same certificate pattern.  Do not attempt a coefficientwise quotient of the full coordinate.  Instead generate explicit algebraic certificates:

```lean
lemma formalAddX_factor_certificate :
    rawAddX_after_w_eq_X3u
      = d^3 * QX
        + AX * (beta - d*betaQuot)
        + BX0 * H₀
        + BX1 * H₁ := by
  ring_nf

lemma formalAddY_factor_certificate :
    rawAddY_after_w_eq_X3u
      = d^3 * QY
        + AY * (beta - d*betaQuot)
        + BY0 * H₀
        + BY1 * H₁ := by
  ring_nf
```

After instantiating actual `u₀,u₁`, `H₀ = H₁ = 0`; after Atom B, `beta - d*betaQuot = 0`; hence:

```lean
lemma formalAddX_eq_d_cube_mul_QX :
    formalAddX = d^3 * QX := ...

lemma formalAddY_eq_d_cube_mul_QY :
    formalAddY = d^3 * QY := ...
```

Finally:

```lean
theorem d_cube_dvd_formalAddXYZ :
    d^3 ∣ formalAddX ∧ d^3 ∣ formalAddY ∧ d^3 ∣ formalAddZ := by
  exact ⟨⟨QX, formalAddX_eq_d_cube_mul_QX.symm⟩,
         ⟨QY, formalAddY_eq_d_cube_mul_QY.symm⟩,
         ⟨QZ, formalAddZ_eq_d_cube_mul_QZ.symm⟩⟩
```

Adjust the `.symm` direction depending on the exact statement orientation.

---

## Answer to the coefficient-by-coefficient quotient idea

Yes, one can construct the quotient by `(X₀-X₁)^3` coefficient-by-coefficient, but it is not the clean final strategy.

For a single diagonal difference `f(X₀)-f(X₁)`, coefficientwise construction is excellent because the quotient has the closed form

```lean
coeff (i,j) = coeff f (i+j+1).
```

For an arbitrary coordinate such as `formalAddY`, coefficientwise construction means solving a two-variable recurrence for the quotient and proving the necessary compatibility conditions.  Conceptually, the clean way to do that is to change variables

```lean
D = X₀ - X₁,
S = X₁
```

and prove that the coefficients of `D^0`, `D^1`, and `D^2` vanish.  But implementing the triangular substitution equivalence

```lean
K⟦X₀,X₁⟧ ≃ K⟦D,S⟧
```

is a larger API project than the present divisibility lemma.

So the recommended division of labor is:

* coefficientwise quotient for generic atoms: `w = T^3*u` and `f(X₀)-f(X₁)`;
* finite `ring_nf` certificates for the actual `formalAddX/Y/Z` coordinates.

This keeps the final proof algebraic, local, and robust over `CommRing`.

---

## Practical CAS instructions

Generate certificates over the polynomial ring

```text
Z[a1,a2,a3,a4,a6,x0,x1,u0,u1,bq]
```

with

```text
d    = x0 - x1
beta = x1^2*u1 - x0^2*u0
H0   = u0 - (1 + a1*x0*u0 + a2*x0^2*u0
              + a3*x0^3*u0^2 + a4*x0^4*u0^2 + a6*x0^6*u0^3)
H1   = u1 - (1 + a1*x1*u1 + a2*x1^2*u1
              + a3*x1^3*u1^2 + a4*x1^4*u1^2 + a6*x1^6*u1^3)
Rbeta = beta - d*bq
w0   = x0^3*u0
w1   = x1^3*u1
```

For each raw coordinate `C`, compute a representation

```text
C = d^3*Q + A*Rbeta + B0*H0 + B1*H1.
```

This is a Gröbner-basis / ideal-membership problem in a finite polynomial ring.  Once the certificate polynomials `Q,A,B0,B1` are found, paste them into Lean as definitions/lemmas and close each certificate by `ring_nf`.

This is much better than checking all truncations: the certificate is one finite identity, and Lean's `ring_nf` proves it universally.

---

## Bottom line

The final proof should be organized around the primitive factor

```lean
beta = X₁^2*u₁ - X₀^2*u₀ = (X₀-X₁)*betaQuot,
```

not around coprimality of `(X₀-X₁)` with `X₀X₁`.  The `X₀^3X₁^3` factors are artifacts of `w = T^3*u`; remove them by normalized coordinate identities.  Then `(X₀-X₁)^3` divisibility follows from one diagonal-difference lemma plus finite `ring_nf` certificates for `formalAddX`, `formalAddY`, and `formalAddZ`.
