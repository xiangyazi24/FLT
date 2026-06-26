# Q798 (dm4): closing `preΨ'_deriv_ne_zero_at_root_general`

## Recommendation

Do **not** try to close the `n ≥ 4` case by the even product-rule descent as currently sketched.  That descent proves only the branch where the old factor vanishes.  In the branch where the new even cofactor vanishes, it asks for the cofactor to have simple roots, which is essentially another separability theorem.

The cleaner route is the Ω-free dual-number proof:

```text
double root of preΨ'(n)
  ⇒ preΨ'(n) vanishes on a nonzero dual tangent lift Pε
  ⇒ projective division-polynomial formula gives [n]Pε = O
  ⇒ Pε is a nonzero infinitesimal vector in ker([n])
  ⇒ contradiction because d[n] = n and (n : K) ≠ 0.
```

This bypasses `Ω_n` completely.  The important correction is that the formal-group argument is **not** “evaluate `[n]_F` at `t(P)`.”  A torsion point `P` is not generally in the formal neighborhood of `O`.  Instead, translate the first-order deformation of `P` back to the identity, use the formal group there, and translate forward again.

## Why the even strong induction is not simpler

Write

```text
preΨ'(2k) = preΨ'(k) · C_k.
```

Let `f = preΨ'(k)` and `g = C_k`.  At a root of `h = f*g`, the derivative is

```text
h' = f'·g + f·g'.
```

There are two cases.

### Case 1: `f(x) = 0`

Then

```text
h'(x) = f'(x) · g(x).
```

This branch is good:

* `f'(x) ≠ 0` by induction on `k`, and
* `g(x) ≠ 0` by the already proved cofactor nonvanishing lemma, for example `evenCofactor_ne_zero_Psi3_ne` plus the relevant side conditions.

### Case 2: `g(x) = 0` and `f(x) ≠ 0`

Then

```text
h'(x) = f(x) · g'(x).
```

Now the proof needs

```text
g'(x) ≠ 0.
```

That is not a consequence of the induction hypothesis on `preΨ'(k)`, because `g` is not just `preΨ'(m)` for one smaller `m`; it is the new part of the `2k`-torsion divisor.  So a “simple” strong induction would have to strengthen the induction predicate to include squarefreeness of every even cofactor/primitive factor and coprimality among all those factors.  That is larger than the theorem you are trying to close.

So the product-rule descent can be made to work, but only after proving a primitive-factor separability package.  It is not the shortest way to close the final sorry.

## The direct dual-number proof

Let

```text
ψ = W.preΨ' n.
```

Assume `x` is a root of `ψ` and also a root of `ψ.derivative`.  Over the algebraically closed field `K`, choose an affine point

```text
P = (x, y)
```

above `x`.  The existing root criterion for `preΨ'` should give

```text
n • P = O.
```

The adjacent-coprimality infrastructure, especially `no_adjacent_preΨ_zero`, should give the corresponding numerator nonvanishing statement

```text
Φ_n(P.x) ≠ 0
```

at a root of `ψ_n`.  This is the same nonvanishing used in the usual argument

```text
Φ_n ≡ -ψ_{n+1}ψ_{n-1} · factor    mod ψ_n.
```

The proof then proceeds infinitesimally.

## Step 1: build a nonzero dual-number lift

Let

```text
A = DualNumber K.
```

You want a point `Pε : W(A)` reducing to `P` with nonzero tangent vector.  In the nonvertical case, take

```text
xε = x + ε,
yε = y + y₁ ε,
```

where `y₁` solves the linearized Weierstrass equation.  For

```text
F = y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆,
```

the linear condition is

```text
F_x(P) + F_y(P) · y₁ = 0,
```

with

```text
F_y(P) = 2y + a₁x + a₃.
```

So when `F_y(P) ≠ 0`, choose

```text
y₁ = -F_x(P) / F_y(P).
```

This gives a genuine dual-number point with `dx = 1`, hence a nonzero tangent vector.

For the normalized `preΨ'`, roots should be nonvertical.  If that is not already available, isolate it as a small lemma:

```lean
-- Schematic name.
theorem preΨ'_root_not_twoTorsion
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn_ge4 : 4 ≤ n) {x : K}
    (hx : (W.preΨ' n).IsRoot x)
    {P : W.AffinePoint K} (hPx : P.x = x)
    (hP_on_root : -- P is the point above the root used by the division-polynomial criterion
      True) :
    2 * P.y + W.a₁ * P.x + W.a₃ ≠ 0 := by
  -- Either follows from the normalization of `preΨ'` removing the Ψ₂ factor,
  -- or is handled by a separate 2-torsion squarefreeness lemma.
  sorry
```

This lemma is much smaller than proving the even cofactor squarefree.  If Mathlib’s normalization does allow vertical roots in `preΨ'`, split those roots off separately; they are controlled by nonsingularity of the cubic, not by the EDS descent.

## Step 2: a double root gives a dual root

For any polynomial `p`, over dual numbers:

```text
p(x + ε) = p(x) + p'(x) ε.
```

Thus from

```lean
hx   : (W.preΨ' n).IsRoot x
hder : (derivative (W.preΨ' n)).IsRoot x
```

you get

```text
(W.preΨ' n)(x + ε) = 0
```

in `DualNumber K`.

The useful Lean lemma is:

```lean
-- Schematic.  Adjust to Mathlib's actual DualNumber and Polynomial API.
theorem polynomial_eval_dual_eq_eval_add_derivative
    (p : Polynomial K) (x u : K) :
    Polynomial.aeval (DualNumber.of x + DualNumber.of u * DualNumber.epsilon) p =
      DualNumber.of (p.eval x) +
        DualNumber.of (u * p.derivative.eval x) * DualNumber.epsilon := by
  -- polynomial induction, or use an existing simp theorem if available
  sorry
```

With `u = 1`, this gives the dual root of `ψ`.

## Step 3: the projective formula gives `[n]Pε = O`

This is the key Ω-free replacement.

Do **not** use the affine formula

```text
[n](P) = (Φ/ψ², Ω/ψ³),
```

because it divides by `ψ`, which is zero on the dual lift.  Use the projective division-polynomial formula instead.  In projective coordinates the `Z`-component is a power of `ψ`; the `X`-component has a factor of `ψ`; and the remaining coordinate is automatically a unit when the triple is a valid projective point reducing to infinity.

The lemma you want is:

```lean
-- Schematic.
theorem nsmul_eq_zero_of_preΨ'_dual_root
    (W : WeierstrassCurve K) [W.IsElliptic]
    {A : Type*} [CommRing A] [Algebra K A]
    {n : ℕ} {Pε : W.ProjectivePoint A}
    (hψ : -- `preΨ' n` evaluates to 0 at the x-coordinate of Pε
      True)
    (hΦ_unit : -- `Φ_n` evaluates to a unit at Pε
      True) :
    n • Pε = 0 := by
  -- Use the projective nsmul/division-polynomial coordinate formula.
  -- Since ψ = 0, the projective `Z` coordinate is 0 and the projective `X`
  -- coordinate is also 0.  Since the triple is a projective point and Φ is a
  -- unit after reduction, the remaining coordinate is a unit, hence the point is O.
  sorry
```

The `hΦ_unit` proof does **not** need `Ω_n`.  It uses only that the residue of `Φ_n(Pε.x)` is nonzero:

```text
Φ_n(P.x) ≠ 0.
```

An element of `DualNumber K` is a unit exactly when its scalar/residue part is nonzero.

A practical helper lemma is:

```lean
-- Schematic.
theorem isUnit_dual_of_residue_ne_zero {z : DualNumber K}
    (hz : DualNumber.re z ≠ 0) : IsUnit z := by
  -- explicit inverse or existing DualNumber unit criterion
  sorry
```

Then `no_adjacent_preΨ_zero` supplies the residue nonvanishing of `Φ_n` at the original root.

## Step 4: `[n]` has no infinitesimal kernel when `(n : K) ≠ 0`

This is the formal-group input.

State it independently of division polynomials:

```lean
-- Schematic.
theorem no_dual_tangent_kernel_of_nsmul
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0)
    {P : W.Point K} (hP_tors : n • P = 0)
    {Pε : W.Point (DualNumber K)}
    (hred : reduce Pε = P)
    (htangent_ne : tangentVector Pε ≠ 0) :
    n • Pε ≠ 0 := by
  -- Let Qε = Pε - const(P).  Then Qε reduces to O and has the same nonzero
  -- tangent vector, transported to the identity.
  -- If n • Pε = O, then n • Qε = O.
  -- In the formal parameter at O, write t(Qε) = u ε with u ≠ 0.
  -- `FormalNsmulDirect` gives t(n • Qε) = (n : K) * u * ε because ε² = 0.
  -- Since `(n : K) ≠ 0` and `u ≠ 0`, this is nonzero. Contradiction.
  sorry
```

This is the right use of `FormalNsmulDirect`: it is applied at the identity after translating the tangent vector from `P` to `O`.

## How the final theorem should look

Once the bridge lemmas above exist, the `n ≥ 4` branch of

```lean
public theorem preΨ'_deriv_ne_zero_at_root_general [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x
```

should not need EDS descent.  It should reduce to one auxiliary theorem:

```lean
-- Schematic.
theorem preΨ'_deriv_ne_zero_at_root_by_dual
    [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x := by
  intro hder

  -- Choose an affine point P above x and get n-torsion from the preΨ' root.
  obtain ⟨P, hPx, hP_tors, hP_ne_O, hΦ_ne⟩ :=
    W.point_torsion_and_Phi_ne_of_preΨ'_root hn hx

  -- Roots of the normalized preΨ' are nonvertical; otherwise split off the
  -- separate 2-torsion squarefreeness case.
  have hv : 2 * P.y + W.a₁ * P.x + W.a₃ ≠ 0 := by
    exact W.preΨ'_root_not_twoTorsion hn hx hPx

  -- Build a dual lift with dx = 1.
  obtain ⟨Pε, hred, hdx⟩ := W.exists_dual_lift_dx_one P hv
  have htangent_ne : tangentVector Pε ≠ 0 := by
    -- follows from `hdx : dx = 1`
    exact W.tangent_ne_zero_of_dx_eq_one hdx

  -- Double root implies ψ_n vanishes on the dual lift.
  have hψ_dual : -- `(W.preΨ' n)` evaluates to 0 on `Pε.x`
      True := by
    -- polynomial_eval_dual_eq_eval_add_derivative + hx + hder + hdx
    trivial

  -- Φ is a unit on the dual lift because its residue at P is nonzero.
  have hΦ_unit : -- `Φ_n(Pε.x)` is a unit
      True := by
    -- residue is `Φ_n(P.x)`, and `hΦ_ne` says this residue is nonzero
    trivial

  -- Projective division-polynomial formula: ψ=0 and Φ unit force `[n]Pε = O`.
  have hnPε : n • Pε = 0 := by
    exact W.nsmul_eq_zero_of_preΨ'_dual_root hψ_dual hΦ_unit

  -- But multiplication by n has no infinitesimal kernel.
  exact W.no_dual_tangent_kernel_of_nsmul hn hP_tors hred htangent_ne hnPε
```

Then the existing theorem becomes:

```lean
public theorem preΨ'_deriv_ne_zero_at_root_general [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) :
    ¬ (derivative (W.preΨ' n)).IsRoot x := by
  -- keep the existing `n ≤ 3` branches if they are already stable
  by_cases hsmall : n ≤ 3
  · exact W.preΨ'_deriv_ne_zero_at_root_small hn hsmall hx
  · exact W.preΨ'_deriv_ne_zero_at_root_by_dual hn hx
```

The small-case split is no longer mathematically necessary once the dual theorem is general, but keeping it is fine if those branches already compile.

## What must be available over `DualNumber K`

The only serious implementation caveat is that `DualNumber K` is not a field.  Therefore any division-polynomial formula used in Step 3 must be stated over a commutative ring or at least over the specific `K`-algebra `DualNumber K`, not only over fields.

If the current projective `[n]` formula is field-only, do not define `Ω_n`; instead generalize the projective coordinate formula by base change.  The formula is polynomial, so it should transport to `DualNumber K` without divisions.

The minimum projective bridge is:

```lean
-- Schematic, Ω-free.
theorem projective_nsmul_Z_eq_preΨ'_power
    (Pε : W.ProjectivePoint (DualNumber K)) :
    Zcoord (n • Pε) = unitFactor * (eval_preΨ' n Pε.x) ^ e := by
  sorry

theorem projective_nsmul_X_has_preΨ'_factor
    (Pε : W.ProjectivePoint (DualNumber K)) :
    Xcoord (n • Pε) = eval_preΨ' n Pε.x * eval_Φ n Pε.x * unitFactor := by
  sorry
```

Together with the projective-point condition, these are enough: when `ψ=0`, both `X` and `Z` are zero, so the point is `O`.

## Final answer to the design question

The dual-number approach is the simpler **mathematical** proof and the better long-term Lean architecture.  It avoids `Ω_n`, avoids division by `2`, avoids the even cofactor derivative branch, and uses exactly the hypothesis `(n : K) ≠ 0`.

However, it is not a one-line local replacement for the sorry.  To make it close, add the four bridge lemmas:

```text
1. double root ⇒ dual-number root of preΨ'(n),
2. nonvertical root ⇒ nonzero dual lift with dx = 1,
3. projective division-polynomial formula over DualNumber K gives [n]Pε = O,
4. FormalNsmulDirect ⇒ no nonzero infinitesimal kernel of [n] when (n : K) ≠ 0.
```

After those are in place, the `n ≥ 4` case of `preΨ'_deriv_ne_zero_at_root_general` is a short contradiction proof, and the EDS descent can be abandoned for this theorem.
