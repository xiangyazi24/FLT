# Q266 (dm4): non-circular content of bridge-2

## Bottom line

Yes: the circularity diagnosis is correct.  A theorem of the form

```lean
preΨ'_n(x + ε) = 0 → TangentO.nsmul₁ W n 1 = 0
```

is useful only if its proof does **not** already use separability / derivative nonvanishing.  The non-circular content is the comparison theorem that identifies the local parameter computed from the division-polynomial projective formula with the abstract tangent map of `[n]`.

The missing step 5 is provable, but it is a separate compatibility lemma:

```text
coefficient of t([n] Pε)
  = TangentO.nsmul₁ W n (tangent-coordinate of Pε at P, transported to O).
```

For an affine dual deformation

```text
Pε = (x + ε dx, y + ε dy)
```

satisfying the linearized curve equation at a nonsingular affine point `P = (x,y)`, that tangent coordinate is

```text
dx / ψ₂(P) = dx / (2*y + a₁*x + a₃).
```

So the precise statement of step 5 should be:

```text
coeffε(t([n]Pε)) = TangentO.nsmul₁ W n (dx / ψ₂(P))
                 = (n : K) * (dx / ψ₂(P)).
```

If you choose `dx = 1`, this is `(n : K) / ψ₂(P)`.  If you want to use the already-proved lemma only in the form

```lean
TangentO.nsmul₁ W n 1 = (n : K)
```

then choose the scaled dual deformation with

```text
dx = ψ₂(P).
```

Because `ψ₂(P) ≠ 0`, this deformation has transported tangent coordinate `1`, and derivative-zero still makes `preΨ'_n(x + ε*ψ₂(P)) = 0`.

That scaled choice is the cleanest Lean route.

## The non-circular lemma chain

Let

```lean
p := W.preΨ' n
ψ2P := 2 * y + W.a₁ * x + W.a₃
```

and suppose:

```lean
hx      : p.eval x = 0
hψ2P    : ψ2P ≠ 0
hn      : (n : K) ≠ 0
hnP     : n • P = 0
```

To prove `p.derivative.eval x ≠ 0`, argue by contradiction.

### 1. Assume a repeated root and make a scaled dual lift

Assume:

```lean
hderiv : p.derivative.eval x = 0
```

Use the affine tangent vector with `dx = ψ2P`, so that the transported tangent coordinate is `1`.  The linearized Weierstrass equation is

```text
F_x dx + F_y dy = 0,
F_y = ψ₂(P).
```

A convenient choice is

```text
dy = -F_x = 3*x^2 + 2*a₂*x + a₄ - a₁*y.
```

Then `F_x * ψ2P + ψ2P * dy = 0`, so

```text
Pε = (x + ε*ψ2P, y + ε*dy)
```

is a dual-number point of the curve lying over `P`, and its tangent coordinate is

```text
dx / ψ2P = ψ2P / ψ2P = 1.
```

Lean lemma to add/prove independently of division polynomials:

```lean
/-- A scaled affine tangent lift at a non-2-torsion affine point.  Its transported
local-parameter tangent coordinate is `1`. -/
theorem exists_dual_lift_tangentCoord_one
    (W : WeierstrassCurve K) {x y : K}
    (hP : (W⁄K).Nonsingular x y)
    (hψ2P : (2 * y + W.a₁ * x + W.a₃) ≠ 0) :
    ∃ Pε, IsDualPointOver W Pε x y ∧
      affineTangentCoord W x y Pε = 1 := by
  -- Take dx = ψ₂(P), dy = -F_x.
  -- This is a direct `ring` proof from the linearized Weierstrass equation.
  sorry
```

The exact structure `IsDualPointOver` can be whatever you use locally for a dual-valued affine point.  The mathematical content is only the first-order equation.

### 2. Repeated root gives a dual root at the scaled lift

Taylor expansion over `TrivSqZeroExt` gives

```text
p(x + ε*ψ2P) = p(x) + ε * p'(x) * ψ2P = 0.
```

Lean shape:

```lean
have hp_dual_zero : evalDualPolynomial p (x + ε * ψ2P) = 0 := by
  rw [eval_dualNumber]
  simp [hx, hderiv]
```

No separability is used here; this is just the already-proved dual-number Taylor formula.

### 3. Convert the normalized dual root to `ψ_n(Pε) = 0`

Use the parity bridge from ATOM 7:

* odd `n`: `ψ_n(Pε) = preΨ'_n(xε)`, hence zero;
* even `n`: `ψ_n(Pε) = ψ₂(Pε) * preΨ'_n(xε)`, hence zero.

Lean shape:

```lean
have hψ_dual_zero : evalΨDual W n Pε = 0 := by
  -- odd: simpa [parity_ψ, hp_dual_zero]
  -- even: simp [parity_ψ, hp_dual_zero]
  exact ψ_dual_zero_of_preΨ'_dual_zero
    (W := W) (n := n) (Pε := Pε) hp_dual_zero
```

This is not separability; it is only the parity formula for the division polynomial.

### 4. Use the evaluated projective formula for `[n]Pε`

The projective division-polynomial formula gives a Jacobian representative

```text
[n]Pε = [φ_n(Pε) : ω_n(Pε) : ψ_n(Pε)].
```

Since `hψ_dual_zero` says the third coordinate is zero as a dual number, the local parameter

```text
t = -X * Z / Y
```

has zero ε-coefficient:

```lean
have ht_coeff_zero : coeffε (localT ([n]Pε)) = 0 := by
  -- rewrite `[n]Pε` by the projective formula;
  -- rewrite its `Z` coordinate by `hψ_dual_zero`;
  -- `simp [localT]` closes because `Z = 0`.
  exact localT_coeff_zero_of_projective_Z_zero
    (W := W) (n := n) (Pε := Pε) hψ_dual_zero
```

This uses the projective formula and the local parameter algebra, not separability.

### 5. Compare the same coefficient with the abstract tangent map

This is the key missing theorem.  It should be proved once from the definition of `TangentO`, translation to the origin, and functoriality of the group law over dual numbers.

```lean
/-- Compatibility between the concrete local parameter `t = -X*Z/Y` and the abstract
tangent map of multiplication-by-`n`.

For a dual lift `Pε` of an affine point `P`, whose transported tangent coordinate is `λ`,
the ε-coefficient of the local parameter of `[n]Pε` is `TangentO.nsmul₁ W n λ`.
This theorem is the real non-circular content of bridge-2. -/
theorem coeff_localT_nsmul_dual_eq_TangentO_nsmul₁
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y : K} (hP : (W⁄K).Nonsingular x y)
    (Pε : DualAffinePoint W x y)
    (λ : K)
    (hλ : affineTangentCoord W x y Pε = λ) :
    coeffε (localT (nsmulDualJacobianRep W n Pε))
      = TangentO.nsmul₁ W n λ := by
  -- Proof ingredients:
  -- 1. identify `λ` with the coefficient of `t(Pε - P)`;
  -- 2. use functoriality of `[n]` and translations:
  --      d([n])_P = d(τ_[n]P)_O ∘ d([n])_O ∘ d(τ_-P)_P;
  -- 3. since `n • P = O`, the target translation is the identity at `O`;
  -- 4. unfold the definition of `TangentO.nsmul₁`.
  -- No division-polynomial separability statement appears here.
  sorry
```

For the scaled lift from step 1, `λ = 1`, so:

```lean
have ht_coeff_tangent :
    coeffε (localT ([n]Pε)) = TangentO.nsmul₁ W n 1 := by
  exact coeff_localT_nsmul_dual_eq_TangentO_nsmul₁
    (W := W) (n := n) hP Pε 1 hλ_one
```

Then combine with the proved tangent formula:

```lean
have ht_coeff_nat : coeffε (localT ([n]Pε)) = (n : K) := by
  calc
    coeffε (localT ([n]Pε)) = TangentO.nsmul₁ W n 1 := ht_coeff_tangent
    _ = (n : K) := by
      simpa using TangentO.nsmul₁_eq_natCast_mul (W := W) (n := n) (a := (1 : K))
```

If your existing lemma is literally only

```lean
TangentO.nsmul₁ W n 1 = (n : K)
```

then the last line is just `simpa using TangentO.nsmul₁_eq_natCast_mul_one (W := W) (n := n)`.

### 6. Contradiction

Now the contradiction is immediate:

```lean
have hn_zero : (n : K) = 0 := by
  calc
    (n : K) = coeffε (localT ([n]Pε)) := ht_coeff_nat.symm
    _ = 0 := ht_coeff_zero
exact hn hn_zero
```

Therefore `p.derivative.eval x ≠ 0`.

## Full bridge-2 skeleton

This is the theorem shape I would implement.  It proves derivative nonvanishing, and the old
“dual root implies tangent zero” statement can be recovered from it if needed, but not the other
way around.

```lean
/-- Non-circular bridge-2: derivative nonvanishing at a normalized division-polynomial root,
proved by comparing the projective division-polynomial formula with the formal tangent map
`d[n]_O = n`.

This theorem must not import or use any separability theorem for `preΨ' n`. -/
theorem preΨ'_derivative_ne_zero_at_root_of_tangent
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} {x y : K}
    (hn : (n : K) ≠ 0)
    (hP : (W⁄K).Nonsingular x y)
    (hroot : (W.preΨ' n).eval x = 0)
    (hψ2P : (2 * y + W.a₁ * x + W.a₃) ≠ 0)
    (hnP : n • (Point.some x y hP : (W⁄K).Point) = 0) :
    (W.preΨ' n).derivative.eval x ≠ 0 := by
  intro hderiv

  rcases exists_dual_lift_tangentCoord_one
      (W := W) (x := x) (y := y) hP hψ2P with
    ⟨Pε, hPε_curve, hλ_one⟩

  have hp_dual_zero :
      evalPreΨ'Dual W n Pε = 0 := by
    -- Taylor: p(x + ε*ψ₂(P)) = p(x) + ε*p'(x)*ψ₂(P).
    -- Both coefficients vanish by `hroot` and `hderiv`.
    exact preΨ'_dual_zero_of_eval_eq_zero_of_derivative_eq_zero
      (W := W) (n := n) (Pε := Pε) hroot hderiv

  have hψ_dual_zero : evalΨDual W n Pε = 0 := by
    exact ψ_dual_zero_of_preΨ'_dual_zero
      (W := W) (n := n) (Pε := Pε) hp_dual_zero

  have ht_coeff_zero : coeffε (localT (nsmulDualJacobianRep W n Pε)) = 0 := by
    exact localT_coeff_zero_of_projective_Z_zero
      (W := W) (n := n) (Pε := Pε) hψ_dual_zero

  have ht_coeff_tangent :
      coeffε (localT (nsmulDualJacobianRep W n Pε)) = TangentO.nsmul₁ W n 1 := by
    exact coeff_localT_nsmul_dual_eq_TangentO_nsmul₁
      (W := W) (n := n) hP Pε 1 hλ_one

  have ht_coeff_nat :
      coeffε (localT (nsmulDualJacobianRep W n Pε)) = (n : K) := by
    calc
      coeffε (localT (nsmulDualJacobianRep W n Pε))
          = TangentO.nsmul₁ W n 1 := ht_coeff_tangent
      _ = (n : K) := by
          simpa using
            TangentO.nsmul₁_eq_natCast_mul
              (W := W) (n := n) (a := (1 : K))

  have hn_zero : (n : K) = 0 := by
    calc
      (n : K) = coeffε (localT (nsmulDualJacobianRep W n Pε)) := ht_coeff_nat.symm
      _ = 0 := ht_coeff_zero
  exact hn hn_zero
```

The names `DualAffinePoint`, `evalPreΨ'Dual`, `evalΨDual`, `localT`, and
`nsmulDualJacobianRep` are placeholders for your local dual-point and projective-representative API.
The important point is the dependency structure.

## Direct `dx = 1` variant

If you keep the original deformation `x + ε`, step 5 should be stated as

```lean
coeffε(t([n]Pε)) = TangentO.nsmul₁ W n ((2*y + W.a₁*x + W.a₃)⁻¹)
                 = (n : K) * (2*y + W.a₁*x + W.a₃)⁻¹.
```

Then contradiction uses both

```lean
hn    : (n : K) ≠ 0
hψ2P : 2*y + W.a₁*x + W.a₃ ≠ 0
```

because the product `(n : K) * ψ2P⁻¹` is nonzero.  This version is mathematically fine, but the scaled `dx = ψ₂(P)` version is cleaner in Lean because it reduces step 5 to `TangentO.nsmul₁ W n 1`.

## Dependency audit

The non-circular bridge may use:

1. the dual-number Taylor formula for `preΨ'`;
2. the parity formula relating `ψ_n` to `preΨ'_n`;
3. the projective division-polynomial formula for `[n]` over dual numbers;
4. the elementary local parameter algebra `t = -X*Z/Y`;
5. the tangent-coordinate compatibility theorem for affine dual lifts;
6. `TangentO.nsmul₁_eq_natCast_mul`.

It must **not** use:

```lean
separable_of_deriv_ne_zero_at_roots
preΨ'_separable
preΨ'_derivative_ne_zero_at_roots
```

or any theorem proved from them.  Those are the downstream conclusions.
