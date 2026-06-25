# Q611 (dm1): bridge from formal `[n]'(0)=n` to no double roots of `preΨ' n`

## Executive answer

`formalNsmulF_coeff_one` at the origin **is sufficient**, but not by evaluating a formal-group derivative at a general torsion point `t₀`.  The formal group only describes an infinitesimal neighborhood of the identity `O`.  The missing step is translation: for an algebraic group, the differential of `[n]` at any point `P` is translation-conjugate to the differential of `[n]` at `O`.  Thus

```text
d[n]_P = d(τ_{[n]P})_O ∘ d[n]_O ∘ d(τ_{-P})_P.
```

If `P` is `n`-torsion, `[n]P = O`, so this is just the origin tangent map, transported by tangent-space isomorphisms.  Since `d[n]_O = n` and `(n : K) ≠ 0`, `d[n]_P` is nonzero/invertible.  Therefore a nonzero first-order tangent vector at `P` cannot be killed by `[n]`, and a dual-number double root of `preΨ' n` gives exactly such a killed tangent vector.  Contradiction.

So: you do **not** need a separate stronger theorem saying the formal power series `[n]_F(T)` has nonzero derivative at every formal root `t₀`; that is the wrong coordinate picture.  You need the translation/tangent bridge.  If stated globally, this is exactly the standard theorem that `[n] : E → E` is étale/separable when `(n : K) ≠ 0`, but for your Lean goal it is better to prove only the dual-number tangent-injectivity consequence.

---

## Why the tempting `t₀` argument is wrong

This sentence is the dangerous part:

```text
Since t_ε = t₀ + ε t₁ and [n]_F(t₀)=0, the ε-coefficient gives [n]'_F(t₀)t₁ = 0.
```

For a general torsion point `P`, its local parameter is **not** the identity formal parameter `t` unless `P = O`.  The formal group law `F` is a completed local object at `O`; it does not give a global coordinate in which all torsion points are formal roots.  The correct local coordinate near `P` is obtained by translating `P` back to `O`.

If `Pε` is a first-order deformation of `P`, define the translated infinitesimal displacement

```text
δ := (-P) + Pε   over K[ε].
```

Then `δ` has constant part `O`, hence it is a genuine formal-group infinitesimal.  If `P` is `n`-torsion, then in the group over dual numbers:

```text
[n] Pε = [n] (P + δ) = [n]P + [n]δ = O + [n]δ = [n]δ.
```

Now the formal tangent computation at `O` applies to `δ`:

```text
localParameter([n]δ).ε = (n : K) * localParameter(δ).ε.
```

If `(n : K) ≠ 0` and `δ` has nonzero tangent, then `[n]δ` is not the infinitesimal identity.  Therefore `[n]Pε ≠ Oε`.

That is the exact contradiction to “double root gives a nontrivial dual lift still killed by `[n]`”.

---

## The Lean atom you actually need

Do not try to prove a global separability theorem first.  Prove this dual-number tangent lemma.

A good statement shape is:

```lean
/-- Infinitesimal injectivity of `[n]` at an `n`-torsion point, reduced to the
formal tangent computation at the origin by translation. -/
theorem nsmul_dual_ne_identity_of_nonzero_translated_tangent
    {K : Type*} [Field K]
    (W : WeierstrassCurve K)
    (n : ℕ)
    (hn : (n : K) ≠ 0)
    (P : W.Point K)                         -- or your projective/affine point type
    (hPtor : n • P = 0)
    (Pε : W.Point (TrivSqZeroExt K K))
    (hfst : fstPoint Pε = P)
    (hδne : tangentOCoord W ((-mapPoint P) + Pε) ≠ 0) :
    n • Pε ≠ identityPointOverDual W := by
  -- 1. Let δ := (-P) + Pε.  Its scalar/fst part is O.
  -- 2. Use group-hom/nsmul compatibility over `TrivSqZeroExt`:
  --      n • Pε = n • (mapPoint P + δ)
  --             = mapPoint (n • P) + n • δ
  --             = n • δ.
  -- 3. Use the formal-group tangent bridge at O:
  --      tangentOCoord W (n • δ) = (n : K) * tangentOCoord W δ.
  --    This is where `formalNsmulF_coeff_one` enters.
  -- 4. Since `(n : K) ≠ 0` and `tangentOCoord W δ ≠ 0`, the RHS is nonzero.
  -- 5. The infinitesimal identity has tangent coordinate zero. Contradiction.
  sorry
```

The important point is that this theorem is about **dual-number points and translation**, not about polynomial roots yet.

You may prefer to split it into two smaller atoms:

```lean
theorem tangentOCoord_nsmul_of_infinitesimal_at_O
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) (n : ℕ)
    (δ : W.Point (TrivSqZeroExt K K))
    (hδfst : fstPoint δ = identityPoint W) :
    tangentOCoord W (n • δ) = (n : K) * tangentOCoord W δ := by
  -- This is the direct `formalNsmulF_coeff_one` bridge.
  sorry

theorem nsmul_translate_to_origin
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) (n : ℕ)
    (P : W.Point K) (Pε : W.Point (TrivSqZeroExt K K))
    (hPtor : n • P = 0)
    (hfst : fstPoint Pε = P) :
    n • Pε = n • ((-mapPoint P) + Pε) := by
  -- More precisely there may be an `identity +` or `mapPoint (n • P) + _`
  -- depending on your point representation; after rewriting `hPtor`, it is `n • δ`.
  sorry
```

Then combine them.

---

## How double root gives the contradictory dual lift

For the derivative lemma, the Lean proof should be organized as follows.

Assumptions, schematically:

```lean
variable {K : Type*} [Field K] [IsAlgClosed K]
variable (W : WeierstrassCurve K)
variable (n : ℕ)
variable (x y : K)

-- affine point on the curve
(hcurve : W.affineEquation x y = 0)
-- not 2-torsion; equivalently ψ₂(P) is nonzero/unit
(hψ2 : W.ψ₂.eval₂ x y ≠ 0)
-- n is nonzero in K
(hn : (n : K) ≠ 0)
-- root of preΨ' n
(hroot : (W.preΨ' n).eval x = 0)
```

Goal:

```lean
(W.preΨ' n).derivative.eval x ≠ 0
```

Prove by contradiction:

```lean
by
  intro hderiv
```

### Step A: build a nonzero tangent lift `Pε`

Because `hψ2 : 2*y + a₁*x + a₃ ≠ 0`, the affine curve equation is smooth in the `Y` direction at `(x,y)`.  Therefore the dual lift with `x`-velocity `1` is obtained by solving for the `y`-velocity.

Mathematically:

```text
Fx = -(3x^2 + 2a₂x + a₄) + a₁y
Fy = 2y + a₁x + a₃ = ψ₂(P)
slope = -Fx / Fy
Pε = (x + ε, y + ε*slope).
```

You probably already have this or something close; if not, this is the helper to add:

```lean
/-- The canonical nonzero tangent lift in the `x` direction at a non-2-torsion affine point. -/
def tangentLiftX
    (W : WeierstrassCurve K) (x y : K) (hψ2 : W.ψ₂.eval₂ x y ≠ 0) :
    W.Point (TrivSqZeroExt K K) :=
  -- x-coordinate: inl x + inr 1
  -- y-coordinate: inl y + inr slope
  -- prove the dual curve equation by linearizing and using the chosen slope
  sorry

lemma tangentLiftX_translated_tangent_ne_zero
    (W : WeierstrassCurve K) (x y : K) (hψ2 : W.ψ₂.eval₂ x y ≠ 0) :
    tangentOCoord W ((-mapPoint (affinePoint W x y)) + tangentLiftX W x y hψ2) ≠ 0 := by
  -- The translated tangent has nonzero tangent vector because the original x-velocity is `1`.
  -- Translation is an isomorphism on tangent spaces; concretely the x-component remains a nonzero
  -- tangent direction in your chosen tangent coordinate.
  sorry
```

If your current tangent coordinate at `O` is `-X/Y` or `-XZ/Y`, the exact nonzero expression after translation may not be literally `1`, but it will be a nonzero scalar multiple of the input tangent.  This is the right place to use your existing `psi2_dual_isUnit` / denominator-unit lemmas.

### Step B: double root gives `preΨ' n` zero on the dual lift

You already described these atoms:

```lean
preΨ'_eval_zero_of_dual_root
preΨ'_deriv_eval_zero_of_dual_root
```

The direction needed here is the standard dual-number Taylor lemma:

```lean
lemma preΨ'_dual_eval_eq_zero_of_root_and_deriv_zero
    (hroot : (W.preΨ' n).eval x = 0)
    (hderiv : (W.preΨ' n).derivative.eval x = 0) :
    evalDualX (W.preΨ' n) (x + ε) = 0 := by
  -- polynomial Taylor over dual numbers:
  -- p(x + ε) = p(x) + ε * p'(x)
  sorry
```

Then for the actual point:

```lean
have hpre_dual :
    dualEvalPreΨ' W n (tangentLiftX W x y hψ2) = 0 :=
  preΨ'_dual_eval_eq_zero_of_root_and_deriv_zero W n x hroot hderiv
```

Since `preΨ' n` is univariate in `x`, the `y`-velocity does not affect this evaluation.

### Step C: dual root implies `[n]Pε = Oε`

This is where `ψ₂` being a unit matters.  For non-2-torsion affine/projective points, the actual `ψ_n` condition and the univariate `preΨ' n` condition agree because

```text
Ψ_n = preΨ_n              if n odd,
Ψ_n = preΨ_n * ψ₂         if n even,
```

and `ψ₂(Pε)` is a unit.

You already have:

```lean
psi2_dual_isUnit
```

so the statement should be:

```lean
lemma nsmul_eq_identity_of_preΨ'_dual_zero
    (W : WeierstrassCurve K) (n : ℕ)
    (Pε : W.Point (TrivSqZeroExt K K))
    (hψ2unit : IsUnit (dualΨ₂ W Pε))
    (hpre : dualEvalPreΨ' W n Pε = 0) :
    n • Pε = identityPointOverDual W := by
  -- Use the projective division-polynomial formula for `[n]Pε`.
  -- For even n, `ψ₂` is a unit, so `preΨ' n = 0` iff `Ψ_n = 0`.
  -- Then the projective representative has the `Z`/denominator coordinate that identifies O.
  sorry
```

This is the second bridge.  It is algebraic/projective, not formal-group-theoretic.

### Step D: contradiction by tangent injectivity

Now assemble:

```lean
theorem preΨ'_deriv_ne_zero_at_nontorsion_root
    {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) (n : ℕ)
    (hn : (n : K) ≠ 0)
    (x y : K)
    (hcurve : W.affineEquation x y = 0)
    (hψ2 : W.ψ₂.eval₂ x y ≠ 0)
    (hroot : (W.preΨ' n).eval x = 0) :
    (W.preΨ' n).derivative.eval x ≠ 0 := by
  intro hderiv

  let P : W.Point K := affinePoint W x y hcurve
  let Pε : W.Point (TrivSqZeroExt K K) := tangentLiftX W x y hψ2

  have hPtor : n • P = 0 := by
    -- root of `preΨ' n`, plus `ψ₂(P) ≠ 0`, implies P is n-torsion.
    exact nsmul_eq_identity_of_preΨ'_root W n P hψ2 hroot

  have hpre_dual : dualEvalPreΨ' W n Pε = 0 := by
    exact preΨ'_dual_eval_eq_zero_of_root_and_deriv_zero W n x hroot hderiv

  have hψ2unit : IsUnit (dualΨ₂ W Pε) := by
    exact psi2_dual_isUnit W x y hψ2

  have hnPε_zero : n • Pε = identityPointOverDual W := by
    exact nsmul_eq_identity_of_preΨ'_dual_zero W n Pε hψ2unit hpre_dual

  have htan_ne : tangentOCoord W ((-mapPoint P) + Pε) ≠ 0 := by
    exact tangentLiftX_translated_tangent_ne_zero W x y hψ2

  exact
    (nsmul_dual_ne_identity_of_nonzero_translated_tangent
      W n hn P hPtor Pε (by simp [Pε, P]) htan_ne) hnPε_zero
```

This is the right high-level Lean shape.  The exact point type names and coercions will differ in your repo, but the theorem dependencies are the correct ones.

---

## Where `formalNsmulF_coeff_one` enters

The theorem

```lean
formalNsmulF_coeff_one
```

should not be used directly in the polynomial derivative proof.  It should be encapsulated in exactly one local tangent theorem at the identity:

```lean
lemma tangentOCoord_nsmul_infinitesimal
    (W : WeierstrassCurve K) (n : ℕ)
    (δ : W.Point (TrivSqZeroExt K K))
    (hδ0 : fstPoint δ = identityPoint W) :
    tangentOCoord W (n • δ) = (n : K) * tangentOCoord W δ := by
  -- Convert `δ` to a formal parameter `t = ε*c` at O.
  -- Use the already-built `formalGroupLaw W` and the theorem
  -- `formalNsmulF_coeff_one` to get coefficient `(n : K)`.
  -- Convert back from formal parameter coefficient to `tangentOCoord`.
  sorry
```

Then all later proofs should only use this lemma.  That keeps the formal-group machinery isolated from the projective division-polynomial machinery.

---

## Do you need separability of `[n]_F`?

There are three levels:

1. **Origin tangent fact:**
   ```text
   d[n]_O = n.
   ```
   This is exactly `formalNsmulF_coeff_one`.

2. **Global tangent injectivity:**
   ```text
   for every P, d[n]_P is nonzero/invertible if (n : K) ≠ 0.
   ```
   This follows from (1) by translation because `[n]` is a group homomorphism.
   This is the level you need.

3. **Global separability/étaleness of `[n]`:**
   ```text
   [n] : E → E is separable/étale.
   ```
   This is the algebro-geometric packaging of (2).  It is standard, but it is overkill for your immediate polynomial derivative goal.

So the answer is:

```text
formalNsmulF_coeff_one is sufficient only after proving the translation bridge from tangent at P to tangent at O.  You do not need a separate all-roots formal-power-series derivative theorem; that theorem is not even naturally stated in the identity formal coordinate.
```

---

## Minimal new atoms to close the sorry

I would add these atoms, in this order:

### Atom 1: dual tangent lift from non-2-torsion

```lean
lemma exists_nonzero_dual_tangent_lift_affine
    (hcurve : W.affineEquation x y = 0)
    (hψ2 : W.ψ₂.eval₂ x y ≠ 0) :
    ∃ Pε : W.Point (TrivSqZeroExt K K),
      fstPoint Pε = affinePoint W x y hcurve ∧
      tangentAtPointNonzero W Pε
```

Prefer a constructive version `tangentLiftX` if you already have formulas.

### Atom 2: root + derivative zero gives dual root

```lean
lemma polynomial_dual_eval_zero_of_eval_and_deriv_zero
    (p : K[X]) (x : K)
    (hp : p.eval x = 0) (hderiv : p.derivative.eval x = 0) :
    evalDual p (TrivSqZeroExt.inl x + TrivSqZeroExt.inr 1) = 0
```

This should be pure polynomial/dual-number arithmetic and reusable.

### Atom 3: dual `preΨ'` root gives dual torsion

```lean
lemma nsmul_dual_eq_zero_of_preΨ'_dual_eval_zero
    (hψ2unit : IsUnit (dualΨ₂ W Pε))
    (hpre : dualEvalPreΨ' W n Pε = 0) :
    n • Pε = identityPointOverDual W
```

This uses the division-polynomial/projective formula side.

### Atom 4: formal tangent at O for dual infinitesimals

```lean
lemma tangentOCoord_nsmul_infinitesimal
    (hδ0 : fstPoint δ = identityPoint W) :
    tangentOCoord W (n • δ) = (n : K) * tangentOCoord W δ
```

This is the exact consumer of `formalNsmulF_coeff_one`.

### Atom 5: translate tangent at torsion point to origin

```lean
lemma nsmul_dual_ne_identity_of_nonzero_translated_tangent
    (hn : (n : K) ≠ 0)
    (hPtor : n • P = 0)
    (hδne : tangentOCoord W ((-mapPoint P) + Pε) ≠ 0) :
    n • Pε ≠ identityPointOverDual W
```

This is the conceptual bridge.

Then `preΨ'_deriv_ne_zero_at_nontorsion_root` is a short contradiction proof.

---

## Common pitfall to avoid

Do **not** try to prove:

```lean
[n]_F'(t₀) ≠ 0 for all formal roots t₀ of [n]_F
```

as the primary bridge.  That suggests a global coordinate on the elliptic curve, which the formal group does not provide.  The correct replacement is:

```lean
translate P to O, apply [n]'_O = n, translate back.
```

This is also exactly how Silverman's proof works: he uses the invariant differential / formal group at the identity to show `[n]` is separable when `n` is not zero in the base field; separability at arbitrary points follows from the group structure, not from evaluating the identity formal coordinate at those points.
