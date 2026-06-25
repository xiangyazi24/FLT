# Q265 (dm1): bridge-2 final assembly — `dual_root_implies_tangent_zero`

## Executive answer

There are two different “closures” for `n = 3`.

1. **Minimal closure if you are allowed to use the already-proved `n = 3` separability certificate:**
   the assumption
   ```lean
   aeval (x + ε) (W.preΨ' 3) = 0
   ```
   is impossible.  Then `TangentO.nsmul₁ W 3 1 = 0` follows by `exfalso`.  This closes the local theorem for `n = 3`, but it does **not** test the geometric bridge; it uses the target-type theorem as input.

2. **Honest bridge closure for `n = 3`:**
   use the projective formula
   ```text
   [3]Pε = [φ₃(Pε) : ω₃(Pε) : ψ₃(Pε)]
   ```
   and the local parameter
   ```text
   t = -X*Z/Y.
   ```
   If `preΨ'_3(x+ε)=0`, then `ψ₃(Pε)=0`, hence `t([3]Pε)=0` because `Z=ψ₃(Pε)=0` and `ω₃(Pε)` is a unit.  To conclude
   ```lean
   TangentO.nsmul₁ W 3 1 = 0
   ```
   you still need the identification lemma saying that the local-parameter coefficient of the actual/projective `[3]Pε` is exactly the abstract `TangentO.nsmul₁ W 3 1`.

Thus, after your items 1–8, the bottleneck is **not** another algebraic simplification of `preΨ'`.  The bottleneck is the bridge theorem:

```text
local coefficient of t([n]Pε) = TangentO.nsmul₁ W n 1.
```

The projective formula proves the left-hand side is zero from the dual root.  `formalNsmul_coeff_one` proves the right-hand side is `(n : K)`.  The missing glue is the theorem that these are the same tangent coefficient for the same actual multiplication-by-`n` map.

---

## Part I: the shortest `n = 3` closure using existing separability

This closes a theorem with conclusion `TangentO.nsmul₁ W 3 1 = 0`, but only because the hypotheses are inconsistent.  It is useful as a sanity check, not as the non-circular bridge for general `n`.

### Minimal lemmas needed

```lean
/-- Dual root of a univariate polynomial with `dx = 1` gives root and derivative root. -/
lemma dual_root_eval_and_deriv_zero
    {K : Type*} [Field K]
    {f : K[X]} {x : K}
    (hdual : aeval (MultipleRootBridge.xε x) f = 0) :
    f.eval x = 0 ∧ (derivative f).eval x = 0 := by
  -- Existing `eval_dualNumber`, then ext on `TrivSqZeroExt.fst/snd`.
  -- For `xε = x + ε*1`, the ε-coefficient is exactly `f'(x)`.
  sorry

/-- Existing from Q93 / Bezout. -/
lemma preΨ'_three_separable
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (h3 : (3 : K) ≠ 0) :
    (W.preΨ' 3).Separable := by
  -- already proved by the Ψ₃ / derivative Bezout certificate
  sorry
```

### Closure skeleton

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- `n = 3` bridge closes trivially if the `n = 3` separability certificate is allowed. -/
theorem dual_root_implies_tangent_zero_three_via_separability
    (h3 : (3 : K) ≠ 0)
    {x : K}
    (hdual : aeval (MultipleRootBridge.xε x) (W.preΨ' 3) = 0) :
    TangentO.nsmul₁ W 3 1 = 0 := by
  exfalso
  have hboth := dual_root_eval_and_deriv_zero (f := W.preΨ' 3) (x := x) hdual
  have hsep : (W.preΨ' 3).Separable :=
    preΨ'_three_separable (W := W) h3
  have hder_ne : (derivative (W.preΨ' 3)).eval x ≠ 0 := by
    -- Mathlib theorem: a separable polynomial has nonzero derivative at every root.
    simpa using hsep.eval₂_derivative_ne_zero (RingHom.id K) hboth.1
  exact hder_ne hboth.2

end

end WeierstrassCurve
```

This is the **minimal** `n=3` proof if you only want a theorem to compile.  But it does not isolate the general-`n` projective bottleneck.

---

## Part II: honest non-circular `n = 3` bridge chain

Here is the exact lemma chain that mirrors the intended general proof but specialized to `n = 3`.

### Input context

Use your existing dual-lift setup:

```lean
R := TrivSqZeroExt K K
xε := MultipleRootBridge.xε x       -- x + ε
/yε/ := AffineJet.equation_dual_lift_of_polynomialY_ne_zero ...
Pε := affine/projective dual point ![xε, yε, 1]
```

Assumptions:

```lean
hP    : W.Equation x y
hY    : W.toAffine.polynomialY.evalEval x y ≠ 0      -- non-2-torsion
hdual : aeval (MultipleRootBridge.xε x) (W.preΨ' 3) = 0
```

### Lemma B1: reduced dual root gives full `ψ₃` dual zero

For `n = 3`, there is no even `ψ₂` factor:

```lean
lemma ψ_three_dual_eq_zero_of_preΨ'_three_dual_eq_zero
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K)
    {x y : K} {yε : TrivSqZeroExt K K}
    (hdual : aeval (MultipleRootBridge.xε x) (W.preΨ' 3) = 0) :
    evalBivarDual (W.ψ 3) (MultipleRootBridge.xε x) yε = 0 := by
  -- `W.preΨ'_three = W.Ψ₃` and `W.ψ_three = C W.Ψ₃`.
  -- Evaluation of `C W.Ψ₃` at `(xε,yε)` is just aeval xε W.Ψ₃.
  simpa [WeierstrassCurve.preΨ'_three, WeierstrassCurve.ψ_three,
    evalBivarDual] using hdual
```

This is easy/mechanical.

### Lemma B2: `φ₃(P) ≠ 0` at a non-2-torsion `ψ₃` root

This is your Seam C specialized to `n=3`.  It can be proved either from the already-proved no-adjacent theorem or directly from small resultants:

```text
φ₃ = X*Ψ₃² - preΨ₄*Ψ₂Sq.
```

At `Ψ₃(x)=0`, this becomes

```text
φ₃(P) = - preΨ₄(x) * Ψ₂Sq(x).
```

Non-2-torsion gives `Ψ₂Sq(x) ≠ 0`; the small resultant `Ψ₃` vs `preΨ₄` gives `preΨ₄(x) ≠ 0` on an elliptic curve.  Or use your no-adjacent theorem.

```lean
lemma φ_three_eval_ne_zero_of_ψ_three_eval_zero_non_two
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {x y : K}
    (hP : W.Equation x y)
    (hψ3 : evalBivar (W.ψ 3) x y = 0)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    evalBivar (W.φ 3) x y ≠ 0 := by
  -- Use Seam C / no_adjacent_preΨ_zero, or the explicit `Φ_three` formula plus
  -- the small resultant cert `Ψ₃` vs `preΨ₄` and non-2-torsion.
  sorry
```

### Lemma B3: `ω₃(P) ≠ 0`, and hence `ω₃(Pε)` is a unit

From the projective equation at `Z=0`:

```text
ω₃(P)^2 = φ₃(P)^3
```

up to the exact Mathlib Jacobian convention.  Thus `φ₃(P) ≠ 0 → ω₃(P) ≠ 0`.

```lean
lemma ω_three_eval_ne_zero_of_ψ_three_eval_zero
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {x y : K}
    (hP : W.Equation x y)
    (hψ3 : evalBivar (W.ψ 3) x y = 0)
    (hφ3 : evalBivar (W.φ 3) x y ≠ 0) :
    evalBivar (W.ω 3) x y ≠ 0 := by
  -- Use `divPolyRep_equation` or projective formula for n=3, then set Z=0.
  -- If omega3 is explicitly defined, this can also be checked by direct polynomial identity.
  sorry

lemma ω_three_dual_isUnit
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K)
    {x y : K} {xε yε : TrivSqZeroExt K K}
    (hxε : TrivSqZeroExt.fst xε = x)
    (hyε : TrivSqZeroExt.fst yε = y)
    (hω3 : evalBivar (W.ω 3) x y ≠ 0) :
    IsUnit (evalBivarDual (W.ω 3) xε yε) := by
  -- In dual numbers over a field, an element is a unit iff its `fst` part is nonzero.
  -- The `fst` of the bivariate dual evaluation is the base bivariate evaluation.
  sorry
```

This is easy once B3 is available.

### Lemma B4: fixed `n=3` projective formula over dual numbers

This is the fixed-`n` version of the projective bridge:

```lean
lemma projective_formula_three_dual
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {xε yε : TrivSqZeroExt K K}
    (hPε : /* dual point lies on W */ True) :
    -- `[3]Pε` is represented by
    --   ![evalBivarDual (W.φ 3) xε yε,
    --     evalBivarDual (W.ω 3) xε yε,
    --     evalBivarDual (W.ψ 3) xε yε]
    True := by
  -- For n=3 this can be proved from raw Jacobian formulas:
  --   [2]Pε = dblXYZ(Pε), then [3]Pε = addXYZ(Pε,[2]Pε)
  -- or by a direct fixed polynomial certificate.
  -- It must not use separability.
  sorry
```

For `n=3`, this is a finite polynomial identity and should be much smaller than the general theorem.

### Lemma B5: local parameter coefficient is zero if `ψ₃(Pε)=0`

The local parameter at `O` in Jacobian coordinates is

```text
t = -X*Z/Y.
```

Using B4:

```text
t([3]Pε) = - φ₃(Pε) * ψ₃(Pε) / ω₃(Pε).
```

If `ψ₃(Pε)=0` and `ω₃(Pε)` is a unit, this is zero, hence its ε-coefficient is zero.

```lean
lemma localCoeff_three_nsmul_eq_zero_of_ψ_three_dual_zero
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {xε yε : TrivSqZeroExt K K}
    (hproj3 : /* projective_formula_three_dual output */ True)
    (hψ3ε : evalBivarDual (W.ψ 3) xε yε = 0)
    (hω3unit : IsUnit (evalBivarDual (W.ω 3) xε yε)) :
    -- coefficient of ε in local parameter `t([3]Pε)` is zero
    True := by
  -- `t = -X*Z/Y`; substitute `Z = ψ₃(Pε)` and use `hψ3ε`.
  sorry
```

This is easy dual-number algebra.

### Lemma B6: identify the local coefficient with `TangentO.nsmul₁`

This is the exact bottleneck lemma.

```lean
lemma localCoeff_three_nsmul_eq_TangentO_nsmul₁
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {x y : K} {yε : TrivSqZeroExt K K}
    (hP : W.Equation x y)
    (hdualPoint : /* `(x+ε,yε)` lies on W */ True)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    -- coefficient of ε in local parameter `t([3]Pε)`
    -- equals the abstract tangent-map output
    /* localCoeff t([3]Pε) */ = TangentO.nsmul₁ W 3 1 := by
  -- This is the missing bridge from the projective/functor-of-points calculation to the
  -- existing abstract `TangentO` API.
  -- It is the fixed-n=3 instance of the general theorem:
  --   localCoeff t([n]Pε) = TangentO.nsmul₁ W n 1.
  sorry
```

This is the theorem that says your abstract tangent formalism is about the same actual map as the projective division-polynomial formula.

### Honest `n=3` assembly

```lean
theorem dual_root_implies_tangent_zero_three_projective
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {x y : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hdual : aeval (MultipleRootBridge.xε x) (W.preΨ' 3) = 0) :
    TangentO.nsmul₁ W 3 1 = 0 := by
  -- Build yε using existing lift theorem.
  let xε := MultipleRootBridge.xε x
  let yε := /* AffineJet.equation_dual_lift_of_polynomialY_ne_zero ... */ Classical.choice inferInstance

  have hψ3ε : evalBivarDual (W.ψ 3) xε yε = 0 := by
    exact ψ_three_dual_eq_zero_of_preΨ'_three_dual_eq_zero (W := W) hdual

  have hψ3_base : evalBivar (W.ψ 3) x y = 0 := by
    -- apply `TrivSqZeroExt.fst` to hψ3ε
    sorry

  have hφ3 : evalBivar (W.φ 3) x y ≠ 0 :=
    φ_three_eval_ne_zero_of_ψ_three_eval_zero_non_two (W := W) hP hψ3_base hY

  have hω3 : evalBivar (W.ω 3) x y ≠ 0 :=
    ω_three_eval_ne_zero_of_ψ_three_eval_zero (W := W) hP hψ3_base hφ3

  have hω3unit : IsUnit (evalBivarDual (W.ω 3) xε yε) := by
    exact ω_three_dual_isUnit (W := W) (x := x) (y := y) (xε := xε) (yε := yε)
      (by simp [xε]) (by /* fst of yε is y */ sorry) hω3

  have hproj3 := projective_formula_three_dual (W := W) (xε := xε) (yε := yε) (by
    -- existing dual equation theorem/lift
    trivial)

  have hlocal0 := localCoeff_three_nsmul_eq_zero_of_ψ_three_dual_zero
    (W := W) hproj3 hψ3ε hω3unit

  have hlocalEq := localCoeff_three_nsmul_eq_TangentO_nsmul₁
    (W := W) hP (by trivial) hY

  -- Rewrite the zero local coefficient through the identification lemma.
  exact by
    -- `simpa [hlocalEq] using hlocal0`, depending on the localCoeff representation.
    sorry
```

---

## Minimal additional lemmas, classified

For **`n = 3` via separability shortcut**:

```text
S1. dual_root_eval_and_deriv_zero                 already/easy
S2. preΨ'_three_separable                         already proved by Bezout
S3. Separable.eval₂_derivative_ne_zero            Mathlib
```

That is all.  This proves the theorem by contradiction, but it is not the intended non-circular bridge.

For **honest `n = 3` projective bridge**:

```text
B1. ψ_three_dual_eq_zero_of_preΨ'_three_dual_eq_zero       easy
B2. φ_three_eval_ne_zero_of_ψ_three_eval_zero_non_two      already Seam C / small resultants
B3. ω_three_eval_ne_zero_of_ψ_three_eval_zero              easy after projective equation at Z=0
B4. projective_formula_three_dual                          fixed finite polynomial identity
B5. localCoeff_three_nsmul_eq_zero_of_ψ_three_dual_zero    easy local-parameter algebra
B6. localCoeff_three_nsmul_eq_TangentO_nsmul₁              bottleneck / conceptual bridge
```

If B6 is already implicit in your `TangentO` definitions, expose it as a theorem.  If it is not, this is the exact theorem to build next.

---

## What this says for general `n`

For general `n`, the corresponding bottleneck lemma is:

```lean
/-- General projective/formal bridge: the projective local parameter coefficient of `[n]Pε`
computed from `[φₙ:ωₙ:ψₙ]` is the same scalar as the abstract tangent map. -/
theorem localCoeff_nsmul_eq_TangentO_nsmul₁
    {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ)
    {x y : K} {yε : TrivSqZeroExt K K}
    (hP : W.Equation x y)
    (hdualPoint : /* `(x+ε,yε)` lies on W */ True)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    /* coeffε of t([n]Pε), using projective div-poly formula */
      = TangentO.nsmul₁ W n 1 := by
  sorry
```

Everything else in the final contradiction is algebraic:

```text
preΨ'_n dual root
  ⇒ full ψₙ(Pε)=0                         -- parity + ψ₂ unit
  ⇒ localCoeff(t([n]Pε)) = 0              -- projective formula + ωₙ unit
  ⇒ TangentO.nsmul₁ W n 1 = 0             -- bottleneck identification
  ⇒ (n : K) = 0                           -- formalNsmul_coeff_one / nsmul₁_eq_natCast_mul
  contradiction.
```

So the minimal set of extra lemmas to close bridge-2 is:

```text
1. full/reduced ψ dual zero conversion              -- general parity lemma, moderate
2. ωₙ(Pε) unit at ψₙ-root                           -- Seam C + equation at Z=0, moderate
3. local parameter formula from [φₙ:ωₙ:ψₙ]           -- easy once projective formula exists
4. projective division-polynomial formula            -- hard, already being built
5. localCoeff_nsmul_eq_TangentO_nsmul₁               -- the real bridge to existing TangentO API
```

For `n = 3`, (1) is trivial and (4) is a fixed finite polynomial identity.  Therefore the fixed-`n=3` exercise isolates (5) as the conceptual bottleneck.

## Final recommendation

Before pushing further on general `n`, implement the fixed theorem

```lean
localCoeff_three_nsmul_eq_TangentO_nsmul₁
```

with all projective objects concrete.  If that theorem is easy because of how `TangentO` is defined, then the remaining work is mostly the general projective formula.  If that theorem is hard, it means the existing `TangentO` API is still disconnected from the actual Weierstrass multiplication map, and no amount of `ωₙ` algebra will close bridge-2 until that identification is added.
