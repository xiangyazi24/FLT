# Q370 (dm1): minimal construction for the tangent bridge

## Executive answer

A dummy first-order formal group with law

```text
F(T₁,T₂) = T₁ + T₂
```

is only the **additive formal group**.  It is easy to define and proves

```lean
formalNsmul_coeff_one F n = (n : K)
```

but it does **not** connect to the Weierstrass curve unless you also prove that the local parameter

```text
t = -X*Z/Y
```

linearizes the actual Weierstrass addition/multiplication map to this additive law.  That identification is exactly the tangent bridge.  So a fake/minimal `W.formalGroupFirstOrder` is about 20 lines, but the theorem that makes it relevant is still the real work.

The absolute minimum is therefore **not** a `FormalGroup` instance.  The absolute minimum is one first-order compatibility theorem:

```lean
localCoeff_t_nsmul_eq_TangentO_nsmul₁
```

stating that the ε-coefficient of the projective local parameter of the actual `[n]` image equals the scalar produced by your existing `TangentO.nsmul₁` API.  Once that theorem exists, everything else in bridge-2 is algebraic.

---

## Why the additive dummy formal group is not enough

Your existing theorem is abstract:

```lean
formalNsmul_coeff_one : coeff_T ([n]_F(T)) = (n : K)
```

for a formal group law `F`.  If you instantiate `F` as the additive formal group, you prove a theorem about the additive formal group, not about `W`.

The missing statement is:

```text
The first-order local parameter of actual Weierstrass addition agrees with the additive tangent law.
```

Over dual numbers, this is the concrete identity:

```text
t(Pε + Qε) = t(Pε) + t(Qε)
```

whenever `Pε,Qε` are first-order points in the infinitesimal neighborhood of `O`, and therefore

```text
t([n]Pε) = n * t(Pε).
```

This is true because every higher-order term in the genuine Weierstrass formal group vanishes modulo `ε²`, but Lean still needs the theorem connecting the projective formulas to the scalar `t`.

So:

```text
additive formal group instance:         20 lines, irrelevant alone
first-order compatibility with W:       real bridge, probably 100–300 lines
full W.formalGroup power series:        larger, probably 500+ lines
```

---

## The minimal theorem to prove

Use the projective/local-parameter side as the source of truth.  Define a small scalar function for the ε-coefficient of `t = -X*Z/Y` on a dual-number Jacobian representative.

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Schematic: ε-coefficient of the projective local parameter `t = -X*Z/Y`. -/
def localTangentCoeffAtO
    (P : Fin 3 → TrivSqZeroExt K K)
    (hY : IsUnit (P 1)) : K :=
  -- In implementation: compute `-(P 0)*(P 2)/(P 1)` in dual numbers,
  -- then take `TrivSqZeroExt.snd`.
  TrivSqZeroExt.snd (-(P 0) * (P 2) / (P 1))

/-- The absolute minimum bridge: the projective local-parameter coefficient of the actual
multiplication-by-`n` image equals the abstract tangent scalar. -/
theorem localCoeff_t_nsmul_eq_TangentO_nsmul₁
    (n : ℕ)
    {x y : K} {yε : TrivSqZeroExt K K}
    (hP : W.Equation x y)
    (hdual : /* `(x+ε,yε)` lies on W over dual numbers */ True)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    -- Schematic RHS: the same scalar from the projective `[n]` formula.
    -- The LHS should be `localTangentCoeffAtO W ([n]Pε) ...` once `[n]Pε`
    -- is represented by your projective division-polynomial formula.
    True := by
  sorry

end

end WeierstrassCurve
```

In the final bridge proof, the left side will be computed from the projective division-polynomial representative

```text
[φₙ(Pε) : ωₙ(Pε) : ψₙ(Pε)]
```

and the local parameter

```text
t = -X*Z/Y.
```

The theorem says this is the same first-order tangent scalar as `TangentO.nsmul₁ W n 1`.

---

## If you want a smaller local version first

Before proving the theorem for all `n`, prove the fixed map version for a generic projective representative near `O`.

```lean
/-- First-order local parameter calculation for a representative reducing to `O`. -/
theorem localTangentCoeffAtO_eq_snd_t
    (P : Fin 3 → TrivSqZeroExt K K)
    (hY : IsUnit (P 1)) :
    localTangentCoeffAtO (W := W) P hY =
      TrivSqZeroExt.snd (-(P 0) * (P 2) / (P 1)) := rfl
```

Then specialize to the projective division-polynomial representative:

```lean
/-- Projective formula gives the local parameter of `[n]Pε`. -/
theorem localCoeff_t_nsmul_from_divPolyRep
    (n : ℕ)
    {x y : K} {xε yε : TrivSqZeroExt K K}
    (hproj :
      -- `[n]Pε` is represented by `[φₙ(Pε), ωₙ(Pε), ψₙ(Pε)]`
      True)
    (hωunit : IsUnit (/* ωₙ(Pε) */ (1 : TrivSqZeroExt K K))) :
    -- local coeff = snd(-φₙ(Pε)*ψₙ(Pε)/ωₙ(Pε))
    True := by
  sorry
```

This theorem is pure dual-number algebra once the projective formula is available.

The only remaining conceptual step is to identify this `localCoeff_t_nsmul_from_divPolyRep` with `TangentO.nsmul₁`.

---

## How to connect with existing `TangentO`

Since `TangentO` is already `K`, do not make another wrapper.  Add a theorem that states what its scalar means in the projective local parameter.

```lean
namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Meaning theorem for the existing abstract `TangentO` scalar.  This is the bridge. -/
theorem TangentO.nsmul₁_eq_localCoeff_t_nsmul
    (n : ℕ)
    {x y : K} {yε : TrivSqZeroExt K K}
    (hP : W.Equation x y)
    (hdual : /* `(x+ε,yε)` lies on W */ True)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    TangentO.nsmul₁ W n 1 =
      -- local coefficient of `t` for the actual/projective `[n]` image
      -- of `(x+ε,yε)`
      (0 : K) := by
  -- The RHS placeholder should be replaced by your `localTangentCoeffAtO` expression.
  -- Prove it by showing the input tangent scalar is `1 / ψ₂(P)` or by aligning
  -- your existing `TangentO` convention with the local parameter convention.
  sorry

end

end WeierstrassCurve
```

This theorem should probably be stated with the RHS as a named expression rather than `(0 : K)`; the sketch uses `(0 : K)` only because the exact local-coefficient expression depends on your projective-formula representation.

---

## What the bridge-2 assembly becomes

Once the meaning theorem exists, bridge-2 has this shape:

```lean
theorem dual_root_implies_tangent_zero
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} {x y : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hdualRoot : aeval (MultipleRootBridge.xε x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ W n 1 = 0 := by
  -- 1. Build yε from the dual-lift theorem.
  -- 2. Convert `preΨ'_n(xε)=0` to full `ψₙ(Pε)=0` using `ψ₂` unit.
  -- 3. Projective formula says `[n]Pε` is represented by `[φₙ,ωₙ,ψₙ]`.
  -- 4. Since `ψₙ(Pε)=0`, local parameter `t=-X*Z/Y` has coeff 0.
  -- 5. Use `TangentO.nsmul₁_eq_localCoeff_t_nsmul` to rewrite that coeff as
  --    `TangentO.nsmul₁ W n 1`.
  sorry
```

All difficult algebra is in steps 2–4 and the projective formula; the **definition-level bridge** is step 5.

---

## Answer to the “20 lines or 200 lines?” question

* Defining an additive `FormalGroup` with `F=T₁+T₂`: around 20 lines if your `FormalGroup` structure is lightweight.
* Making it a legitimate `W.formalGroupFirstOrder`: not legitimate unless you prove the local parameter of `W` uses that law to first order.
* Proving the actual first-order compatibility theorem: likely 100–300 lines, depending on how much projective dual-number boilerplate is already available.

The shortest honest route is to **skip the dummy `FormalGroup` instance** and prove the compatibility theorem directly for `TangentO` and the projective local parameter.

---

## Final recommendation

Do not define `W.formalGroupFirstOrder : FormalGroup K` unless it is just a renamed additive formal group used internally.  It will not by itself close bridge-2.

Define instead:

```lean
localTangentCoeffAtO : (Fin 3 → TrivSqZeroExt K K) → ... → K
```

and prove one meaning theorem:

```lean
TangentO.nsmul₁_eq_localCoeff_t_nsmul
```

That is the absolute minimum bridge.  It directly connects the two sides you need:

```text
projective local parameter coefficient  =  abstract TangentO scalar.
```

Everything else is algebraic assembly around that theorem.
