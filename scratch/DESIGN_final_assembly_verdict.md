# Q356 (dm3): Final assembly from projective formula to bridge-2 closure

## Definitive assessment

With assumptions 1–8 exactly as listed, the requested theorem

```lean
theorem preΨ'_deriv_ne_zero_at_nontorsion_root [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hroot : (W.preΨ' n).eval x = 0) :
    (derivative (W.preΨ' n)).eval x ≠ 0
```

**still cannot be closed non-circularly.**  The missing theorem is precisely the
identification of the dual-number/local-parameter coefficient of the projective
formula with the tangent map of the group endomorphism `[n]`:

```text
coeffε(t_O([n]Pε)) = (n : K) · coeffε(t_P(Pε)).
```

Equivalently, one needs one of the following bridge lemmas:

```text
TangentO.nsmul₁ = n,
formalNsmul_coeff_one transported to the geometric local parameter,
[n] is étale/unramified when (n : K) ≠ 0,
```

or a non-circular `IsCoprime (W.preΨ' n) (derivative (W.preΨ' n))`, for example
from a Bezout/resultant certificate.

The projective formula plus ATOMS 5–7 proves the formula for the output local
parameter coefficient:

```text
coeffε(t_O([n]Pε))
  = - φ_n(P) / ω_n(P) · parityUnit(P) · (preΨ'_n)'(x).
```

If `(preΨ'_n)'(x)=0`, this coefficient is `0`.  But to contradict
`(n : K) ≠ 0`, one must know independently that the same coefficient is
`(n : K)` times the nonzero input tangent coefficient.  That is exactly the
TangentO/formal-group bridge.  It is not contained in the projective formula
itself.

So the honest final assembly theorem is not the original theorem, but the original
theorem **with one additional bridge hypothesis**.  Once that bridge is supplied,
the final assembly is straightforward.

---

## What ATOMS 5–7 actually give

At a non-2-torsion root of `preΨ'_n`, after the projective X/Y/Z formulas land,
we have:

1. `ψ_n(P)=0`, so the projective representative of `[n]P` has `Z = 0`.
2. `no_adjacent_preΨ_zero` plus the definition of `φ_n` gives `φ_n(P) ≠ 0`.
3. ATOM 5 gives `ω_n(P) ≠ 0` from the curve equation at `Z=0`.
4. ATOM 6 gives

   ```text
   coeffε(t_O([n]Pε)) = -φ_n(P)/ω_n(P) · snd(ψ_n(Pε)).
   ```

5. ATOM 7 gives

   ```text
   snd(ψ_n(Pε)) = parityUnit(P) · (preΨ'_n)'(x).
   ```

6. Bridge-1 gives `Ψ₂Sq(P) ≠ 0`, hence the parity factor is a unit in the even
   case; in the odd case it is `1`.

Therefore the purely projective/dual-number part proves:

```text
coeffε(t_O([n]Pε))
  = unit · (preΨ'_n)'(x),
```

where

```text
unit = -φ_n(P)/ω_n(P) · parityUnit(P) ≠ 0.
```

This is a correct and useful theorem.  It identifies the derivative of the
x-division polynomial with the tangent coefficient of `[n]` at that torsion point,
up to a nonzero scalar.

But it is only half the proof of derivative nonvanishing.  The other half is that
`[n]` has nonzero tangent coefficient when `(n : K) ≠ 0`.

---

## The missing bridge theorem to add

The exact theorem should be stated at the same abstraction level as ATOMS 6–7: a
chosen dual deformation `Pε` of `P` with input local parameter coefficient `1`, and
`[n]Pε` computed by the projective formula.

A good seam theorem is:

```lean
/--
Tangent bridge for the local parameter used in the projective formula.

This is the missing non-algebraic input.  It says that the first-order coefficient
of the local parameter at the output of `[n]` is multiplication by `(n : K)` on the
input tangent coefficient.
-/
theorem coeff_t_output_nsmul_eq_natCast_mul_coeff_input
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    -- `Pε` is the chosen tangent vector at `(x,y)`, usually `x + ε`,
    -- `y + ε*slope` with curve equation over dual numbers.
    (Pε : /* dual affine point data */ Sort _)
    (hInputCoeff : inputLocalCoeff W x y Pε = 1) :
    outputLocalCoeffOfNsmul W n Pε = (n : K) := by
  -- This should be proved from `formalNsmul_coeff_one`, or from the tangent map
  -- of the elliptic curve group law.
  sorry
```

Depending on the local API, it may be cleaner to state the bridge directly in the
formal group coordinates:

```lean
theorem formal_tangent_coeff_nsmul
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) :
    coeffε ([n]^* t) = (n : K) * coeffε t := by
  exact W.formalNsmul_coeff_one n
```

but then you need an additional identification lemma between the formal parameter
`t` and the projective local parameter

```text
t_O = -X*Z/Y
```

used by ATOM 6.

The essential point: the bridge must identify the **same local parameter** and the
**same dual-number deformation** used in the projective formula.  A theorem about
some formal coordinate is not enough until the coordinate-identification lemma is
proved.

---

## Correct final assembly shape with the tangent bridge

Below is the theorem shape that can close once ATOMS 5–7 and the tangent bridge
are available.  This is intentionally schematic at the atom-API boundaries, since
those theorem names/data structures are project-local.

```lean
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

namespace WeierstrassCurve

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Parity factor in ATOM 7. -/
noncomputable def preΨParityUnit
    (W : WeierstrassCurve K) (n : ℕ) (x y : K) : K :=
  if Even n then W.Ψ₂Sq.eval x else 1

/-- The final derivative-nonvanishing theorem, assuming the tangent bridge. -/
theorem preΨ'_deriv_ne_zero_at_nontorsion_root_of_tangent_bridge
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hroot : (W.preΨ' n).eval x = 0)
    -- Bridge-1 / non-2-torsion root input.
    (hΨ₂ : W.Ψ₂Sq.eval x ≠ 0)
    -- From no_adjacent_preΨ_zero + φ definition at ψ_n=0.
    (hφ : phiEval W n x y ≠ 0)
    -- ATOM 5 result.
    (hω : omegaEval W n x y ≠ 0)
    -- ATOM 6 + ATOM 7 combined.
    (hCoeffFormula :
      outputCoeff W n x y =
        (-phiEval W n x y / omegaEval W n x y)
          * preΨParityUnit W n x y
          * (Polynomial.derivative (W.preΨ' n)).eval x)
    -- TangentO/formal-group bridge for the same chosen deformation.
    (hTangent : outputCoeff W n x y = (n : K)) :
    (Polynomial.derivative (W.preΨ' n)).eval x ≠ 0 := by
  intro hderiv

  have hParity : preΨParityUnit W n x y ≠ 0 := by
    unfold preΨParityUnit
    split_ifs with hnEven
    · exact hΨ₂
    · exact one_ne_zero

  have hUnit :
      (-phiEval W n x y / omegaEval W n x y)
          * preΨParityUnit W n x y ≠ 0 := by
    exact mul_ne_zero
      (neg_ne_zero.mpr (div_ne_zero hφ hω))
      hParity

  have hOutZero : outputCoeff W n x y = 0 := by
    simp [hCoeffFormula, hderiv]

  have hOutNonzero : outputCoeff W n x y ≠ 0 := by
    rw [hTangent]
    exact hn

  exact hOutNonzero hOutZero

end WeierstrassCurve
```

In the real file, the placeholder symbols should be replaced by your atom APIs:

```lean
phiEval      := evaluated φ_n at `(x,y)`
omegaEval    := evaluated ω_n at `(x,y)`
outputCoeff  := `snd(t_O([n]Pε))`
hCoeffFormula := ATOM 6 + ATOM 7
hTangent      := TangentO/formal group bridge
```

The proof body is the entire final assembly.  The only nontrivial dependencies are
proving `hφ`, `hω`, `hCoeffFormula`, and `hTangent` upstream.

---

## Why projective formula evaluated at dual numbers does not close by itself

Suppose `(preΨ'_n)'(x)=0`.  ATOMS 6–7 imply

```text
snd(ψ_n(Pε)) = 0,
```

and therefore the dual-number representative has

```text
[n]Pε = [φ + εa : ω + εb : 0]
```

in the projective formula, with `φ ≠ 0` and `ω ≠ 0`.

This says that the **projective local parameter coefficient at infinity is zero**.
It does not by itself contradict anything.  A nonzero tangent vector at the input
can map to a zero tangent vector under a morphism if the morphism is ramified or
inseparable.  The statement that this cannot happen for `[n]` when `(n : K) ≠ 0`
is exactly:

```text
d[n] is multiplication by n on the tangent line,
```

or, equivalently, `[n]` is étale/unramified at that point.

Thus the argument

```text
projective formula + derivative zero ⇒ output first-order tangent is zero
```

is only a computation of the differential.  To get a contradiction, you need the
independent theorem that the differential is nonzero.  That theorem is the formal
content of `formalNsmul_coeff_one` after transporting it to the projective local
parameter.

---

## Why `IsCoprime` closure is circular here

The alternative closure

```lean
IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
```

immediately gives

```text
¬ (preΨ'_n(x)=0 ∧ (preΨ'_n)'(x)=0).
```

But this is exactly the desired separability brick.  If `IsCoprime` is obtained
from per-`n` Bezout/resultant certificates, then it is a valid independent route.
If it is assumed in the proof of

```lean
preΨ'_deriv_ne_zero_at_nontorsion_root
```

then the proof is circular.

So there are only two non-circular closures:

1. **Certificate closure:** prove `IsCoprime` independently by Bezout/resultants.
2. **Tangent closure:** prove the `TangentO`/formal-group bridge independently,
   then use ATOMS 5–7.

The projective formula infrastructure is valuable for tangent closure, but it is
not itself the tangent closure.

---

## Minimal remaining theorem after projective infrastructure

After addX/addY/addZ/dblZ and ATOMS 5–7 are all proved, the only missing theorem
for the local-parameter route is:

```lean
/--
For the same dual-number deformation used in ATOMS 6–7, the coefficient of the
output local parameter under `[n]` is `(n : K)` times the input coefficient.
-/
theorem projectiveLocalCoeff_nsmul
    {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (Pε : /* chosen dual tangent point */ Sort _)
    (hPε : /* Pε lies on W over dual numbers */ True)
    (hInput : inputLocalCoeff W x y Pε = 1) :
    outputLocalCoeffOfProjectiveFormula W n Pε = (n : K) := by
  -- Prove by transporting `formalNsmul_coeff_one` to the projective local
  -- parameter `t_O = -X*Z/Y`.
  sorry
```

A slightly lower-level and often cleaner split is:

```lean
theorem formalParameter_eq_projectiveLocalParameter_at_O :
    formal_t = -X*Z/Y + higher_order_terms_matching_to_first_order := by
  ...

theorem coeff_formal_nsmul :
    coeffε (([n])^* formal_t) = (n : K) * coeffε formal_t := by
  exact formalNsmul_coeff_one ...
```

Then combine them to get `projectiveLocalCoeff_nsmul`.

This is the real final seam.

## Final recommendation

Do not try to state

```lean
preΨ'_deriv_ne_zero_at_nontorsion_root
```

as a 0-sorry theorem from assumptions 1–8 alone.  It is missing the tangent
bridge and cannot be proved non-circularly.

Instead, proceed in one of these two ways:

* For the quickest Mazur `n ≤ 16` closure, use the per-`n` Bezout/resultant
  `IsCoprime` certificates.
* For the all-`n` conceptual proof, add the single remaining theorem
  `projectiveLocalCoeff_nsmul` / `TangentO.nsmul₁`, then the final assembly proof
  above becomes short and completely formal.
