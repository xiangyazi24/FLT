# Q163 (dm1): dual-number tangent roadmap for division-polynomial multiple roots

## Executive answer

For the exact dual-number argument you describe, the **mathematically right object is the formal completion / formal group of the elliptic curve**, not `WeierstrassCurve.Affine.Point`.  Current pinned Mathlib has useful pieces:

```lean
Mathlib.Algebra.TrivSqZeroExt
Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
```

but it does **not** currently package the Weierstrass formal group, the formal completion at `O`, or a group law on `WeierstrassCurve.Affine.Point` over non-field base rings such as

```lean
R := TrivSqZeroExt K K.
```

`WeierstrassCurve.Affine.Point` is field-oriented; its group structure is built for nonsingular points over a field.  Thus the formal-group route is conceptually correct but requires new infrastructure.

For the separability theorem itself, the shorter current-Mathlib path is **not** to formalize the dual-number tangent proof.  The shorter path is the pure polynomial route:

```lean
Polynomial.aeval_dual_number
  +  direct IsCoprime/Bezout certificate for W.preΨ' n and derivative (W.preΨ' n)
```

In other words, use dual numbers only to convert

```lean
aeval (x + ε) (W.preΨ' n) = 0
```

into

```lean
(W.preΨ' n).eval x = 0 ∧ derivative (W.preΨ' n).eval x = 0,
```

and then contradict a separately proved

```lean
(W.preΨ' n).Separable
-- equivalently:
IsCoprime (W.preΨ' n) (derivative (W.preΨ' n)).
```

There is no currently available Mathlib identity that directly relates

```lean
(derivative (W.preΨ' n)).eval x
```

to the tangent map of `[n]` on a Weierstrass curve.  Building such an identity would essentially require the same formal-group / group-scheme infrastructure as route (a).

Bottom line:

* If the goal is **to prove separability**, use the polynomial/Bezout route.
* If the goal is **to formalize the geometric dual-number proof**, build the minimal formal-group/functor-of-points bridge.  The hardest missing step is not dual-number algebra; it is connecting `preΨ'_n` vanishing over `K[ε]/ε²` to membership in the infinitesimal kernel of `[n]` without a group law over the dual-number ring.

---

## 0. Dual-number algebra: small and worth adding

This helper is useful in both routes.  It should be easy; it is just Taylor expansion to first order.

```lean
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

open Polynomial

namespace Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- First-order Taylor expansion in the trivial square-zero extension.

The dual element is `x + ε v`, represented as
`TrivSqZeroExt.inl x + TrivSqZeroExt.inr v`. -/
theorem aeval_trivSqZeroExt_inl_add_inr
    (p : K[X]) (x v : K) :
    aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt K K) p
      = TrivSqZeroExt.inl (p.eval x)
        + TrivSqZeroExt.inr (v * (derivative p).eval x) := by
  -- Suggested proof:
  --   induction p using Polynomial.induction_on' with
  --   | monomial n a =>
  --       reduce to `(x + εv)^n = x^n + ε * (n*x^(n-1)*v)`.
  --   | add p q hp hq => simp [hp, hq, derivative_add]
  -- or prove by `Polynomial.induction_on` using `C`, `X`, `add`, `mul`.
  -- Useful API:
  --   TrivSqZeroExt.inl, TrivSqZeroExt.inr,
  --   TrivSqZeroExt.fst, TrivSqZeroExt.snd,
  --   Polynomial.derivative_C, derivative_X, derivative_add, derivative_mul,
  --   Polynomial.aeval_def / eval₂.
  sorry

/-- Immediate corollary: a dual root gives a root and a derivative root. -/
theorem eval_and_derivative_eq_zero_of_aeval_dual_eq_zero
    {p : K[X]} {x v : K}
    (hv : v ≠ 0)
    (h : aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt K K) p = 0) :
    p.eval x = 0 ∧ (derivative p).eval x = 0 := by
  have ht := aeval_trivSqZeroExt_inl_add_inr p x v
  have hfst : p.eval x = 0 := by
    -- Apply `TrivSqZeroExt.fst` to `h` after rewriting by `ht`.
    -- `simp [ht] at h` is likely enough after unfolding the extensionality fields.
    sorry
  have hsnd : v * (derivative p).eval x = 0 := by
    -- Apply `TrivSqZeroExt.snd` to `h` after rewriting by `ht`.
    sorry
  exact ⟨hfst, (mul_eq_zero.mp hsnd).resolve_left hv⟩

end

end Polynomial
```

For your concrete deformation `x + ε·1`, `hv` is `one_ne_zero`, so the derivative vanishes.

---

## 1. Route (b): the short path currently compatible with Mathlib

This route does **not** try to prove that the dual-number point is killed by `[n]`.  It proves directly that a double root is impossible.

### Lemma chain

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

/-- The main polynomial brick, proved separately by Bezout/resultant/EDS recurrence. -/
theorem preΨ'_isCoprime_derivative_of_natCast_ne_zero
    {n : ℕ} (hn : (n : K) ≠ 0) :
    IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)) := by
  -- This is the real separability brick.
  -- For fixed n: Sylvester/Bezout certificate.
  -- For general n: EDS/resultant recurrence or a future formal-group proof.
  sorry

theorem preΨ'_separable_of_natCast_ne_zero
    {n : ℕ} (hn : (n : K) ≠ 0) :
    (W.preΨ' n).Separable := by
  rw [Polynomial.separable_def]
  exact W.preΨ'_isCoprime_derivative_of_natCast_ne_zero hn

/-- Dual-number contradiction form of separability. -/
theorem not_aeval_dual_root_preΨ'_of_natCast_ne_zero
    {n : ℕ} (hn : (n : K) ≠ 0) {x v : K} (hv : v ≠ 0) :
    ¬ aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v : TrivSqZeroExt K K)
        (W.preΨ' n) = 0 := by
  intro hdual
  have hboth := Polynomial.eval_and_derivative_eq_zero_of_aeval_dual_eq_zero
    (p := W.preΨ' n) (x := x) (v := v) hv hdual
  have hsep : (W.preΨ' n).Separable :=
    W.preΨ'_separable_of_natCast_ne_zero hn
  -- `Polynomial.Separable.eval₂_derivative_ne_zero` is already in Mathlib.
  have hder_ne : (derivative (W.preΨ' n)).eval x ≠ 0 := by
    simpa using hsep.eval₂_derivative_ne_zero (RingHom.id K) hboth.1
  exact hder_ne hboth.2

end

end WeierstrassCurve
```

This is the shortest formalization path once the separability brick is available.  It relies on existing general polynomial API:

```lean
Polynomial.Separable
Polynomial.separable_def
Polynomial.Separable.eval₂_derivative_ne_zero
Polynomial.derivative
Polynomial.aeval
```

The missing mathematical content is exactly the same brick you are already building:

```lean
IsCoprime (W.preΨ' n) (derivative (W.preΨ' n)).
```

### Why this does not prove torsion membership

This route proves the dual lift cannot exist.  It does **not** build a dual-number group law or show that the lifted point is killed by `[n]`.  For separability, that is fine and much shorter.

---

## 2. Route (a): formal-group / infinitesimal kernel route

This is the correct route if you specifically want the statement

```text
preΨ'_n(x + ε) = 0  ⇒  n • tangent = 0.
```

But current Mathlib does not appear to have the Weierstrass formal group packaged.  The minimal infrastructure should be built as a small local replacement rather than as a full scheme-theoretic theory at first.

### Step A1: dual points and tangent vectors

Define a tangent vector at a finite point by linearizing the Weierstrass equation.

```lean
namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- A tangent vector at an affine point `(x,y)` on `W`. -/
structure AffineTangentAt (x y : K) where
  dx : K
  dy : K
  lin_eq :
    -- Schematic: Fx(x,y) * dx + Fy(x,y) * dy = 0.
    -- Use the actual names from `WeierstrassCurve.Affine`:
    --   W.toAffine.polynomial,
    --   W.toAffine.polynomialY,
    -- and the X/Y partial derivative polynomial if present; otherwise expand by `ring_nf`.
    True

/-- First-order curve equation over dual numbers iff the special point is on the curve and
`(dx,dy)` satisfies the tangent equation. -/
theorem dual_equation_iff_tangent
    {x y dx dy : K} :
    W.Equation x y ∧ AffineTangentAt W x y dx dy
      ↔
    -- Schematic statement: `(x + ε dx, y + ε dy)` satisfies the Weierstrass equation
    -- over `TrivSqZeroExt K K`.
    True := by
  -- Proof uses `Polynomial.aeval_trivSqZeroExt_inl_add_inr` for the bivariate equation,
  -- or direct coordinate expansion and `TrivSqZeroExt.ext`.
  sorry

end

end WeierstrassCurve
```

For your non-2-torsion hypothesis, the important local lemma is an implicit-function step:

```lean
/-- If `∂F/∂Y` is nonzero at `(x,y)`, the tangent equation determines `dy` uniquely from `dx`. -/
theorem tangent_dy_eq_of_polynomialY_ne_zero
    {x y dx dy : K}
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (ht : AffineTangentAt W x y dx dy) :
    dy = - (/* Fx(x,y) */) / W.toAffine.polynomialY.evalEval x y * dx := by
  sorry
```

The actual `polynomialY` is available in the affine API; the X-partial may need a local expanded definition if no named partial derivative is exposed.

### Step A2: formal completion at `O`

The standard local parameter is usually

```text
t = -X/Y
```

near `O`, with another parameter

```text
w = -1/Y.
```

The formal group law is obtained by writing the group law in `t`-coordinates.

Minimal theorem to add:

```lean
/-- The Weierstrass formal group law in the local parameter at `O`. -/
noncomputable def formalGroupLaw (W : WeierstrassCurve K) :
    -- Schematic: a one-dimensional commutative formal group law over K.
    Type := by
  exact PUnit

/-- Linear term of multiplication-by-n on the Weierstrass formal group. -/
theorem formalGroup_nsmul_linearCoeff
    (W : WeierstrassCurve K) (n : ℕ) :
    -- Schematic:
    --   [n]_W(T) = C (n : K) * T + terms of order ≥ 2.
    True := by
  -- Prove by induction from the formal group law:
  --   F(T,U) = T + U + terms of total degree ≥ 2.
  -- No division-polynomial theorem should be needed here.
  sorry

/-- On dual numbers, the formal `[n]` map is scalar multiplication by `(n : K)`. -/
theorem formalGroup_nsmul_dual
    (W : WeierstrassCurve K) (n : ℕ) (v : K) :
    -- Schematic: `[n]_(formal) (ε v) = ε ((n : K) * v)`.
    True := by
  -- Follows immediately from `formalGroup_nsmul_linearCoeff`, since ε² = 0.
  sorry
```

This part is conceptually straightforward once the formal group law exists.  The formal group law itself is absent, so this is new infrastructure.

### Step A3: translate the tangent at `P` to the tangent at `O`

For a field point `P`, translation by `-P` identifies the tangent line at `P` with the tangent line at `O`.  Over dual numbers this should be the map

```text
P + εv  ↦  (P + εv) - P.
```

But this expression needs a group law over the dual-number ring or a formal/scheme-theoretic replacement.

Minimal theorem:

```lean
/-- Translation by a field-valued point identifies first-order deformations of `P`
with the formal group at `O`. -/
theorem translate_dual_point_to_formalGroup
    (W : WeierstrassCurve K) [W.IsElliptic]
    {x y : K} (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (v : AffineTangentAt W x y 1 /*s*/) :
    -- Schematic: tangent parameter in the formal group is a nonzero scalar multiple
    -- of `dx = 1`.
    True := by
  -- Needs either:
  --   * group law over `TrivSqZeroExt K K`, or
  --   * explicit local coordinate formulas for translation by `-P` to `O`.
  sorry
```

This is one of the two hard bridges.

### Step A4: connect division-polynomial vanishing over dual numbers to infinitesimal `[n]`-kernel

This is the other hard bridge, and probably the single most likely place where new infrastructure is unavoidable.

You need a theorem of the following shape:

```lean
/-- Division-polynomial criterion over dual numbers, away from the two-torsion factor. -/
theorem nsmul_dual_eq_zero_of_preΨ'_aeval_eq_zero
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} {x y s : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hpre : aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr (1 : K) : TrivSqZeroExt K K)
        (W.preΨ' n) = 0) :
    -- Schematic: the dual-number point `(x+ε, y+εs)` is killed by `[n]`.
    True := by
  -- This is not currently available from `Affine.Point`, because the group law is field-only.
  -- Prove either by:
  --   * building the projective Weierstrass group scheme/functor of points over `TrivSqZeroExt`, or
  --   * proving the division-polynomial coordinate formulas algebraically over any commutative ring
  --     and interpreting the vanishing denominators in projective coordinates.
  sorry
```

Once this is available, the desired tangent conclusion is short:

```lean
theorem tangent_killed_by_n_of_preΨ'_dual_root
    (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} {x y s : K}
    (hP : W.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hpre : aeval (TrivSqZeroExt.inl x + TrivSqZeroExt.inr (1 : K) : TrivSqZeroExt K K)
        (W.preΨ' n) = 0) :
    -- Schematic: `(n : K) • tangent = 0`.
    True := by
  have hker := nsmul_dual_eq_zero_of_preΨ'_aeval_eq_zero
    (W := W) hP hY hpre
  -- Translate to the formal group at `O`, then apply `formalGroup_nsmul_dual`.
  sorry
```

Finally, if `(n : K) ≠ 0`, scalar multiplication by `(n : K)` is injective on the one-dimensional `K`-vector space of tangents:

```lean
theorem tangent_eq_zero_of_n_tangent_eq_zero
    {n : ℕ} (hn : (n : K) ≠ 0) {v : K}
    (h : (n : K) * v = 0) : v = 0 := by
  exact (mul_eq_zero.mp h).resolve_left hn
```

This contradicts `dx = 1` after the translation/coordinate-identification lemma shows that the formal tangent parameter is a nonzero scalar multiple of the chosen deformation.

---

## 3. Route (b) as phrased in the question: no existing derivative-to-group identity

The ε-linearization itself is clean:

```lean
aeval (x + ε) (W.preΨ' n) = 0
  ⇒ (W.preΨ' n).eval x = 0
  ⇒ (derivative (W.preΨ' n)).eval x = 0.
```

But there is currently no Mathlib theorem of the form

```lean
(derivative (W.preΨ' n)).eval x = some_group_theoretic_differential_expression
```

nor a theorem identifying the derivative of `preΨ'_n` with a sum over `n`-torsion points.  The standard mathematical explanations pass through one of:

1. the differential of `[n]`,
2. reducedness/étaleness of `ker[n]`,
3. a resultant/Bezout identity showing coprimality with the derivative.

Items 1 and 2 are formal-group/group-scheme infrastructure.  Item 3 is the pure polynomial separability brick.

So route (b) is short only if you make it a direct polynomial proof:

```lean
IsCoprime (W.preΨ' n) (derivative (W.preΨ' n))
```

not if you try to route the derivative through torsion geometry.

---

## 4. Recommended implementation order

### If your goal is the separability theorem

Implement in this order:

```lean
-- 1. Generic dual-number Taylor lemma.
Polynomial.aeval_trivSqZeroExt_inl_add_inr

-- 2. Direct separability brick, by your selected polynomial method.
WeierstrassCurve.preΨ'_isCoprime_derivative_of_natCast_ne_zero

-- 3. Wrapper.
WeierstrassCurve.preΨ'_separable_of_natCast_ne_zero

-- 4. Optional: dual-number contradiction corollary.
WeierstrassCurve.not_aeval_dual_root_preΨ'_of_natCast_ne_zero
```

This path needs no group law over `TrivSqZeroExt K K`.

### If your goal is the geometric tangent proof

Implement in this order:

```lean
-- 1. Dual equation / tangent equivalence.
WeierstrassCurve.dual_equation_iff_tangent

-- 2. Minimal formal group at O and `[n]` linear term.
WeierstrassCurve.formalGroupLaw
WeierstrassCurve.formalGroup_nsmul_linearCoeff
WeierstrassCurve.formalGroup_nsmul_dual

-- 3. Translation of first-order deformations from P to O.
WeierstrassCurve.translate_dual_point_to_formalGroup

-- 4. Division-polynomial criterion over dual numbers.
WeierstrassCurve.nsmul_dual_eq_zero_of_preΨ'_aeval_eq_zero

-- 5. Tangent killed by n, then scalar injectivity from `(n : K) ≠ 0`.
WeierstrassCurve.tangent_killed_by_n_of_preΨ'_dual_root
```

The likely biggest new-infrastructure step is **Step 4**, because it asks for the division-polynomial coordinate formula for `[n]` over a non-field square-zero ring, or equivalently the functor-of-points interpretation of the kernel of `[n]`.  Step 2 is also new, but the theorem `[n](T) = nT + O(T²)` is local and relatively standard once the formal group law is defined.

---

## 5. Honest assessment

* The formal-group route is the clean mathematical proof but is not currently a small Lean patch.  It requires building at least a minimal formal completion/formal group or group functor over dual numbers.
* The derivative linearization route is already supported at the polynomial level, but Mathlib has no bridge from `derivative preΨ'_n` to the group law.  Without that bridge, it reduces to proving separability directly by `IsCoprime`/Bezout.
* Therefore, for the current FLT formalization, the shortest axiom-removal path is the pure polynomial route.  The dual-number argument is valuable as mathematical guidance, but formalizing it faithfully will probably be larger than the separability brick itself.
