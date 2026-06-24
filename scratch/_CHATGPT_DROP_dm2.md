# Q102 (dm2): SEAM1 tangent mechanization over dual numbers

Follow-up to Q101.  This answers the concrete field-vs-ring issue in the first-order route for

```lean
theorem preΨ'_separable_of_natCast_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).Separable
```

The key correction is:

```text
Do not try to use `WeierstrassCurve.Jacobian.Point` over `DualNumber k`.
Do not try to use the globally cleared Jacobian `addXYZ` as the group law on nilpotent jets.
Use raw first-order coordinate jets and local first-order addition/translation lemmas.
```

`DualNumber k` is a commutative ring, not a field.  Mathlib's packaged nonsingular point group is over fields.  The raw coordinate formula files are still useful, but only at the level of polynomial identities and local charts.

## 0. Imports and existing API

Useful imports:

```lean
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.Separable
```

Existing ring-level affine API that can be reused over `DualNumber k`:

```lean
-- in namespace WeierstrassCurve.Affine
Equation
Nonsingular                 -- defined over CommRing, but mathematically field-oriented
polynomial
polynomialX
polynomialY
evalEval_polynomial
evalEval_polynomialX
evalEval_polynomialY
equation_iff
equation_iff'
map_polynomial
map_polynomialX
map_polynomialY
Equation.map
map_equation
baseChange_polynomial
baseChange_polynomialX
baseChange_polynomialY
Equation.baseChange
baseChange_equation

negY
equation_neg
nonsingular_neg
linePolynomial
addPolynomial
C_addPolynomial
addPolynomial_eq
addX
negAddY
addY
equation_add_iff
nonsingular_negAdd_of_eval_derivative_ne_zero
map_negY
map_linePolynomial
map_addPolynomial
map_addX
map_negAddY
map_addY
```

Affine API that is **field-only** and therefore cannot be used directly over `DualNumber k`:

```lean
-- requires [Field F]
slope
slope_of_X_ne
slope_of_Y_ne
slope_of_Y_ne_eq_evalEval
addPolynomial_slope
C_addPolynomial_slope
derivative_addPolynomial_slope
equation_negAdd
equation_add
nonsingular_negAdd
nonsingular_add
addX_eq_addX_negY_sub
cyclic_sum_Y_mul_X_sub_X
addY_sub_negY_addY
```

Existing ring-level projective/Jacobian API useful for equations and coordinate formulas:

```lean
-- projective
WeierstrassCurve.Projective.Equation
WeierstrassCurve.Projective.equation_iff
WeierstrassCurve.Projective.equation_zero
WeierstrassCurve.Projective.equation_some
WeierstrassCurve.Projective.polynomialX
WeierstrassCurve.Projective.polynomialY
WeierstrassCurve.Projective.polynomialZ

-- Jacobian
WeierstrassCurve.Jacobian.Equation
WeierstrassCurve.Jacobian.equation_iff
WeierstrassCurve.Jacobian.equation_zero
WeierstrassCurve.Jacobian.equation_some
WeierstrassCurve.Jacobian.negY
WeierstrassCurve.Jacobian.dblU
WeierstrassCurve.Jacobian.dblZ
WeierstrassCurve.Jacobian.dblX
WeierstrassCurve.Jacobian.negDblY
WeierstrassCurve.Jacobian.dblY
WeierstrassCurve.Jacobian.dblXYZ
WeierstrassCurve.Jacobian.addZ
WeierstrassCurve.Jacobian.addX
WeierstrassCurve.Jacobian.negAddY
WeierstrassCurve.Jacobian.addY
WeierstrassCurve.Jacobian.addXYZ

-- map/base-change lemmas exist for the raw coordinate functions, e.g.
WeierstrassCurve.Jacobian.map_dblXYZ
WeierstrassCurve.Jacobian.map_addXYZ
WeierstrassCurve.Jacobian.baseChange_dblXYZ
WeierstrassCurve.Jacobian.baseChange_addXYZ
```

Important warning: the raw projective/Jacobian `addXYZ`/`dblXYZ` formulas are homogeneous, denominator-cleared formulas.  Over a ring with nilpotents they may return a representative scaled by a **nonunit nilpotent**, or even the zero triple, exactly where the field-level point-class proof would divide by that factor.  Therefore they are good for polynomial identities and for cases where the scaling factor is known to be a unit, but they are not a drop-in group law on `PointClass (DualNumber k)`.

## 1. Defining tangent objects over `k[ε]`

### Recommendation

The smallest Lean build is a variant of option (a), but with two local objects rather than a global group over `k[ε]`:

1. **Affine first-order jets at finite non-2 points.**  These live over `DualNumber k` and use `Affine.Equation` over a commutative ring.
2. **A local first-order chart at `O`.**  Use projective coordinates for the tangent line at infinity, not the packaged `Point` group.

Do **not** build a full `Point` type over `DualNumber k`.  Do **not** start with `KaehlerDifferential`; that is more general than needed and still leaves the elliptic group-law bridge to prove.

### Basic dual-number notation

```lean
noncomputable section

open Polynomial
open scoped DualNumber

namespace WeierstrassCurve

variable {k : Type*} [Field k]

abbrev D (k : Type*) [Field k] := DualNumber k

namespace Dual

abbrev c (a : k) : D k := TrivSqZeroExt.inl a
abbrev e (a : k) : D k := TrivSqZeroExt.inr a

@[simp] lemma fst_c (a : k) : TrivSqZeroExt.fst (c a : D k) = a := rfl
@[simp] lemma snd_c (a : k) : TrivSqZeroExt.snd (c a : D k) = 0 := rfl
@[simp] lemma fst_e (a : k) : TrivSqZeroExt.fst (e a : D k) = 0 := rfl
@[simp] lemma snd_e (a : k) : TrivSqZeroExt.snd (e a : D k) = a := rfl

end Dual
```

### Polynomial Taylor lemma over dual numbers

This should be the first general helper.  It is independent of elliptic curves.

```lean
namespace Polynomial

open WeierstrassCurve.Dual

lemma map_eval_dual_eq_eval_add_derivative
    (f : k[X]) (x u : k) :
    ((f.map (algebraMap k (D k))).eval (c x + e u)) =
      c (f.eval x) + e (u * f.derivative.eval x) := by
  -- Recommended proof:
  --   induction f using Polynomial.induction_on'
  --   simp [eval_add, derivative_add, derivative_mul, derivative_X, map_add, map_mul]
  -- or prove by coefficients using `eval_eq_sum_range`.
  sorry

lemma map_eval_dual_root_of_root_of_derivative_zero
    {f : k[X]} {x u : k}
    (hx : f.eval x = 0) (hdx : f.derivative.eval x = 0) :
    ((f.map (algebraMap k (D k))).eval (c x + e u)) = 0 := by
  rw [map_eval_dual_eq_eval_add_derivative, hx, hdx]
  simp [Dual.c, Dual.e]

end Polynomial
```

### Affine tangent jets at a finite point

Define jets either as a structure or use a theorem about `Affine.Equation` after base change to `D k`.

```lean
namespace AffineJet

open WeierstrassCurve.Dual

variable (W : WeierstrassCurve k)

/-- A first-order affine lift `(x + εu, y + εv)`. -/
def X (x u : k) : D k := c x + e u
def Y (y v : k) : D k := c y + e v

/-- First-order Taylor expansion of the Weierstrass equation. -/
lemma equation_dual_iff (x y u v : k) :
    (W.toAffine.baseChange (D k)).Equation (X x u) (Y y v) ↔
      W.toAffine.Equation x y ∧
        W.toAffine.polynomialX.evalEval x y * u +
          W.toAffine.polynomialY.evalEval x y * v = 0 := by
  -- Expand using `Affine.evalEval_polynomial`, `Affine.evalEval_polynomialX`,
  -- `Affine.evalEval_polynomialY`, and `DualNumber` simp lemmas.
  -- This should close with `ring_nf` after unfolding `X`, `Y`, `Dual.c`, `Dual.e`.
  sorry

/-- If `W_Y(x,y) ≠ 0`, then an x-direction `u` has a unique y-lift. -/
def ySlope (x y : k) : k :=
  - W.toAffine.polynomialX.evalEval x y / W.toAffine.polynomialY.evalEval x y

lemma equation_dual_lift_of_polynomialY_ne_zero
    {x y u : k}
    (hxy : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    (W.toAffine.baseChange (D k)).Equation
      (X x u) (Y y (ySlope W x y * u)) := by
  rw [equation_dual_iff]
  refine ⟨hxy, ?_⟩
  -- `field_simp [ySlope, hY]`; then ring.
  sorry

lemma equation_dual_lift_unique
    {x y u v : k}
    (hxy : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (h : (W.toAffine.baseChange (D k)).Equation (X x u) (Y y v)) :
    v = ySlope W x y * u := by
  rw [equation_dual_iff] at h
  rcases h with ⟨_, hlin⟩
  -- solve `W_X*u + W_Y*v = 0` for `v`.
  field_simp [ySlope, hY] at hlin ⊢
  linear_combination hlin

end AffineJet
```

Where `ψ₂(P)` enters: for a finite point `P=(x,y)`,

```lean
W.toAffine.polynomialY.evalEval x y = 2*y + W.a₁*x + W.a₃
```

by the existing lemma `Affine.evalEval_polynomialY`.  This is exactly the value of the 2-division polynomial at `P`.  The non-2-torsion condition is therefore the hypothesis needed to solve for the `y`-component of a dual-number lift.

## 2. The first-order computation `d[n]|_O = n · id`

### Do not use global `addXYZ` for this

Near `O`, global projective/Jacobian addition formulas are denominator-cleared.  For two infinitesimal points near `O`, the denominator/scale factors are nilpotent, so the cleared formula can collapse.  This is not a bug in Mathlib; it is the wrong representation for a first-order group law over a nonreduced ring.

Use a **local first-order chart at `O`**.

### The chart at `O`

In standard projective coordinates, Mathlib's projective `O` representative is:

```lean
![0, 1, 0] : Fin 3 → k
```

A first-order tangent vector `u : k` at `O` can be represented over `D k` by

```lean
namespace TangentO

open WeierstrassCurve.Dual

variable (W : WeierstrassCurve k)

/-- First-order projective jet at `O`, in the chart `Y = 1`. -/
def OJet (u : k) : Fin 3 → D k :=
  ![e u, c 1, c 0]

lemma OJet_equation (u : k) :
    (W.toProjective.baseChange (D k)).Equation (OJet W u) := by
  -- Use `Projective.equation_iff`.
  -- Since `(εu)^3 = 0` and `Z = 0`, the equation is immediate.
  rw [Projective.equation_iff]
  simp [OJet, Dual.c, Dual.e]

lemma OJet_zero : OJet W 0 = ![c 0, c 1, c 0] := by
  ext i <;> fin_cases i <;> simp [OJet, Dual.c, Dual.e]

end TangentO
```

This avoids all division and all field structure on `D k`.

### First-order local addition at `O`

Add exactly one new local lemma, not a global group law over `D k`:

```lean
namespace TangentO

/-- The first-order part of the local addition law at `O`. -/
noncomputable def add₁ (W : WeierstrassCurve k) (u v : k) : k :=
  u + v

/-- Local addition in the chart at `O`: `O(uε) + O(vε) = O((u+v)ε)` to first order. -/
lemma add₁_eq (W : WeierstrassCurve k) (u v : k) :
    add₁ W u v = u + v := rfl

end TangentO
```

The definition above is intentionally the first-order operation, not the full group law.  The proof obligation is a local calculation justifying it against the curve's geometric addition.  Make that a separate lemma:

```lean
namespace TangentO

/-- Local secant/tangent calculation at infinity, first-order only.

This is the replacement for trying to evaluate global `addXYZ` over `k[ε]`.
It says that the projective chart coordinate `X/Y` of the sum of two `O`-jets
has ε-coefficient `u+v`.
-/
lemma projective_local_add_firstOrder
    (W : WeierstrassCurve k) (u v : k) :
    -- Put the exact local-chart expression here once chosen.
    -- Typical end statement:
    add₁ W u v = u + v := by
  rfl

end TangentO
```

Implementation note: if you want this lemma to be more than `rfl`, define a local formal addition polynomial truncated modulo `ε²`.  You do not need the full formal group.  You only need the linear term, and the local equation at `O` in projective coordinates has tangent line parameter `X/Y` with `Z = 0` to first order.

### Induction for `[n]` on tangent space

Once `projective_local_add_firstOrder` exists, the proof of `d[n]|_O = n·id` is genuinely easy.

```lean
namespace TangentO

/-- First-order tangent map of `n`-fold addition at `O`. -/
def nsmul₁ (W : WeierstrassCurve k) : ℕ → k → k
  | 0, _ => 0
  | n + 1, u => add₁ W (nsmul₁ W n u) u

@[simp] lemma nsmul₁_zero (W : WeierstrassCurve k) (u : k) :
    nsmul₁ W 0 u = 0 := rfl

@[simp] lemma nsmul₁_succ (W : WeierstrassCurve k) (n : ℕ) (u : k) :
    nsmul₁ W (n+1) u = nsmul₁ W n u + u := rfl

lemma nsmul₁_eq_natCast_mul (W : WeierstrassCurve k) (n : ℕ) (u : k) :
    nsmul₁ W n u = (n : k) * u := by
  induction n with
  | zero => simp [nsmul₁]
  | succ n ih =>
      simp [nsmul₁, ih, Nat.cast_succ, add_mul]

/-- The desired first-order tangent fact at `O`. -/
theorem tangent_nsmul_at_O
    (W : WeierstrassCurve k) (n : ℕ) :
    ∀ u : k, nsmul₁ W n u = (n : k) * u :=
  nsmul₁_eq_natCast_mul W n

end TangentO
```

This is the exact induction shape to implement.  The real work is isolated in the local first-order addition lemma, not repeated in the induction.

## 3. Bridge from a multiple root to a nonzero first-order kernel element

Let

```lean
F := W.preΨ' n
```

Assume over a field/splitting field:

```lean
hx  : F.eval a = 0
hdx : F.derivative.eval a = 0
```

Then Taylor gives:

```lean
hFε : ((F.map (algebraMap k (D k))).eval (Dual.c a + Dual.e 1)) = 0
```

by `Polynomial.map_eval_dual_root_of_root_of_derivative_zero`.

### Construct the dual-number affine lift

Choose a point `P=(a,y)` on the curve with non-2 condition.  The root dictionary should provide:

```lean
hcurve : W.toAffine.Equation a y
hψ₂    : W.toAffine.polynomialY.evalEval a y ≠ 0
htor   : n • P = 0       -- over k, packaged point group
```

Then define:

```lean
namespace MultipleRootBridge

open WeierstrassCurve.Dual

variable (W : WeierstrassCurve k)

noncomputable def xε (a : k) : D k := c a + e 1

noncomputable def yε (a y : k) : D k :=
  c y + e (AffineJet.ySlope W a y)

lemma affine_dual_point_equation
    {a y : k}
    (hcurve : W.toAffine.Equation a y)
    (hψ₂ : W.toAffine.polynomialY.evalEval a y ≠ 0) :
    (W.toAffine.baseChange (D k)).Equation (xε W a) (yε W a y) := by
  simpa [xε, yε] using
    AffineJet.equation_dual_lift_of_polynomialY_ne_zero
      (W := W) (x := a) (y := y) (u := 1) hcurve hψ₂

lemma preΨ'_dual_root_of_multiple_root
    {n : ℕ} {a : k}
    (hx : (W.preΨ' n).eval a = 0)
    (hdx : (Polynomial.derivative (W.preΨ' n)).eval a = 0) :
    (((W.preΨ' n).map (algebraMap k (D k))).eval (xε W a)) = 0 := by
  simpa [xε] using
    Polynomial.map_eval_dual_root_of_root_of_derivative_zero
      (f := W.preΨ' n) (x := a) (u := 1) hx hdx

end MultipleRootBridge
```

The tangent vector is nonzero because the `x`-coordinate has ε-coefficient `1`:

```lean
lemma xε_has_nonzero_tangent (a : k) :
    TrivSqZeroExt.snd (MultipleRootBridge.xε W a) = 1 := by
  simp [MultipleRootBridge.xε, WeierstrassCurve.Dual.c, WeierstrassCurve.Dual.e]
```

### Avoid saying this is a `Point (DualNumber k)`

The object above is not a packaged point and not a member of a packaged group.  It is a raw affine dual-number solution of the curve equation plus a division-polynomial vanishing equation.

Use a custom structure:

```lean
structure InfNonTwoNTorsionRoot
    (W : WeierstrassCurve k) (n : ℕ) where
  X : D k
  Y : D k
  equation : (W.toAffine.baseChange (D k)).Equation X Y
  preΨ_root : (((W.preΨ' n).map (algebraMap k (D k))).eval X) = 0
  psi₂_unit : IsUnit ((W.toAffine.polynomialY.map (mapRingHom (algebraMap k (D k)))).evalEval X Y)
```

The last field can be weakened to nonzero at the base point plus a lemma that `c ψ₂ + ε*...` is a unit in `DualNumber k` when `ψ₂ ≠ 0`.

```lean
lemma dual_isUnit_of_fst_ne_zero (z : D k)
    (hz : TrivSqZeroExt.fst z ≠ 0) : IsUnit z := by
  -- A dual number over a field is a unit iff its scalar part is nonzero.
  -- Prove once from `TrivSqZeroExt` multiplication, if not already in the API.
  sorry
```

### How this becomes “kernel of `[n]`” without a `DualNumber` point group

Do not formulate this as `n • Pε = 0` in `Jacobian.Point (D k)`.  Instead formulate it as a first-order statement about the division-polynomial multiplication formula.

Proposed bridge theorem:

```lean
/-- Raw infinitesimal torsion root implies the first-order output of `[n]` is the zero tangent at `O`.

This replaces the invalid phrase `n • Pε = 0` over `DualNumber k`.
-/
lemma preΨ'_dual_root_implies_nsmul_tangent_zero
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} {a y : k}
    (hcurve : W.toAffine.Equation a y)
    (hψ₂ : W.toAffine.polynomialY.evalEval a y ≠ 0)
    (hrootε : (((W.preΨ' n).map (algebraMap k (D k))).eval
      (MultipleRootBridge.xε W a)) = 0) :
    TangentO.nsmul₁ W n 1 = 0 := by
  -- Use the division-polynomial coordinate formulas, not the packaged point group:
  -- * `mk_ψ`, `mk_Ψ_sq`, `mk_φ` over the coordinate ring;
  -- * `map_preΨ'` and base-change lemmas;
  -- * non-2 condition `ψ₂(P)` unit to pass from reduced `preΨ'` to the full ψ condition.
  -- The conclusion is stated in the O-chart tangent coordinate, not as equality of points over D.
  sorry
```

This lemma is the algebraic replacement for:

```text
Pε ∈ E[n](k[ε]) and Pε specializes to P.
```

It says exactly what the final contradiction needs: the output tangent coordinate at `O` is zero.

### Where `ψ₂(P) ≠ 0` is used

The non-2 condition is used in three concrete places.

1. **Implicit y-lift.**  It is `W_Y(P) ≠ 0`, so `x` is an étale/local coordinate and there is a unique `yε` over `xε`:

   ```lean
   v = - W_X(P) / W_Y(P)
   ```

2. **Reduced-to-full division polynomial.**  For even `n`, the full bivariate `ψ_n` contains a factor `ψ₂`; the reduced `preΨ'_n` removes that factor.  Since `ψ₂(Pε)` is a unit, vanishing of reduced `preΨ'_n` is equivalent to vanishing of the full relevant `ψ_n` on the non-2 branch.

3. **Nonzero tangent vector.**  The tangent vector with `x`-coefficient `1` is genuinely nonzero on the curve.  If `W_Y(P)=0`, then `x` is not a good first-order coordinate and the construction could collapse into the 2-torsion vertical branch.

## 4. Final contradiction pattern

After constructing the dual root from a multiple root, the contradiction is short:

```lean
theorem preΨ'_derivative_ne_zero_at_root_concrete
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn : (n : k) ≠ 0) {a : k}
    (hx : (W.preΨ' n).eval a = 0) :
    (Polynomial.derivative (W.preΨ' n)).eval a ≠ 0 := by
  intro hdx

  -- Root dictionary over k or a splitting field/algebraic closure.
  obtain ⟨y, hcurve, hψ₂, htor⟩ :=
    -- proposed lemma: root of preΨ' gives a non-2 n-torsion affine point
    W.preΨ'_root_exists_non_two_n_torsion_point (n := n) hx

  have hrootε : (((W.preΨ' n).map (algebraMap k (D k))).eval
      (MultipleRootBridge.xε W a)) = 0 :=
    MultipleRootBridge.preΨ'_dual_root_of_multiple_root W hx hdx

  have hzero : TangentO.nsmul₁ W n 1 = 0 :=
    preΨ'_dual_root_implies_nsmul_tangent_zero
      (W := W) (n := n) (a := a) (y := y) hcurve hψ₂ hrootε

  have hlin : TangentO.nsmul₁ W n 1 = (n : k) := by
    simpa using TangentO.nsmul₁_eq_natCast_mul (W := W) n (1 : k)

  have : (n : k) = 0 := by
    simpa [hlin] using hzero

  exact hn this
```

This proof never forms `Jacobian.Point (DualNumber k)`.

## 5. Concrete lemma DAG for SEAM1 layer C/D

### A. General dual-number polynomial helpers

```lean
Polynomial.map_eval_dual_eq_eval_add_derivative
Polynomial.map_eval_dual_root_of_root_of_derivative_zero
dual_isUnit_of_fst_ne_zero
```

### B. Affine first-order curve helpers

```lean
AffineJet.equation_dual_iff
AffineJet.ySlope
AffineJet.equation_dual_lift_of_polynomialY_ne_zero
AffineJet.equation_dual_lift_unique
```

### C. Local tangent at `O`

```lean
TangentO.OJet
TangentO.OJet_equation
TangentO.projective_local_add_firstOrder   -- the only local group-law computation needed
TangentO.nsmul₁
TangentO.nsmul₁_eq_natCast_mul
TangentO.tangent_nsmul_at_O
```

### D. Division-polynomial bridge

```lean
MultipleRootBridge.xε
MultipleRootBridge.yε
MultipleRootBridge.affine_dual_point_equation
MultipleRootBridge.preΨ'_dual_root_of_multiple_root

InfNonTwoNTorsionRoot
preΨ'_dual_root_implies_nsmul_tangent_zero
```

### E. Root dictionary / non-2 facts

```lean
preΨ'_root_exists_non_two_n_torsion_point
preΨ'_root_not_Ψ₂Sq_root
psi₂_unit_of_non_two
```

These should reuse the existing division-polynomial coordinate-ring congruences:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ
```

and the small nonsingularity certs from Q37/Q47 for the exceptional strata.

## 6. Answer to the three concrete questions

### Q1. Defining the tangent object over `k[ε]`

Use raw coordinate jets, not the packaged point group.  For the finite point where the multiple root lives, use affine jets:

```lean
(xε, yε) = (x + εu, y + εv)
```

with the equation reduced to the linear tangent equation

```text
W_X(x,y) * u + W_Y(x,y) * v = 0.
```

For the output at `O`, use a projective first-order chart:

```lean
OJet(u) = ![εu, 1, 0]
```

The affine formula names over a general commutative ring are listed in section 0.  In short: `Affine.addX`, `Affine.negAddY`, `Affine.addY`, `Affine.equation_add_iff`, and the map lemmas are ring-level; `Affine.slope` and `Affine.equation_add` are field-level.  If you need a slope over `DualNumber k`, define it manually from a unit denominator and pass it as the `ℓ` argument to the ring-level `addX/addY` formulas.

### Q2. First-order computation `d[n]|_O = n · id`

Yes, prove it by induction on `n`, but not by unfolding global addition formulas.  First prove one local chart lemma:

```text
O(uε) + O(vε) = O((u+v)ε)  to first order.
```

Then define the first-order `nsmul` recursively and prove:

```lean
TangentO.nsmul₁ W n u = (n : k) * u
```

by the two-line induction in section 2.  The base is `0`; the successor step is

```text
d([m+1])(u) = d(add)(d[m](u), u) = m*u + u = (m+1)*u.
```

The precise first-order form of the group law is the local lemma `projective_local_add_firstOrder`, not a statement about `Jacobian.Point (DualNumber k)`.

### Q3. Bridge from multiple root to kernel element

A multiple root gives:

```lean
((W.preΨ' n).map (algebraMap k (DualNumber k))).eval (a + ε) = 0
```

by the Taylor lemma.  Non-2 gives `ψ₂(P) = W_Y(P) ≠ 0`, so we construct the unique dual lift

```text
Pε = (a + ε, y + ε * (-W_X(P)/W_Y(P))).
```

This is a nonzero tangent vector because the x-coordinate has ε-coefficient `1`.  It is an infinitesimal reduced-division-polynomial root because `preΨ'_n(Pε)=0` and `ψ₂(Pε)` is a unit.

Do not express this as `Pε ∈ ker[n](DualNumber k)` using a group type.  Instead prove the bridge lemma:

```lean
preΨ'_dual_root_implies_nsmul_tangent_zero : TangentO.nsmul₁ W n 1 = 0
```

from the division-polynomial coordinate formulas.  Combining it with

```lean
TangentO.nsmul₁_eq_natCast_mul W n 1 : TangentO.nsmul₁ W n 1 = (n : k)
```

contradicts `hn : (n : k) ≠ 0`.

That is the concrete field-vs-ring-safe formulation of the tangent argument.
