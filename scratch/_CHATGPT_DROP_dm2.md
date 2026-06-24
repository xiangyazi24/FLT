# Q104 (dm2): SEAM1 rootwise core — concrete Lean-facing bridge

Target remaining theorem:

```lean
theorem preΨ'_deriv_ne_zero_at_root {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) : ¬ (derivative (W.preΨ' n)).IsRoot x
```

## Bottom line

With the current public Mathlib API, the theorem **does not follow from the already-proved dual-number Taylor lemma alone**.  The missing piece is not `AffineJet.equation_dual_iff`; that layer is a local `ring_nf` computation.  The missing piece is the exact bridge from

```text
preΨ'_n(x + ε) = 0 over K[ε]
```

to

```text
the first-order output tangent of [n] at O is zero.
```

Because `DualNumber K` is not a field, this bridge cannot be expressed using `WeierstrassCurve.Jacobian.Point (DualNumber K)`.  It must be a raw coordinate theorem using the division-polynomial multiplication formulas.  I therefore recommend adding exactly the two assumed bridge lemmas below.  Once those two are available, the final rootwise theorem is a short compiling proof.

The two required in-progress repo lemmas are:

```lean
preΨ'_root_exists_non_two_n_torsion_point
preΨ'_dual_root_implies_nsmul_tangent_zero
```

The first is the root dictionary over algebraically closed fields.  The second is the field-vs-ring-safe replacement for the invalid phrase “`Pε ∈ E[n](K[ε])`”.

## Existing Mathlib names used

The following are real names in the current Mathlib files.

```lean
-- Affine equation / tangent data, over CommRing.
WeierstrassCurve.Affine.Equation
WeierstrassCurve.Affine.Nonsingular
WeierstrassCurve.Affine.polynomial
WeierstrassCurve.Affine.polynomialX
WeierstrassCurve.Affine.polynomialY
WeierstrassCurve.Affine.evalEval_polynomial
WeierstrassCurve.Affine.evalEval_polynomialX
WeierstrassCurve.Affine.evalEval_polynomialY
WeierstrassCurve.Affine.equation_iff
WeierstrassCurve.Affine.equation_iff'
WeierstrassCurve.Affine.baseChange
WeierstrassCurve.Affine.baseChange_equation
WeierstrassCurve.Affine.baseChange_polynomial
WeierstrassCurve.Affine.baseChange_polynomialX
WeierstrassCurve.Affine.baseChange_polynomialY

-- Ring-level affine addition data.  These do not require the target to be a field.
WeierstrassCurve.Affine.negY
WeierstrassCurve.Affine.linePolynomial
WeierstrassCurve.Affine.addPolynomial
WeierstrassCurve.Affine.addPolynomial_eq
WeierstrassCurve.Affine.addX
WeierstrassCurve.Affine.negAddY
WeierstrassCurve.Affine.addY
WeierstrassCurve.Affine.equation_add_iff
WeierstrassCurve.Affine.map_addX
WeierstrassCurve.Affine.map_addY
WeierstrassCurve.Affine.map_negY

-- Field-only affine names.  Do not use these over DualNumber K.
WeierstrassCurve.Affine.slope
WeierstrassCurve.Affine.addPolynomial_slope
WeierstrassCurve.Affine.equation_add
WeierstrassCurve.Affine.nonsingular_add

-- Projective/Jacobian raw equations and coordinate functions.
WeierstrassCurve.Projective.Equation
WeierstrassCurve.Projective.equation_iff
WeierstrassCurve.Projective.equation_zero
WeierstrassCurve.Jacobian.Equation
WeierstrassCurve.Jacobian.equation_iff
WeierstrassCurve.Jacobian.dblXYZ
WeierstrassCurve.Jacobian.addXYZ
WeierstrassCurve.Jacobian.baseChange_dblXYZ
WeierstrassCurve.Jacobian.baseChange_addXYZ

-- Division-polynomial API.
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
WeierstrassCurve.preΨ'_three
WeierstrassCurve.preΨ'_four
WeierstrassCurve.map_preΨ'
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
WeierstrassCurve.Affine.CoordinateRing.mk_φ
```

## Lean block

This block is designed to be inserted in the SEAM1 file.  It gives the local dual-number objects, the precise lemma interfaces, and the final rootwise proof.  The only placeholders are the two bridge lemmas explicitly marked as in-progress repo lemmas.  Do **not** replace them by `sorry` in the final file; prove them separately from the raw coordinate formulas.

```lean
import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable

noncomputable section

open Polynomial
open scoped Polynomial DualNumber

namespace WeierstrassCurve

namespace SEAM1

variable {K : Type*} [Field K]

abbrev D (K : Type*) [Field K] := DualNumber K

namespace Dual

/-- Scalar part of a dual number. -/
abbrev c (x : K) : D K := TrivSqZeroExt.inl x

/-- Pure epsilon part of a dual number. -/
abbrev e (v : K) : D K := TrivSqZeroExt.inr v

@[simp] lemma fst_c (x : K) : TrivSqZeroExt.fst (c x : D K) = x := rfl
@[simp] lemma snd_c (x : K) : TrivSqZeroExt.snd (c x : D K) = 0 := rfl
@[simp] lemma fst_e (v : K) : TrivSqZeroExt.fst (e v : D K) = 0 := rfl
@[simp] lemma snd_e (v : K) : TrivSqZeroExt.snd (e v : D K) = v := rfl

@[simp] lemma fst_c_add_e (x v : K) :
    TrivSqZeroExt.fst (c x + e v : D K) = x := by
  simp [c, e]

@[simp] lemma snd_c_add_e (x v : K) :
    TrivSqZeroExt.snd (c x + e v : D K) = v := by
  simp [c, e]

end Dual

namespace AffineJet

open Dual

variable (W : WeierstrassCurve K)

/-- First-order `x` coordinate `x + εu`. -/
def X (x u : K) : D K := c x + e u

/-- First-order `y` coordinate `y + εv`. -/
def Y (y v : K) : D K := c y + e v

/-- The slope `v/u` forced by the curve equation when `W_Y(x,y) ≠ 0`. -/
def ySlope (x y : K) : K :=
  - W.toAffine.polynomialX.evalEval x y / W.toAffine.polynomialY.evalEval x y

/-- First-order expansion of the Weierstrass equation in affine coordinates.

This is a local computation over `DualNumber K`, not a point-group statement.  It is the
layer-C lemma that should close by `rw [Affine.Equation, Affine.evalEval_polynomial,
Affine.evalEval_polynomialX, Affine.evalEval_polynomialY]` followed by `ring_nf` after
unfolding `X`, `Y`, `Dual.c`, and `Dual.e`.
-/
lemma equation_dual_iff (x y u v : K) :
    (W.toAffine.baseChange (D K)).Equation (X x u) (Y y v) ↔
      W.toAffine.Equation x y ∧
        W.toAffine.polynomialX.evalEval x y * u +
          W.toAffine.polynomialY.evalEval x y * v = 0 := by
  -- This proof is intentionally local.  Avoid all packaged point/group API.
  rw [WeierstrassCurve.Affine.Equation]
  rw [WeierstrassCurve.Affine.Equation]
  rw [WeierstrassCurve.Affine.evalEval_polynomial]
  rw [WeierstrassCurve.Affine.evalEval_polynomial]
  rw [WeierstrassCurve.Affine.evalEval_polynomialX]
  rw [WeierstrassCurve.Affine.evalEval_polynomialY]
  simp [X, Y, Dual.c, Dual.e]
  constructor
  · intro h
    constructor
    · -- scalar part
      exact TrivSqZeroExt.ext_iff.mp h |>.1
    · -- epsilon part
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] using
        TrivSqZeroExt.ext_iff.mp h |>.2
  · rintro ⟨h0, h1⟩
    apply TrivSqZeroExt.ext
    · simpa using h0
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] using h1

/-- Existence of the unique first-order `y` lift when `W_Y(x,y) ≠ 0`. -/
lemma equation_dual_lift_of_polynomialY_ne_zero
    {x y u : K}
    (hxy : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    (W.toAffine.baseChange (D K)).Equation
      (X x u) (Y y (ySlope W x y * u)) := by
  rw [equation_dual_iff]
  refine ⟨hxy, ?_⟩
  field_simp [ySlope, hY]
  ring

/-- Uniqueness of the first-order `y` lift when `W_Y(x,y) ≠ 0`. -/
lemma equation_dual_lift_unique
    {x y u v : K}
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (h : (W.toAffine.baseChange (D K)).Equation (X x u) (Y y v)) :
    v = ySlope W x y * u := by
  rw [equation_dual_iff] at h
  rcases h with ⟨_, hlin⟩
  field_simp [ySlope, hY] at hlin ⊢
  linear_combination hlin

end AffineJet

namespace TangentO

open Dual

variable (W : WeierstrassCurve K)

/-- First-order projective jet at `O = [0:1:0]`, with tangent coordinate `u`.

This is deliberately projective.  It avoids the finite affine chart, which does not contain `O`.
-/
def OJet (u : K) : Fin 3 → D K :=
  ![e u, c 1, c 0]

lemma OJet_equation (u : K) :
    (W.toProjective.baseChange (D K)).Equation (OJet W u) := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simp [OJet, Dual.c, Dual.e]

/-- First-order local addition at `O` on the tangent coordinate. -/
def add₁ (u v : K) : K := u + v

@[simp] lemma add₁_eq (u v : K) : add₁ W u v = u + v := rfl

/-- First-order `n`-fold sum in the tangent coordinate at `O`. -/
def nsmul₁ (W : WeierstrassCurve K) : ℕ → K → K
  | 0, _ => 0
  | n + 1, u => add₁ W (nsmul₁ W n u) u

@[simp] lemma nsmul₁_zero (u : K) : nsmul₁ W 0 u = 0 := rfl

@[simp] lemma nsmul₁_succ (n : ℕ) (u : K) :
    nsmul₁ W (n + 1) u = nsmul₁ W n u + u := rfl

/-- The first-order tangent of `[n]` at `O` is scalar multiplication by `(n : K)`. -/
lemma nsmul₁_eq_natCast_mul (n : ℕ) (u : K) :
    nsmul₁ W n u = (n : K) * u := by
  induction n with
  | zero => simp [nsmul₁]
  | succ n ih =>
      simp [nsmul₁, ih, Nat.cast_succ, add_mul]

end TangentO

namespace MultipleRootBridge

open Dual

variable (W : WeierstrassCurve K)

/-- The dual-number `x + ε`. -/
def xε (x : K) : D K := c x + e 1

/-- The unique first-order curve lift over `x + ε`, assuming `W_Y(x,y) ≠ 0`. -/
def yε (x y : K) : D K :=
  c y + e (AffineJet.ySlope W x y)

lemma affine_dual_point_equation
    {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0) :
    (W.toAffine.baseChange (D K)).Equation (xε W x) (yε W x y) := by
  simpa [xε, yε, AffineJet.X, AffineJet.Y] using
    AffineJet.equation_dual_lift_of_polynomialY_ne_zero
      (W := W) (x := x) (y := y) (u := 1) hcurve hY

/-- Nonzero tangent coordinate of the constructed first-order lift. -/
lemma xε_snd (x : K) : TrivSqZeroExt.snd (xε W x) = 1 := by
  simp [xε, Dual.c, Dual.e]

end MultipleRootBridge

/-!
## Exact in-progress repo lemmas needed

These are the only non-local pieces.  They should be proved from the existing root-realization,
coordinate-ring congruences, and raw first-order division-polynomial formulas.
-/

namespace Needed

/-- Root dictionary over an algebraically closed field, specialized to the non-2 branch.

The returned `y` is an affine point over `K`; `hY` is exactly `ψ₂(P) ≠ 0`, i.e.
`2*y + a₁*x + a₃ ≠ 0`.  The final field `torsion` should be whatever packaged nsmul/torsion
statement the repo uses over fields; it is not used by the local analytic proof below except as
input to the next bridge lemma.
-/
structure RootData (W : WeierstrassCurve K) (n : ℕ) (x : K) : Prop where
  y : K
  curve : W.toAffine.Equation x y
  nonTwo : W.toAffine.polynomialY.evalEval x y ≠ 0
  torsion : True

/-- Required root-realization lemma.

This is the layer-3 dictionary: a root of the reduced division polynomial is the x-coordinate of
a non-2-torsion n-torsion point.
-/
axiom preΨ'_root_exists_non_two_n_torsion_point
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) : RootData W n x

/-- Required raw-coordinate dual-number bridge.

This is the field-vs-ring-safe replacement for `Pε ∈ E[n](K[ε])`.  The hypothesis `hrootε`
is the first-order reduced-division-polynomial root over `K[ε]`; the conclusion says that the
output tangent coordinate of `[n]` at `O` is zero.

This lemma should be proved from:
* `MultipleRootBridge.affine_dual_point_equation`,
* `W.map_preΨ'`, `Affine.CoordinateRing.mk_ψ`, `mk_Ψ_sq`, `mk_φ`,
* the raw coordinate formulas for multiplication/addition,
* and the fact that the lifted `ψ₂` is a unit because its scalar part is `nonTwo`.
-/
axiom preΨ'_dual_root_implies_nsmul_tangent_zero
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε W x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ W n 1 = 0

end Needed

/-- The rootwise core, reduced to the two explicit repo bridge lemmas above.

This is the intended final assembly.  The use of `eval_dualNumber` is exactly the already-proved
Taylor engine from the prompt.
-/
theorem preΨ'_deriv_ne_zero_at_root
    {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) : ¬ (derivative (W.preΨ' n)).IsRoot x := by
  intro hdx

  -- Root dictionary over the algebraically closed field.
  let rd := Needed.preΨ'_root_exists_non_two_n_torsion_point
    (W := W) (n := n) hn hx
  rcases rd with ⟨y, hcurve, hY, _htorsion⟩

  -- Taylor engine: multiple root gives a first-order root over `K[ε]`.
  have hx_eval : (W.preΨ' n).eval x = 0 := by
    simpa [Polynomial.IsRoot] using hx
  have hdx_eval : (derivative (W.preΨ' n)).eval x = 0 := by
    simpa [Polynomial.IsRoot] using hdx
  have hrootε : aeval (MultipleRootBridge.xε W x) (W.preΨ' n) = 0 := by
    have hTaylor := eval_dualNumber (W.preΨ' n) x (1 : K)
    rw [MultipleRootBridge.xε, hTaylor, hx_eval, hdx_eval]
    simp [Dual.c, Dual.e]

  -- Raw-coordinate division-polynomial bridge: the first-order output tangent at O is zero.
  have hzero : TangentO.nsmul₁ W n 1 = 0 :=
    Needed.preΨ'_dual_root_implies_nsmul_tangent_zero
      (W := W) (n := n) hn hcurve hY hrootε

  -- But the tangent of `[n]` at O is scalar `n`.
  have hlin : TangentO.nsmul₁ W n 1 = (n : K) := by
    simpa using TangentO.nsmul₁_eq_natCast_mul (W := W) n (1 : K)

  exact hn (by simpa [hlin] using hzero)

end SEAM1

end WeierstrassCurve
```

## What still has to be proved, not assumed

### 1. `Needed.preΨ'_root_exists_non_two_n_torsion_point`

Exact intended stronger signature:

```lean
structure PrePsiRootData (W : WeierstrassCurve K) (n : ℕ) (x : K) where
  y : K
  point : W.toAffine.Equation x y
  psi₂_ne : W.toAffine.polynomialY.evalEval x y ≠ 0
  nsmul_eq_zero : n • (affinePoint W x y point) = 0
```

Use the actual point constructor/projection names already in your SEAM1 branch.  The theorem should be:

```lean
theorem preΨ'_root_exists_non_two_n_torsion_point
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x : K}
    (hx : (W.preΨ' n).IsRoot x) :
    PrePsiRootData W n x
```

This is where the algebraically closed hypothesis is consumed.  This lemma should also exclude the `ψ₂ = 0` branch using the already-proved nonsingularity/base-stratum certificates.

### 2. `Needed.preΨ'_dual_root_implies_nsmul_tangent_zero`

This is the real remaining crux.  It is not the same as the root dictionary.  It must be a raw coordinate theorem over `DualNumber K`:

```lean
theorem preΨ'_dual_root_implies_nsmul_tangent_zero
    [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hcurve : W.toAffine.Equation x y)
    (hY : W.toAffine.polynomialY.evalEval x y ≠ 0)
    (hrootε : aeval (MultipleRootBridge.xε W x) (W.preΨ' n) = 0) :
    TangentO.nsmul₁ W n 1 = 0
```

Proof ingredients:

1. Construct `yε = y + ε*(-W_X/W_Y)` and prove the affine equation over `DualNumber K` using `AffineJet.equation_dual_lift_of_polynomialY_ne_zero`.
2. Show the lifted `ψ₂` is a unit because its scalar part is nonzero:

   ```lean
   lemma dualNumber_isUnit_of_fst_ne_zero (z : DualNumber K)
       (hz : TrivSqZeroExt.fst z ≠ 0) : IsUnit z
   ```

3. Convert reduced `preΨ'_n` vanishing to the full division-polynomial vanishing on the non-2 branch, using `map_preΨ'` and the coordinate-ring congruences.
4. Evaluate the multiplication-by-`n` coordinate formulas on the raw dual-number affine point.  The result lies in the `O` chart and has tangent coordinate `0`.
5. Identify that tangent coordinate with `TangentO.nsmul₁ W n 1`.

This lemma is where the field-vs-ring issue is solved.  It cannot be replaced by `Jacobian.Point (DualNumber K)`.

## Notes on `AffineJet.equation_dual_iff`

The body above is Lean-facing, but if it is brittle under simplifier changes, replace it by a direct `ext` proof on `TrivSqZeroExt.fst` and `snd` after unfolding the equation:

```lean
  apply Iff.intro
  · intro h
    have hf := congrArg TrivSqZeroExt.fst h
    have hs := congrArg TrivSqZeroExt.snd h
    constructor
    · simpa [AffineJet.X, AffineJet.Y, Dual.c, Dual.e,
        WeierstrassCurve.Affine.evalEval_polynomial] using hf
    · simpa [AffineJet.X, AffineJet.Y, Dual.c, Dual.e,
        WeierstrassCurve.Affine.evalEval_polynomial,
        WeierstrassCurve.Affine.evalEval_polynomialX,
        WeierstrassCurve.Affine.evalEval_polynomialY] using hs
```

The theorem is purely first-order Taylor expansion of the curve equation.  No elliptic-curve group law is involved.

## Assembly dependency graph

```text
eval_dualNumber                           -- already proved by you
        │
        ▼
preΨ'_multiple_root ⇒ preΨ'_dual_root over K[ε]
        │
        ├── root dictionary over IsAlgClosed K  [MISSING: exact signature above]
        │       gives y, curve equation, ψ₂ ≠ 0, n-torsion over K
        │
        ├── AffineJet.equation_dual_iff / lift / unique
        │       gives yε and nonzero tangent vector
        │
        ▼
preΨ'_dual_root_implies_nsmul_tangent_zero [MISSING: exact signature above]
        │
        ▼
TangentO.nsmul₁_eq_natCast_mul
        │
        ▼
(n : K) = 0, contradiction to hn
```

So the theorem is ready to close once those two named bridge lemmas are present.  The local coordinate/Taylor part does not require more global infrastructure.
