# Q2921 (dm-codex1): next split of `kubert_C12_tate_curve_normal_form`

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.KubertBridgeN12`

Current only residual:

```lean
axiom kubert_C12_tate_curve_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateCurveModel E
```

The next bounded shrink should split this into:

* **A. marked-point Tate normal form**: from an exact-order-12 point on `E`, produce some Tate normal form `tateW b c`, with the distinguished origin on `tateW b c` still having exact order 12;
* **B. Kubert C12 table inside Tate normal form**: classify the pairs `(b,c)` for which the distinguished origin on `tateW b c` has exact order 12.

This removes the C12 parameter table from the coordinate-normalization problem.

## Support definitions

Add these if not already present.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN12

noncomputable section

/-- `(0,0)` is nonsingular on Tate normal form when `b ≠ 0`. -/
theorem tateW_origin_nonsingular {b c : ℚ} (hb : b ≠ 0) :
    (WeierstrassCurve.toAffine (tateW b c)).Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  simp [tateW, hb]

/-- The distinguished Tate point `(0,0)`. -/
noncomputable def tateOriginAffine (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (tateW b c)) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tateW_origin_nonsingular (b := b) (c := c) hb)

/-- Additive equivalences preserve additive order.  Use a Mathlib lemma if one exists locally. -/
theorem addOrderOf_apply_addEquiv
    {A B : Type*} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (P : A) :
    addOrderOf (e P) = addOrderOf P := by
  -- Try first in your local file:
  --   simpa using e.addOrderOf_eq P
  -- If that name is unavailable, prove by the defining characterization of `addOrderOf`:
  -- `n • e P = 0 ↔ n • P = 0`, using `map_nsmul`, `map_zero`, and `e.injective`.
  sorry
```

If you do not want a new order lemma yet, keep `addOrderOf_apply_addEquiv` as a tiny local residual.  It is Lean plumbing, not mathematical content.

## A. Marked-point Tate normal form residual

Use this as the first new residual.  It has no C12 table content and no hidden point-group equivalence field.

```lean
/--
Tate normal form produced from the marked exact-order-12 point.

The field `hOriginOrder` is the only marked-point trace needed downstream: after the
coordinate change, the distinguished Tate point `(0,0)` has exact order 12.
-/
structure TateNormalFormAtOrder12 (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  b c : ℚ
  hb : b ≠ 0
  hDelta : (tateW b c).Δ ≠ 0
  C : WeierstrassCurve.VariableChange ℚ
  hCurve : C • E = tateW b c
  hOriginOrder : addOrderOf (tateOriginAffine b c hb) = 12

/--
Residual A: coordinate-normalization of a marked rational point of exact order 12 into
Tate normal form.

This should eventually be provable from current Mathlib APIs plus the checked variable-change
point equivalences.  It is not the Kubert table.
-/
axiom tate_normal_form_at_point_of_addOrder12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    TateNormalFormAtOrder12 E
```

### Why A is plausible from current APIs

This is coordinate plumbing plus small order-exclusion lemmas.

Suggested proof route:

```lean
/-- Exact order 12 points are nonzero. -/
theorem point_ne_zero_of_addOrderOf_eq_12
    {G : Type*} [AddGroup G] {P : G} (hP : addOrderOf P = 12) : P ≠ 0 := by
  intro hzero
  subst hzero
  -- `addOrderOf_zero` should close this; otherwise unfold/order APIs.
  simpa using hP
```

Then for `P : (E⁄ℚ).Point`:

1. Case split on the affine point.  The zero case contradicts `addOrderOf P = 12`.  The `some x y h` case gives rational coordinates.
2. Translate `P` to `(0,0)` using

```lean
C0 : WeierstrassCurve.VariableChange ℚ :=
  { u := 1, r := x, s := 0, t := y }
```

Mathlib already has `WeierstrassCurve.Affine.equation_iff_variableChange` and `nonsingular_iff_variableChange` for the special translation-to-origin move.

3. On the translated curve `W0 = C0 • E`, prove `W0.a₆ = 0` and the transported origin has order 12 using your checked `affinePointAddEquivOfVariableChange`.
4. Since the origin is not order 2, prove `W0.a₃ ≠ 0`.  In coordinates, origin has negation `(0,-a₃)`, so if `a₃ = 0`, then `(0,0)` is 2-torsion.
5. Kill `a₄` while fixing the origin with a shear

```lean
C1 : WeierstrassCurve.VariableChange ℚ :=
  { u := 1, r := 0, s := W0.a₄ / W0.a₃, t := 0 }
```

because `a₄' = a₄ - s*a₃` when `r=t=0`.

6. Let the resulting coefficients after `C1` be `a₁₁ a₂₁ a₃₁` with `a₄=0`, `a₆=0`, `a₃₁≠0`.  To reach Tate form we need `a₂'=a₃'=-b`.  A final scale with

```lean
u = a₃₁ / a₂₁
```

works if `a₂₁ ≠ 0`.  The missing small order-exclusion lemma is: if this `a₂₁ = 0`, then the origin has order 3 or 4, contradicting exact order 12.  This is still coordinate algebra with the pinned affine addition formulas.

Use bounded sublemmas:

```lean
/-- On a curve with `(0,0)` and `a₆=0`, if `a₃=0`, then the origin is 2-torsion. -/
theorem origin_order_two_if_a3_eq_zero
    (W : WeierstrassCurve ℚ)
    (h6 : W.a₆ = 0)
    (h3 : W.a₃ = 0)
    (hO : (WeierstrassCurve.toAffine W).Nonsingular 0 0) :
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 hO) = 0 := by
  -- Use `Affine.Point.add_of_Y_eq`; `negY 0 0 = 0` when `a₃=0`.
  sorry

/-- The scale denominator needed to make `a₂'=a₃'` is nonzero for an exact-order-12 origin. -/
theorem tate_scale_denominator_ne_zero_of_origin_order12
    (W : WeierstrassCurve ℚ)
    (h6 : W.a₆ = 0)
    (h4 : W.a₄ = 0)
    (h3 : W.a₃ ≠ 0)
    (hO : (WeierstrassCurve.toAffine W).Nonsingular 0 0)
    (hOrder : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    W.a₂ ≠ 0 := by
  -- Prove by contradiction using explicit `2O`, `3O`, or `4O` formulas on the simplified curve.
  -- This is the only nontrivial local group-law algebra in A.
  sorry
```

I would not block the split on proving A.  Introduce A as a residual now, then attack the sublemmas above.

## B. Kubert C12 table inside Tate normal form

This is the genuine Kubert table row and should remain residual for now.

```lean
/--
Residual B: Kubert's C12 table row, isolated to Tate normal form.

No arbitrary elliptic curve, no point transport, no projective equivalence.  Just the
classification of Tate parameters `(b,c)` for which `(0,0)` has exact order 12.
-/
axiom kubert_C12_table_of_tate_origin_order12
    (b c : ℚ) (hb : b ≠ 0)
    (hDelta : (tateW b c).Δ ≠ 0)
    (hOrder : addOrderOf (tateOriginAffine b c hb) = 12) :
    ∃ q : ℚ, TateC12Good q ∧ b = tateC12_b q ∧ c = tateC12_c q
```

This is strictly smaller than `kubert_C12_tate_curve_normal_form`: it assumes the curve is already in Tate normal form and the marked point is already `(0,0)`.

## Rebuild current curve-level residual from A+B

```lean
/-- Reconstruct the existing curve-level residual from the two smaller residuals. -/
theorem kubert_C12_tate_curve_normal_form_from_split
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateCurveModel E := by
  rcases tate_normal_form_at_point_of_addOrder12 E P hP with
    ⟨b, c, hb, hDelta, C, hCurve, hOriginOrder⟩
  rcases kubert_C12_table_of_tate_origin_order12 b c hb hDelta hOriginOrder with
    ⟨q, hgood, hbq, hcq⟩
  refine
    { q := q
      hgood := hgood
      C := C
      hCurve := ?_ }
  rw [hCurve, hbq, hcq]
  rfl
```

If the final `rfl` fails because `tateC12W` is not reducible enough, use:

```lean
  simp [tateC12W]
```

or:

```lean
  change tateW (tateC12_b q) (tateC12_c q) = tateC12W q
  rfl
```

Then replace the old axiom by:

```lean
theorem kubert_C12_tate_curve_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateCurveModel E :=
  kubert_C12_tate_curve_normal_form_from_split E P hP
```

## Later attack on residual B

Prove low-multiple formulas in `tateW b c`, then solve the order-12 equations.

Start with declarations like:

```lean
/-- First low multiple on Tate normal form.  Verify the coordinate formula in Lean. -/
theorem tate_origin_two_formula
    {b c : ℚ} (hb : b ≠ 0) :
    (2 : ℕ) • tateOriginAffine b c hb =
      -- fill with the point produced by `Affine.Point.some` after computing `addX/addY`
      (by
        -- placeholder target; derive by expanding `Affine.Point.add_some`
        exact tateOriginAffine b c hb) := by
  -- Do not trust handwritten coordinates until checked by `simp [Affine.slope/addX/addY]`.
  sorry
```

Recommended order:

1. prove `2O`, `3O`, `4O`, `6O` formulas on `tateW b c` using `Affine.Point.add_some`, `slope`, `addX`, `addY`;
2. prove `12O = 0` iff the Kubert polynomial relation holds;
3. solve the rational parametrization to obtain `q`, `b = tateC12_b q`, `c = tateC12_c q` and `TateC12Good q`.

This is genuine Kubert-table mathematics; do not hide it in the coordinate-normal-form residual.

## False shortcuts to avoid

* Do not replace B by proving only that `tateC12W q` has an order-12 point.  The needed direction is converse: arbitrary Tate form with origin order 12 lies in the C12 row.
* Do not use equality of `j` invariants to get `C`; twists share `j`.
* Do not keep an additive equivalence in any new residual.  Variable-change point transport is already checked.
* Do not omit `hDelta`; singular Tate curves can have misleading formal group-law artifacts.

## Recommended immediate implementation

Add A and B as the only new residuals, prove `kubert_C12_tate_curve_normal_form_from_split`, and make the old `kubert_C12_tate_curve_normal_form` a theorem.  Then the remaining axioms will distinguish cleanly:

* `tate_normal_form_at_point_of_addOrder12`: Lean/coordinate-normalization plumbing, probably provable from current APIs;
* `kubert_C12_table_of_tate_origin_order12`: genuine Kubert C12 table row.
