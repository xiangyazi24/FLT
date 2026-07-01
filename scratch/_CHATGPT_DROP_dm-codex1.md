# Q2914 (dm-codex1): audit of final Kubert/Tate residual

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.KubertBridgeN12`

Current final residual:

```lean
axiom kubert_C12_tate_projective_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateProjectiveModel E
```

where `KubertC12TateProjectiveModel E` returns a parameter `q`, `TateC12Good q`, and an additive equivalence from `(E⁄ℚ).Point` to projective points on `tateC12W q`.

## Shortest honest shrink

Now that `projectivePointAddEquivOfVariableChange` is a theorem, the remaining residual should **not** return an `AddEquiv`.  The strictly smaller honest residual is curve-level:

```lean
structure KubertC12TateCurveModel (E : WeierstrassCurve ℚ) where
  q : ℚ
  hgood : TateC12Good q
  C : WeierstrassCurve.VariableChange ℚ
  hCurve : C • E = tateC12W q

axiom kubert_C12_tate_curve_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateCurveModel E
```

This is the best immediate replacement.  It contains exactly the missing Kubert/Tate classification: an elliptic curve over `ℚ` with a rational point of exact order `12` is `ℚ`-isomorphic, by an admissible Weierstrass variable change, to the C12 Tate family.

The old projective package can then be rebuilt by checked plumbing:

```lean
noncomputable def projectivePointAddEquivOfVariableChangeEq
    (E E' : WeierstrassCurve ℚ) (C : WeierstrassCurve.VariableChange ℚ)
    (hC : C • E = E') :
    (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective E') := by
  subst hC
  -- In the current file this should be definally the same domain.  If Lean refuses,
  -- insert a `change` to the exact type printed by the goal.
  change (E⁄ℚ).Point ≃+
    WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (C • E))
  exact projectivePointAddEquivOfVariableChange E C

/-- Rebuild the previous residual interface from the smaller curve-level residual. -/
theorem kubert_C12_tate_projective_normal_form_from_curve
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateProjectiveModel E := by
  rcases kubert_C12_tate_curve_normal_form E P hP with ⟨q, hgood, C, hC⟩
  exact
    { q := q
      hgood := hgood
      pointAddEquiv := projectivePointAddEquivOfVariableChangeEq E (tateC12W q) C hC }
```

If the actual field name in `KubertC12TateProjectiveModel` is `pointAddEquiv` but the parameter field is `q` or `t`, adjust the record labels only.

## Exact mathematical theorem still missing

The mathematical theorem is Kubert/Tate normal form for a marked point of exact order `12` over `ℚ`:

* Tate normal form:

```lean
def tateW (b c : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 1 - c
    a₂ := -b
    a₃ := -b
    a₄ := 0
    a₆ := 0 }
```

* Distinguished point: `(0,0)` on `tateW b c`.

* C12 parameterization:

```lean
def tateC12_b (q : ℚ) : ℚ :=
  q * (q - 1) * (q ^ 2 + 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 4

def tateC12_c (q : ℚ) : ℚ :=
  q * (q - 1) * (3 * q ^ 2 + 1) / (q + 1) ^ 3

def tateC12W (q : ℚ) : WeierstrassCurve ℚ :=
  tateW (tateC12_b q) (tateC12_c q)
```

* Classification theorem, in its marked form:

```lean
structure KubertC12TateMarkedModel
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) where
  q : ℚ
  hgood : TateC12Good q
  C : WeierstrassCurve.VariableChange ℚ
  hCurve : C • E = tateC12W q
  hP_origin :
    projectivePointAddEquivOfVariableChangeEq E (tateC12W q) C hCurve P =
      tateC12OriginProjective q hgood

/-- Strong marked Kubert theorem.  This is the actual classical theorem. -/
axiom kubert_C12_tate_marked_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateMarkedModel E P
```

Then the weaker curve-level residual is a theorem:

```lean
theorem kubert_C12_tate_curve_normal_form_from_marked
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateCurveModel E := by
  rcases kubert_C12_tate_marked_normal_form E P hP with ⟨q, hgood, C, hCurve, _hP⟩
  exact ⟨q, hgood, C, hCurve⟩
```

For downstream N12, **use the curve-level residual**, not the marked one.  The marked theorem is the clean proof target, but the downstream proof only needs the curve isomorphism to `tateC12W q`.

## Checkable support lemmas to add now

These are algebra/Lean plumbing, not Kubert content.

```lean
/-- `TateC12Good` implies the Tate `b` coefficient is nonzero. -/
theorem tateC12_b_ne_zero_of_good {q : ℚ}
    (h : TateC12Good q) : tateC12_b q ≠ 0 := by
  -- unfold `tateC12_b`; use all factor nonzero fields from `h`, plus denominator.
  -- The exact field names depend on your current `TateC12Good` structure.
  unfold tateC12_b
  field_simp [h.hq_add_one]
  repeat' apply mul_ne_zero
  · exact h.hq_ne_zero
  · exact h.hq_sub_one
  · exact h.hq_sq_add_one
  · exact h.hthree_q_sq_add_one

/-- `(0,0)` is nonsingular on `tateW b c` when `b ≠ 0`. -/
theorem tateW_origin_nonsingular {b c : ℚ} (hb : b ≠ 0) :
    (WeierstrassCurve.toAffine (tateW b c)).Nonsingular 0 0 := by
  -- `Affine.nonsingular_zero` says `a₆=0 ∧ (a₃≠0 ∨ a₄≠0)`.
  rw [WeierstrassCurve.Affine.nonsingular_zero]
  simp [tateW, hb]

noncomputable def tateOriginAffine (b c : ℚ) (hb : b ≠ 0) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (tateW b c)) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tateW_origin_nonsingular (b := b) (c := c) hb)

noncomputable def tateC12OriginAffine (q : ℚ) (h : TateC12Good q) :
    WeierstrassCurve.Affine.Point (WeierstrassCurve.toAffine (tateC12W q)) := by
  simpa [tateC12W] using
    tateOriginAffine (tateC12_b q) (tateC12_c q) (tateC12_b_ne_zero_of_good h)

noncomputable def tateC12OriginProjective (q : ℚ) (h : TateC12Good q) :
    WeierstrassCurve.Projective.Point (WeierstrassCurve.toProjective (tateC12W q)) :=
  WeierstrassCurve.Affine.Point.toProjective (tateC12OriginAffine q h)
```

Order is preserved by the checked point equivalences; add a generic helper if Mathlib does not already have one.

```lean
#check AddEquiv.addOrderOf_eq
#check addOrderOf_eq_card_of_forall_mem_zmultiples

/-- If not already available as an API lemma, prove once and reuse. -/
theorem addOrderOf_apply_addEquiv
    {A B : Type*} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (P : A) :
    addOrderOf (e P) = addOrderOf P := by
  -- First try:
  -- simpa using e.addOrderOf_eq P
  -- If the name differs, prove by extensionality of `n • P = 0`:
  -- `map_nsmul`, `e.map_zero`, and `e.injective` are enough.
  sorry
```

Use it to move the order-12 assumption to the Tate origin in the marked theorem proof:

```lean
theorem tate_origin_order12_of_marked_model
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12)
    (M : KubertC12TateMarkedModel E P) :
    addOrderOf (tateC12OriginProjective M.q M.hgood) = 12 := by
  rw [← M.hP_origin]
  simpa [hP] using
    addOrderOf_apply_addEquiv
      (projectivePointAddEquivOfVariableChangeEq E (tateC12W M.q) M.C M.hCurve) P
```

## Staged proof plan

### Stage 1: Replace current residual by curve-level residual

This is pure Lean plumbing and should be done immediately:

```lean
structure KubertC12TateCurveModel ...
axiom kubert_C12_tate_curve_normal_form ...
theorem kubert_C12_tate_projective_normal_form_from_curve ...
```

This removes the now-checked point-transport infrastructure from the residual.

### Stage 2: Formalize Tate origin and basic algebra

Add:

```lean
tateC12_b_ne_zero_of_good
tateW_origin_nonsingular
tateOriginAffine
tateC12OriginAffine
tateC12OriginProjective
addOrderOf_apply_addEquiv
```

This is checkable with current Mathlib APIs.

### Stage 3: Split the classical Kubert theorem into two missing pieces

#### 3A. Marked Tate normal form at a rational point

This is mostly Lean plumbing plus standard coordinate algebra.  No Kubert table yet.

```lean
structure TateNormalFormAtPoint
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) where
  b c : ℚ
  hb : b ≠ 0
  C : WeierstrassCurve.VariableChange ℚ
  hCurve : C • E = tateW b c
  hP_origin :
    projectivePointAddEquivOfVariableChangeEq E (tateW b c) C hCurve P =
      WeierstrassCurve.Affine.Point.toProjective (tateOriginAffine b c hb)

/-- Every nonzero rational point can be moved to `(0,0)` and then to Tate normal form. -/
theorem tate_normal_form_at_point_of_addOrder12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    TateNormalFormAtPoint E P := by
  -- Route:
  -- 1. `P ≠ 0` from `addOrderOf P = 12`.
  -- 2. Use `Projective.Point.toAffineAddEquiv` to get an affine nonzero point.
  -- 3. Case split on `Affine.Point`; zero contradicts `P ≠ 0`; `some x y h` gives coordinates.
  -- 4. First variable change `VariableChange.mk 1 x 0 y` moves the point to `(0,0)`;
  --    Mathlib has `Affine.equation_iff_variableChange` and `nonsingular_iff_variableChange`
  --    for this translation.
  -- 5. Further scale/shear to the standard Tate equation
  --    `y² + (1-c)xy - by = x³ - bx²`.
  -- 6. Use the already checked variable-change point equivalence to record `hP_origin`.
  sorry
```

What is missing here is not deep number theory; it is a carefully written coordinate normalization and marked-point transport proof.

#### 3B. Kubert C12 parameterization inside Tate normal form

This is the real mathematical core.

```lean
/-- Kubert table row for `N = 12`, stated only for Tate normal form. -/
axiom kubert_C12_parameter_of_tate_origin_order12
    (b c : ℚ) (hb : b ≠ 0)
    [hEll : (tateW b c).IsElliptic]
    (hOrder : addOrderOf
      (WeierstrassCurve.Affine.Point.toProjective (tateOriginAffine b c hb)) = 12) :
    ∃ q : ℚ, TateC12Good q ∧ b = tateC12_b q ∧ c = tateC12_c q
```

This residual is strictly smaller and more honest than the current one: it is just the Kubert table calculation for a Tate curve whose distinguished point is already known to have exact order `12`.

Use it to get the marked C12 theorem:

```lean
theorem kubert_C12_tate_marked_normal_form_from_tate_and_parameter
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateMarkedModel E P := by
  rcases tate_normal_form_at_point_of_addOrder12 E P hP with
    ⟨b, c, hb, C, hCurve, hP_origin⟩
  haveI : (tateW b c).IsElliptic := by
    -- Transport ellipticity across `C • E = tateW b c`.
    -- `VariableChange` already has an instance `(C • E).IsElliptic` from `[E.IsElliptic]`.
    subst hCurve
    infer_instance
  have hOrder : addOrderOf
      (WeierstrassCurve.Affine.Point.toProjective (tateOriginAffine b c hb)) = 12 := by
    rw [← hP_origin]
    simpa [hP] using
      addOrderOf_apply_addEquiv
        (projectivePointAddEquivOfVariableChangeEq E (tateW b c) C hCurve) P
  rcases kubert_C12_parameter_of_tate_origin_order12 b c hb hOrder with
    ⟨q, hgood, hbq, hcq⟩
  have hCurveC12 : C • E = tateC12W q := by
    rw [hCurve]
    ext <;> simp [tateC12W, tateW, hbq, hcq]
  refine ⟨q, hgood, C, hCurveC12, ?_⟩
  -- `hP_origin` target mentions `tateW b c`; rewrite by `hbq`, `hcq`.
  -- This may need `subst hbq; subst hcq` instead of `simpa`.
  simpa [tateC12W, hbq, hcq] using hP_origin
```

### Stage 4: Remove the Kubert table residual

To replace `kubert_C12_parameter_of_tate_origin_order12`, prove explicit multiple formulas for `(0,0)` on `tateW b c`, then solve the exact-order-12 equations.

Start with checked low multiples:

```lean
/-- `2(0,0) = (b, b*c)` on Tate normal form. -/
theorem tate_origin_two
    {b c : ℚ} (hb : b ≠ 0) :
    (2 : ℕ) • (WeierstrassCurve.Affine.Point.toProjective (tateOriginAffine b c hb)) =
      WeierstrassCurve.Affine.Point.toProjective
        (WeierstrassCurve.Affine.Point.some b (b * c) (by
          -- prove nonsingularity of `(b,b*c)` from ellipticity or direct algebra
          sorry)) := by
  -- Use `Affine.Point.add_self_of_Y_ne` or `add_some`, expand `slope`, `addX`, `addY`.
  sorry

/-- `3(0,0) = (c, b-c)` on Tate normal form. -/
theorem tate_origin_three
    {b c : ℚ} (hb : b ≠ 0) :
    (3 : ℕ) • (WeierstrassCurve.Affine.Point.toProjective (tateOriginAffine b c hb)) =
      WeierstrassCurve.Affine.Point.toProjective
        (WeierstrassCurve.Affine.Point.some c (b - c) (by
          sorry)) := by
  sorry
```

These two formulas are safe: they follow directly from the pinned affine formulas.  Do **not** write later `4P`, `6P`, `12P` formulas from memory unless verified in Lean/Python; the Kubert table proof should be driven by computed lemmas from `Affine.slope/addX/addY` and then simplified.

Expected final table theorem shape:

```lean
theorem tate_origin_order12_iff_exists_C12_parameter
    {b c : ℚ} (hb : b ≠ 0) [(tateW b c).IsElliptic] :
    addOrderOf (WeierstrassCurve.Affine.Point.toProjective (tateOriginAffine b c hb)) = 12 ↔
      ∃ q : ℚ, TateC12Good q ∧ b = tateC12_b q ∧ c = tateC12_c q := by
  -- Hard Kubert table algebra.
  sorry
```

## What current Mathlib can support

Likely checkable from current APIs:

* variable-change point transport: already proved locally;
* rebuilding projective `AddEquiv` from curve-level variable-change equality;
* order preservation under `AddEquiv`;
* affine coordinate extraction from nonzero projective points using `Projective.Point.toAffineAddEquiv`;
* moving a marked affine point to `(0,0)` using `VariableChange.mk 1 x 0 y`;
* basic Tate origin nonsingularity and first low multiple formulas.

Genuine missing infrastructure/content:

* no Mathlib Kubert/Tate torsion normal form theorem;
* no Mathlib row for `N=12` in Kubert's table;
* no ready theorem saying an arbitrary rational point can be normalized to Tate normal form while tracking that point;
* no ready exact-order-12 classification for the Tate distinguished point.

## False shortcuts to avoid

* Do **not** use `NormalForms.toShortNF` as a substitute for Kubert/Tate classification.  It changes equation shape; it does not classify rational torsion or produce the C12 parameter.
* Do **not** prove only that `tateC12W q` has a point of order `12`.  Downstream needs the converse direction from an arbitrary order-12 point to the family.
* Do **not** use equality of `j`-invariants as a replacement.  Over `ℚ`, twists can share `j`; this does not give the required rational variable change or point-group equivalence.
* Do **not** keep an `AddEquiv` in the residual now that variable-change point transport is checked.  The residual should be curve-level or, better, a marked Tate/Kubert table statement.
* Do **not** omit denominator/nondegeneracy fields.  `TateC12Good q` is part of the theorem, not a cosmetic condition; it prevents singular curves and invalid rational substitutions.

## Recommended endpoint for now

Replace the remaining residual by this single axiom:

```lean
axiom kubert_C12_tate_curve_normal_form
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    KubertC12TateCurveModel E
```

Then make `kubert_C12_tate_projective_normal_form` a theorem.  This is the shortest honest shrink that preserves the downstream N12 proof and isolates the remaining mathematical content as Kubert's C12 classification, rather than bundling it with point-transport plumbing that is now already checked.
