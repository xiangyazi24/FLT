# Q3011 (dm-codex1): next residual after `kubert_C10_shortW_projective_normal_form`

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN10.lean`.

I could not fetch the exact local working file through the connector, so names below follow the prompt and the previous N10 snippets.  The route is Lean-oriented and avoids the false same-parameter C10 statement.

## Executive patch plan

Replace the current residual

```lean
axiom kubert_C10_shortW_projective_normal_form ... :
  KubertC10ShortWProjectiveModel E
```

by a **p-parameter Tate normal-form residual**:

```lean
axiom kubert_C10_tate_param_projective_normal_form ... :
  KubertC10TateParamProjectiveModel E
```

Then make `kubert_C10_shortW_projective_normal_form` a theorem obtained by:

1. the new Tate-param residual,
2. the explicit corrected parameter change `T = 1/(1-2*p)`,
3. the explicit Weierstrass variable change from `tateW (tateC10_b p) (tateC10_c p)` to `shortW (A10 T) (B10 T)`,
4. one general API theorem/residual converting an invertible Weierstrass variable change into a projective-point additive equivalence.

This is the right next cut because it removes all C10 short-family geometry from the residual.  What remains residualized is only: “an elliptic curve with a rational point of order 10 admits the C10 Tate normal form with Tate parameter `p`.”  The `p -> T` short conversion is then explicit algebra.

## 1. Best next residual statement

Add this structure next to `KubertC10ShortWProjectiveModel`:

```lean
structure KubertC10TateParamProjectiveModel (E : WeierstrassCurve ℚ) where
  p : ℚ
  hden : tateC10_den p ≠ 0
  hDeltaTate :
    (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0
  pointAddEquiv :
    (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective
          (tateW (tateC10_b p) (tateC10_c p)))
```

Then replace the old shortW residual by:

```lean
axiom kubert_C10_tate_param_projective_normal_form
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
  KubertC10TateParamProjectiveModel E
```

This is the immediate replacement I recommend.

### Optional even narrower residual for the next pass

Once the Tate-row origin point is convenient in the local API, reduce one step further to a raw Tate-row model:

```lean
structure KubertC10TateRowProjectiveModel (E : WeierstrassCurve ℚ) where
  b c : ℚ
  hDeltaTate : (tateW b c).Δ ≠ 0
  -- Use the local projective point for `(0,0)` on `tateW b c` if already defined.
  hOriginOrder10 : addOrderOf (tateWOriginProjectivePoint b c) = 10
  pointAddEquiv :
    (E⁄ℚ).Point ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective (tateW b c))

axiom kubert_C10_tate_row_projective_normal_form
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
  KubertC10TateRowProjectiveModel E
```

Then prove `KubertC10TateParamProjectiveModel E` using the already checked row algebra:

```lean
theorem kubert_C10_tate_param_projective_normal_form_of_tate_row
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
  KubertC10TateParamProjectiveModel E := by
  let M := kubert_C10_tate_row_projective_normal_form E P hP
  -- Existing checked theorem should give:
  --   ∃ p, tateC10_den p ≠ 0 ∧ M.b = tateC10_b p ∧ M.c = tateC10_c p
  -- from `M.hOriginOrder10`.
  obtain ⟨p, hden, hb, hc⟩ :=
    tateC10_param_of_origin_order10 M.b M.c M.hOriginOrder10
  refine ⟨p, hden, ?_, ?_⟩
  · simpa [hb, hc] using M.hDeltaTate
  · simpa [hb, hc] using M.pointAddEquiv
```

The exact signature of `tateC10_param_of_origin_order10` may differ, but this is the intended wrapper.  This optional split is good later; for the immediate de-axiomatization, the p-param residual above is cleaner.

## 2. Explicit corrected `p -> T` coordinate change

Use these definitions.  The field name `t` in `VariableChange` may be `tau` or similar in your local Mathlib; rename only that field if needed.

```lean
def tateC10_pToShortParam (p : ℚ) : ℚ :=
  1 / (1 - 2 * p)

noncomputable def tateC10_pToShortVC (p : ℚ) :
    WeierstrassCurve.VariableChange ℚ :=
  let b : ℚ := tateC10_b p
  let c : ℚ := tateC10_c p
  let r0 : ℚ := -p ^ 3 * (p - 1) / tateC10_den p
  { u := (2 * p - 1) ^ 3 / (8 * tateC10_den p)
    r := r0
    s := (c - 1) / 2
    t := (b - r0 * (1 - c)) / 2 }
```

Mathlib convention used here:

```text
x_old = u^2*x_new + r
y_old = u^3*y_new + u^2*s*x_new + t
```

With `b=tateC10_b p`, `c=tateC10_c p`, `D=tateC10_den p`, and `T=1/(1-2p)`, this variable change sends the Tate row to the corrected short family:

```lean
theorem tateC10_p_to_shortW
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    tateC10_pToShortVC p •
        tateW (tateC10_b p) (tateC10_c p) =
      shortW (A10 (tateC10_pToShortParam p))
             (B10 (tateC10_pToShortParam p)) := by
  have h2 : 2 * p - 1 ≠ 0 := by
    intro h
    apply hpT
    linarith
  ext <;>
    dsimp [tateC10_pToShortVC, tateC10_pToShortParam,
      tateC10_b, tateC10_c, tateC10_den,
      tateW, shortW, A10, B10, F10] <;>
    field_simp [hden, hpT, h2] <;>
    ring
```

If this direct `field_simp` is too slow, rewrite it using the already compiled small identities:

```lean
pToShort_sq_sub_one
pToShort_shortQ
pToShort_phi
```

and add coefficient-specific lemmas instead of one five-field `ext` proof:

```lean
theorem tateC10_p_to_shortW_a1 ... :
  (tateC10_pToShortVC p • tateW ...).a1 = 0 := by ...

theorem tateC10_p_to_shortW_a2 ... :
  (tateC10_pToShortVC p • tateW ...).a2 = A10 (tateC10_pToShortParam p) := by ...

theorem tateC10_p_to_shortW_a3 ... :
  (tateC10_pToShortVC p • tateW ...).a3 = 0 := by ...

theorem tateC10_p_to_shortW_a4 ... :
  (tateC10_pToShortVC p • tateW ...).a4 = B10 (tateC10_pToShortParam p) := by ...

theorem tateC10_p_to_shortW_a6 ... :
  (tateC10_pToShortVC p • tateW ...).a6 = 0 := by ...
```

The five coefficient goals are pure algebra.  They should be `ring`/`field_simp` goals only.

### Nonzero `u`

```lean
theorem tateC10_pToShortVC_u_ne_zero
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2 * p ≠ 0) :
    (tateC10_pToShortVC p).u ≠ 0 := by
  have h2 : 2 * p - 1 ≠ 0 := by
    intro h
    apply hpT
    linarith
  dsimp [tateC10_pToShortVC]
  exact div_ne_zero
    (pow_ne_zero 3 h2)
    (mul_ne_zero (by norm_num) hden)
```

### Deriving `hpT` from Tate nonsingularity

You do not need the full C10 Tate discriminant factorization just to exclude `p=1/2`.  Use the already checked direct lemma that `p=1/2` makes the Tate discriminant zero.

```lean
theorem one_sub_two_mul_ne_zero_of_tateC10_delta_ne_zero
    {p : ℚ}
    (hDelta :
      (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    1 - 2 * p ≠ 0 := by
  intro hpole
  have hp : p = (1 : ℚ) / 2 := by
    linarith
  subst p
  exact hDelta tateC10_delta_half_zero
```

This assumes you have the direct compiled lemma:

```lean
theorem tateC10_delta_half_zero :
    (tateW (tateC10_b ((1 : ℚ) / 2))
           (tateC10_c ((1 : ℚ) / 2))).Δ = 0 := by
  -- your current direct proof
  norm_num [tateC10_b, tateC10_c, tateC10_den,
    tateW, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
```

## 3. Smallest projective-point API theorem needed

If Mathlib/local code already has this, use it.  If not, make this the **only** non-C10 projective residual:

```lean
axiom projectivePointAddEquivOfVariableChange
    (W W' : WeierstrassCurve ℚ)
    (C : WeierstrassCurve.VariableChange ℚ)
    (hCu : C.u ≠ 0)
    (hW' : C • W = W') :
    WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective W) ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective W')
```

This is much better than a C10-specific axiom: it is a general functoriality statement for invertible Weierstrass coordinate changes.  It can later be proved once and reused for N=10, N=12, etc.

Using it, define the corrected C10 Tate-to-short projective equivalence:

```lean
def tateC10_p_to_short_projective_addEquiv
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hDelta :
      (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective
          (tateW (tateC10_b p) (tateC10_c p))) ≃+
      WeierstrassCurve.Projective.Point
        (WeierstrassCurve.toProjective
          (shortW (A10 (tateC10_pToShortParam p))
                  (B10 (tateC10_pToShortParam p)))) := by
  have hpT : 1 - 2 * p ≠ 0 :=
    one_sub_two_mul_ne_zero_of_tateC10_delta_ne_zero hDelta
  exact projectivePointAddEquivOfVariableChange
    (W := tateW (tateC10_b p) (tateC10_c p))
    (W' := shortW (A10 (tateC10_pToShortParam p))
                  (B10 (tateC10_pToShortParam p)))
    (C := tateC10_pToShortVC p)
    (tateC10_pToShortVC_u_ne_zero hden hpT)
    (tateC10_p_to_shortW hden hpT)
```

## 4. `Delta10 T ≠ 0` without the full Tate discriminant factorization

Prefer deriving short nonsingularity from the variable-change API rather than proving the full Tate discriminant factorization first.

Add a general discriminant transport theorem if it does not already exist:

```lean
axiom discriminant_ne_zero_of_variableChange_eq
    (W W' : WeierstrassCurve ℚ)
    (C : WeierstrassCurve.VariableChange ℚ)
    (hCu : C.u ≠ 0)
    (hDelta : W.Δ ≠ 0)
    (hW' : C • W = W') :
    W'.Δ ≠ 0
```

Again, this is general and not C10-specific.  Then:

```lean
theorem Delta10_pToShortParam_ne_zero_of_tate_delta
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hDelta :
      (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    Delta10 (tateC10_pToShortParam p) ≠ 0 := by
  have hpT : 1 - 2 * p ≠ 0 :=
    one_sub_two_mul_ne_zero_of_tateC10_delta_ne_zero hDelta
  have hW :
      tateC10_pToShortVC p •
          tateW (tateC10_b p) (tateC10_c p) =
        shortW (A10 (tateC10_pToShortParam p))
               (B10 (tateC10_pToShortParam p)) :=
    tateC10_p_to_shortW hden hpT
  have hShortDelta :
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).Δ ≠ 0 :=
    discriminant_ne_zero_of_variableChange_eq
      (W := tateW (tateC10_b p) (tateC10_c p))
      (W' := shortW (A10 (tateC10_pToShortParam p))
                    (B10 (tateC10_pToShortParam p)))
      (C := tateC10_pToShortVC p)
      (tateC10_pToShortVC_u_ne_zero hden hpT)
      hDelta
      hW
  have hDeltaEq :
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).Δ =
        Delta10 (tateC10_pToShortParam p) := by
    dsimp [shortW, A10, B10, F10, Delta10]
    ring
  simpa [hDeltaEq] using hShortDelta
```

If the local variable-change discriminant theorem states the exact scaling formula, use that instead:

```lean
(C • W).Δ = C.u ^ (-12) * W.Δ
```

or the equivalent local convention.  Be careful about direction; Mathlib conventions vary depending on whether `C • W` is old-to-new or new-to-old.

## 5. The replacement theorem deriving the old model

Once the pieces above exist, define the old residual as a theorem, not an axiom:

```lean
theorem kubert_C10_shortW_projective_normal_form
  (E : WeierstrassCurve ℚ) [E.IsElliptic]
  (P : (E⁄ℚ).Point) (hP : addOrderOf P = 10) :
  KubertC10ShortWProjectiveModel E := by
  let M := kubert_C10_tate_param_projective_normal_form E P hP
  let T : ℚ := tateC10_pToShortParam M.p
  refine
    { t := T
      hDelta := ?_
      pointAddEquiv := ?_ }
  · simpa [T] using
      Delta10_pToShortParam_ne_zero_of_tate_delta
        M.hden M.hDeltaTate
  · exact M.pointAddEquiv.trans
      (tateC10_p_to_short_projective_addEquiv
        M.hden M.hDeltaTate)
```

If `AddEquiv.trans` expects the reverse order in your local notation, use:

```lean
(tateC10_p_to_short_projective_addEquiv M.hden M.hDeltaTate).trans M.pointAddEquiv
```

only if the type errors show that the direction is reversed.  Mathematically, the intended direction is:

```text
E.Point  --M.pointAddEquiv-->  Tate(p).Point  --p_to_short-->  Short(T).Point.
```

## 6. Classification of proof obligations

### Pure `ring`/`field_simp` algebra

These should be actual theorems, not residuals:

```lean
tateC10_pToShortParam
pToShort_sq_sub_one
pToShort_shortQ
pToShort_phi
tateC10_pToShortVC_u_ne_zero
tateC10_p_to_shortW        -- maybe split into five coefficient lemmas
shortW_delta_eq_Delta10    -- the `hDeltaEq` proof above
one_sub_two_mul_ne_zero_of_tateC10_delta_ne_zero -- using the half-zero lemma
```

### General elliptic/projective API, not C10-specific

These are acceptable temporary residuals if local Mathlib API is missing:

```lean
projectivePointAddEquivOfVariableChange
discriminant_ne_zero_of_variableChange_eq
```

They should live in `KubertTateCommon.lean` or another common file, not as C10-specific axioms.

### Actual remaining C10/Kubert residual

Only this should remain for now:

```lean
kubert_C10_tate_param_projective_normal_form
```

And later this can be replaced by the raw Tate-row residual plus the already checked `tateC10_param_of_origin_order10` algebra.

## 7. Known API pitfalls

1. **`VariableChange` field name**: in some Mathlib versions the final translation field is `t`, in others local code may avoid `t` because of parser/name conflicts.  Rename only the field in `tateC10_pToShortVC`.

2. **Action direction**: verify whether `C • W` means “old curve transformed to new curve” with
   `x_old = u^2*x_new + r`, `y_old = u^3*y_new + u^2*s*x_new + t`.  The coefficient formulas above assume that convention.

3. **Projective point equivalence direction**: the induced map may be named from `W` to `C • W` or the inverse.  If the available API gives the inverse, use `.symm` before composing with `M.pointAddEquiv`.

4. **`Delta10` equality**: keep a separate theorem
   ```lean
   theorem shortW_delta_eq_Delta10 (T : ℚ) :
       (shortW (A10 T) (B10 T)).Δ = Delta10 T := by
     dsimp [shortW, A10, B10, F10, Delta10]
     ring
   ```
   Then avoid re-expanding it everywhere.

5. **Do not use same parameter**: no theorem should mention
   ```lean
   shortW (A10 p) (B10 p)
   ```
   from the Tate-row parameter `p`.  Always use
   ```lean
   T = tateC10_pToShortParam p = 1/(1-2*p)
   ```

## 8. Verification plan

Create a temporary Lean check file, for example `scratch/Q3011Check.lean`:

```lean
import FLT.Assumptions.MazurProof.KubertBridgeN10

open MazurProof.KubertBridgeN10

#print axioms kubert_C10_shortW_projective_normal_form
#print axioms kubert_C10_tate_param_projective_normal_form
#print axioms tateC10_p_to_shortW
#print axioms Delta10_pToShortParam_ne_zero_of_tate_delta
#print axioms tateC10_p_to_short_projective_addEquiv
```

Run targeted checks:

```bash
lake env lean FLT/Assumptions/MazurProof/KubertBridgeN10.lean
lake env lean scratch/Q3011Check.lean
```

Expected result after this patch stage:

```text
#print axioms kubert_C10_shortW_projective_normal_form
```

should list only:

```text
kubert_C10_tate_param_projective_normal_form
projectivePointAddEquivOfVariableChange       -- only if not yet proved
discriminant_ne_zero_of_variableChange_eq     -- only if not yet proved
```

It should no longer list `kubert_C10_shortW_projective_normal_form` as an axiom, and it should not list any same-parameter C10 short-family theorem.

Also run:

```bash
grep -R "axiom kubert_C10_shortW_projective_normal_form" -n FLT/Assumptions/MazurProof
 grep -R "shortW (A10 p)" -n FLT/Assumptions/MazurProof
 grep -R "shortW (A10 t)" -n FLT/Assumptions/MazurProof/KubertBridgeN10.lean
```

The first grep should return nothing.  The second and third should not find a Tate-row parameter being reused as the short-family parameter.
