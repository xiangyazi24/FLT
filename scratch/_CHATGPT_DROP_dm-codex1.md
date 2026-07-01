# Q2987 (dm-codex1): replacing `tate_normal_form_at_point_of_addOrder12`

I could not inspect the current local worktree through the GitHub connector: the accessible GitHub search did not expose the current `KubertBridgeN12.lean` contents, so this answer is based on the checked declarations you listed.  The conclusion is still sharp:

**The later variable-change lemmas should already prove the axiom, after moving them above the first downstream use of the axiom.**  The axiom should be replaced by an assembly theorem that chains:

1. affine extraction of `P`,
2. translation of `P` to `(0,0)`,
3. origin-normal `a₄=0` cleanup,
4. scaling to the Tate model,
5. composition of the three variable changes,
6. order transport to `tateOriginAffine`.

The only pieces that may still be missing are tiny wrappers, not new mathematics:

- a wrapper that `tateBOfOriginNormal` is nonzero;
- a wrapper that the scaled Tate curve has nonzero discriminant because it is variable-change equivalent to an elliptic curve;
- a wrapper transporting the origin order through `scaleToTateVC`, if it is not already present;
- possibly a variable-change composition rewrite, if `mul_smul`/`one_smul` does not fire for `WeierstrassCurve.VariableChange`.

## Declaration-order change

Do **not** import a new file that imports `KubertBridgeN12.lean`; that creates the wrong direction.  Instead reorder declarations in `KubertBridgeN12.lean`:

```text
basic Tate definitions: tateW, tateOriginAffine, tateP3, ...
TateNormalFormAtOrder12 structure
variable-change helper block:
  AffineMarkedPointOfOrder12
  affineMarkedPointOfOrder12_of_addOrder12
  translatePointToOriginVC
  translate_order12_point_to_origin
  killA4VC and killA4_* lemmas
  scaleToTateVC, tateBOfOriginNormal, tateCOfOriginNormal
  scaleToTate_eq_tateW
  order-transport wrappers
replacement theorem tate_normal_form_at_point_of_addOrder12
kubert_C12_tate_curve_normal_form and downstream code
```

The theorem must be declared before `kubert_C12_tate_curve_normal_form`.

## Core replacement theorem

This is the intended replacement for the axiom.  It assumes the helper names from your file.  If your `scaleToTateVC` takes only `h3` and not `h2`, use the shorter variant noted below.

```lean
-- Replace the axiom with this theorem after moving the helper block above it.
theorem tate_normal_form_at_point_of_addOrder12
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 12) :
    TateNormalFormAtOrder12 E := by
  classical

  -- 1. Translate the chosen order-12 point to the origin.
  rcases translate_order12_point_to_origin E P hP with
    ⟨x0, y0, hxy, C0, hC0, hA6_0, hO0, hOrd0⟩

  let E0 : WeierstrassCurve ℚ := C0 • E
  haveI : E0.IsElliptic := by
    -- If this does not infer, use the `variableChange_isElliptic` lemma already
    -- used by the additive-equivalence infrastructure.
    dsimp [E0]
    infer_instance

  -- Exact order 12 at the origin forces the origin not to be 2-torsion.
  have h3_0 : E0.a₃ ≠ 0 := by
    simpa [E0] using
      (origin_a3_ne_zero_of_addOrderOf_eq_12
        (W := E0) hO0 hOrd0)

  -- 2. Kill a₄ while fixing the origin.
  let C1 : WeierstrassCurve.VariableChange ℚ := killA4VC E0 h3_0
  let E1 : WeierstrassCurve ℚ := C1 • E0
  haveI : E1.IsElliptic := by
    dsimp [E1, C1]
    infer_instance

  have hA4_1 : E1.a₄ = 0 := by
    simpa [E1, C1] using killA4_a4 E0 h3_0
  have hA6_1 : E1.a₆ = 0 := by
    simpa [E1, C1] using killA4_a6 E0 h3_0 hA6_0
  have hO1 : (E1⁄ℚ).Nonsingular 0 0 := by
    simpa [E1, C1] using killA4_origin_nonsingular E0 h3_0 hO0
  have hOrd1 :
      addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO1) = 12 := by
    simpa [E1, C1] using killA4_origin_order12 E0 h3_0 hO0 hOrd0
  have h3_1 : E1.a₃ ≠ 0 := by
    simpa [E1, C1] using killA4_a3_ne_zero E0 h3_0

  -- This is needed if `scaleToTateVC` uses u = a₃/a₂.  If your local
  -- `scaleToTateVC` signature does not require h2, delete h2_1 from the calls.
  have h2_1 : E1.a₂ ≠ 0 := by
    simpa [E1] using
      (origin_a2_ne_zero_of_addOrderOf_eq_12
        (W := E1) hO1 hOrd1)

  -- 3. Scale the origin-normal curve to Tate normal form.
  let b : ℚ := tateBOfOriginNormal E1 h2_1 h3_1
  let c : ℚ := tateCOfOriginNormal E1 h2_1 h3_1
  let C2 : WeierstrassCurve.VariableChange ℚ := scaleToTateVC E1 h2_1 h3_1

  have hb : b ≠ 0 := by
    simpa [b] using tateBOfOriginNormal_ne_zero E1 h2_1 h3_1

  have hCurve2 : C2 • E1 = tateW b c := by
    simpa [E1, C2, b, c] using
      (scaleToTate_eq_tateW
        (W := E1) hA4_1 hA6_1 h2_1 h3_1)

  have hOriginOrder2 : addOrderOf (tateOriginAffine b c hb) = 12 := by
    simpa [E1, C2, b, c, tateOriginAffine] using
      (scaleToTate_origin_order12
        (W := E1) (hA4 := hA4_1) (hA6 := hA6_1)
        (h2 := h2_1) (h3 := h3_1)
        (hO := hO1) (hOrd := hOrd1))

  -- 4. Compose the variable changes.  With the standard monoid action convention,
  -- `(C2 * C1 * C0) • E = C2 • (C1 • (C0 • E))`.
  let C : WeierstrassCurve.VariableChange ℚ := C2 * C1 * C0

  have hCurve : C • E = tateW b c := by
    dsimp [C, E1, E0]
    -- If this line fails, use the explicit composition wrapper below.
    rw [mul_smul, mul_smul]
    exact hCurve2

  have hDelta : (tateW b c).Δ ≠ 0 := by
    exact tateW_delta_ne_zero_of_variableChange_eq
      (W := E1) (C := C2) (b := b) (c := c) hCurve2

  exact
    { b := b
      c := c
      hb := hb
      hDelta := hDelta
      C := C
      hCurve := hCurve
      hOriginOrder := hOriginOrder2 }
```

### If `scaleToTateVC` takes only `h3`

Use this local substitution in the scaling block:

```lean
  let b : ℚ := tateBOfOriginNormal E1 h3_1
  let c : ℚ := tateCOfOriginNormal E1 h3_1
  let C2 : WeierstrassCurve.VariableChange ℚ := scaleToTateVC E1 h3_1

  have hb : b ≠ 0 := by
    simpa [b] using tateBOfOriginNormal_ne_zero E1 h3_1

  have hCurve2 : C2 • E1 = tateW b c := by
    simpa [E1, C2, b, c] using
      (scaleToTate_eq_tateW
        (W := E1) hA4_1 hA6_1 h3_1)

  have hOriginOrder2 : addOrderOf (tateOriginAffine b c hb) = 12 := by
    simpa [E1, C2, b, c, tateOriginAffine] using
      (scaleToTate_origin_order12
        (W := E1) (hA4 := hA4_1) (hA6 := hA6_1)
        (h3 := h3_1) (hO := hO1) (hOrd := hOrd1))
```

## Small missing wrappers, if the file does not already have them

### 1. `a₂ ≠ 0` at an order-12 origin

This is needed only if your scaling uses `u = a₃/a₂`.  It is a tiny order obstruction: if `a₂=0` after `a₄=a₆=0`, then the origin has order dividing `3`, not `12`.

```lean
theorem origin_a2_ne_zero_of_addOrderOf_eq_12
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrd : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    W.a₂ ≠ 0 := by
  intro h2
  -- Existing group-law API route:
  -- with a₄=0 in the post-killA4 use site, doubling gives x(2O)=-a₂=0;
  -- hence 2O has the same x-coordinate as O, and the line calculation gives 3O=0.
  -- Prefer proving the specialized lemma below after killA4, because it has fewer fields.
  exact origin_a2_ne_zero_of_addOrderOf_eq_12_of_a4_a6
    (W := W) hO hOrd h2
```

A more local statement, usually easier to prove and sufficient for the assembly theorem, is:

```lean
theorem origin_a2_ne_zero_of_addOrderOf_eq_12_of_a4_a6
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrd : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12)
    (hA4 : W.a₄ = 0) (hA6 : W.a₆ = 0) :
    W.a₂ ≠ 0 := by
  intro h2
  -- Skeleton using existing affine-add lemmas, no new math:
  -- 1. `Point.add_self_of_Y_ne` at `(0,0)` uses `W.a₃ ≠ 0`, already available
  --    from `origin_a3_ne_zero_of_addOrderOf_eq_12`.
  -- 2. Under `hA4,hA6,h2`, the formula gives `2O = -O`.
  -- 3. Hence `3O=0`, so `addOrderOf O ∣ 3`, contradicting `hOrd = 12`.
  have h3 : W.a₃ ≠ 0 := origin_a3_ne_zero_of_addOrderOf_eq_12 (W := W) hO hOrd
  have hthree : (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 hO = 0 := by
    exact origin_three_nsmul_eq_zero_of_a2_eq_zero_a4_eq_zero_a6_eq_zero
      (W := W) hO h2 hA4 hA6 h3
  have hdiv : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) ∣ 3 := by
    exact addOrderOf_dvd_of_nsmul_eq_zero hthree
  rw [hOrd] at hdiv
  norm_num at hdiv
```

If you already have a lemma named differently, use that instead.  The assembly theorem only needs the final `E1.a₂ ≠ 0`.

### 2. `b ≠ 0`

If `tateBOfOriginNormal` is the standard normalized value

```text
b = - E1.a₂ ^ 3 / E1.a₃ ^ 2
```

then the proof is just `field_simp`.

```lean
theorem tateBOfOriginNormal_ne_zero
    (W : WeierstrassCurve ℚ) (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0) :
    tateBOfOriginNormal W h2 h3 ≠ 0 := by
  simp [tateBOfOriginNormal]
  exact div_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero 3 h2))
    (pow_ne_zero 2 h3)
```

If your local definition uses the opposite sign, the same proof works after deleting `neg_ne_zero.mpr`.

### 3. Discriminant nonzero for the Tate target

This wrapper is the cleanest way to fill the `hDelta` field.  It avoids unfolding the large discriminant polynomial.

```lean
theorem tateW_delta_ne_zero_of_variableChange_eq
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    {b c : ℚ} (hCurve : C • W = tateW b c) :
    (tateW b c).Δ ≠ 0 := by
  rw [← hCurve]
  -- Prefer an existing lemma if present:
  --   exact variableChange_delta_ne_zero (W := W) (C := C)
  -- If not, the direct discriminant formula route is:
  rw [WeierstrassCurve.variableChange_Δ]
  -- Depending on the local formula, this is either `C.u ^ 12 * W.Δ`
  -- or `W.Δ / C.u ^ 12`.  In both cases `field_simp` closes from
  -- the nonzero `u` built into the variable-change/equivalence API and `W.Δ_ne_zero`.
  field_simp
```

If the last two lines need exact local names, use whichever one of these is already present in the file:

```lean
  exact WeierstrassCurve.variableChange_delta_ne_zero (W := W) (C := C)
```

or

```lean
  exact (show (C • W).Δ ≠ 0 from inferInstance.Δ_ne_zero)
```

or

```lean
  haveI : (C • W).IsElliptic := by infer_instance
  exact WeierstrassCurve.IsElliptic.delta_ne_zero (C • W)
```

The important point: this is a wrapper around existing ellipticity/variable-change infrastructure, not a Tate-specific calculation.

### 4. Origin order through `scaleToTateVC`

If not already present, prove this once and use it in the assembly theorem.

```lean
theorem scaleToTate_origin_order12
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hA4 : W.a₄ = 0) (hA6 : W.a₆ = 0)
    (h2 : W.a₂ ≠ 0) (h3 : W.a₃ ≠ 0)
    (hO : (W⁄ℚ).Nonsingular 0 0)
    (hOrd : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO) = 12) :
    addOrderOf
      (tateOriginAffine
        (tateBOfOriginNormal W h2 h3)
        (tateCOfOriginNormal W h2 h3)
        (tateBOfOriginNormal_ne_zero W h2 h3)) = 12 := by
  classical
  let C := scaleToTateVC W h2 h3
  let b := tateBOfOriginNormal W h2 h3
  let c := tateCOfOriginNormal W h2 h3
  have hCurve : C • W = tateW b c := by
    simpa [C, b, c] using scaleToTate_eq_tateW (W := W) hA4 hA6 h2 h3
  have hO' : ((C • W)⁄ℚ).Nonsingular 0 0 := by
    simpa [C] using scaleToTate_origin_nonsingular (W := W) h2 h3 hO
  have hmap :
      affineVariableChangeMap W C
        (WeierstrassCurve.Affine.Point.some 0 0 hO) =
      WeierstrassCurve.Affine.Point.some 0 0 hO' := by
    simpa [C, scaleToTateVC, vcNewX, vcNewY]
      using scaleToTate_origin_map (W := W) h2 h3 hO
  let e := affinePointAddEquivOfVariableChange W C
  have hOrd' : addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 hO') = 12 := by
    rw [← hmap]
    simpa [e, hOrd] using
      addOrderOf_apply_addEquiv e
        (WeierstrassCurve.Affine.Point.some 0 0 hO)
  -- Transport across `hCurve` and proof irrelevance for the nonsingularity proof.
  simpa [b, c, hCurve, tateOriginAffine] using hOrd'
```

If your `scaleToTateVC` takes only `h3`, delete `h2` from the statement and calls.

### 5. Variable-change composition wrapper if `rw [mul_smul, mul_smul]` fails

If `VariableChange` is not registered as a monoid action in your local Mathlib snapshot, add this explicit wrapper using the composition operation already used by your additive-equivalence lemmas.

```lean
theorem variableChange_three_smul
    (E : WeierstrassCurve ℚ)
    (C0 C1 C2 : WeierstrassCurve.VariableChange ℚ) :
    (C2 * C1 * C0) • E = C2 • (C1 • (C0 • E)) := by
  rw [mul_smul, mul_smul]
```

Then replace the `hCurve` proof by:

```lean
  have hCurve : C • E = tateW b c := by
    dsimp [C]
    rw [variableChange_three_smul]
    simpa [E1, E0] using hCurve2
```

## Why this shrinks the residual correctly

The old axiom asserts existence of a Tate normal form with an order-12 origin.  The checked later infrastructure already gives exactly that:

- `affineMarkedPointOfOrder12_of_addOrder12` removes the point-at-infinity case;
- `translate_order12_point_to_origin` produces a variable change `C0`, an origin on `C0 • E`, `a₆=0`, and order `12` at the origin;
- `killA4VC` produces `C1` with `a₄=0`, preserves `a₆=0`, and transports the origin order;
- `scaleToTate_eq_tateW` produces `C2 • (C1 • (C0 • E)) = tateW b c`;
- the `b ≠ 0` field is just the nonzero denominator/numerator fact in the scaling formula;
- the `hDelta` field follows from ellipticity under variable change;
- the `hOriginOrder` field follows from additive equivalence/order preservation and the fact that `killA4VC` and `scaleToTateVC` fix `(0,0)`.

So the axiom is not mathematically needed anymore.  At most, the file needs the small wrappers above and a declaration-order move.
