# Q3003 (dm-codex1): N10 route from exact order 10 to `tateC10_K = 0`

Target: shrink the remaining group-law part of `FLT/Assumptions/MazurProof/KubertBridgeN10.lean`.

The safe split is:

1. Prove `b-c ≠ 0` from exact order 10.
2. Prove one coordinate lemma: the explicit point `(tateC10_5P_x b c, tateC10_5P_y b c)` is `5 • tateOriginAffine b c hb`.
3. Reuse/genericize the N12 affine-two-torsion linear relation: if an affine point on `tateW b c` is killed by `2`, then `tateC10Psi2 b c x y = 0`.
4. Use the already-checked algebra theorem `tateC10_psi2_5P_eq_K_div` to clear denominators and get `K=0`.

## Names to search/reuse from N12

Search in `KubertBridgeN12.lean` for these names or analogous declarations:

```text
tatePsi4CoreAt3P_eq_zero_of_origin_order12
tatePsi4CoreAt3P_eq_zero_of_double_psi2
tateP3_add_self_eq_tateDouble3P_of_some
tate_double_psi2_core_at_3P
psi2_eq_zero_of_affine_two_torsion
tatePsi2_eq_zero_of_affine_two_torsion
WeierstrassCurve.Affine.Point.add_self_of_Y_ne
WeierstrassCurve.Affine.Point.add_of_X_ne
WeierstrassCurve.Affine.slope_of_X_ne
WeierstrassCurve.Affine.nonsingular_add
addOrderOf_nsmul_eq_zero
addOrderOf_dvd_of_nsmul_eq_zero
addOrderOf_dvd_iff_nsmul_eq_zero
```

Do not import `KubertBridgeN12.lean` into N10 unless you have verified the import DAG.  The cleaner route is to move generic affine/torsion helper lemmas to a shared helper file, for example `KubertTateCommon.lean`, and import that from both N10 and N12.  For the smallest local patch, copy the generic helper wrappers into N10.

## Minimal residual split

If the full coordinate proof is too long, leave exactly this small residual, not the old `kubert_C10_square`:

```lean
/-- The only remaining group-law/table residual: explicit affine coordinates for `5P`. -/
axiom tateC10_5P_eq
    {b c : ℚ} (hb : b ≠ 0) (hbc : b - c ≠ 0) :
    ∃ h5 : ((tateW b c)⁄ℚ).Nonsingular
        (tateC10_5P_x b c) (tateC10_5P_y b c),
      (5 : ℕ) • tateOriginAffine b c hb =
        WeierstrassCurve.Affine.Point.some
          (tateC10_5P_x b c) (tateC10_5P_y b c) h5
```

Then everything after it is checked Lean.  If you want an even smaller but less structural residual, use:

```lean
/-- Smallest possible residual for this step, but less reusable than `tateC10_5P_eq`. -/
axiom tateC10Psi2_5P_eq_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    tateC10Psi2 b c (tateC10_5P_x b c) (tateC10_5P_y b c) = 0
```

I recommend the first residual: it isolates the affine group law, and the exact-order/two-torsion part remains checked.

## Wrapper 1: `b-c ≠ 0`

The clean proof is: if `b=c`, then `5 • P = 0`, so `addOrderOf P ∣ 5`, contradicting `addOrderOf P = 10`.

Add this small residual/lemma first if you do not already have the `b=c` table degeneration:

```lean
/-- If `b=c`, the Tate origin is 5-torsion.  This is a short Tate-table computation. -/
theorem tateOrigin_five_nsmul_eq_zero_of_b_eq_c
    {b c : ℚ} (hb : b ≠ 0) (hbc_eq : b = c) :
    (5 : ℕ) • tateOriginAffine b c hb = 0 := by
  -- Route:
  --   use the same table lemmas as `tateOrigin_threeP_eq` / `tate_three_nsmul_origin_eq`;
  --   compute `5P` by `2P+3P` or direct repeated addition;
  --   after `b=c`, the addition denominator branch is the vertical branch, so the sum is `0`.
  -- If this is too long, keep this theorem as the only helper residual for `b-c ≠ 0`.
  exact tateOrigin_five_nsmul_eq_zero_of_b_eq_c_residual hb hbc_eq
```

Then the nonzero theorem is short:

```lean
theorem tateC10_b_sub_c_ne_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    b - c ≠ 0 := by
  intro hbc0
  have hbc_eq : b = c := sub_eq_zero.mp hbc0
  have h5 : (5 : ℕ) • tateOriginAffine b c hb = 0 :=
    tateOrigin_five_nsmul_eq_zero_of_b_eq_c (b := b) (c := c) hb hbc_eq
  have hdiv : addOrderOf (tateOriginAffine b c hb) ∣ 5 := by
    exact addOrderOf_dvd_of_nsmul_eq_zero h5
  rw [hOrd] at hdiv
  norm_num at hdiv
```

If your Mathlib snapshot does not have `addOrderOf_dvd_of_nsmul_eq_zero`, use the iff form:

```lean
  have hdiv : addOrderOf (tateOriginAffine b c hb) ∣ 5 := by
    exact (addOrderOf_dvd_iff_nsmul_eq_zero).2 h5
```

## Wrapper 2: affine two-torsion gives the Tate `ψ₂` linear relation

This is generic and should be copied from the N12 proof if present.

```lean
theorem tateC10Psi2_eq_zero_of_two_nsmul_eq_zero
    {b c x y : ℚ}
    {hxy : ((tateW b c)⁄ℚ).Nonsingular x y}
    (h2 : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hxy = 0) :
    tateC10Psi2 b c x y = 0 := by
  -- Generic route:
  --   let R := Point.some x y hxy;
  --   from `2 • R = 0`, get `R = -R`;
  --   affine negation on `tateW b c` is `(x, -y - (1-c)*x + b)`;
  --   coordinate equality gives `2*y + (1-c)*x - b = 0`.
  -- Usually the final step is exactly the N12 `psi2_eq_zero_of_affine_two_torsion`.
  simpa [tateC10Psi2, tateW] using
    (tatePsi2_eq_zero_of_affine_two_torsion
      (W := tateW b c) (x := x) (y := y) (hxy := hxy) h2)
```

If the N12 helper is not available, paste this local generic version and adjust only the affine negation simp lemma name if necessary:

```lean
theorem tateC10Psi2_eq_zero_of_two_nsmul_eq_zero_local
    {b c x y : ℚ}
    {hxy : ((tateW b c)⁄ℚ).Nonsingular x y}
    (h2 : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hxy = 0) :
    tateC10Psi2 b c x y = 0 := by
  classical
  let R : ((tateW b c)⁄ℚ).Point :=
    WeierstrassCurve.Affine.Point.some x y hxy
  have hRadd : R + R = 0 := by
    simpa [R, two_nsmul] using h2
  have hReqNeg : R = -R := by
    calc
      R = R + 0 := by simp
      _ = R + (R + -R) := by simp
      _ = (R + R) + -R := by abel
      _ = 0 + -R := by rw [hRadd]
      _ = -R := by simp
  -- If this `simpa` fails, search for the N12 negation proof and replace
  -- `WeierstrassCurve.Affine.Point.neg` by the local simp theorem it uses.
  have hy : y = -y - (1 - c) * x + b := by
    simpa [R, tateW, WeierstrassCurve.Affine.Point.neg] using hReqNeg
  dsimp [tateC10Psi2]
  linarith
```

## Wrapper 3: coordinate theorem `tateC10_5P_eq`

This is the main coordinate proof.  It should mirror the N12 proof of `2(3P)` but use `2P + 3P` with distinct x-coordinates.

Recommended exact statement:

```lean
theorem tateC10_5P_eq
    {b c : ℚ} (hb : b ≠ 0) (hbc : b - c ≠ 0) :
    ∃ h5 : ((tateW b c)⁄ℚ).Nonsingular
        (tateC10_5P_x b c) (tateC10_5P_y b c),
      (5 : ℕ) • tateOriginAffine b c hb =
        WeierstrassCurve.Affine.Point.some
          (tateC10_5P_x b c) (tateC10_5P_y b c) h5 := by
  classical
  let P : ((tateW b c)⁄ℚ).Point := tateOriginAffine b c hb

  -- Use existing Tate table facts.  Search for these exact N12 names:
  --   tate_origin_twoP_eq / tate_two_nsmul_origin_eq
  --   tate_origin_threeP_eq / tate_three_nsmul_origin_eq
  have h2P := tate_two_nsmul_origin_eq (b := b) (c := c) hb
  have h3P := tate_three_nsmul_origin_eq (b := b) (c := c) hb

  -- Split `5P` as `2P + 3P`.
  have h5split : (5 : ℕ) • P = (2 : ℕ) • P + (3 : ℕ) • P := by
    norm_num [P, add_nsmul]

  -- Distinct-x branch for adding `(b,bc)` and `(c,b-c)`.
  have hX_ne : b ≠ c := by
    intro h
    exact hbc (sub_eq_zero.mpr h)

  -- The following three local coordinate lemmas are pure `field_simp; ring`.
  have hslope :
      ((tateW b c)⁄ℚ).slope b c (b * c) (b - c) =
        (b - c - b * c) / (c - b) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hX_ne]
    simp [tateW]
    field_simp [sub_ne_zero.mpr hX_ne]
    ring

  have hx :
      ((tateW b c)⁄ℚ).addX b c
          (((tateW b c)⁄ℚ).slope b c (b * c) (b - c)) =
        tateC10_5P_x b c := by
    rw [hslope]
    simp [tateW, tateC10_5P_x]
    have hcb : c - b ≠ 0 := sub_ne_zero.mpr hX_ne.symm
    have hbc2 : (b - c) ^ 2 ≠ 0 := pow_ne_zero 2 hbc
    field_simp [hbc, hbc2, hcb]
    ring

  have hy :
      ((tateW b c)⁄ℚ).addY b c (b * c)
          (((tateW b c)⁄ℚ).slope b c (b * c) (b - c)) =
        tateC10_5P_y b c := by
    rw [hslope]
    simp [tateW, tateC10_5P_y, tateC10_5P_x]
    have hcb : c - b ≠ 0 := sub_ne_zero.mpr hX_ne.symm
    have hbc2 : (b - c) ^ 2 ≠ 0 := pow_ne_zero 2 hbc
    field_simp [hbc, hbc2, hcb]
    ring

  -- Add the affine points by the distinct-x formula.
  -- The exact proof terms for nonsingularity of `2P` and `3P` are hidden inside h2P/h3P;
  -- if the final `simpa` does not recover them, make an `_of_some` version analogous
  -- to N12's `tateP3_add_self_eq_tateDouble3P_of_some`.
  refine ⟨?h5, ?eq⟩
  · -- Let Mathlib construct the nonsingularity proof for the sum.
    exact by
      -- Usually follows from `WeierstrassCurve.Affine.nonsingular_add` plus `hx/hy`.
      -- Prefer copying the N12 pattern.
      simpa [hx, hy] using
        WeierstrassCurve.Affine.nonsingular_add
          (W := (tateW b c)⁄ℚ)
          (by exact (by
            -- extract from h2P if needed
            exact tateP2_nonsingular (b := b) (c := c) hb))
          (by exact (by
            -- extract from h3P if needed
            exact tateP3_nonsingular (b := b) (c := c) hb))
          (by intro h; exact hX_ne h.left)
  · -- Now use `Point.add_of_X_ne` and the split.
    rw [h5split, h2P, h3P]
    have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne
      (W := (tateW b c)⁄ℚ) (x₁ := b) (x₂ := c)
      (y₁ := b * c) (y₂ := b - c) hX_ne
    simpa [hx, hy] using hadd
```

The last block is the only likely non-pasteable part because it depends on how your local `h2P`/`h3P` package nonsingularity proofs.  The safe version is an `_of_some` theorem that takes the two nonsingularity proofs explicitly:

```lean
theorem tateC10_P2_add_P3_eq_of_some
    {b c : ℚ}
    {h2 : ((tateW b c)⁄ℚ).Nonsingular b (b * c)}
    {h3 : ((tateW b c)⁄ℚ).Nonsingular c (b - c)}
    (hbc : b - c ≠ 0) :
    ∃ h5 : ((tateW b c)⁄ℚ).Nonsingular
        (tateC10_5P_x b c) (tateC10_5P_y b c),
      WeierstrassCurve.Affine.Point.some b (b * c) h2 +
        WeierstrassCurve.Affine.Point.some c (b - c) h3 =
        WeierstrassCurve.Affine.Point.some
          (tateC10_5P_x b c) (tateC10_5P_y b c) h5 := by
  -- This is exactly the N12 `_of_some` pattern, but with `Point.add_of_X_ne`.
  -- All coordinate subgoals are the `hslope/hx/hy` field_simp/ring blocks above.
  exact tateC10_P2_add_P3_eq_of_some_residual (b := b) (c := c) hbc
```

Then `tateC10_5P_eq` becomes a packaging theorem using `h2P`, `h3P`, and `(5:ℕ)•P = 2P+3P`.

## Wrapper 4: exact order 10 gives `K=0`

This is the wrapper that should compile once `tateC10_b_sub_c_ne_zero_of_origin_order10`, `tateC10_5P_eq`, and the two-torsion linear relation are available.

```lean
theorem tateC10_K_eq_zero_of_origin_order10
    {b c : ℚ} (hb : b ≠ 0)
    (hOrd : addOrderOf (tateOriginAffine b c hb) = 10) :
    tateC10_K b c = 0 := by
  have hbc : b - c ≠ 0 :=
    tateC10_b_sub_c_ne_zero_of_origin_order10 (b := b) (c := c) hb hOrd

  rcases tateC10_5P_eq (b := b) (c := c) hb hbc with ⟨h5, h5eq⟩

  have h10 : (10 : ℕ) • tateOriginAffine b c hb = 0 := by
    rw [← hOrd]
    exact addOrderOf_nsmul_eq_zero (tateOriginAffine b c hb)

  have htwo_five :
      (2 : ℕ) •
        (WeierstrassCurve.Affine.Point.some
          (tateC10_5P_x b c) (tateC10_5P_y b c) h5) = 0 := by
    rw [← h5eq]
    simpa [nsmul_nsmul, mul_comm, mul_left_comm, mul_assoc] using h10

  have hpsi :
      tateC10Psi2 b c (tateC10_5P_x b c) (tateC10_5P_y b c) = 0 :=
    tateC10Psi2_eq_zero_of_two_nsmul_eq_zero
      (b := b) (c := c)
      (x := tateC10_5P_x b c) (y := tateC10_5P_y b c)
      (hxy := h5) htwo_five

  -- Adjust the call if your local theorem has `(hb)` as an extra argument.
  have hrel := tateC10_psi2_5P_eq_K_div (b := b) (c := c) hbc
  rw [hpsi] at hrel

  have hbc3 : (b - c) ^ 3 ≠ 0 := pow_ne_zero 3 hbc
  have hquot : b * tateC10_K b c / (b - c) ^ 3 = 0 := by
    simpa using hrel.symm
  have hmul := congrArg (fun z : ℚ => z * (b - c) ^ 3) hquot
  field_simp [hbc3] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left hb
```

If your `tateC10_psi2_5P_eq_K_div` statement is:

```lean
tateC10_psi2_5P_eq_K_div (hb : b ≠ 0) (hbc : b - c ≠ 0) : ...
```

replace the `hrel` line by:

```lean
  have hrel := tateC10_psi2_5P_eq_K_div (b := b) (c := c) hb hbc
```

If Mathlib cannot rewrite `h10` with `addOrderOf_nsmul_eq_zero`, use:

```lean
  have h10 : (10 : ℕ) • tateOriginAffine b c hb = 0 := by
    have h := addOrderOf_nsmul_eq_zero (tateOriginAffine b c hb)
    simpa [hOrd] using h
```

## Edge cases and warnings

- `hb : b ≠ 0` is essential in this file because `tateOriginAffine b c hb` is constructed using nonsingularity of the origin.  It is also needed to clear the factor `b` in `b*K/(b-c)^3 = 0`.
- `b-c=0` is exactly the order-5 degeneration.  Do not try to use the explicit `5P` coordinate formulas in that branch: their denominator is `(b-c)`.  Prove `b-c≠0` first from exact order 10.
- Singularity should not enter the `K=0` wrapper if the point is already `tateOriginAffine b c hb` with exact order 10.  In the full bridge, singular cases are excluded by `[E.IsElliptic]` and variable-change transport.
- There is no point-at-infinity case in this local step: `tateOriginAffine b c hb` and the explicit `5P` result are affine `Point.some` values.
- The coordinate proof should use the distinct-x addition branch `Point.add_of_X_ne`, not the tangent branch `Point.add_self_of_Y_ne` used in the N12 `2(3P)` proof.

## Shortest safe path

The shortest safe patch is:

1. Add residual `tateOrigin_five_nsmul_eq_zero_of_b_eq_c` or prove it from existing Tate table facts.
2. Add checked `tateC10_b_sub_c_ne_zero_of_origin_order10`.
3. Add residual `tateC10_5P_eq`.
4. Copy/genericize N12 `psi2_eq_zero_of_affine_two_torsion`.
5. Add checked `tateC10_K_eq_zero_of_origin_order10` using the code above.

This shrinks the hard residual from a global Kubert/full-2 bridge statement to one explicit affine addition theorem for `5P` on the Tate curve.
