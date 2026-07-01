# Q2974 (dm-codex1): Tate C12 `ψ₂(2·3P)` computation and affine doubling glue

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN12.lean`  
Namespace: `MazurProof.KubertBridgeN12`

Below is the insertion I recommend.  The arithmetic theorem is fully direct and should close with `field_simp; ring`.  The group-law lemma is written in a robust `of_some` form: it takes the nonsingularity proof of the already-known point `(c,b-c)` as an implicit argument.  This avoids depending on the private proof term used internally by `tateP3`.  After this lemma is in the file, the wrapper for your concrete `tateP3 b c hb` should be just `simpa [tateP3]` if `tateP3` is reducible.

```lean
import FLT.Assumptions.MazurProof.KubertBridgeN12
import Mathlib.Tactic

open scoped WeierstrassCurve.Affine

namespace MazurProof.KubertBridgeN12

noncomputable section

/-- The usual `ψ₂ = 2y + a₁x + a₃` on the Tate normal form
`a₁=1-c`, `a₃=-b`. -/
def tatePsi2 (b c x y : ℚ) : ℚ :=
  2 * y + (1 - c) * x - b

/-- The tangent denominator at `3P = (c,b-c)`. -/
def tateDouble3P_D (b c : ℚ) : ℚ :=
  b - c - c ^ 2

/-- The tangent slope at `3P = (c,b-c)`. -/
def tateDouble3P_L (b c : ℚ) : ℚ :=
  (2 * c ^ 2 - b * c + c - b) / tateDouble3P_D b c

/-- The x-coordinate of `2(3P)`, written through the tangent slope. -/
def tateDouble3P_x (b c : ℚ) : ℚ :=
  let L := tateDouble3P_L b c
  L ^ 2 + (1 - c) * L + b - 2 * c

/-- The y-coordinate of `2(3P)`, written through the tangent line and final negation. -/
def tateDouble3P_y (b c : ℚ) : ℚ :=
  let L := tateDouble3P_L b c
  let x := tateDouble3P_x b c
  - (L * (x - c) + (b - c)) - (1 - c) * x + b

@[simp] theorem tatePsi2_at_3P_eq_D (b c : ℚ) :
    tatePsi2 b c c (b - c) = tateDouble3P_D b c := by
  simp [tatePsi2, tateDouble3P_D]
  ring

/-- Closed form for the tangent slope after unfolding Mathlib's formula. -/
theorem tateDouble3P_slope_formula
    {b c : ℚ} (hD : tateDouble3P_D b c ≠ 0) :
    ((tateW b c)⁄ℚ).slope c c (b - c) (b - c) = tateDouble3P_L b c := by
  have hD0 : b - c - c ^ 2 ≠ 0 := by
    simpa [tateDouble3P_D] using hD
  have hY_ne : b - c ≠ ((tateW b c)⁄ℚ).negY c (b - c) := by
    intro h
    apply hD0
    -- `negY c (b-c)` is `c^2` on this Tate curve.
    simp [tateW, WeierstrassCurve.Affine.negY] at h
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hY_ne]
  simp [tateW, tateDouble3P_L, tateDouble3P_D, hD0]
  field_simp [hD0]
  ring

/-- Mathlib's `addX` coordinate agrees with `tateDouble3P_x`. -/
theorem tateDouble3P_addX_formula
    {b c : ℚ} (hD : tateDouble3P_D b c ≠ 0) :
    ((tateW b c)⁄ℚ).addX c c (((tateW b c)⁄ℚ).slope c c (b - c) (b - c)) =
      tateDouble3P_x b c := by
  rw [tateDouble3P_slope_formula (b := b) (c := c) hD]
  simp [tateW, tateDouble3P_x]
  ring

/-- Mathlib's `addY` coordinate agrees with `tateDouble3P_y`. -/
theorem tateDouble3P_addY_formula
    {b c : ℚ} (hD : tateDouble3P_D b c ≠ 0) :
    ((tateW b c)⁄ℚ).addY c c (b - c)
        (((tateW b c)⁄ℚ).slope c c (b - c) (b - c)) =
      tateDouble3P_y b c := by
  rw [tateDouble3P_slope_formula (b := b) (c := c) hD]
  simp [tateW, tateDouble3P_y, tateDouble3P_x]
  ring

/-- Pure arithmetic: `ψ₂(2·3P)=c*K/D^3`. -/
theorem tatePsi2_double3P_eq_core_div
    {b c : ℚ} (hD : tateDouble3P_D b c ≠ 0) :
    tatePsi2 b c (tateDouble3P_x b c) (tateDouble3P_y b c) =
      c * tateC12_K b c / (tateDouble3P_D b c) ^ 3 := by
  have hD0 : b - c - c ^ 2 ≠ 0 := by
    simpa [tateDouble3P_D] using hD
  have hD2 : (b - c - c ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hD0
  have hD3 : (b - c - c ^ 2) ^ 3 ≠ 0 := pow_ne_zero 3 hD0
  simp [tatePsi2, tateDouble3P_y, tateDouble3P_x, tateDouble3P_L,
    tateDouble3P_D, tateC12_K]
  field_simp [hD0, hD2, hD3]
  ring

/-- Same arithmetic theorem, using the already-existing core identity name. -/
theorem tatePsi2_double3P_eq_psi4Core_div
    {b c : ℚ} (hD : tateDouble3P_D b c ≠ 0) :
    tatePsi2 b c (tateDouble3P_x b c) (tateDouble3P_y b c) =
      tatePsi4CoreAt3P b c / (tateDouble3P_D b c) ^ 3 := by
  rw [tatePsi4CoreAt3P_eq_c_mul_K]
  exact tatePsi2_double3P_eq_core_div (b := b) (c := c) hD

/-- If the arithmetic identity is zero on the left, the `ψ₄` core vanishes. -/
theorem tatePsi4CoreAt3P_eq_zero_of_tatePsi2_double3P_eq_zero
    {b c : ℚ} (hD : tateDouble3P_D b c ≠ 0)
    (hpsi : tatePsi2 b c (tateDouble3P_x b c) (tateDouble3P_y b c) = 0) :
    tatePsi4CoreAt3P b c = 0 := by
  have hrel := tatePsi2_double3P_eq_psi4Core_div (b := b) (c := c) hD
  rw [hpsi] at hrel
  have hD3 : (tateDouble3P_D b c) ^ 3 ≠ 0 := pow_ne_zero 3 hD
  have hquot : tatePsi4CoreAt3P b c / (tateDouble3P_D b c) ^ 3 = 0 := by
    simpa using hrel.symm
  have hmul := congrArg (fun z : ℚ => z * (tateDouble3P_D b c) ^ 3) hquot
  field_simp [hD3] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

/--
Affine group-law computation, independent of the internal proof term inside `tateP3`.

Use this with the nonsingularity proof already carried by your `tateP3` definition.  If
`tateP3` unfolds to `Point.some c (b-c) hQ`, the concrete wrapper is usually:

```lean
  simpa [tateP3] using
    (tateP3_add_self_eq_tateDouble3P_of_some (b := b) (c := c) (hQ := hQ) hD)
```
-/
theorem tateP3_add_self_eq_tateDouble3P_of_some
    {b c : ℚ}
    {hQ : ((tateW b c)⁄ℚ).Nonsingular c (b - c)}
    (hD : tateDouble3P_D b c ≠ 0) :
    ∃ h2Q : ((tateW b c)⁄ℚ).Nonsingular
        (tateDouble3P_x b c) (tateDouble3P_y b c),
      WeierstrassCurve.Affine.Point.some c (b - c) hQ +
          WeierstrassCurve.Affine.Point.some c (b - c) hQ =
        WeierstrassCurve.Affine.Point.some
          (tateDouble3P_x b c) (tateDouble3P_y b c) h2Q := by
  classical
  let W := (tateW b c)⁄ℚ
  have hD0 : b - c - c ^ 2 ≠ 0 := by
    simpa [tateDouble3P_D] using hD
  have hY_ne : b - c ≠ W.negY c (b - c) := by
    intro h
    apply hD0
    simp [W, tateW, WeierstrassCurve.Affine.negY] at h
    linarith
  have hx : W.addX c c (W.slope c c (b - c) (b - c)) = tateDouble3P_x b c := by
    simpa [W] using tateDouble3P_addX_formula (b := b) (c := c) hD
  have hy : W.addY c c (b - c) (W.slope c c (b - c) (b - c)) =
      tateDouble3P_y b c := by
    simpa [W] using tateDouble3P_addY_formula (b := b) (c := c) hD
  have h2Qraw : W.Nonsingular
      (W.addX c c (W.slope c c (b - c) (b - c)))
      (W.addY c c (b - c) (W.slope c c (b - c) (b - c))) :=
    WeierstrassCurve.Affine.nonsingular_add
      (W := W) hQ hQ (fun hxy => hY_ne hxy.right)
  have h2Q : W.Nonsingular (tateDouble3P_x b c) (tateDouble3P_y b c) := by
    simpa [hx, hy] using h2Qraw
  refine ⟨h2Q, ?_⟩
  have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := W) (x₁ := c) (y₁ := b - c) (h₁ := hQ) hY_ne
  simpa [W, hx, hy] using hadd

end

end MazurProof.KubertBridgeN12
```

## If the `simp [tateW]` lines need local adjustment

The only fragile lines are the ones unfolding the affine coefficients of `(tateW b c)⁄ℚ`:

```lean
simp [tateW, WeierstrassCurve.Affine.negY] at h
simp [tateW, tateDouble3P_L, tateDouble3P_D, hD0]
simp [tateW, tateDouble3P_x]
simp [tateW, tateDouble3P_y, tateDouble3P_x]
```

If your local coercion from `WeierstrassCurve ℚ` to affine curve does not reduce by `simp [tateW]`, replace those lines by the local simp lemmas for the five coefficients of `tateW`, e.g.

```lean
simp [tateW_a1, tateW_a2, tateW_a3, tateW_a4, tateW_a6,
  WeierstrassCurve.Affine.negY]
```

or, if the coefficient projections are reducible but the base-change notation is not, use:

```lean
change (2 * c ^ 2 - b * c + c - b) / (b - c - c ^ 2) = _
```

right after `rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hY_ne]`, then close with `field_simp [hD0]; ring`.

## Concrete wrapper for your `tateP3`

If `tateP3 b c hb` unfolds to `WeierstrassCurve.Affine.Point.some c (b-c) _`, this wrapper should compile:

```lean
theorem tateP3_add_self_eq_tateDouble3P
    {b c : ℚ} (hb : b ≠ 0) (hD : tateDouble3P_D b c ≠ 0) :
    ∃ h2Q : ((tateW b c)⁄ℚ).Nonsingular
        (tateDouble3P_x b c) (tateDouble3P_y b c),
      tateP3 b c hb + tateP3 b c hb =
        WeierstrassCurve.Affine.Point.some
          (tateDouble3P_x b c) (tateDouble3P_y b c) h2Q := by
  -- This is the exact line that may need adjustment if `tateP3` is opaque.
  simpa [tateP3] using
    (tateP3_add_self_eq_tateDouble3P_of_some (b := b) (c := c) hD)
```

If that final `simpa [tateP3]` fails because `tateP3` hides its nonsingularity proof behind an opaque theorem, keep the `of_some` theorem above and call it at the construction site where that proof is available.  Do not reprove the group law: the Mathlib line is precisely

```lean
WeierstrassCurve.Affine.Point.add_self_of_Y_ne
```

with non-vertical hypothesis

```lean
b - c ≠ ((tateW b c)⁄ℚ).negY c (b - c)
```

which is equivalent by `ring` to `b - c - c^2 ≠ 0`.
