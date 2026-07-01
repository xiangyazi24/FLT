# Q3010 (dm-codex1): denominator-cancellation proof shape for C10 Tate discriminant

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN10.lean`.

I could not fetch the exact local working file through the connector, and I did not run a local Lean check.  The snippet below is designed to avoid the failure mode you described: it never asks `field_simp` to understand that

```lean
1 - p * 3 + p ^ 2
```

is the same denominator as `tateC10_den p`.  Instead, it first binds

```lean
D := tateC10_den p
```

and clears denominators in generic lemmas whose denominator is exactly the variable `D`.

The most important compile target is `tateC10_b_cube_num`; that proof uses no `field_simp` at all.

## Patchable Lean snippet

Drop this inside `namespace MazurProof.KubertBridgeN10`, after the definitions of `tateC10_den`, `tateC10_b`, `tateC10_c`, and `tateW`.

```lean
/-- The compact residual factor in the discriminant of the Tate normal form
`y^2 + (1-c)xy - b y = x^3 - b x^2`. -/
def tateWDeltaCore (b c : ℚ) : ℚ :=
  16 * b ^ 2 + (1 - 20 * c - 8 * c ^ 2) * b + c * (c - 1) ^ 3

/-- Pure denominator cancellation for `(N / D^2)^3`, avoiding `field_simp`.
This is the robust replacement for the exploding direct proof of `tateC10_b_cube_num`. -/
private theorem clear_cube_div_sq (N D : ℚ) (hD : D ≠ 0) :
    D ^ 6 * (N / D ^ 2) ^ 3 = N ^ 3 := by
  have hD6 : D ^ 6 ≠ 0 := pow_ne_zero 6 hD
  calc
    D ^ 6 * (N / D ^ 2) ^ 3
        = D ^ 6 * (N ^ 3 / (D ^ 2) ^ 3) := by
            rw [div_pow]
    _ = D ^ 6 * (N ^ 3 / D ^ 6) := by
            rw [show (D ^ 2) ^ 3 = D ^ 6 by ring]
    _ = N ^ 3 := by
            rw [div_eq_mul_inv]
            calc
              D ^ 6 * (N ^ 3 * (D ^ 6)⁻¹)
                  = N ^ 3 * (D ^ 6 * (D ^ 6)⁻¹) := by
                      ring
              _ = N ^ 3 * 1 := by
                      rw [mul_inv_cancel₀ hD6]
              _ = N ^ 3 := by
                      ring

/-- Numerator identity for the cube of the C10 Tate `b` parameter.
This proof does not call `field_simp`, so it should not leave inverse factors. -/
theorem tateC10_b_cube_num
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateC10_den p) ^ 6 * (tateC10_b p) ^ 3 =
      p ^ 9 * (p - 1) ^ 3 * (2 * p - 1) ^ 3 := by
  let D : ℚ := tateC10_den p
  let N : ℚ := p ^ 3 * (p - 1) * (2 * p - 1)
  have hD : D ≠ 0 := by
    simpa [D] using hden
  calc
    (tateC10_den p) ^ 6 * (tateC10_b p) ^ 3
        = D ^ 6 * (N / D ^ 2) ^ 3 := by
            simp [D, N, tateC10_b]
    _ = N ^ 3 := clear_cube_div_sq N D hD
    _ = p ^ 9 * (p - 1) ^ 3 * (2 * p - 1) ^ 3 := by
            dsimp [N]
            ring
```

That should be the first lemma to add/check.  If this compiles, add the core-clearing version below.

## Core numerator lemma without expanding rational functions at the top level

The trick is to clear the generic denominator before substituting the actual polynomial denominator.

```lean
/-- Polynomial numerator after clearing the denominator in `tateWDeltaCore`. -/
def tateWDeltaCoreNum (B C D : ℚ) : ℚ :=
  16 * B ^ 2 + B * (D ^ 2 - 20 * C * D - 8 * C ^ 2) + C * (C - D) ^ 3

/-- Generic clearing lemma for the core.  This uses `field_simp` only with the
literal denominator variable `D`, not with the expanded polynomial `tateC10_den p`.
So the canonical-form mismatch `(1 - p*3 + p^2)⁻¹` cannot arise here. -/
private theorem clear_core_den4 (B C D : ℚ) (hD : D ≠ 0) :
    D ^ 4 * tateWDeltaCore (B / D ^ 2) (C / D) =
      tateWDeltaCoreNum B C D := by
  have hD2 : D ^ 2 ≠ 0 := pow_ne_zero 2 hD
  have hD3 : D ^ 3 ≠ 0 := pow_ne_zero 3 hD
  have hD4 : D ^ 4 ≠ 0 := pow_ne_zero 4 hD
  dsimp [tateWDeltaCore, tateWDeltaCoreNum]
  field_simp [hD, hD2, hD3, hD4]
  ring

/-- Numerator identity for the compact residual core. -/
theorem tateC10_deltaCore_num
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateC10_den p) ^ 4 *
        tateWDeltaCore (tateC10_b p) (tateC10_c p) =
      p * (p - 1) ^ 7 * (2 * p - 1) ^ 2 *
        (4 * p ^ 2 - 2 * p - 1) := by
  let D : ℚ := tateC10_den p
  let B : ℚ := p ^ 3 * (p - 1) * (2 * p - 1)
  let C : ℚ := -p * (p - 1) * (2 * p - 1)
  have hD : D ≠ 0 := by
    simpa [D] using hden
  have hb : tateC10_b p = B / D ^ 2 := by
    simp [B, D, tateC10_b]
  have hc : tateC10_c p = C / D := by
    simp [C, D, tateC10_c]
  calc
    (tateC10_den p) ^ 4 *
        tateWDeltaCore (tateC10_b p) (tateC10_c p)
        = D ^ 4 * tateWDeltaCore (B / D ^ 2) (C / D) := by
            rw [hb, hc]
            simp [D]
    _ = tateWDeltaCoreNum B C D := clear_core_den4 B C D hD
    _ = p * (p - 1) ^ 7 * (2 * p - 1) ^ 2 *
        (4 * p ^ 2 - 2 * p - 1) := by
            dsimp [tateWDeltaCoreNum, B, C, D, tateC10_den]
            ring
```

If `clear_core_den4` still leaves inverses, try replacing its proof with:

```lean
  dsimp [tateWDeltaCore, tateWDeltaCoreNum]
  ring_nf
  field_simp [hD]
  ring
```

but I would try the displayed `field_simp [hD, hD2, hD3, hD4]; ring` version first, because the expression is generic in `D` and much smaller than the original expanded rational function.

## Optional arbitrary Tate-normal-form discriminant lemma

This is the compact discriminant formula that should close with plain polynomial algebra.

```lean
theorem tateW_delta_factored (b c : ℚ) :
    (tateW b c).Δ = b ^ 3 * tateWDeltaCore b c := by
  simp [tateW, tateWDeltaCore,
    WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring
```

If projection simplification is brittle locally, split it as follows:

```lean
theorem tateW_b₂ (b c : ℚ) :
    (tateW b c).b₂ = (1 - c) ^ 2 - 4 * b := by
  simp [tateW, WeierstrassCurve.b₂]
  ring

theorem tateW_b₄ (b c : ℚ) :
    (tateW b c).b₄ = b * (c - 1) := by
  simp [tateW, WeierstrassCurve.b₄]
  ring

theorem tateW_b₆ (b c : ℚ) :
    (tateW b c).b₆ = b ^ 2 := by
  simp [tateW, WeierstrassCurve.b₆]
  ring

theorem tateW_b₈ (b c : ℚ) :
    (tateW b c).b₈ = - b ^ 3 := by
  simp [tateW, WeierstrassCurve.b₈]
  ring

theorem tateW_delta_factored' (b c : ℚ) :
    (tateW b c).Δ = b ^ 3 * tateWDeltaCore b c := by
  simp [WeierstrassCurve.Δ,
    tateW_b₂ b c, tateW_b₄ b c, tateW_b₆ b c, tateW_b₈ b c,
    tateWDeltaCore]
  ring
```

## Full numerator and divided factorization

After `tateC10_b_cube_num`, `tateC10_deltaCore_num`, and `tateW_delta_factored` compile, the final identities should be light.

```lean
theorem tateC10_delta_num
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateC10_den p) ^ 10 *
        (tateW (tateC10_b p) (tateC10_c p)).Δ =
      p ^ 10 * (p - 1) ^ 10 * (2 * p - 1) ^ 5 *
        (4 * p ^ 2 - 2 * p - 1) := by
  rw [tateW_delta_factored]
  calc
    (tateC10_den p) ^ 10 *
        ((tateC10_b p) ^ 3 *
          tateWDeltaCore (tateC10_b p) (tateC10_c p))
        = ((tateC10_den p) ^ 6 * (tateC10_b p) ^ 3) *
          ((tateC10_den p) ^ 4 *
            tateWDeltaCore (tateC10_b p) (tateC10_c p)) := by
            ring
    _ = p ^ 10 * (p - 1) ^ 10 * (2 * p - 1) ^ 5 *
        (4 * p ^ 2 - 2 * p - 1) := by
          rw [tateC10_b_cube_num p hden, tateC10_deltaCore_num p hden]
          ring

theorem tateC10_delta_factor
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateW (tateC10_b p) (tateC10_c p)).Δ =
      p ^ 10 * (p - 1) ^ 10 * (2 * p - 1) ^ 5 *
        (4 * p ^ 2 - 2 * p - 1) / (tateC10_den p) ^ 10 := by
  have hden10 : (tateC10_den p) ^ 10 ≠ 0 := pow_ne_zero 10 hden
  have hnum := tateC10_delta_num p hden
  rw [← hnum]
  field_simp [hden10]
```

The last `field_simp` is safe: the only denominator is literally `(tateC10_den p)^10`, and `hden10` matches it exactly.

## Why this avoids the inverse-term problem

The bad proof makes `field_simp` normalize the expanded denominator.  It sees expressions such as

```lean
(t ^ 2 - 3*t + 1)⁻¹
```

and later the ring normalizer sees the same polynomial as

```lean
(1 - t*3 + t^2)⁻¹
```

which is not syntactically tied to `hden` anymore.

The robust proof never clears denominators after expanding `tateC10_den p`.  It first rewrites

```lean
D = tateC10_den p,
B = p^3*(p-1)*(2*p-1),
C = -p*(p-1)*(2*p-1),
```

proves denominator cancellation for `B/D^2` and `C/D`, and only then unfolds `D,B,C` in a denominator-free polynomial goal.  The final `ring` goals are polynomial, not rational-function normalization goals.
