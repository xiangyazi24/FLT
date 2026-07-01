# Q3008 (dm-codex1): corrected C10 Tate-parameter `p` to short-family `T`

Assumed local imports for the snippets below:

```lean
import FLT.Assumptions.MazurProof.KubertBridgeN10
import FLT.Assumptions.MazurProof.KubertTateCommon
```

Lean-name uncertainty: I am using the names from the prompt and the previous N10 scratch drop: `tateC10_den`, `tateC10_b`, `tateC10_c`, `tateW`, `shortW`, `A10`, `B10`, and `Delta10`.  The exact local name of the variable-change discriminant lemma may differ; I give both the direct factor route and the variable-change route.

## Executive answer

For a Tate-row parameter `p`, the corrected short-family parameter is

```lean
def tateC10_pToShortParam (p : ℚ) : ℚ :=
  1 / (1 - 2*p)
```

The extra fact needed for the parameter change is

```lean
1 - 2*p ≠ 0
```

Equivalently, `2*p - 1 ≠ 0`.  This is **not** implied by `tateC10_den p ≠ 0` alone.  It **is** implied by Tate discriminant nonzero, provided you have the C10 Tate discriminant factorization.

A clean final interface should not mention the false same-parameter statement.  It should output `T = 1/(1-2*p)` and prove/assume a corrected variable change

```lean
C • tateW (tateC10_b p) (tateC10_c p) =
  shortW (A10 (tateC10_pToShortParam p))
         (B10 (tateC10_pToShortParam p))
```

with `C.u ≠ 0`.

## 1. `1 - 2*p ≠ 0`: false from `hden` alone, true from `hDelta`

Assume the local denominator is

```lean
-- already present locally, included here only for readability
-- def tateC10_den (p : ℚ) : ℚ := p^2 - 3*p + 1
```

Then `hden` alone does not exclude `p = 1/2`:

```lean
example :
    tateC10_den ((1 : ℚ) / 2) ≠ 0 ∧
    1 - 2 * ((1 : ℚ) / 2) = 0 := by
  norm_num [tateC10_den]
```

So the theorem

```lean
theorem one_sub_two_mul_p_ne_zero
    {p : ℚ} (hden : tateC10_den p ≠ 0) :
    1 - 2*p ≠ 0
```

is false.

The correct theorem uses Tate discriminant nonzero.  First add/prove the factorization:

```lean
theorem tateC10_delta_factor
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateW (tateC10_b p) (tateC10_c p)).Δ =
      p^10 * (p - 1)^10 * (2*p - 1)^5 *
        (4*p^2 - 2*p - 1) / (tateC10_den p)^10 := by
  -- Expand the generalized Weierstrass discriminant of
  --   y^2 + (1-c)xy - b y = x^3 - b x^2
  -- with
  --   b = p^3*(p-1)*(2*p-1)/(tateC10_den p)^2
  --   c = -p*(p-1)*(2*p-1)/(tateC10_den p)
  dsimp [tateW, tateC10_b, tateC10_c, tateC10_den]
  field_simp [hden]
  ring
```

Then derive the parameter denominator from `hDelta`:

```lean
theorem one_sub_two_mul_p_ne_zero_of_tateC10_delta_ne_zero
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hDelta : (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    1 - 2*p ≠ 0 := by
  intro hbad
  have h2 : 2*p - 1 = 0 := by
    linarith
  have hDz : (tateW (tateC10_b p) (tateC10_c p)).Δ = 0 := by
    rw [tateC10_delta_factor p hden]
    simp [h2]
  exact hDelta hDz
```

If you do not want to formalize `tateC10_delta_factor` immediately, the honest temporary assumption is exactly

```lean
(hpT : 1 - 2*p ≠ 0)
```

not something weaker involving only `hden`.

## 2. Inverse parameter identity: `T = 1/(1-2*p)` gives `(T-1)/(2*T)=p`

Use this helper definition:

```lean
def tateC10_pToShortParam (p : ℚ) : ℚ :=
  1 / (1 - 2*p)
```

The inverse theorem needs only `1 - 2*p ≠ 0`:

```lean
theorem T_of_p_shortToTateParam
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    let T : ℚ := tateC10_pToShortParam p
    (T - 1) / (2*T) = p := by
  dsimp [tateC10_pToShortParam]
  have hT : (1 / (1 - 2*p) : ℚ) ≠ 0 := one_div_ne_zero hpT
  have h2T : (2 * (1 / (1 - 2*p)) : ℚ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hT
  field_simp [hpT, hT, h2T]
  ring
```

If the file already has

```lean
def tateC10_shortToTateParam (T : ℚ) : ℚ :=
  (T - 1) / (2*T)
```

then the preferred theorem is:

```lean
theorem tateC10_shortToTateParam_pToShortParam
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    tateC10_shortToTateParam (tateC10_pToShortParam p) = p := by
  dsimp [tateC10_shortToTateParam, tateC10_pToShortParam]
  have hT : (1 / (1 - 2*p) : ℚ) ≠ 0 := one_div_ne_zero hpT
  have h2T : (2 * (1 / (1 - 2*p)) : ℚ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hT
  field_simp [hpT, hT, h2T]
  ring
```

Useful derived facts:

```lean
theorem tateC10_pToShortParam_ne_zero
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    tateC10_pToShortParam p ≠ 0 := by
  dsimp [tateC10_pToShortParam]
  exact one_div_ne_zero hpT

theorem two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    2*p - 1 ≠ 0 := by
  intro h
  apply hpT
  linarith
```

## 3. Proving `Delta10 T ≠ 0`

There are two Lean-friendly routes.

### Route A: use variable-change discriminant transport

Define the corrected variable change in `p`-coordinates:

```lean
noncomputable def tateC10_pToShortVC (p : ℚ) :
    WeierstrassCurve.VariableChange ℚ :=
  let b : ℚ := tateC10_b p
  let c : ℚ := tateC10_c p
  let r0 : ℚ := -p^3 * (p - 1) / tateC10_den p
  { u := (2*p - 1)^3 / (8 * tateC10_den p)
    r := r0
    s := (c - 1) / 2
    t := (b - r0 * (1 - c)) / 2 }
```

If your local `VariableChange` field is named `tau`/`t₁` instead of `t`, only rename that final field.

The `u`-nonzero proof needs `hden` and `hpT`:

```lean
theorem tateC10_pToShortVC_u_ne_zero
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2*p ≠ 0) :
    (tateC10_pToShortVC p).u ≠ 0 := by
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  dsimp [tateC10_pToShortVC]
  exact div_ne_zero
    (pow_ne_zero 3 h2)
    (mul_ne_zero (by norm_num) hden)
```

The corrected coefficient theorem is:

```lean
theorem tateC10_p_to_shortW
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2*p ≠ 0) :
    tateC10_pToShortVC p •
        tateW (tateC10_b p) (tateC10_c p) =
      shortW (A10 (tateC10_pToShortParam p))
             (B10 (tateC10_pToShortParam p)) := by
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  ext <;>
    dsimp [tateC10_pToShortVC, tateC10_pToShortParam,
      tateC10_b, tateC10_c, tateC10_den,
      tateW, shortW, A10, B10, F10] <;>
    field_simp [hden, hpT, h2] <;>
    ring
```

Then `Delta10 T ≠ 0` follows from the local discriminant-transport lemma:

```lean
theorem Delta10_pToShortParam_ne_zero_of_tate_delta
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hDelta : (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    Delta10 (tateC10_pToShortParam p) ≠ 0 := by
  have hpT : 1 - 2*p ≠ 0 :=
    one_sub_two_mul_p_ne_zero_of_tateC10_delta_ne_zero hden hDelta
  let C := tateC10_pToShortVC p
  have hCu : C.u ≠ 0 := by
    simpa [C] using tateC10_pToShortVC_u_ne_zero hden hpT
  have hCurve :
      C • tateW (tateC10_b p) (tateC10_c p) =
        shortW (A10 (tateC10_pToShortParam p))
               (B10 (tateC10_pToShortParam p)) := by
    simpa [C] using tateC10_p_to_shortW hden hpT
  have hShortDelta :
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).Δ ≠ 0 := by
    -- Replace this with the exact local lemma name/signature.
    -- It should use hCu, hDelta, and hCurve.
    exact discriminant_ne_zero_of_variableChange_eq
      (C := C) hCu hDelta hCurve
  have hDeltaEq :
      (shortW (A10 (tateC10_pToShortParam p))
              (B10 (tateC10_pToShortParam p))).Δ =
        Delta10 (tateC10_pToShortParam p) := by
    dsimp [shortW, A10, B10, F10, Delta10]
    ring
  simpa [hDeltaEq] using hShortDelta
```

The only uncertain identifier above is `discriminant_ne_zero_of_variableChange_eq`; in the local files it may have the equality reversed or may package `hCu` differently.

### Route B: use direct discriminant identities

This route avoids relying on the variable-change discriminant API.

For `T = 1/(1-2*p)`, the short discriminant factors transform as follows:

```text
T^2 - 1       = -4*p*(p - 1)/(2*p - 1)^2
T^2 - 4*T - 1 = -4*(p^2 - 3*p + 1)/(2*p - 1)^2
T^2 + T - 1   = -(4*p^2 - 2*p - 1)/(2*p - 1)^2
```

Lean statements:

```lean
theorem pToShort_sq_sub_one
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    (tateC10_pToShortParam p)^2 - 1 =
      -4*p*(p - 1)/(2*p - 1)^2 := by
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  dsimp [tateC10_pToShortParam]
  field_simp [hpT, h2]
  ring

theorem pToShort_shortQ
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    (tateC10_pToShortParam p)^2 - 4*(tateC10_pToShortParam p) - 1 =
      -4*tateC10_den p/(2*p - 1)^2 := by
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  dsimp [tateC10_pToShortParam, tateC10_den]
  field_simp [hpT, h2]
  ring

theorem pToShort_phi
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    (tateC10_pToShortParam p)^2 + (tateC10_pToShortParam p) - 1 =
      -(4*p^2 - 2*p - 1)/(2*p - 1)^2 := by
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  dsimp [tateC10_pToShortParam]
  field_simp [hpT, h2]
  ring
```

Assuming the current `Delta10` factorization is

```text
Delta10 T = 4096*T^5*(T^2 + T - 1)*(T^2 - 1)^10*(T^2 - 4*T - 1)^2,
```

the exact substitution identity is

```lean
theorem Delta10_pToShortParam_factor
    {p : ℚ} (hpT : 1 - 2*p ≠ 0) :
    Delta10 (tateC10_pToShortParam p) =
      (2 : ℚ)^36 * p^10 * (p - 1)^10 *
        (tateC10_den p)^2 * (4*p^2 - 2*p - 1) /
        (2*p - 1)^31 := by
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  dsimp [Delta10, tateC10_pToShortParam, tateC10_den]
  field_simp [hpT, h2]
  ring
```

Combining this with the Tate factorization gives the cleaner scaling identity

```lean
theorem Delta10_pToShortParam_eq_scaled_tate_delta
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2*p ≠ 0) :
    Delta10 (tateC10_pToShortParam p) =
      ((8 * tateC10_den p) / (2*p - 1)^3)^12 *
        (tateW (tateC10_b p) (tateC10_c p)).Δ := by
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  rw [Delta10_pToShortParam_factor hpT,
      tateC10_delta_factor p hden]
  field_simp [hden, h2]
  ring
```

Then nonzero is immediate:

```lean
theorem Delta10_pToShortParam_ne_zero_of_tate_delta_direct
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hDelta : (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    Delta10 (tateC10_pToShortParam p) ≠ 0 := by
  have hpT : 1 - 2*p ≠ 0 :=
    one_sub_two_mul_p_ne_zero_of_tateC10_delta_ne_zero hden hDelta
  have h2 : 2*p - 1 ≠ 0 :=
    two_mul_p_sub_one_ne_zero_of_one_sub_two_mul_ne_zero hpT
  rw [Delta10_pToShortParam_eq_scaled_tate_delta hden hpT]
  exact mul_ne_zero
    (pow_ne_zero 12
      (div_ne_zero
        (mul_ne_zero (by norm_num) hden)
        (pow_ne_zero 3 h2)))
    hDelta
```

## 4. Factor correspondence

Let

```text
D(p) = tateC10_den p = p^2 - 3*p + 1,
K(p) = 4*p^2 - 2*p - 1,
T = 1/(1-2*p).
```

The C10 Tate discriminant factor is

```text
Δ_Tate(p) = p^10*(p-1)^10*(2p-1)^5*K(p)/D(p)^10.
```

The short discriminant factor is

```text
Delta10(T) = 4096*T^5*(T^2+T-1)*(T^2-1)^10*(T^2-4*T-1)^2.
```

Under `T = 1/(1-2*p)`:

| short-family factor | Tate-parameter expression | meaning |
| --- | --- | --- |
| `T` | `1/(1-2*p)` | never zero for finite valid `p`; `T=0` is the inverse map's pole, not a finite Tate parameter |
| `T^2 - 1` | `-4*p*(p-1)/(2p-1)^2` | zeros `p=0` and `p=1`; these are Tate discriminant zeros |
| `T^2 - 4*T - 1` | `-4*D(p)/(2p-1)^2` | zero exactly when `tateC10_den p=0`; this is excluded by `hden` |
| `T^2 + T - 1` | `-K(p)/(2p-1)^2` | the remaining Tate discriminant factor `K(p)=4p^2-2p-1` |
| parameter pole | `2p-1=0`, i.e. `p=1/2` | `T` undefined/infinite; also a Tate discriminant zero via `(2p-1)^5` |

So, from `hden` and `hDelta`, you get:

```text
p ≠ 0, p ≠ 1, p ≠ 1/2, K(p) ≠ 0, D(p) ≠ 0.
```

For Lean, you do not need to prove all of those separately if you use the scaled discriminant identity above.

## 5. Minimal honest residual interface

The current projective-normal-form residual should be replaced by a corrected Tate-to-short residual using `T = 1/(1-2*p)`.  The minimal useful single residual is:

```lean
theorem tateC10_corrected_tate_to_short_residual
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hDelta : (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    let T : ℚ := tateC10_pToShortParam p
    Delta10 T ≠ 0 ∧
      ∃ C : WeierstrassCurve.VariableChange ℚ,
        C.u ≠ 0 ∧
        C • tateW (tateC10_b p) (tateC10_c p) =
          shortW (A10 T) (B10 T) := by
  intro T
  have hpT : 1 - 2*p ≠ 0 :=
    one_sub_two_mul_p_ne_zero_of_tateC10_delta_ne_zero hden hDelta
  refine ⟨?_, ⟨tateC10_pToShortVC p, ?_, ?_⟩⟩
  · simpa [T] using Delta10_pToShortParam_ne_zero_of_tate_delta_direct hden hDelta
  · simpa using tateC10_pToShortVC_u_ne_zero hden hpT
  · simpa [T] using tateC10_p_to_shortW hden hpT
```

If you want the residual to be smaller and easier to discharge later, split it into the two algebraic pieces:

```lean
theorem tateC10_p_to_shortW_residual
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hpT : 1 - 2*p ≠ 0) :
    tateC10_pToShortVC p •
        tateW (tateC10_b p) (tateC10_c p) =
      shortW (A10 (tateC10_pToShortParam p))
             (B10 (tateC10_pToShortParam p))

 theorem Delta10_pToShortParam_ne_zero_residual
    {p : ℚ}
    (hden : tateC10_den p ≠ 0)
    (hDelta : (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0) :
    Delta10 (tateC10_pToShortParam p) ≠ 0
```

Then the checked upstream theorem

```lean
tateC10_param_of_origin_order10 :
  let p := tateC10_tInv b c
  den(p) ≠ 0 ∧ b = tateC10_b p ∧ c = tateC10_c p
```

can be followed by:

1. set `p := tateC10_tInv b c`,
2. use the reconstructed `hden`, `b = ...`, `c = ...`,
3. transport the original Tate discriminant hypothesis to `hDelta : (tateW (tateC10_b p) (tateC10_c p)).Δ ≠ 0`,
4. define `T := tateC10_pToShortParam p`,
5. apply the corrected residual above.

No theorem should state or assume that the same parameter `p`/`t` gives `shortW (A10 p) (B10 p)`.  The only honest short-family parameter obtained from the Tate row is `T = 1/(1-2*p)`.
