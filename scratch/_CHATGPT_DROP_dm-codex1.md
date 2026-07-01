# Q3009 (dm-codex1): Lean-friendly C10 Tate discriminant factorization

Target file: `FLT/Assumptions/MazurProof/KubertBridgeN10.lean`.

I could not fetch that exact file through the connector path, but the algebra below only uses the definitions stated in the prompt.  The proof strategy should be independent of surrounding project code.  The only local-name uncertainty is the exact namespace/name of the Mathlib Weierstrass auxiliary invariants (`b₂`, `b₄`, `b₆`, `b₈`, `Δ`).  I use the names from the prompt.

## Main recommendation

Do **not** prove the full factorization by expanding

```lean
(tateW (tateC10_b p) (tateC10_c p)).Δ
```

after substituting `b(p), c(p)`.  First prove the compact denominator-free Tate-normal-form discriminant formula

```text
Δ(tateW b c) = b^3 * (16*b^2 + (1 - 20*c - 8*c^2)*b + c*(c-1)^3).
```

Then substitute the C10 `b(p), c(p)` through two small numerator lemmas:

```text
den^6 * b(p)^3 = p^9*(p-1)^3*(2p-1)^3,

den^4 * core(b(p),c(p))
  = p*(p-1)^7*(2p-1)^2*(4p^2 - 2p - 1).
```

Finally combine them by `ring`:

```text
den^10 * Δ =
  p^10*(p-1)^10*(2p-1)^5*(4p^2 - 2p - 1).
```

Only after that divide by `den^10`.  This keeps `field_simp` out of the huge expression.

## Suggested Lean code

If this is inserted directly into `KubertBridgeN10.lean`, omit the imports.  If testing in a scratch Lean file, use imports like:

```lean
import FLT.Assumptions.MazurProof.KubertBridgeN10
import FLT.Assumptions.MazurProof.KubertTateCommon
```

### 1. Name the compact core

```lean
/-- The compact residual factor in the discriminant of the Tate normal form
`y^2 + (1-c)xy - b y = x^3 - b x^2`. -/
def tateWDeltaCore (b c : ℚ) : ℚ :=
  16 * b ^ 2 + (1 - 20 * c - 8 * c ^ 2) * b + c * (c - 1) ^ 3
```

### 2. Prove the arbitrary `b,c` formula first

This is the high-value lemma.  It contains no divisions, so `ring` should close it.

```lean
theorem tateW_delta_factored (b c : ℚ) :
    (tateW b c).Δ = b ^ 3 * tateWDeltaCore b c := by
  simp [tateW, tateWDeltaCore,
    WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring
```

If the `simp` unfolds too much or misses the local notation, prove the same fact from the four invariants:

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

Use whichever variant matches the local projection notation.

### 3. Small numerator lemma for `b(p)^3`

```lean
theorem tateC10_b_cube_num
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateC10_den p) ^ 6 * (tateC10_b p) ^ 3 =
      p ^ 9 * (p - 1) ^ 3 * (2 * p - 1) ^ 3 := by
  dsimp [tateC10_b, tateC10_den] at *
  field_simp [hden]
  ring
```

This should stay small because it only sees one rational function.

### 4. Small numerator lemma for the residual core

```lean
theorem tateC10_deltaCore_num
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateC10_den p) ^ 4 *
        tateWDeltaCore (tateC10_b p) (tateC10_c p) =
      p * (p - 1) ^ 7 * (2 * p - 1) ^ 2 *
        (4 * p ^ 2 - 2 * p - 1) := by
  dsimp [tateWDeltaCore, tateC10_b, tateC10_c, tateC10_den] at *
  field_simp [hden]
  ring
```

This is the only moderately large algebra step, but it is far smaller than the full discriminant.  If it is still slow, split it once more by naming the numerator of the core:

```lean
def tateC10_deltaCoreNum (p : ℚ) : ℚ :=
  p * (p - 1) ^ 7 * (2 * p - 1) ^ 2 *
    (4 * p ^ 2 - 2 * p - 1)

theorem tateC10_deltaCore_num'
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateC10_den p) ^ 4 *
        tateWDeltaCore (tateC10_b p) (tateC10_c p) =
      tateC10_deltaCoreNum p := by
  dsimp [tateC10_deltaCoreNum,
    tateWDeltaCore, tateC10_b, tateC10_c, tateC10_den] at *
  field_simp [hden]
  ring
```

### 5. Prove the multiplied/numerator discriminant identity

This is the most Lean-friendly theorem to use downstream.  It has no division on the right.

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
```

This theorem is often enough for zero/nonzero arguments.  For example, to show `p = 1/2` forces zero, it is better to use either `tateW_delta_factored` and `tateC10_b (1/2)=0`, or this numerator theorem plus `den(1/2)≠0`; no full rational-function factorization is needed.

### 6. Derive the divided factorization only at the end

```lean
theorem tateC10_delta_factor
    (p : ℚ) (hden : tateC10_den p ≠ 0) :
    (tateW (tateC10_b p) (tateC10_c p)).Δ =
      p ^ 10 * (p - 1) ^ 10 * (2 * p - 1) ^ 5 *
        (4 * p ^ 2 - 2 * p - 1) / (tateC10_den p) ^ 10 := by
  have hden10 : (tateC10_den p) ^ 10 ≠ 0 := pow_ne_zero 10 hden
  have hnum := tateC10_delta_num p hden
  calc
    (tateW (tateC10_b p) (tateC10_c p)).Δ
        = ((tateC10_den p) ^ 10 *
            (tateW (tateC10_b p) (tateC10_c p)).Δ) /
            (tateC10_den p) ^ 10 := by
            field_simp [hden10]
            ring
    _ = p ^ 10 * (p - 1) ^ 10 * (2 * p - 1) ^ 5 *
        (4 * p ^ 2 - 2 * p - 1) / (tateC10_den p) ^ 10 := by
          rw [hnum]
```

This last proof uses `field_simp` only on the trivial identity `x = den^10*x/den^10`, so it should not explode.

## Very small direct proof for `p = 1/2`

If all you need at some point is the pole exclusion, do this rather than using the full theorem:

```lean
theorem tateC10_delta_half_zero :
    (tateW (tateC10_b ((1 : ℚ) / 2))
           (tateC10_c ((1 : ℚ) / 2))).Δ = 0 := by
  rw [tateW_delta_factored]
  have hb : tateC10_b ((1 : ℚ) / 2) = 0 := by
    norm_num [tateC10_b, tateC10_den]
  simp [hb]
```

The `simp [hb]` closes because the arbitrary formula has a factor `b^3`.

## Sympy verification script

This verifies both the arbitrary `b,c` formula and the two numerator identities.

```python
import sympy as sp

b, c, p = sp.symbols('b c p')

# Tate normal form: y^2 + (1-c)xy - b y = x^3 - b x^2
a1 = 1 - c
a2 = -b
a3 = -b
a4 = 0
a6 = 0

b2 = a1**2 + 4*a2
b4 = a1*a3 + 2*a4
b6 = a3**2 + 4*a6
b8 = a1**2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3**2 - a4**2
Delta = -b2**2*b8 - 8*b4**3 - 27*b6**2 + 9*b2*b4*b6
core = 16*b**2 + (1 - 20*c - 8*c**2)*b + c*(c - 1)**3

assert sp.factor(Delta - b**3*core) == 0
print('Delta(tateW b c) =', sp.factor(Delta))

D = p**2 - 3*p + 1
bp = p**3*(p - 1)*(2*p - 1)/D**2
cp = -p*(p - 1)*(2*p - 1)/D
K = 4*p**2 - 2*p - 1

corep = core.subs({b: bp, c: cp})
assert sp.factor(D**6 * bp**3 - p**9*(p - 1)**3*(2*p - 1)**3) == 0
assert sp.factor(D**4 * corep - p*(p - 1)**7*(2*p - 1)**2*K) == 0

Deltap = Delta.subs({b: bp, c: cp})
assert sp.factor(D**10 * Deltap - p**10*(p - 1)**10*(2*p - 1)**5*K) == 0
assert sp.factor(Deltap - p**10*(p - 1)**10*(2*p - 1)**5*K/D**10) == 0
print('C10 factorization verified')
```

## If one lemma still times out

If `tateC10_deltaCore_num` is still slow in Lean, split the core numerator by common subexpressions rather than by expanding `Δ`.  For example:

```lean
def tateC10_A (p : ℚ) : ℚ := p * (p - 1) * (2 * p - 1)
def tateC10_Bnum (p : ℚ) : ℚ := p ^ 3 * (p - 1) * (2 * p - 1)
def tateC10_Cnum (p : ℚ) : ℚ := - tateC10_A p
```

Then prove:

```lean
theorem tateC10_b_eq_Bnum_div (p : ℚ) :
    tateC10_b p = tateC10_Bnum p / (tateC10_den p) ^ 2 := by
  simp [tateC10_b, tateC10_Bnum]

theorem tateC10_c_eq_Cnum_div (p : ℚ) :
    tateC10_c p = tateC10_Cnum p / tateC10_den p := by
  simp [tateC10_c, tateC10_Cnum, tateC10_A]
```

and run `field_simp` after rewriting only these two equalities.  In practice, however, the two numerator lemmas above should already be much smaller than the naive full-discriminant proof.
