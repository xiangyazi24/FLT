# Q669 (dm2): coefficient `(3,0)` of `Projective.negAddY` at formal points

## Executive answer

Do **not** use `negAddY_eq'` for this coefficient computation.  That lemma is curve-equation dependent, while this is a pure polynomial-level truncation computation.  The right Lean shape is:

1. define `P := formalPointMv W 0`, `Q := formalPointMv W 1`;
2. unfold only `WeierstrassCurve.Projective.negAddY` and `formalPointMv`;
3. push `MvPowerSeries.coeff e30` through `+`, `-`, and `*`;
4. prove a local truncation lemma saying the degree-3 part is

```lean
(3 : R) • (X₀ ^ 2 * X₁) - (3 : R) • (X₀ * X₁ ^ 2) + Q 2 - P 2
```

5. finish with

```lean
coeff e30 (X₀ ^ 2 * X₁) = 0
coeff e30 (X₀ * X₁ ^ 2) = 0
coeff e30 (Q 2) = 0
coeff e30 (P 2) = 1
```

so the answer is `-1`.

The key point is that, for the target exponent

```lean
e30 = Finsupp.single (0 : Fin 2) 3
```

any factor containing a positive `X₁` exponent cannot contribute, and any `aᵢ` term has total degree at least `4` after substituting formal points.

---

## Lean proof skeleton

The following is the proof structure I would put in the file.  I wrote it to be practical rather than magical: the only local names you may need to adjust are the already-proved low-degree coefficient lemmas for `formalPointMv`/`formalW`.

```lean
import Mathlib

open scoped BigOperators
open MvPowerSeries

namespace WeierstrassCurve
namespace Projective

variable {R : Type*} [CommRing R]

local abbrev Mv2 : Type _ := MvPowerSeries (Fin 2) R

local abbrev X₀ : Mv2 := MvPowerSeries.X (0 : Fin 2)
local abbrev X₁ : Mv2 := MvPowerSeries.X (1 : Fin 2)

local abbrev e30 : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) 3

/-- Coefficient at `X₀^3`. -/
local notation "c30" P => MvPowerSeries.coeff e30 P
```

---

## Small coefficient helpers

These are the helpers that make the final proof readable.  The exact theorem names around `Finsupp.antidiagonal` differ a bit between Mathlib pins; if `Finsupp.mem_antidiagonal.mp hp` does not elaborate, search for `mem_antidiagonal` near `Finsupp.antidiagonal` and replace that one line.

```lean
private lemma coeff_e30_mul_X₁_right (A : Mv2) :
    c30 (A * X₁) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hp_sum : p.1 + p.2 = e30 := by
    simpa [e30] using (Finsupp.mem_antidiagonal.mp hp)
  have hp2_one_zero : p.2 (1 : Fin 2) = 0 := by
    have hcoord := congrArg (fun f : Fin 2 →₀ ℕ => f (1 : Fin 2)) hp_sum
    simpa [e30] using hcoord
  have hp2_ne : p.2 ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro h
    have : p.2 (1 : Fin 2) = 1 := by simp [h]
    omega
  simp [X₁, MvPowerSeries.coeff_X, hp2_ne]

private lemma coeff_e30_X₀_sq_mul_X₁ :
    c30 (X₀ ^ 2 * X₁) = 0 := by
  simpa [mul_assoc] using coeff_e30_mul_X₁_right (R := R) (X₀ ^ 2)

private lemma coeff_e30_X₀_mul_X₁_sq :
    c30 (X₀ * X₁ ^ 2) = 0 := by
  -- Commute one `X₁` to the far right and use the previous helper.
  have h := coeff_e30_mul_X₁_right (R := R) (X₀ * X₁)
  simpa [pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using h
```

For the formal point `z`-coordinates, use your existing formal-`W` coefficient facts.  The names below are placeholders for the facts that should follow from `formalW = X^3 * formalU` and `formalUCoeff W 0 = 1`:

```lean
-- The left point has z-coordinate `w₀`, whose first term is `X₀^3`.
private lemma formalPointMv_left_z_coeff_e30
    (W : WeierstrassCurve R) :
    c30 ((formalPointMv W (0 : Fin 2)) 2) = 1 := by
  -- Typically:
  --   simp [formalPointMv, formalW, formalU, formalUCoeff_eq,
  --     formalUCoeffBody, MvPowerSeries.coeff_mul, e30]
  -- or use your already-proved coefficient extraction lemma.
  simpa using formalW_coeff_self_cubic_mv (W := W) (i := (0 : Fin 2))

-- The right point has z-coordinate `w₁`, whose first term is `X₁^3`, so its
-- coefficient at `X₀^3` is zero.
private lemma formalPointMv_right_z_coeff_e30
    (W : WeierstrassCurve R) :
    c30 ((formalPointMv W (1 : Fin 2)) 2) = 0 := by
  -- Typically:
  --   simp [formalPointMv, formalW, formalU, MvPowerSeries.rename,
  --     MvPowerSeries.coeff_mul, e30]
  -- or use your already-proved coefficient extraction lemma.
  simpa using formalW_coeff_other_cubic_mv
    (W := W) (i := (1 : Fin 2)) (j := (0 : Fin 2)) (by decide)
```

If you do not have those two `formalW_*` lemmas yet, prove them once directly from the definition of `formalW`.  They are independent of `negAddY`.

---

## The useful truncation lemma

This is the workhorse.  It says that, after substitution of formal points, the coefficient at `(3,0)` only sees the four core terms.  Of those four, only `-P 2` contributes at `(3,0)`, but I keep all four in the statement because it mirrors the paper/CAS computation and makes the sign check transparent.

```lean
private lemma negAddY_formalPointMv_coeff_e30_low_part
    (W : WeierstrassCurve R) :
    let P := formalPointMv W (0 : Fin 2)
    let Q := formalPointMv W (1 : Fin 2)
    c30 ((W.toProjective).negAddY P Q)
      =
    c30 ((3 : R) • (X₀ ^ 2 * X₁)
        - (3 : R) • (X₀ * X₁ ^ 2)
        + Q 2
        - P 2) := by
  classical
  intro P Q

  -- This is the one controlled unfold of the 18-term polynomial.
  -- After this, never use `negAddY_eq'`; this is purely polynomial.
  simp only [WeierstrassCurve.Projective.negAddY]

  -- Substitute the formal point coordinates:
  --   P 0 = X₀, P 1 = -1, P 2 = w₀
  --   Q 0 = X₁, Q 1 = -1, Q 2 = w₁
  -- Keep `P 2` and `Q 2` opaque except for low-degree coefficient facts.
  simp only [P, Q, formalPointMv]

  -- Push `coeff e30` through the expanded ring expression.  In most Mathlib pins,
  -- `simp` has the additive coefficient lemmas tagged, but I list them to make the
  -- intended normalization clear.
  simp only [
    MvPowerSeries.coeff_add,
    MvPowerSeries.coeff_sub,
    MvPowerSeries.coeff_neg,
    MvPowerSeries.coeff_smul,
    smul_eq_mul
  ]

  -- At this point the goal is an equality in `R` whose summands are coefficients
  -- of the 18 expanded terms.  The following `simp` kills the irrelevant terms.
  -- Why it works:
  --   * terms containing an `X₁` factor cannot contribute to `X₀^3` unless no
  --     other nonconstant factor is present; this kills the first two core terms
  --     at the final stage and most mixed terms immediately;
  --   * every `aᵢ` term has total degree ≥ 4 after substitution;
  --   * every term containing `P 2` or `Q 2` plus any extra `X` or `z` factor has
  --     degree ≥ 4, because `P 2`/`Q 2` start in degree 3.
  --
  -- Replace the two `formalPointMv_*_low` names below by your local min-degree
  -- lemmas for `formalW` if they are named differently.
  simp [
    coeff_e30_X₀_sq_mul_X₁,
    coeff_e30_X₀_mul_X₁_sq,
    coeff_e30_mul_X₁_right,
    formalPointMv_left_z_coeff_e30,
    formalPointMv_right_z_coeff_e30,
    formalPointMv_left_z_coeff_lt_three,
    formalPointMv_right_z_coeff_lt_three,
    MvPowerSeries.coeff_mul,
    mul_assoc, mul_left_comm, mul_comm
  ]

  -- The remaining scalar identity is just the simplification of
  --   -3 * X₀^2 * X₁ * (-1)  ↦  +3 * X₀^2 * X₁
  --    3 * X₀ * X₁^2 * (-1) ↦  -3 * X₀ * X₁^2
  --   -(-1)^2 * (-1) * Q₂  ↦  +Q₂
  --    (-1) * (-1)^2 * P₂  ↦  -P₂
  ring
```

The two min-degree simp lemmas used above should have a shape like this:

```lean
-- Any coefficient of `wᵢ` below total degree 3 is zero.
-- A convenient version for the 18-term computation is to expose it as `[simp]`.
lemma formalPointMv_left_z_coeff_lt_three
    (W : WeierstrassCurve R) (d : Fin 2 →₀ ℕ)
    (hd : d.sum (fun _ n => n) < 3) :
    MvPowerSeries.coeff d ((formalPointMv W (0 : Fin 2)) 2) = 0 := by
  -- from `formalW = X^3 * formalU`
  sorry

lemma formalPointMv_right_z_coeff_lt_three
    (W : WeierstrassCurve R) (d : Fin 2 →₀ ℕ)
    (hd : d.sum (fun _ n => n) < 3) :
    MvPowerSeries.coeff d ((formalPointMv W (1 : Fin 2)) 2) = 0 := by
  -- same proof, after renaming the variable to coordinate `1`
  sorry
```

In the actual proof above, if Lean does not use these automatically from `simp`, instantiate them explicitly at the few exponents that occur in the convolution sums after `rw [MvPowerSeries.coeff_mul]`.

---

## Final theorem

Once the truncation lemma is in place, the target coefficient proof is short and robust.

```lean
theorem negAddY_formalPointMv_coeff_e30
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3)
      ((W.toProjective).negAddY
        (formalPointMv W (0 : Fin 2))
        (formalPointMv W (1 : Fin 2)))
      = (-1 : R) := by
  classical

  let P := formalPointMv W (0 : Fin 2)
  let Q := formalPointMv W (1 : Fin 2)

  have hlow := negAddY_formalPointMv_coeff_e30_low_part (R := R) W

  have hX₀X₀X₁ : c30 (X₀ ^ 2 * X₁ : Mv2) = 0 :=
    coeff_e30_X₀_sq_mul_X₁ (R := R)

  have hX₀X₁X₁ : c30 (X₀ * X₁ ^ 2 : Mv2) = 0 :=
    coeff_e30_X₀_mul_X₁_sq (R := R)

  have hQz : c30 (Q 2) = 0 := by
    simpa [Q] using formalPointMv_right_z_coeff_e30 (R := R) W

  have hPz : c30 (P 2) = 1 := by
    simpa [P] using formalPointMv_left_z_coeff_e30 (R := R) W

  change c30 ((W.toProjective).negAddY P Q) = (-1 : R)

  calc
    c30 ((W.toProjective).negAddY P Q)
        = c30 ((3 : R) • (X₀ ^ 2 * X₁)
            - (3 : R) • (X₀ * X₁ ^ 2)
            + Q 2
            - P 2) := by
              simpa [P, Q] using hlow
    _ = (3 : R) * c30 (X₀ ^ 2 * X₁)
          - (3 : R) * c30 (X₀ * X₁ ^ 2)
          + c30 (Q 2)
          - c30 (P 2) := by
              simp [MvPowerSeries.coeff_add, MvPowerSeries.coeff_sub,
                MvPowerSeries.coeff_smul, smul_eq_mul]
    _ = (-1 : R) := by
              simp [hX₀X₀X₁, hX₀X₁X₁, hQz, hPz]
```

---

## A more compact version after the helpers are tagged `[simp]`

After tagging the low-degree helper lemmas as `[simp]`, the final theorem can often be compressed to this:

```lean
theorem negAddY_formalPointMv_coeff_e30_short
    (W : WeierstrassCurve R) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 3)
      ((W.toProjective).negAddY
        (formalPointMv W (0 : Fin 2))
        (formalPointMv W (1 : Fin 2)))
      = (-1 : R) := by
  classical
  let P := formalPointMv W (0 : Fin 2)
  let Q := formalPointMv W (1 : Fin 2)
  change c30 ((W.toProjective).negAddY P Q) = (-1 : R)
  rw [negAddY_formalPointMv_coeff_e30_low_part (R := R) W]
  simp [
    P, Q,
    coeff_e30_X₀_sq_mul_X₁,
    coeff_e30_X₀_mul_X₁_sq,
    formalPointMv_left_z_coeff_e30,
    formalPointMv_right_z_coeff_e30,
    MvPowerSeries.coeff_add,
    MvPowerSeries.coeff_sub,
    MvPowerSeries.coeff_smul,
    smul_eq_mul
  ]
```

---

## Sign check

The four degree-3 terms after substituting `P[1] = Q[1] = -1` are

```text
-3*P0^2*Q0*Q1      =  3 X₀²X₁
 3*P0*Q0^2*P1      = -3 X₀X₁²
-P1^2*Q1*Q2        =  Q2 = w₁
 P1*Q1^2*P2        = -P2 = -w₀
```

At coefficient `(3,0)`, the first two mixed monomials are zero, `w₁` contributes zero, and `w₀` contributes one.  Hence the coefficient is `-1`.

end Projective
end WeierstrassCurve
```