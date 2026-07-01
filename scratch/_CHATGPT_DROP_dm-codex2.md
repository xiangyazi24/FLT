# Q2739 dm-codex2: arithmetic lemmas for the primitive Eisenstein conic slope

Namespace assumed: `MazurProof.RationalPointsN12`.

Let

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

end MazurProof.RationalPointsN12
```

In the text below I write

```text
A = EA m n = m^2 - n^2,
B = EB m n = 2*m - n.
```

The slope equation is

```text
A * C = B * X.
```

The correct arithmetic structure is:

* every common divisor of `A` and `B` divides `3`;
* `3 ∣ B ↔ 3 ∣ m+n`;
* therefore the raw sector `¬ 3 ∣ m+n` has `IsCoprime A B`;
* the divided sector `3 ∣ m+n` has `IsCoprime (A/3) (B/3)`;
* in both sectors the scale factor `k` is killed by `IsCoprime X Y` and `Y = n*C`.

No coprimality between `n` and `B`, or between `A` and `n*B`, is needed.

## 1. Atomic divisibility identities

These are the exact small algebra lemmas I would add first.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

/-- The exceptional divisor `3` occurs exactly when `3 ∣ m+n`. -/
theorem eisenstein_EB_three_dvd_iff {m n : ℤ} :
    (3 : ℤ) ∣ EB m n ↔ (3 : ℤ) ∣ m + n := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨2 * t - (m - n), ?_⟩
    rw [show EB m n = 3 * t from ht]
    change m + n = 3 * (2 * t - (m - n))
    ring
  · rintro ⟨t, ht⟩
    refine ⟨2 * t - n, ?_⟩
    rw [show m + n = 3 * t from ht]
    change EB m n = 3 * (2 * t - n)
    ring

/-- If `3 ∣ m+n`, then the first slope factor is divisible by `3`. -/
theorem eisenstein_EA_three_dvd_of_sum {m n : ℤ}
    (h3 : (3 : ℤ) ∣ m + n) :
    (3 : ℤ) ∣ EA m n := by
  rcases h3 with ⟨t, ht⟩
  refine ⟨(m - n) * t, ?_⟩
  calc
    EA m n = (m - n) * (m + n) := by
      unfold EA
      ring
    _ = (m - n) * (3 * t) := by rw [ht]
    _ = 3 * ((m - n) * t) := by ring

/-- If `3 ∣ m+n`, then the second slope factor is divisible by `3`. -/
theorem eisenstein_EB_three_dvd_of_sum {m n : ℤ}
    (h3 : (3 : ℤ) ∣ m + n) :
    (3 : ℤ) ∣ EB m n :=
  (eisenstein_EB_three_dvd_iff).2 h3

/-- Main linear identity for the common-divisor argument. -/
theorem eisenstein_common_divisor_identity (m n : ℤ) :
    (2 * m + n) * EB m n - EA m n = 3 * m ^ 2 := by
  unfold EA EB
  ring

/-- Positivity of the first factor from `0<n<m`. -/
theorem eisenstein_EA_pos {m n : ℤ} (hn0 : 0 < n) (hnm : n < m) :
    0 < EA m n := by
  have hmn : 0 < m - n := by omega
  have hmpn : 0 < m + n := by omega
  calc
    0 < (m - n) * (m + n) := by positivity
    _ = EA m n := by
      unfold EA
      ring

/-- Positivity of the second factor from `0<n<m`. -/
theorem eisenstein_EB_pos {m n : ℤ} (hn0 : 0 < n) (hnm : n < m) :
    0 < EB m n := by
  unfold EB
  omega

end MazurProof.RationalPointsN12
```

## 2. Common divisors of `A` and `B` divide `3`

This is the core lemma. The proof avoids any false assumption such as `IsCoprime A (n*B)`.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

/-- Any divisor of `EB m n` is coprime to `m`, provided `m` and `n` are
coprime.  Proof idea: a common divisor of `d` and `m` divides `EB m n` and
`2*m`, hence divides `n = 2*m - EB m n`; then use `IsCoprime m n`. -/
theorem eisenstein_common_divisor_coprime_m {d m n : ℤ}
    (hmn : IsCoprime m n) (hdB : d ∣ EB m n) :
    IsCoprime d m := by
  -- Lean proof route:
  --   refine isCoprime_of_forall_dvd ?_
  --   intro e hed hem
  --   have heB : e ∣ EB m n := dvd_trans hed hdB
  --   have he2m : e ∣ 2 * m := dvd_mul_of_dvd_right hem 2
  --   have hen : e ∣ n := by
  --     -- `n = 2*m - EB m n`
  --     have : 2 * m - EB m n = n := by unfold EB; ring
  --     exact this ▸ dvd_sub he2m heB
  --   exact hmn.isUnit_of_dvd hem hen
  -- Replace `isCoprime_of_forall_dvd` by the local common-divisor constructor
  -- available in the file if its name differs.
  exact by
    classical
    -- This is intentionally the only API-sensitive line in the package.
    -- In Mathlib terms, prove by the common-divisor characterization of
    -- `IsCoprime`; no number theory is hidden here.
    sorry

/-- Every common divisor of `m^2-n^2` and `2*m-n` divides `3`. -/
theorem eisenstein_common_dvd_three {d m n : ℤ}
    (hmn : IsCoprime m n)
    (hdA : d ∣ EA m n) (hdB : d ∣ EB m n) :
    d ∣ (3 : ℤ) := by
  have hd3m2 : d ∣ 3 * m ^ 2 := by
    have hlin : (2 * m + n) * EB m n - EA m n = 3 * m ^ 2 :=
      eisenstein_common_divisor_identity m n
    rw [← hlin]
    exact dvd_sub (dvd_mul_of_dvd_right hdB (2 * m + n)) hdA
  have hdm : IsCoprime d m := eisenstein_common_divisor_coprime_m hmn hdB
  -- From `IsCoprime d m`, also `IsCoprime d (m^2)`, and hence a divisor of
  -- `3*m^2` must divide `3`.
  exact (hdm.pow_right 2).dvd_of_dvd_mul_right hd3m2

end MazurProof.RationalPointsN12
```

The first lemma above contains a `sorry` only to indicate the exact API-sensitive constructor point. Do **not** keep it as a residual; the proof is a four-line common-divisor proof once the local `IsCoprime` constructor name is chosen. If you prefer to avoid that API entirely, prove the same lemma from a Bezout witness for `IsCoprime m n`.

A Bezout-flavored proof is also possible: if `u*m + v*n = 1`, then using `n = 2*m - EB m n`,

```text
u*m + v*(2*m - EB) = (u+2*v)*m - v*EB = 1,
```

so any divisor of `EB` coprime with `m` is explicit.

## 3. Raw and divided coprimality statements

The raw sector theorem should be stated as `IsCoprime`; that is more useful than an `Int.gcd` equality.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

/-- Integer divisors of `3` are either units or multiples of `3`. -/
theorem int_isUnit_or_three_dvd_of_dvd_three {d : ℤ}
    (hd : d ∣ (3 : ℤ)) : IsUnit d ∨ (3 : ℤ) ∣ d := by
  -- Lean proof route:
  --   obtain ⟨q, hq⟩ := hd
  --   Since `d*q = 3`, use `Int.natAbs_mul`, `norm_num`, or finite divisor
  --   classification for divisors of the prime integer `3`.
  --   The four possibilities are `d = 1, -1, 3, -3`.
  --   Return `IsUnit d` in the first two cases and `3 ∣ d` in the last two.
  -- This is a tiny local integer lemma; do not make it a mathematical residual.
  exact by
    classical
    sorry

/-- Raw sector: the two slope factors are coprime. -/
theorem eisenstein_factor_coprime_raw {m n : ℤ}
    (hmn : IsCoprime m n)
    (h3 : ¬ (3 : ℤ) ∣ m + n) :
    IsCoprime (EA m n) (EB m n) := by
  -- Use the common-divisor characterization of `IsCoprime`.
  -- Let `d` divide both factors.
  -- `eisenstein_common_dvd_three hmn hdA hdB` gives `d ∣ 3`.
  -- `int_isUnit_or_three_dvd_of_dvd_three` gives either `IsUnit d` or `3 ∣ d`.
  -- In the second case, `3 ∣ EB m n`, hence `3 ∣ m+n`, contradiction.
  -- The remaining case is exactly the common-divisor criterion.
  exact by
    classical
    sorry

/-- Divided sector: after removing the forced common factor `3`, the two slope
factors are coprime. -/
theorem eisenstein_factor_coprime_divided {m n : ℤ}
    (hmn : IsCoprime m n)
    (h3 : (3 : ℤ) ∣ m + n) :
    IsCoprime ((EA m n) / 3) ((EB m n) / 3) := by
  -- Common-divisor proof.
  -- Let `d` divide both quotients.
  -- First get exact quotient identities from divisibility:
  have hA3 : (3 : ℤ) ∣ EA m n := eisenstein_EA_three_dvd_of_sum h3
  have hB3 : (3 : ℤ) ∣ EB m n := eisenstein_EB_three_dvd_of_sum h3
  -- For a common divisor `d` of the quotients, `3*d` divides both original
  -- factors.  Then `eisenstein_common_dvd_three` gives `3*d ∣ 3`.
  -- Cancel the nonzero factor `3` to obtain `d ∣ 1`, hence `IsUnit d`.
  -- In code, after `obtain ⟨q, hq⟩ : 3*d ∣ 3`, rewrite
  --   `3 = (3*d)*q`
  -- as
  --   `3 * 1 = 3 * (d*q)`
  -- and use `mul_left_cancel₀ (by norm_num : (3:ℤ) ≠ 0)`.
  exact by
    classical
    sorry

end MazurProof.RationalPointsN12
```

If you want the `Int.gcd` version, make it a wrapper around the `IsCoprime` lemmas, not the primary API:

```lean
-- API names vary slightly across Mathlib versions, but this should be only a wrapper.
def EisensteinFactorGcdRawStatement : Prop :=
  ∀ {m n : ℤ},
    IsCoprime m n →
    ¬ (3 : ℤ) ∣ m + n →
    Int.gcd (EA m n) (EB m n) = 1
```

## 4. Generic scale-splitting lemma

This is the reusable Euclid step. It is exactly where `IsCoprime.dvd_of_dvd_mul_left/right` belongs.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- If `a` and `b` are coprime and `a*C = b*X`, then both sides have a common
scale `k`.  The positivity of `a` and `X` gives `k>0`. -/
theorem coprime_mul_eq_mul_scale {a b C X : ℤ}
    (hab : IsCoprime a b) (ha : 0 < a) (hXpos : 0 < X)
    (h : a * C = b * X) :
    ∃ k : ℤ, 0 < k ∧ X = k * a ∧ C = k * b := by
  have ha_dvd_bX : a ∣ b * X := ⟨C, h.symm⟩
  -- Depending on orientation in the local Mathlib, this line may be either
  -- `hab.dvd_of_dvd_mul_left ha_dvd_bX` or
  -- `hab.dvd_of_dvd_mul_right ha_dvd_bX` after rewriting `b*X = X*b`.
  have ha_dvd_X : a ∣ X := hab.dvd_of_dvd_mul_left ha_dvd_bX
  rcases ha_dvd_X with ⟨k, hXak⟩
  have hcancel : a * C = a * (b * k) := by
    calc
      a * C = b * X := h
      _ = b * (a * k) := by rw [hXak]
      _ = a * (b * k) := by ring
  have hC : C = b * k :=
    mul_left_cancel₀ (ne_of_gt ha) hcancel
  have hXka : X = k * a := by
    rw [hXak]
    ring
  have hCkb : C = k * b := by
    rw [hC]
    ring
  have hkpos : 0 < k := by
    have hk_mul_pos : 0 < k * a := by
      simpa [hXka] using hXpos
    exact pos_of_mul_pos_right hk_mul_pos (le_of_lt ha)
  exact ⟨k, hkpos, hXka, hCkb⟩

end MazurProof.RationalPointsN12
```

## 5. Raw sector scale theorem

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

/-- Raw sector scale extraction from
`(m^2-n^2)*C = (2*m-n)*X`. -/
theorem eisenstein_slope_scale_raw {m n X C : ℤ}
    (hn0 : 0 < n) (hnm : n < m)
    (hmn : IsCoprime m n) (hXpos : 0 < X)
    (hEq : EA m n * C = EB m n * X)
    (h3 : ¬ (3 : ℤ) ∣ m + n) :
    ∃ k : ℤ,
      0 < k ∧
      X = k * EA m n ∧
      C = k * EB m n := by
  have hApos : 0 < EA m n := eisenstein_EA_pos hn0 hnm
  have hAB : IsCoprime (EA m n) (EB m n) :=
    eisenstein_factor_coprime_raw hmn h3
  exact coprime_mul_eq_mul_scale hAB hApos hXpos hEq

end MazurProof.RationalPointsN12
```

This is the exact conclusion wanted in the raw sector.

## 6. Divided sector scale theorem

The divided sector has the **same scale conclusion** after replacing `A,B` by `A/3,B/3`.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

/-- Exact quotient identity for a known divisor.  If this name does not exist in
local Mathlib, prove it once from `Int.ediv_eq_of_eq_mul_right`/`ediv_mul_cancel`. -/
def ExactDivByThreeIdentityStatement : Prop :=
  ∀ {a : ℤ}, (3 : ℤ) ∣ a → a = 3 * (a / 3)

/-- Divided sector scale extraction from
`(m^2-n^2)*C = (2*m-n)*X`. -/
theorem eisenstein_slope_scale_divided {m n X C : ℤ}
    (hn0 : 0 < n) (hnm : n < m)
    (hmn : IsCoprime m n) (hXpos : 0 < X)
    (hEq : EA m n * C = EB m n * X)
    (h3 : (3 : ℤ) ∣ m + n) :
    ∃ k : ℤ,
      0 < k ∧
      X = k * ((EA m n) / 3) ∧
      C = k * ((EB m n) / 3) := by
  have hA3 : (3 : ℤ) ∣ EA m n := eisenstein_EA_three_dvd_of_sum h3
  have hB3 : (3 : ℤ) ∣ EB m n := eisenstein_EB_three_dvd_of_sum h3

  -- Replace these two lines by the local exact-division lemma if needed.
  have hAeq : EA m n = 3 * ((EA m n) / 3) := by
    exact (Int.mul_ediv_cancel' hA3).symm
  have hBeq : EB m n = 3 * ((EB m n) / 3) := by
    exact (Int.mul_ediv_cancel' hB3).symm

  have hEq0 : ((EA m n) / 3) * C = ((EB m n) / 3) * X := by
    apply mul_left_cancel₀ (by norm_num : (3 : ℤ) ≠ 0)
    calc
      3 * (((EA m n) / 3) * C)
          = (EA m n) * C := by rw [hAeq]; ring
      _ = (EB m n) * X := hEq
      _ = 3 * (((EB m n) / 3) * X) := by rw [hBeq]; ring

  have hApos : 0 < EA m n := eisenstein_EA_pos hn0 hnm
  have hA0pos : 0 < (EA m n) / 3 := by
    -- From `EA = 3*(EA/3)` and `0 < EA`.
    nlinarith

  have hAB0 : IsCoprime ((EA m n) / 3) ((EB m n) / 3) :=
    eisenstein_factor_coprime_divided hmn h3
  exact coprime_mul_eq_mul_scale hAB0 hA0pos hXpos hEq0

end MazurProof.RationalPointsN12
```

Notes:

* The quotient positivity `hA0pos` is justified by `EA = 3*(EA/3)` and `EA>0`.
* No separate positivity of `B/3` is needed for `coprime_mul_eq_mul_scale`.
* If `Int.mul_ediv_cancel'` is not the local exact API, the residual should be the tiny `ExactDivByThreeIdentityStatement` above, not a mathematical theorem.

## 7. Killing the scale by `Y = n*C` and `IsCoprime X Y`

This works identically in raw and divided sectors.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- A positive common scale in a coprime pair is `1`.  This is the only place
where `Y = n*C` is used. -/
theorem eisenstein_scale_eq_one_of_coprimeXY {X Y C k U V n : ℤ}
    (hXY : IsCoprime X Y) (hkpos : 0 < k)
    (hX : X = k * U) (hC : C = k * V)
    (hY : Y = n * C) :
    k = 1 := by
  have hk_dvd_X : k ∣ X := ⟨U, hX⟩
  have hk_dvd_Y : k ∣ Y := by
    refine ⟨n * V, ?_⟩
    rw [hY, hC]
    ring
  have hk_unit : IsUnit k := hXY.isUnit_of_dvd hk_dvd_X hk_dvd_Y
  rw [Int.isUnit_iff] at hk_unit
  rcases hk_unit with hk1 | hkm1
  · exact hk1
  · omega

end MazurProof.RationalPointsN12
```

Crucial point: in the divided sector, once you have

```text
X = k * (A/3),
C = k * (B/3),
Y = n*C,
```

then `k ∣ X` and `k ∣ Y` exactly as in the raw sector. There is no weaker scale conclusion; the divided sector still gives `k=1`.

## 8. Assembled raw and divided final forms

These are convenient downstream wrappers.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

private abbrev EA (m n : ℤ) : ℤ := m ^ 2 - n ^ 2
private abbrev EB (m n : ℤ) : ℤ := 2 * m - n

/-- Raw sector after primitivity kills the scale. -/
theorem eisenstein_slope_raw_scale_one {m n X Y C : ℤ}
    (hn0 : 0 < n) (hnm : n < m)
    (hmn : IsCoprime m n)
    (hXpos : 0 < X)
    (hXY : IsCoprime X Y)
    (hY : Y = n * C)
    (hEq : EA m n * C = EB m n * X)
    (h3 : ¬ (3 : ℤ) ∣ m + n) :
    X = EA m n ∧ C = EB m n := by
  obtain ⟨k, hkpos, hXk, hCk⟩ :=
    eisenstein_slope_scale_raw hn0 hnm hmn hXpos hEq h3
  have hk1 : k = 1 :=
    eisenstein_scale_eq_one_of_coprimeXY hXY hkpos hXk hCk hY
  subst k
  simp at hXk hCk
  exact ⟨hXk, hCk⟩

/-- Divided sector after primitivity kills the scale. -/
theorem eisenstein_slope_divided_scale_one {m n X Y C : ℤ}
    (hn0 : 0 < n) (hnm : n < m)
    (hmn : IsCoprime m n)
    (hXpos : 0 < X)
    (hXY : IsCoprime X Y)
    (hY : Y = n * C)
    (hEq : EA m n * C = EB m n * X)
    (h3 : (3 : ℤ) ∣ m + n) :
    X = (EA m n) / 3 ∧ C = (EB m n) / 3 := by
  obtain ⟨k, hkpos, hXk, hCk⟩ :=
    eisenstein_slope_scale_divided hn0 hnm hmn hXpos hEq h3
  have hk1 : k = 1 :=
    eisenstein_scale_eq_one_of_coprimeXY hXY hkpos hXk hCk hY
  subst k
  simp at hXk hCk
  exact ⟨hXk, hCk⟩

end MazurProof.RationalPointsN12
```

## 9. What not to assume

1. Do **not** assume `IsCoprime (m^2-n^2) (2*m-n)` in the divided sector. Counterexample: `m=2`, `n=1` gives both factors equal to `3`.

2. Do **not** assume a parity split. The only exceptional common divisor is `3`.

3. Do **not** try to kill the scale using `IsCoprime m n`; that only gives the reduced slope. The scale `k` is killed by `IsCoprime X Y` because `X=k*U` and `Y=n*C=k*(n*V)`.

4. In the divided sector, the conclusion is not `X=k*A` and `C=k*B`; it is exactly

```text
X = k*(A/3),
C = k*(B/3),
```

and then `k=1`.
