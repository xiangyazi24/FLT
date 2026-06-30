# Q2669 (dm-codex1): positive coprime square-factor lemmas

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target Lean area: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`

Below is the Lean code I would paste near the quartic/Eisenstein descent helpers.  The key pinned-Mathlib facts are `Int.sq_of_isCoprime` / `Int.sq_of_gcd_eq_one`; they return the signed branch `x = a^2 ∨ x = -a^2`, and positivity kills the negative branch.

I did not run Lean locally in this connector-only path, but the theorem names/signatures below were checked against the pinned Mathlib source in `lake-manifest.json` (`mathlib` rev `96fd0fff3b8837985ae21dd02e712cb5df72ec05`).

```lean
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Algebra.Order.Ring.Abs

namespace MazurProof.RationalPointsN12

#check Int.sq_of_isCoprime
#check Int.sq_of_gcd_eq_one
#check Int.Prime.dvd_pow'
#check Nat.prime_two
#check sq_abs
#check sq_nonneg

/-- Positive version of `Int.sq_of_isCoprime` for a product which is a square. -/
def PosSqOfCoprimeMulSqStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x → 0 < y → IsCoprime x y → z ^ 2 = x * y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2

/-- Usable theorem form of `PosSqOfCoprimeMulSqStatement`. -/
theorem posSq_of_coprime_mul_sq
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y) (hxy : IsCoprime x y)
    (hz : z ^ 2 = x * y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2 := by
  have hmul : x * y = z ^ 2 := hz.symm
  obtain ⟨a0, hx_sq | hx_neg_sq⟩ := Int.sq_of_isCoprime hxy hmul
  · have hmul_yx : y * x = z ^ 2 := by
      simpa [mul_comm] using hmul
    obtain ⟨b0, hy_sq | hy_neg_sq⟩ := Int.sq_of_isCoprime hxy.symm hmul_yx
    · have ha0_ne : a0 ≠ 0 := by
        intro ha0
        have hx0 : x = 0 := by
          simpa [ha0] using hx_sq
        linarith
      have hb0_ne : b0 ≠ 0 := by
        intro hb0
        have hy0 : y = 0 := by
          simpa [hb0] using hy_sq
        linarith
      refine ⟨|a0|, |b0|, abs_pos.mpr ha0_ne, abs_pos.mpr hb0_ne, ?_, ?_⟩
      · simpa [hx_sq, sq_abs]
      · simpa [hy_sq, sq_abs]
    · exfalso
      have hyneg : 0 < -(b0 ^ 2) := by
        simpa [hy_neg_sq] using hy
      nlinarith [sq_nonneg b0]
  · exfalso
    have hxneg : 0 < -(a0 ^ 2) := by
      simpa [hx_neg_sq] using hx
    nlinarith [sq_nonneg a0]

theorem posSqOfCoprimeMulSqStatement_checked : PosSqOfCoprimeMulSqStatement := by
  intro x y z hx hy hxy hz
  exact posSq_of_coprime_mul_sq hx hy hxy hz

/-- The corresponding `2`-factor version.

If `x = 2u`, `y = 2v`, `gcd(u,v)=1`, and `xy` is a square, then `u` and `v`
are positive squares; equivalently `x = 2a^2` and `y = 2b^2`.
-/
def PosSqOfCoprimeMulSqTwoFactorStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x → 0 < y → (2 : ℤ) ∣ x → (2 : ℤ) ∣ y →
    IsCoprime (x / 2) (y / 2) → z ^ 2 = x * y →
      ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2 * a ^ 2 ∧ y = 2 * b ^ 2

/-- Usable theorem form of the `2`-factor square extraction lemma. -/
theorem posSq_of_coprime_mul_sq_twoFactor
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y)
    (hx2 : (2 : ℤ) ∣ x) (hy2 : (2 : ℤ) ∣ y)
    (hxy : IsCoprime (x / 2) (y / 2))
    (hz : z ^ 2 = x * y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2 * a ^ 2 ∧ y = 2 * b ^ 2 := by
  rcases hx2 with ⟨u, rfl⟩
  rcases hy2 with ⟨v, rfl⟩
  have hu : 0 < u := by
    nlinarith
  have hv : 0 < v := by
    nlinarith
  have huv_coprime : IsCoprime u v := by
    simpa using hxy
  have hz2_dvd : (2 : ℤ) ∣ z ^ 2 := by
    rw [hz]
    exact dvd_mul_of_dvd_left (dvd_mul_right (2 : ℤ) u) (2 * v)
  have hz_dvd : (2 : ℤ) ∣ z :=
    Int.Prime.dvd_pow' (p := 2) (n := z) (k := 2) Nat.prime_two hz2_dvd
  rcases hz_dvd with ⟨w, rfl⟩
  have huw : w ^ 2 = u * v := by
    nlinarith [hz]
  obtain ⟨a, b, ha, hb, hu_sq, hv_sq⟩ :=
    posSq_of_coprime_mul_sq hu hv huv_coprime huw
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rw [hu_sq]
  · rw [hv_sq]

theorem posSqOfCoprimeMulSqTwoFactorStatement_checked :
    PosSqOfCoprimeMulSqTwoFactorStatement := by
  intro x y z hx hy hx2 hy2 hxy hz
  exact posSq_of_coprime_mul_sq_twoFactor hx hy hx2 hy2 hxy hz

end MazurProof.RationalPointsN12
```

## If `simpa using hxy` in the `2`-factor lemma fails

The only fragile simplification is reducing `(2 * u) / 2` and `(2 * v) / 2` after destructing divisibility.  If the local simp set does not close it, replace the `huv_coprime` block by this slightly more explicit version:

```lean
  have htwo : (2 : ℤ) ≠ 0 := by norm_num
  have huv_coprime : IsCoprime u v := by
    simpa [Int.mul_ediv_cancel_left, htwo] using hxy
```

If the explicit rewrite is still finicky because the term is `2 * u / 2` rather than `(2 * u) / 2`, use:

```lean
  have huv_coprime : IsCoprime u v := by
    simpa [mul_comm, mul_left_comm, mul_assoc, Int.mul_ediv_cancel_left] using hxy
```

## If `Int.Prime.dvd_pow'` elaboration is finicky

Use this spelling:

```lean
  have hz_dvd : (2 : ℤ) ∣ z := by
    exact Int.Prime.dvd_pow' (p := 2) (n := z) (k := 2) Nat.prime_two hz2_dvd
```

or, if implicit argument order changes under imports:

```lean
  have hz_dvd : (2 : ℤ) ∣ z := by
    exact Int.Prime.dvd_pow' Nat.prime_two hz2_dvd
```

## Minimal grep targets

```bash
grep -R "theorem sq_of_isCoprime" .lake/packages/mathlib/Mathlib/RingTheory/Int/Basic.lean
grep -R "theorem sq_of_gcd_eq_one" .lake/packages/mathlib/Mathlib/RingTheory/Int/Basic.lean
grep -R "theorem Int.Prime.dvd_pow'" .lake/packages/mathlib/Mathlib/RingTheory/Int/Basic.lean
grep -R "lemma sq_abs" .lake/packages/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean
```
