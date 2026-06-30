# Q2669 (dm-codex1): positive coprime square-factor lemmas

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target Lean area: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`

Pinned facts checked in the repo manifest/mathlib source:

```lean
#check Int.sq_of_isCoprime
-- Int.sq_of_isCoprime {a b c : ℤ} :
--   IsCoprime a b → a * b = c ^ 2 → ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2

#check Int.sq_of_gcd_eq_one
-- Int.sq_of_gcd_eq_one {a b c : ℤ} :
--   Int.gcd a b = 1 → a * b = c ^ 2 → ∃ a0 : ℤ, a = a0 ^ 2 ∨ a = -a0 ^ 2

#check Int.Prime.dvd_pow'
-- Int.Prime.dvd_pow' {n : ℤ} {k p : ℕ} :
--   Nat.Prime p → (p : ℤ) ∣ n ^ k → (p : ℤ) ∣ n

#check Nat.prime_two
#check Int.mul_ediv_cancel_left
```

Pasteable Lean code:

```lean
import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic

namespace MazurProof.RationalPointsN12

#check Int.sq_of_isCoprime
#check Int.sq_of_gcd_eq_one
#check Int.Prime.dvd_pow'
#check Nat.prime_two
#check Int.mul_ediv_cancel_left

/-- Target statement: positive coprime factors of an integer square are squares. -/
def PosSqOfCoprimeMulSqStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x → 0 < y → IsCoprime x y → z ^ 2 = x * y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2

private lemma exists_pos_sq_of_pos_eq_sq {x a0 : ℤ}
    (hx : 0 < x) (hxa : x = a0 ^ 2) :
    ∃ a : ℤ, 0 < a ∧ x = a ^ 2 := by
  by_cases ha_pos : 0 < a0
  · exact ⟨a0, ha_pos, hxa⟩
  · have ha0_ne : a0 ≠ 0 := by
      intro ha0
      have hx0 : x = 0 := by
        simpa [ha0] using hxa
      linarith
    have ha_le : a0 ≤ 0 := le_of_not_gt ha_pos
    have ha_lt : a0 < 0 := lt_of_le_of_ne ha_le ha0_ne
    refine ⟨-a0, by linarith, ?_⟩
    calc
      x = a0 ^ 2 := hxa
      _ = (-a0) ^ 2 := by ring

/-- Usable theorem form of `PosSqOfCoprimeMulSqStatement`. -/
theorem posSqOfCoprimeMulSq
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y)
    (hcop : IsCoprime x y) (hz : z ^ 2 = x * y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2 := by
  have hmul : x * y = z ^ 2 := hz.symm
  rcases Int.sq_of_isCoprime hcop hmul with ⟨a0, hx_sq | hx_neg_sq⟩
  · have hmul_yx : y * x = z ^ 2 := by
      simpa [mul_comm] using hmul
    rcases Int.sq_of_isCoprime hcop.symm hmul_yx with ⟨b0, hy_sq | hy_neg_sq⟩
    · rcases exists_pos_sq_of_pos_eq_sq hx hx_sq with ⟨a, ha, hxa⟩
      rcases exists_pos_sq_of_pos_eq_sq hy hy_sq with ⟨b, hb, hyb⟩
      exact ⟨a, b, ha, hb, hxa, hyb⟩
    · exfalso
      have hyneg : 0 < -(b0 ^ 2) := by
        simpa [hy_neg_sq] using hy
      have hb_nonneg : 0 ≤ b0 ^ 2 := sq_nonneg b0
      nlinarith
  · exfalso
    have hxneg : 0 < -(a0 ^ 2) := by
      simpa [hx_neg_sq] using hx
    have ha_nonneg : 0 ≤ a0 ^ 2 := sq_nonneg a0
    nlinarith

theorem posSqOfCoprimeMulSqStatement_checked :
    PosSqOfCoprimeMulSqStatement := by
  intro x y z hx hy hcop hz
  exact posSqOfCoprimeMulSq hx hy hcop hz

/-- Analogous `2`-factor statement. -/
def PosSqOfCoprimeMulSqTwoFactorStatement : Prop :=
  ∀ {x y z : ℤ}, 0 < x → 0 < y → (2 : ℤ) ∣ x → (2 : ℤ) ∣ y →
    IsCoprime (x / 2) (y / 2) → z ^ 2 = x * y →
      ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2 * a ^ 2 ∧ y = 2 * b ^ 2

/-- If `x = 2u`, `y = 2v`, `IsCoprime u v`, and `xy` is a square,
then `u` and `v` are positive squares. -/
theorem posSqOfCoprimeMulSq_twoFactor
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y)
    (hx2 : (2 : ℤ) ∣ x) (hy2 : (2 : ℤ) ∣ y)
    (hcop : IsCoprime (x / 2) (y / 2))
    (hz : z ^ 2 = x * y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2 * a ^ 2 ∧ y = 2 * b ^ 2 := by
  rcases hx2 with ⟨u, rfl⟩
  rcases hy2 with ⟨v, rfl⟩
  have hu_pos : 0 < u := by
    nlinarith
  have hv_pos : 0 < v := by
    nlinarith
  have h2_ne : (2 : ℤ) ≠ 0 := by norm_num
  have hdiv_u : ((2 : ℤ) * u) / 2 = u := by
    exact Int.mul_ediv_cancel_left u h2_ne
  have hdiv_v : ((2 : ℤ) * v) / 2 = v := by
    exact Int.mul_ediv_cancel_left v h2_ne
  have hcop_uv : IsCoprime u v := by
    simpa [hdiv_u, hdiv_v] using hcop
  have hz2_dvd : (2 : ℤ) ∣ z ^ 2 := by
    rw [hz]
    exact ⟨u * (2 * v), by ring⟩
  have hz_dvd : (2 : ℤ) ∣ z := by
    exact Int.Prime.dvd_pow' (p := 2) (n := z) (k := 2) Nat.prime_two hz2_dvd
  rcases hz_dvd with ⟨w, rfl⟩
  have h4 : 4 * (w ^ 2) = 4 * (u * v) := by
    calc
      4 * (w ^ 2) = (2 * w) ^ 2 := by ring
      _ = (2 * u) * (2 * v) := hz
      _ = 4 * (u * v) := by ring
  have hw : w ^ 2 = u * v := by
    nlinarith
  rcases posSqOfCoprimeMulSq hu_pos hv_pos hcop_uv hw with
    ⟨a, b, ha, hb, hu_sq, hv_sq⟩
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rw [hu_sq]
  · rw [hv_sq]

theorem posSqOfCoprimeMulSqTwoFactorStatement_checked :
    PosSqOfCoprimeMulSqTwoFactorStatement := by
  intro x y z hx hy hx2 hy2 hcop hz
  exact posSqOfCoprimeMulSq_twoFactor hx hy hx2 hy2 hcop hz

end MazurProof.RationalPointsN12
```

If a name fails in the local file, grep these exact pinned targets first:

```bash
grep -R "theorem sq_of_isCoprime" .lake/packages/mathlib/Mathlib/RingTheory/Int/Basic.lean
grep -R "theorem sq_of_gcd_eq_one" .lake/packages/mathlib/Mathlib/RingTheory/Int/Basic.lean
grep -R "theorem Int.Prime.dvd_pow'" .lake/packages/mathlib/Mathlib/RingTheory/Int/Basic.lean
grep -R "mul_ediv_cancel_left" .lake/packages/mathlib/Mathlib/Data/Int .lake/packages/mathlib/Mathlib/Algebra
```

Notes for integration:

* `Mathlib.RingTheory.Int.Basic` is needed for `Int.sq_of_isCoprime` and `Int.Prime.dvd_pow'`.
* The first theorem avoids `abs`, `sq_abs`, and `abs_pos`; it chooses either `a0` or `-a0` by sign.
* The `2`-factor theorem deliberately proves evenness of `z` from `2 ∣ z^2` using `Int.Prime.dvd_pow'`, then divides the equation by rewriting `z = 2*w` and cancelling the resulting factor `4` with `nlinarith`.
