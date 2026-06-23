# Q35 (dm1): Ψ₃=0 stratum — rank-3 apparition lemma

## Executive answer

For the `Ψ₃.eval x = 0` stratum, do **not** use adjacent-Somos propagation.  The cleaner proof is a strong induction on the positive index using the defining `preΨ_odd` / `preΨ_even` recurrences.  Modulo `3`, exactly one summand survives in each nonzero case, and both summands vanish in the divisible-by-`3` case.

State the rank-3 lemma with the two nonsingularity base facts as local hypotheses:

```lean
(hs2 : W.Ψ₂Sq.eval x ≠ 0)
(hd4 : (W.preΨ 4).eval x ≠ 0)
(hc3 : W.Ψ₃.eval x = 0)
```

For the modified `preΨ`, note that `preΨ 2 = 1`; `hs2` is not the base value at index `2`, but is needed because the recurrence coefficients are powers of `Ψ₂Sq.eval x`.

---

## The recurrence table

Write

```lean
A i := (W.preΨ i).eval x
S   := W.Ψ₂Sq.eval x
```

At `A 3 = W.Ψ₃.eval x = 0`, with `S ≠ 0`, the evaluated recurrences give:

### Odd index, `N = 2*m + 1`

```text
A(2*m+1)
  = A(m+2) * A(m)^3 * (if Even m then S^2 else 1)
    - A(m-1) * A(m+1)^3 * (if Even m then 1 else S^2)
```

* If `m ≡ 0 mod 3`, then `A(m)=0`; the second summand is nonzero, so `A(2*m+1) ≠ 0` and `2*m+1 ≡ 1 mod 3`.
* If `m ≡ 1 mod 3`, then `A(m+2)=0` and `A(m-1)=0`, so `A(2*m+1)=0` and `2*m+1 ≡ 0 mod 3`.
* If `m ≡ 2 mod 3`, then `A(m+1)=0`; the first summand is nonzero, so `A(2*m+1) ≠ 0` and `2*m+1 ≡ 2 mod 3`.

### Even index, `N = 2*m`

```text
A(2*m)
  = A(m-1)^2 * A(m) * A(m+2)
    - A(m-2) * A(m) * A(m+1)^2
```

* If `m ≡ 0 mod 3`, then `A(m)=0`, so `A(2*m)=0` and `2*m ≡ 0 mod 3`.
* If `m ≡ 1 mod 3`, then `A(m-1)=0`; the second summand is nonzero, so `A(2*m) ≠ 0` and `2*m ≡ 2 mod 3`.
* If `m ≡ 2 mod 3`, then `A(m+1)=0`; the first summand is nonzero, so `A(2*m) ≠ 0` and `2*m ≡ 1 mod 3`.

The bases are:

```text
A 0 = 0
A 1 = 1
A 2 = 1
A 3 = 0
A 4 ≠ 0
```

The last base is exactly `hd4`.

---

## Lean skeleton

This is written as an implementation skeleton for `KeystoneCoprimality.lean`.  The only likely name adjustments are the exact names for `preΨ_zero`, `preΨ_two`, `preΨ_three`, and `preΨ_four` if your local imports expose them under slightly different names.  The arithmetic facts are deliberately isolated; in current Mathlib they are usually one-line `omega` goals.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace WeierstrassCurve

noncomputable section

variable {k : Type*} [Field k]

private abbrev pe (W : WeierstrassCurve k) (x : k) (i : ℤ) : k :=
  (W.preΨ i).eval x

private abbrev sx (W : WeierstrassCurve k) (x : k) : k :=
  W.Ψ₂Sq.eval x

private lemma coeff_left_ne_zero
    (W : WeierstrassCurve k) (x : k)
    (hs2 : sx W x ≠ 0) (m : ℤ) :
    (if Even m then (sx W x)^2 else 1) ≠ 0 := by
  by_cases hm : Even m
  · simp [hm, pow_ne_zero 2 hs2]
  · simp [hm]

private lemma coeff_right_ne_zero
    (W : WeierstrassCurve k) (x : k)
    (hs2 : sx W x ≠ 0) (m : ℤ) :
    (if Even m then 1 else (sx W x)^2) ≠ 0 := by
  by_cases hm : Even m
  · simp [hm]
  · simp [hm, pow_ne_zero 2 hs2]

private lemma eval_preΨ_odd
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    pe W x (2*m + 1)
      = pe W x (m + 2) * (pe W x m)^3 *
          (if Even m then (sx W x)^2 else 1)
        - pe W x (m - 1) * (pe W x (m + 1))^3 *
          (if Even m then 1 else (sx W x)^2) := by
  simpa [pe, sx, map_mul, map_sub, map_pow, mul_assoc, mul_left_comm, mul_comm]
    using congrArg (fun p : k[X] => p.eval x) (W.preΨ_odd m)

private lemma eval_preΨ_even
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    pe W x (2*m)
      = (pe W x (m - 1))^2 * pe W x m * pe W x (m + 2)
        - pe W x (m - 2) * pe W x m * (pe W x (m + 1))^2 := by
  simpa [pe, map_mul, map_sub, map_pow, mul_assoc, mul_left_comm, mul_comm, pow_two]
    using congrArg (fun p : k[X] => p.eval x) (W.preΨ_even m)

/-- Exactly one of `z`, `z-1`, `z+1` is divisible by `3`.  The implication
form is more convenient for the case split below. -/
private lemma mod3_trichotomy (z : ℤ) :
    (3 : ℤ) ∣ z ∨ (3 : ℤ) ∣ z - 1 ∨ (3 : ℤ) ∣ z + 1 := by
  omega

private lemma not_three_dvd_of_three_dvd_sub_one {z : ℤ}
    (h : (3 : ℤ) ∣ z - 1) : ¬ (3 : ℤ) ∣ z := by
  omega

private lemma not_three_dvd_of_three_dvd_add_one {z : ℤ}
    (h : (3 : ℤ) ∣ z + 1) : ¬ (3 : ℤ) ∣ z := by
  omega

private lemma three_dvd_two_mul_add_one_iff_sub_one {m : ℤ} :
    ((3 : ℤ) ∣ 2*m + 1) ↔ (3 : ℤ) ∣ m - 1 := by
  omega

private lemma three_dvd_two_mul_iff {m : ℤ} :
    ((3 : ℤ) ∣ 2*m) ↔ (3 : ℤ) ∣ m := by
  omega

private lemma not_three_dvd_two_mul_add_one_of_three_dvd {m : ℤ}
    (hm : (3 : ℤ) ∣ m) : ¬ (3 : ℤ) ∣ 2*m + 1 := by
  omega

private lemma not_three_dvd_two_mul_add_one_of_three_dvd_add_one {m : ℤ}
    (hm : (3 : ℤ) ∣ m + 1) : ¬ (3 : ℤ) ∣ 2*m + 1 := by
  omega

private lemma not_three_dvd_two_mul_of_three_dvd_sub_one {m : ℤ}
    (hm : (3 : ℤ) ∣ m - 1) : ¬ (3 : ℤ) ∣ 2*m := by
  omega

private lemma not_three_dvd_two_mul_of_three_dvd_add_one {m : ℤ}
    (hm : (3 : ℤ) ∣ m + 1) : ¬ (3 : ℤ) ∣ 2*m := by
  omega

/-- Nat-indexed rank-3 apparition.  This is the actual strong induction. -/
private lemma preΨ_eval_zero_iff_three_dvd_nat_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k)
    (hc3 : W.Ψ₃.eval x = 0)
    (hs2 : sx W x ≠ 0)
    (hd4 : pe W x 4 ≠ 0) :
    ∀ N : ℕ, pe W x (N : ℤ) = 0 ↔ (3 : ℤ) ∣ (N : ℤ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N IH =>
    by_cases hsmall : N ≤ 4
    · interval_cases N
      · -- N = 0
        constructor
        · intro _; norm_num
        · intro _
          simpa [pe] using congrArg (fun p : k[X] => p.eval x) (W.preΨ_zero)
      · -- N = 1
        constructor
        · intro h
          have : (1 : k) = 0 := by simpa [pe] using h
          exact (one_ne_zero this).elim
        · intro h
          omega
      · -- N = 2
        constructor
        · intro h
          have : (1 : k) = 0 := by simpa [pe] using h
          exact (one_ne_zero this).elim
        · intro h
          omega
      · -- N = 3
        constructor
        · intro _; norm_num
        · intro _
          simpa [pe] using hc3
      · -- N = 4
        constructor
        · intro h
          exact (hd4 h).elim
        · intro h
          omega
    · have hN5 : 5 ≤ N := by omega
      rcases Nat.even_or_odd N with hEven | hOdd
      · rcases hEven with ⟨M, rfl⟩
        have hM3 : 3 ≤ M := by omega
        have hMlt : M < 2*M := by omega
        have hMm1lt : M - 1 < 2*M := by omega
        have hMm2lt : M - 2 < 2*M := by omega
        have hMp1lt : M + 1 < 2*M := by omega
        have hMp2lt : M + 2 < 2*M := by omega
        have IHm   := IH M hMlt
        have IHm1  := IH (M - 1) hMm1lt
        have IHm2  := IH (M - 2) hMm2lt
        have IHp1  := IH (M + 1) hMp1lt
        have IHp2  := IH (M + 2) hMp2lt
        have hev := eval_preΨ_even W x (M : ℤ)
        rcases mod3_trichotomy (M : ℤ) with h0 | hrest
        · -- M ≡ 0: the common factor A(M) vanishes.
          have hAm : pe W x (M : ℤ) = 0 := IHm.mpr h0
          have hA : pe W x (2*(M : ℤ)) = 0 := by
            simpa [hAm, mul_assoc, mul_left_comm, mul_comm] using hev
          constructor
          · intro _
            exact (three_dvd_two_mul_iff.mp ?_)
          · intro _
            simpa [Int.ofNat_mul, hA]
        · rcases hrest with hm1 | hp1
          · -- M ≡ 1: first summand zero, second summand nonzero.
            have hAm1 : pe W x ((M : ℤ) - 1) = 0 := by
              have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
              simpa [hcast] using (IHm1.mpr (by omega : (3 : ℤ) ∣ ((M - 1 : ℕ) : ℤ)))
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_sub_one hm1 (IHm.mp h)
            have hAm2_ne : pe W x ((M : ℤ) - 2) ≠ 0 := by
              intro h
              have hcast : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by omega
              have hdvd := IHm2.mp (by simpa [hcast] using h)
              omega
            have hAp1_ne : pe W x ((M : ℤ) + 1) ≠ 0 := by
              intro h
              have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
              have hdvd := IHp1.mp (by simpa [hcast] using h)
              omega
            have hsecond_ne :
                pe W x ((M : ℤ) - 2) * pe W x (M : ℤ) *
                    (pe W x ((M : ℤ) + 1))^2 ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero hAm2_ne hAm_ne) (pow_ne_zero 2 hAp1_ne)
            have hAne : pe W x (2*(M : ℤ)) ≠ 0 := by
              rw [hev]
              simp [hAm1, hsecond_ne]
            constructor
            · intro h
              exact (hAne h).elim
            · intro hdvd
              exact (not_three_dvd_two_mul_of_three_dvd_sub_one hm1 hdvd).elim
          · -- M ≡ 2: second summand zero, first summand nonzero.
            have hAp1 : pe W x ((M : ℤ) + 1) = 0 := by
              have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
              simpa [hcast] using (IHp1.mpr (by omega : (3 : ℤ) ∣ ((M + 1 : ℕ) : ℤ)))
            have hAm1_ne : pe W x ((M : ℤ) - 1) ≠ 0 := by
              intro h
              have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
              have hdvd := IHm1.mp (by simpa [hcast] using h)
              omega
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_add_one hp1 (IHm.mp h)
            have hAp2_ne : pe W x ((M : ℤ) + 2) ≠ 0 := by
              intro h
              have hcast : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
              have hdvd := IHp2.mp (by simpa [hcast] using h)
              omega
            have hfirst_ne :
                (pe W x ((M : ℤ) - 1))^2 * pe W x (M : ℤ) *
                    pe W x ((M : ℤ) + 2) ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAm1_ne) hAm_ne) hAp2_ne
            have hAne : pe W x (2*(M : ℤ)) ≠ 0 := by
              rw [hev]
              simp [hAp1, hfirst_ne]
            constructor
            · intro h
              exact (hAne h).elim
            · intro hdvd
              exact (not_three_dvd_two_mul_of_three_dvd_add_one hp1 hdvd).elim
      · rcases hOdd with ⟨M, rfl⟩
        have hM2 : 2 ≤ M := by omega
        have hMlt : M < 2*M + 1 := by omega
        have hMm1lt : M - 1 < 2*M + 1 := by omega
        have hMp1lt : M + 1 < 2*M + 1 := by omega
        have hMp2lt : M + 2 < 2*M + 1 := by omega
        have IHm   := IH M hMlt
        have IHm1  := IH (M - 1) hMm1lt
        have IHp1  := IH (M + 1) hMp1lt
        have IHp2  := IH (M + 2) hMp2lt
        have hodd := eval_preΨ_odd W x (M : ℤ)
        have hcleft := coeff_left_ne_zero W x hs2 (M : ℤ)
        have hcright := coeff_right_ne_zero W x hs2 (M : ℤ)
        rcases mod3_trichotomy (M : ℤ) with h0 | hrest
        · -- M ≡ 0: first summand zero, second summand nonzero.
          have hAm : pe W x (M : ℤ) = 0 := IHm.mpr h0
          have hAm1_ne : pe W x ((M : ℤ) - 1) ≠ 0 := by
            intro h
            have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
            have hdvd := IHm1.mp (by simpa [hcast] using h)
            omega
          have hAp1_ne : pe W x ((M : ℤ) + 1) ≠ 0 := by
            intro h
            have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
            have hdvd := IHp1.mp (by simpa [hcast] using h)
            omega
          have hsecond_ne :
              pe W x ((M : ℤ) - 1) * (pe W x ((M : ℤ) + 1))^3 *
                  (if Even (M : ℤ) then 1 else (sx W x)^2) ≠ 0 := by
            exact mul_ne_zero (mul_ne_zero hAm1_ne (pow_ne_zero 3 hAp1_ne)) hcright
          have hAne : pe W x (2*(M : ℤ) + 1) ≠ 0 := by
            rw [hodd]
            simp [hAm, hsecond_ne]
          constructor
          · intro h
            exact (hAne h).elim
          · intro hdvd
            exact (not_three_dvd_two_mul_add_one_of_three_dvd h0 hdvd).elim
        · rcases hrest with hm1 | hp1
          · -- M ≡ 1: both summands vanish.
            have hAm1 : pe W x ((M : ℤ) - 1) = 0 := by
              have hcast : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
              simpa [hcast] using (IHm1.mpr (by omega : (3 : ℤ) ∣ ((M - 1 : ℕ) : ℤ)))
            have hAp2 : pe W x ((M : ℤ) + 2) = 0 := by
              have hcast : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
              simpa [hcast] using (IHp2.mpr (by omega : (3 : ℤ) ∣ ((M + 2 : ℕ) : ℤ)))
            have hA : pe W x (2*(M : ℤ) + 1) = 0 := by
              rw [hodd]
              simp [hAm1, hAp2]
            constructor
            · intro _
              exact three_dvd_two_mul_add_one_iff_sub_one.mpr hm1
            · intro _
              simpa [hA]
          · -- M ≡ 2: second summand zero, first summand nonzero.
            have hAp1 : pe W x ((M : ℤ) + 1) = 0 := by
              have hcast : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
              simpa [hcast] using (IHp1.mpr (by omega : (3 : ℤ) ∣ ((M + 1 : ℕ) : ℤ)))
            have hAp2_ne : pe W x ((M : ℤ) + 2) ≠ 0 := by
              intro h
              have hcast : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
              have hdvd := IHp2.mp (by simpa [hcast] using h)
              omega
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_add_one hp1 (IHm.mp h)
            have hfirst_ne :
                pe W x ((M : ℤ) + 2) * (pe W x (M : ℤ))^3 *
                    (if Even (M : ℤ) then (sx W x)^2 else 1) ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero hAp2_ne (pow_ne_zero 3 hAm_ne)) hcleft
            have hAne : pe W x (2*(M : ℤ) + 1) ≠ 0 := by
              rw [hodd]
              simp [hAp1, hfirst_ne]
            constructor
            · intro h
              exact (hAne h).elim
            · intro hdvd
              exact (not_three_dvd_two_mul_add_one_of_three_dvd_add_one hp1 hdvd).elim

private lemma preΨ_eval_zero_iff_three_dvd_abs
    (W : WeierstrassCurve k) (x : k)
    (hNat : ∀ N : ℕ, pe W x (N : ℤ) = 0 ↔ (3 : ℤ) ∣ (N : ℤ))
    (n : ℤ) :
    pe W x n = 0 ↔ (3 : ℤ) ∣ n := by
  by_cases hn : 0 ≤ n
  · have hcast : ((Int.toNat n : ℕ) : ℤ) = n := by omega
    simpa [hcast] using hNat (Int.toNat n)
  · have hnle : n ≤ 0 := by omega
    have hpos : 0 ≤ -n := by omega
    have hcast : ((Int.toNat (-n) : ℕ) : ℤ) = -n := by omega
    have hneg_eval : pe W x (-n) = 0 ↔ pe W x n = 0 := by
      have h := congrArg (fun p : k[X] => p.eval x) (W.preΨ_neg n)
      -- `preΨ_neg` has the usual sign, so zero is invariant under negating the index.
      -- Depending on the local theorem orientation, `simpa [pe] using h` or
      -- `simpa [pe, eq_comm] using h` closes this.
      simpa [pe] using h
    have hneg_dvd : ((3 : ℤ) ∣ -n) ↔ (3 : ℤ) ∣ n := by omega
    have hNatNeg := hNat (Int.toNat (-n))
    calc
      pe W x n = 0 ↔ pe W x (-n) = 0 := hneg_eval.symm
      _ ↔ (3 : ℤ) ∣ -n := by simpa [hcast] using hNatNeg
      _ ↔ (3 : ℤ) ∣ n := hneg_dvd

/-- Rank-3 apparition on the `Ψ₃.eval x = 0` stratum. -/
theorem preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0)
    (hc3 : W.Ψ₃.eval x = 0)
    (hs2 : W.Ψ₂Sq.eval x ≠ 0)
    (hd4 : (W.preΨ 4).eval x ≠ 0)
    (n : ℤ) :
    (W.preΨ n).eval x = 0 ↔ (3 : ℤ) ∣ n := by
  -- `h4` and `[W.IsElliptic]` are kept in the statement for the final caller;
  -- this local rank-3 induction only uses `hc3`, `hs2`, `hd4`, and the recurrences.
  have hNat := preΨ_eval_zero_iff_three_dvd_nat_of_Ψ₃_eval_zero
    (W := W) (x := x) hc3 (by simpa [sx] using hs2) (by simpa [pe] using hd4)
  simpa [pe] using preΨ_eval_zero_iff_three_dvd_abs (W := W) (x := x) hNat n

/-- No adjacent vanishing on the `Ψ₃.eval x = 0` stratum. -/
theorem no_adjacent_preΨ_zero_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0)
    (hc3 : W.Ψ₃.eval x = 0)
    (hs2 : W.Ψ₂Sq.eval x ≠ 0)
    (hd4 : (W.preΨ 4).eval x ≠ 0)
    (r : ℤ) :
    ¬ ((W.preΨ r).eval x = 0 ∧ (W.preΨ (r + 1)).eval x = 0) := by
  intro hz
  have hr : (3 : ℤ) ∣ r :=
    (preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
      (W := W) (x := x) h4 hc3 hs2 hd4 r).mp hz.left
  have hr1 : (3 : ℤ) ∣ r + 1 :=
    (preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero
      (W := W) (x := x) h4 hc3 hs2 hd4 (r + 1)).mp hz.right
  omega

end

end WeierstrassCurve
```

---

## Notes for integration

1. The theorem intentionally takes `hs2` and `hd4` as hypotheses.  These are exactly the two finite resultant/Bezout certificates you said are being proved separately.

2. The proof uses `h4` only to match the caller shape.  The rank-3 induction itself does not need adjacent-Somos or `h4`; it only needs the already-defined `preΨ_odd` and `preΨ_even` recurrences plus the two nonzero base facts.

3. If `Nat.even_or_odd` has a different local name in your pinned Mathlib, replace that case split with:

```lean
by_cases hEven : Even N
· rcases hEven with ⟨M, rfl⟩
  ...
· have hOdd : Odd N := Nat.not_even_iff_odd.mp hEven
  rcases hOdd with ⟨M, rfl⟩
  ...
```

4. If `omega` does not close `mod3_trichotomy` in your local Mathlib, prove it via `ZMod 3` or by `obtain ⟨q, rfl | rfl | rfl⟩` from Euclidean division.  All later arithmetic facts are the same linear/divisibility obligations.

5. The corollary is the desired closure of the `Ψ₃=0` stratum: by the rank-3 lemma, adjacent vanishings imply `3 ∣ r` and `3 ∣ r+1`, impossible by `omega`.
