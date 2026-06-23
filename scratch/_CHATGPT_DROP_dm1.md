# Q53 (dm1): corrected rank-3 apparition strong induction

Below is the corrected replacement for the Q35 main strong-induction block.  The changes are:

* the even branch is treated as the Nat index `M + M`, with explicit cast normalizers to `2 * (M : ℤ)` at every final use;
* the `M ≡ 0 mod 3` placeholder is replaced by `three_dvd_two_mul_iff.mpr h0`;
* the nonzero branches avoid fragile `simp [hsecond_ne]` / `simp [hfirst_ne]` goals and instead derive a contradiction by turning a zero of the whole recurrence into a zero of the explicitly nonzero surviving factor.

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
  have h := congrArg (fun p : k[X] => p.eval x) (W.preΨ_odd m)
  simp only [pe, sx, eval_mul, eval_sub, eval_add, eval_pow,
    apply_ite (fun p : k[X] => p.eval x), eval_one] at h ⊢
  linear_combination h

private lemma eval_preΨ_even
    (W : WeierstrassCurve k) (x : k) (m : ℤ) :
    pe W x (2*m)
      = (pe W x (m - 1))^2 * pe W x m * pe W x (m + 2)
        - pe W x (m - 2) * pe W x m * (pe W x (m + 1))^2 := by
  have h := congrArg (fun p : k[X] => p.eval x) (W.preΨ_even m)
  simp only [pe, eval_mul, eval_sub, eval_add, eval_pow] at h ⊢
  linear_combination h

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

private lemma nat_even_cast_to_int (M : ℕ) :
    ((M + M : ℕ) : ℤ) = 2 * (M : ℤ) := by
  omega

private lemma nat_even_mul_cast_to_int (M : ℕ) :
    ((2 * M : ℕ) : ℤ) = 2 * (M : ℤ) := by
  omega

private lemma nat_odd_cast_to_int (M : ℕ) :
    ((M + M + 1 : ℕ) : ℤ) = 2 * (M : ℤ) + 1 := by
  omega

private lemma nat_odd_mul_cast_to_int (M : ℕ) :
    ((2 * M + 1 : ℕ) : ℤ) = 2 * (M : ℤ) + 1 := by
  omega

private lemma nat_sub_one_cast (M : ℕ) (hM : 1 ≤ M) :
    ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by
  omega

private lemma nat_sub_two_cast (M : ℕ) (hM : 2 ≤ M) :
    ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 := by
  omega

/-- Nat-indexed rank-3 apparition on the `Ψ₃.eval x = 0` stratum. -/
private lemma preΨ_eval_zero_iff_three_dvd_nat_of_Ψ₃_eval_zero
    (W : WeierstrassCurve k) (x : k)
    (h4 : (4 : k) ≠ 0)
    (hc3 : W.Ψ₃.eval x = 0)
    (hs2 : sx W x ≠ 0)
    (hd4 : (W.preΨ 4).eval x ≠ 0) :
    ∀ N : ℕ, pe W x (N : ℤ) = 0 ↔ (3 : ℤ) ∣ (N : ℤ) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N IH =>
    by_cases hsmall : N ≤ 4
    · interval_cases N
      · constructor
        · intro _; norm_num
        · intro _
          simpa [pe] using congrArg (fun p : k[X] => p.eval x) (W.preΨ_zero)
      · constructor
        · intro h
          have h1 : (1 : k) = 0 := by simpa [pe] using h
          exact (one_ne_zero h1).elim
        · intro h; omega
      · constructor
        · intro h
          have h2 : (1 : k) = 0 := by simpa [pe] using h
          exact (one_ne_zero h2).elim
        · intro h; omega
      · constructor
        · intro _; norm_num
        · intro _
          simpa [pe] using hc3
      · constructor
        · intro h
          exact (hd4 (by simpa [pe] using h)).elim
        · intro h; omega
    · have hN5 : 5 ≤ N := by omega
      rcases Nat.even_or_odd N with hEven | hOdd
      · rcases hEven with ⟨M, rfl⟩
        have hM3 : 3 ≤ M := by omega
        have hM1 : 1 ≤ M := by omega
        have hM2 : 2 ≤ M := by omega
        have hMlt : M < M + M := by omega
        have hMm1lt : M - 1 < M + M := by omega
        have hMm2lt : M - 2 < M + M := by omega
        have hMp1lt : M + 1 < M + M := by omega
        have hMp2lt : M + 2 < M + M := by omega
        have IHm   := IH M hMlt
        have IHm1  := IH (M - 1) hMm1lt
        have IHm2  := IH (M - 2) hMm2lt
        have IHp1  := IH (M + 1) hMp1lt
        have IHp2  := IH (M + 2) hMp2lt
        have hev := eval_preΨ_even W x (M : ℤ)
        have hcastEven : ((M + M : ℕ) : ℤ) = 2 * (M : ℤ) := nat_even_cast_to_int M
        have hcastEvenMul : ((2 * M : ℕ) : ℤ) = 2 * (M : ℤ) := nat_even_mul_cast_to_int M
        rcases mod3_trichotomy (M : ℤ) with h0 | hrest
        · -- M ≡ 0: A(M) is the common factor, so A(2M)=0.
          have hAm : pe W x (M : ℤ) = 0 := IHm.mpr h0
          have hA : pe W x (2 * (M : ℤ)) = 0 := by
            simpa [hAm, mul_assoc, mul_left_comm, mul_comm] using hev
          constructor
          · intro _
            have hdiv : (3 : ℤ) ∣ 2 * (M : ℤ) :=
              (three_dvd_two_mul_iff (m := (M : ℤ))).mpr h0
            simpa [hcastEven, hcastEvenMul] using hdiv
          · intro _
            simpa [hcastEven, hcastEvenMul] using hA
        · rcases hrest with hm1 | hp1
          · -- M ≡ 1: first summand zero, second summand nonzero.
            have hcast_m1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 :=
              nat_sub_one_cast M hM1
            have hcast_m2 : ((M - 2 : ℕ) : ℤ) = (M : ℤ) - 2 :=
              nat_sub_two_cast M hM2
            have hcast_p1 : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
            have hAm1 : pe W x ((M : ℤ) - 1) = 0 := by
              have hraw : pe W x ((M - 1 : ℕ) : ℤ) = 0 :=
                IHm1.mpr (by simpa [hcast_m1] using hm1)
              simpa [hcast_m1] using hraw
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_sub_one hm1 (IHm.mp h)
            have hAm2_ne : pe W x ((M : ℤ) - 2) ≠ 0 := by
              intro h
              have hraw : pe W x ((M - 2 : ℕ) : ℤ) = 0 := by simpa [hcast_m2] using h
              have hdvd := IHm2.mp hraw
              omega
            have hAp1_ne : pe W x ((M : ℤ) + 1) ≠ 0 := by
              intro h
              have hraw : pe W x ((M + 1 : ℕ) : ℤ) = 0 := by simpa [hcast_p1] using h
              have hdvd := IHp1.mp hraw
              omega
            have hsecond_ne :
                pe W x ((M : ℤ) - 2) * pe W x (M : ℤ) *
                    (pe W x ((M : ℤ) + 1))^2 ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero hAm2_ne hAm_ne) (pow_ne_zero 2 hAp1_ne)
            have hAne : pe W x (2 * (M : ℤ)) ≠ 0 := by
              intro hz
              apply hsecond_ne
              have hneg :
                  - (pe W x ((M : ℤ) - 2) * pe W x (M : ℤ) *
                      (pe W x ((M : ℤ) + 1))^2) = 0 := by
                simpa [hev, hAm1, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
                  using hz
              exact neg_eq_zero.mp hneg
            constructor
            · intro h
              have hz : pe W x (2 * (M : ℤ)) = 0 := by
                simpa [hcastEven, hcastEvenMul] using h
              exact (hAne hz).elim
            · intro hdvd
              have hdvd' : (3 : ℤ) ∣ 2 * (M : ℤ) := by
                simpa [hcastEven, hcastEvenMul] using hdvd
              exact (not_three_dvd_two_mul_of_three_dvd_sub_one hm1 hdvd').elim
          · -- M ≡ 2: second summand zero, first summand nonzero.
            have hcast_m1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 :=
              nat_sub_one_cast M hM1
            have hcast_p1 : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
            have hcast_p2 : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
            have hAp1 : pe W x ((M : ℤ) + 1) = 0 := by
              have hraw : pe W x ((M + 1 : ℕ) : ℤ) = 0 :=
                IHp1.mpr (by simpa [hcast_p1] using hp1)
              simpa [hcast_p1] using hraw
            have hAm1_ne : pe W x ((M : ℤ) - 1) ≠ 0 := by
              intro h
              have hraw : pe W x ((M - 1 : ℕ) : ℤ) = 0 := by simpa [hcast_m1] using h
              have hdvd := IHm1.mp hraw
              omega
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_add_one hp1 (IHm.mp h)
            have hAp2_ne : pe W x ((M : ℤ) + 2) ≠ 0 := by
              intro h
              have hraw : pe W x ((M + 2 : ℕ) : ℤ) = 0 := by simpa [hcast_p2] using h
              have hdvd := IHp2.mp hraw
              omega
            have hfirst_ne :
                (pe W x ((M : ℤ) - 1))^2 * pe W x (M : ℤ) *
                    pe W x ((M : ℤ) + 2) ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hAm1_ne) hAm_ne) hAp2_ne
            have hAne : pe W x (2 * (M : ℤ)) ≠ 0 := by
              intro hz
              apply hfirst_ne
              simpa [hev, hAp1, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
                using hz
            constructor
            · intro h
              have hz : pe W x (2 * (M : ℤ)) = 0 := by
                simpa [hcastEven, hcastEvenMul] using h
              exact (hAne hz).elim
            · intro hdvd
              have hdvd' : (3 : ℤ) ∣ 2 * (M : ℤ) := by
                simpa [hcastEven, hcastEvenMul] using hdvd
              exact (not_three_dvd_two_mul_of_three_dvd_add_one hp1 hdvd').elim
      · rcases hOdd with ⟨M, rfl⟩
        have hM2 : 2 ≤ M := by omega
        have hM1 : 1 ≤ M := by omega
        have hMlt : M < M + M + 1 := by omega
        have hMm1lt : M - 1 < M + M + 1 := by omega
        have hMp1lt : M + 1 < M + M + 1 := by omega
        have hMp2lt : M + 2 < M + M + 1 := by omega
        have IHm   := IH M hMlt
        have IHm1  := IH (M - 1) hMm1lt
        have IHp1  := IH (M + 1) hMp1lt
        have IHp2  := IH (M + 2) hMp2lt
        have hodd := eval_preΨ_odd W x (M : ℤ)
        have hcleft := coeff_left_ne_zero W x hs2 (M : ℤ)
        have hcright := coeff_right_ne_zero W x hs2 (M : ℤ)
        have hcastOdd : ((M + M + 1 : ℕ) : ℤ) = 2 * (M : ℤ) + 1 :=
          nat_odd_cast_to_int M
        have hcastOddMul : ((2 * M + 1 : ℕ) : ℤ) = 2 * (M : ℤ) + 1 :=
          nat_odd_mul_cast_to_int M
        rcases mod3_trichotomy (M : ℤ) with h0 | hrest
        · -- M ≡ 0: first summand zero, second summand nonzero.
          have hcast_m1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 :=
            nat_sub_one_cast M hM1
          have hcast_p1 : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
          have hAm : pe W x (M : ℤ) = 0 := IHm.mpr h0
          have hAm1_ne : pe W x ((M : ℤ) - 1) ≠ 0 := by
            intro h
            have hraw : pe W x ((M - 1 : ℕ) : ℤ) = 0 := by simpa [hcast_m1] using h
            have hdvd := IHm1.mp hraw
            omega
          have hAp1_ne : pe W x ((M : ℤ) + 1) ≠ 0 := by
            intro h
            have hraw : pe W x ((M + 1 : ℕ) : ℤ) = 0 := by simpa [hcast_p1] using h
            have hdvd := IHp1.mp hraw
            omega
          have hsecond_ne :
              pe W x ((M : ℤ) - 1) * (pe W x ((M : ℤ) + 1))^3 *
                  (if Even (M : ℤ) then 1 else (sx W x)^2) ≠ 0 := by
            exact mul_ne_zero (mul_ne_zero hAm1_ne (pow_ne_zero 3 hAp1_ne)) hcright
          have hAne : pe W x (2 * (M : ℤ) + 1) ≠ 0 := by
            intro hz
            apply hsecond_ne
            have hneg :
                - (pe W x ((M : ℤ) - 1) * (pe W x ((M : ℤ) + 1))^3 *
                    (if Even (M : ℤ) then 1 else (sx W x)^2)) = 0 := by
              simpa [hodd, hAm, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
                using hz
            exact neg_eq_zero.mp hneg
          constructor
          · intro h
            have hz : pe W x (2 * (M : ℤ) + 1) = 0 := by
              simpa [hcastOdd, hcastOddMul] using h
            exact (hAne hz).elim
          · intro hdvd
            have hdvd' : (3 : ℤ) ∣ 2 * (M : ℤ) + 1 := by
              simpa [hcastOdd, hcastOddMul] using hdvd
            exact (not_three_dvd_two_mul_add_one_of_three_dvd h0 hdvd').elim
        · rcases hrest with hm1 | hp1
          · -- M ≡ 1: both summands vanish, so A(2M+1)=0.
            have hcast_m1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 :=
              nat_sub_one_cast M hM1
            have hcast_p2 : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
            have hAm1 : pe W x ((M : ℤ) - 1) = 0 := by
              have hraw : pe W x ((M - 1 : ℕ) : ℤ) = 0 :=
                IHm1.mpr (by simpa [hcast_m1] using hm1)
              simpa [hcast_m1] using hraw
            have hAp2 : pe W x ((M : ℤ) + 2) = 0 := by
              have hraw : pe W x ((M + 2 : ℕ) : ℤ) = 0 :=
                IHp2.mpr (by omega)
              simpa [hcast_p2] using hraw
            have hA : pe W x (2 * (M : ℤ) + 1) = 0 := by
              simpa [hodd, hAm1, hAp2, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
            constructor
            · intro _
              have hdiv : (3 : ℤ) ∣ 2 * (M : ℤ) + 1 :=
                (three_dvd_two_mul_add_one_iff_sub_one (m := (M : ℤ))).mpr hm1
              simpa [hcastOdd, hcastOddMul] using hdiv
            · intro _
              simpa [hcastOdd, hcastOddMul] using hA
          · -- M ≡ 2: second summand zero, first summand nonzero.
            have hcast_p1 : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
            have hcast_p2 : ((M + 2 : ℕ) : ℤ) = (M : ℤ) + 2 := by omega
            have hAp1 : pe W x ((M : ℤ) + 1) = 0 := by
              have hraw : pe W x ((M + 1 : ℕ) : ℤ) = 0 :=
                IHp1.mpr (by simpa [hcast_p1] using hp1)
              simpa [hcast_p1] using hraw
            have hAp2_ne : pe W x ((M : ℤ) + 2) ≠ 0 := by
              intro h
              have hraw : pe W x ((M + 2 : ℕ) : ℤ) = 0 := by simpa [hcast_p2] using h
              have hdvd := IHp2.mp hraw
              omega
            have hAm_ne : pe W x (M : ℤ) ≠ 0 := by
              intro h
              exact not_three_dvd_of_three_dvd_add_one hp1 (IHm.mp h)
            have hfirst_ne :
                pe W x ((M : ℤ) + 2) * (pe W x (M : ℤ))^3 *
                    (if Even (M : ℤ) then (sx W x)^2 else 1) ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero hAp2_ne (pow_ne_zero 3 hAm_ne)) hcleft
            have hAne : pe W x (2 * (M : ℤ) + 1) ≠ 0 := by
              intro hz
              apply hfirst_ne
              simpa [hodd, hAp1, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
                using hz
            constructor
            · intro h
              have hz : pe W x (2 * (M : ℤ) + 1) = 0 := by
                simpa [hcastOdd, hcastOddMul] using h
              exact (hAne hz).elim
            · intro hdvd
              have hdvd' : (3 : ℤ) ∣ 2 * (M : ℤ) + 1 := by
                simpa [hcastOdd, hcastOddMul] using hdvd
              exact (not_three_dvd_two_mul_add_one_of_three_dvd_add_one hp1 hdvd').elim

end

end WeierstrassCurve
```

## Two notes if Lean still complains

1. If your local `Nat.even_or_odd` rewrites the even case to `2 * M` instead of `M + M`, keep the same proof body and replace the final casts with `hcastEvenMul`.  Both normalizers are included above on purpose.

2. If `simp` does not turn the surviving recurrence into the exact negated factor in the nonzero branches, replace the relevant `simpa [...] using hz` by:

```lean
linear_combination (norm := ring_nf) hz - hodd
```

or, in the even branch,

```lean
linear_combination (norm := ring_nf) hz - hev
```

The important change is that the proof now proves nonzero by contradiction from the recurrence, rather than asking `simp` to prove a `sub ≠ 0` goal directly.
