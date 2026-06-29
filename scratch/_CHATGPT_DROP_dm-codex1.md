# Q2291: Lean helper for coprime integer factors of a square

```lean
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace FLT.N12

private noncomputable def halfFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => e / 2) (by simp)

private theorem halfFactorization_support_prime (n : ℕ) :
    ∀ p ∈ (halfFactorization n).support, Nat.Prime p := by
  intro p hp
  rw [Finsupp.mem_support_iff] at hp
  by_contra hprime
  exact hp (by
    simp [halfFactorization, Nat.factorization_eq_zero_of_not_prime n hprime])

private noncomputable def factorizationHalfRoot (n : ℕ) : ℕ :=
  (halfFactorization n).prod fun p e => p ^ e

private theorem factorizationHalfRoot_ne_zero (n : ℕ) :
    factorizationHalfRoot n ≠ 0 := by
  classical
  rw [factorizationHalfRoot]
  change ((halfFactorization n).support.prod fun p => p ^ halfFactorization n p) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (by
    intro p hp
    exact pow_ne_zero _ ((halfFactorization_support_prime n p hp).ne_zero))

private theorem factorization_factorizationHalfRoot (n : ℕ) :
    (factorizationHalfRoot n).factorization = halfFactorization n := by
  exact Nat.prod_pow_factorization_eq_self (halfFactorization_support_prime n)

private theorem Nat_exists_sq_of_factorization_even {n : ℕ}
    (h : ∀ p, Even (n.factorization p)) :
    ∃ r : ℕ, n = r ^ 2 := by
  by_cases hn : n = 0
  · exact ⟨0, by simp [hn]⟩
  refine ⟨factorizationHalfRoot n, ?_⟩
  apply Nat.eq_of_factorization_eq hn (pow_ne_zero 2 (factorizationHalfRoot_ne_zero n))
  intro p
  have hroot : (factorizationHalfRoot n).factorization = halfFactorization n :=
    factorization_factorizationHalfRoot n
  calc
    n.factorization p = 2 * (n.factorization p / 2) := by
      rcases h p with ⟨k, hk⟩
      omega
    _ = (2 • halfFactorization n) p := by
      simp [halfFactorization]
    _ = (2 • (factorizationHalfRoot n).factorization) p := by
      rw [← hroot]
    _ = ((factorizationHalfRoot n) ^ 2).factorization p := by
      simp [Nat.factorization_pow]

private theorem Nat_even_factorization_of_coprime_mul_eq_sq
    {a b z p : ℕ} (hcop : a.Coprime b) (h : a * b = z ^ 2) :
    Even (a.factorization p) ∧ Even (b.factorization p) := by
  have hsum : a.factorization p + b.factorization p = 2 * z.factorization p := by
    calc
      a.factorization p + b.factorization p = (a * b).factorization p := by
        rw [Nat.factorization_mul_apply_of_coprime hcop]
      _ = (z ^ 2).factorization p := by rw [h]
      _ = (2 • z.factorization) p := by rw [Nat.factorization_pow]
      _ = 2 * z.factorization p := by simp
  by_cases hpa : a.factorization p = 0
  · rw [hpa, zero_add] at hsum
    exact ⟨by simp [hpa], ⟨z.factorization p, by omega⟩⟩
  · have hpb : b.factorization p = 0 := by
      by_contra hpb
      have hpprime : Nat.Prime p := by
        by_contra hpnot
        exact hpa (Nat.factorization_eq_zero_of_not_prime a hpnot)
      have hdva : p ∣ a := Nat.dvd_of_factorization_pos hpa
      have hdvb : p ∣ b := Nat.dvd_of_factorization_pos hpb
      have hdvg : p ∣ Nat.gcd a b := Nat.dvd_gcd hdva hdvb
      have hgcd : Nat.gcd a b = 1 := by simpa [Nat.Coprime] using hcop
      have hdv1 : p ∣ 1 := by simpa [hgcd] using hdvg
      exact hpprime.not_dvd_one hdv1
    rw [hpb, add_zero] at hsum
    exact ⟨⟨z.factorization p, by omega⟩, by simp [hpb]⟩

theorem Nat_coprime_mul_eq_sq {a b z : ℕ}
    (hcop : a.Coprime b) (h : a * b = z ^ 2) :
    ∃ r s : ℕ, a = r ^ 2 ∧ b = s ^ 2 := by
  have haEven : ∀ p, Even (a.factorization p) := fun p =>
    (Nat_even_factorization_of_coprime_mul_eq_sq (a := a) (b := b) (z := z) (p := p) hcop h).1
  have hbEven : ∀ p, Even (b.factorization p) := fun p =>
    (Nat_even_factorization_of_coprime_mul_eq_sq (a := a) (b := b) (z := z) (p := p) hcop h).2
  rcases Nat_exists_sq_of_factorization_even haEven with ⟨r, hr⟩
  rcases Nat_exists_sq_of_factorization_even hbEven with ⟨s, hs⟩
  exact ⟨r, s, hr, hs⟩

theorem Int_coprime_mul_eq_sq_of_nonneg {a b z : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hcop : Int.gcd a b = 1)
    (h : a * b = z ^ 2) :
    ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2 := by
  let A : ℕ := a.natAbs
  let B : ℕ := b.natAbs
  let Z : ℕ := z.natAbs
  have hnat : A * B = Z ^ 2 := by
    change a.natAbs * b.natAbs = z.natAbs ^ 2
    calc
      a.natAbs * b.natAbs = (a * b).natAbs := by simpa using (Int.natAbs_mul a b).symm
      _ = (z ^ 2).natAbs := by rw [h]
      _ = z.natAbs ^ 2 := by simp
  have hcopNat : A.Coprime B := by
    change Nat.gcd a.natAbs b.natAbs = 1
    simpa [A, B, Int.gcd_def] using hcop
  rcases Nat_coprime_mul_eq_sq hcopNat hnat with ⟨r, s, hr, hs⟩
  refine ⟨(r : ℤ), (s : ℤ), ?_, ?_⟩
  · calc
      a = (A : ℤ) := by simpa [A] using (Int.natAbs_of_nonneg ha).symm
      _ = (r : ℤ) ^ 2 := by simpa using congrArg (fun n : ℕ => (n : ℤ)) hr
  · calc
      b = (B : ℤ) := by simpa [B] using (Int.natAbs_of_nonneg hb).symm
      _ = (s : ℤ) ^ 2 := by simpa using congrArg (fun n : ℕ => (n : ℤ)) hs

end FLT.N12
```

## Notes

The Nat helper is the reusable core:

```lean
theorem Nat_coprime_mul_eq_sq {a b z : ℕ}
    (hcop : a.Coprime b) (h : a * b = z ^ 2) :
    ∃ r s : ℕ, a = r ^ 2 ∧ b = s ^ 2
```

The Int wrapper is the requested API:

```lean
theorem Int_coprime_mul_eq_sq_of_nonneg {a b z : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hcop : Int.gcd a b = 1)
    (h : a * b = z ^ 2) :
    ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2
```

Zero cases are handled by `Nat_exists_sq_of_factorization_even`: it branches on `n = 0` before using `Nat.eq_of_factorization_eq`, because `Nat.factorization 0 = 0` and `Nat.factorization 1 = 0`.

Key Mathlib APIs to check/grep:

```lean
#check Nat.factorization_mul_apply_of_coprime
#check Nat.factorization_pow
#check Nat.prod_pow_factorization_eq_self
#check Nat.eq_of_factorization_eq
#check Nat.dvd_of_factorization_pos
#check Nat.factorization_eq_zero_of_not_prime
#check Int.gcd_def
#check Int.natAbs_mul
#check Int.natAbs_of_nonneg
```

```bash
grep -R "factorization_mul_apply_of_coprime\|prod_pow_factorization_eq_self\|eq_of_factorization_eq" .lake/packages/mathlib/Mathlib/Data/Nat/Factorization
grep -R "dvd_of_factorization_pos\|factorization_eq_zero_of_not_prime\|factorization_pow" .lake/packages/mathlib/Mathlib/Data/Nat/Factorization
grep -R "gcd_def\|natAbs_mul\|natAbs_of_nonneg" .lake/packages/mathlib/Mathlib/Data/Int
```

For QuarticA/QuarticB split lemmas, prove the half-factors `A B : ℤ` satisfy `0 ≤ A`, `0 ≤ B`, `Int.gcd A B = 1`, and `A * B = W ^ 2`, then use:

```lean
rcases Int_coprime_mul_eq_sq_of_nonneg hA_nonneg hB_nonneg hcopAB hprod
  with ⟨r, s, hA_sq, hB_sq⟩
```

For the QuarticB “twice squares” form, define `A := (3*u^2 - v^2)/2` and `B := (u^2 + v^2)/2`, prove `A * B = (Z/2)^2`, apply the helper, then rewrite back with `ring_nf` and the evenness/divisibility facts.
