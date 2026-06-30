# Q2619 / Q2616 Nat eight-square coprime split

Target theorem:

```lean
theorem Nat.coprime_product_eq_eight_square_split
    {N m n : Nat}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Nat.Coprime m n)
    (hparity : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    ∃ A D : Nat,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ Nat.Coprime A D ∧
      N = A * D ∧
      ((m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
       (m = D ^ 2 ∧ n = 8 * A ^ 2))
```

The clean route is not to fight `Nat.factorization` directly in the final theorem.  Divide the even factor by `8`, reduce to a coprime product equal to a square, and use the already-imported `Int.sq_of_gcd_eq_one` from `Mathlib.NumberTheory.FLT.Four` for square extraction.

Paste this in a convenient file/namespace.  The names are under `namespace Nat`, so the final theorem has the requested fully-qualified name.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

namespace Nat

lemma exists_sq_of_coprime_mul_eq_sq_left
    {a b c : ℕ}
    (ha : 0 < a)
    (hcop : Nat.Coprime a b)
    (h : a * b = c ^ 2) :
    ∃ A : ℕ, a = A ^ 2 := by
  have hcopInt : Int.gcd (a : ℤ) (b : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hInt : (a : ℤ) * (b : ℤ) = (c : ℤ) ^ 2 := by
    exact_mod_cast h
  obtain ⟨u, hu | hu⟩ := Int.sq_of_gcd_eq_one hcopInt hInt
  · refine ⟨u.natAbs, ?_⟩
    calc
      a = Int.natAbs (a : ℤ) := by simp
      _ = Int.natAbs (u ^ 2) := by rw [hu]
      _ = u.natAbs ^ 2 := by rw [Int.natAbs_pow]
  · exfalso
    have hapos : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
    rw [hu] at hapos
    nlinarith [sq_nonneg u]

/--
If two positive coprime natural numbers multiply to a square, then both are
squares, and the square root of the product is the product of the square roots.
-/
lemma coprime_mul_eq_square_split
    {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b)
    (hcop : Nat.Coprime a b)
    (h : a * b = c ^ 2) :
    ∃ A D : ℕ,
      0 < A ∧ 0 < D ∧
      a = A ^ 2 ∧ b = D ^ 2 ∧ c = A * D := by
  obtain ⟨A, hA⟩ :=
    Nat.exists_sq_of_coprime_mul_eq_sq_left (a := a) (b := b) (c := c) ha hcop h
  obtain ⟨D, hD⟩ :=
    Nat.exists_sq_of_coprime_mul_eq_sq_left (a := b) (b := a) (c := c) hb hcop.symm
      (by simpa [mul_comm] using h)
  have hApos : 0 < A := by
    by_contra hAz
    have hA0 : A = 0 := by omega
    have ha0 : a = 0 := by
      rw [hA, hA0]
      norm_num
    exact (ne_of_gt ha) ha0
  have hDpos : 0 < D := by
    by_contra hDz
    have hD0 : D = 0 := by omega
    have hb0 : b = 0 := by
      rw [hD, hD0]
      norm_num
    exact (ne_of_gt hb) hb0
  have hsq : (A * D) ^ 2 = c ^ 2 := by
    calc
      (A * D) ^ 2 = A ^ 2 * D ^ 2 := by ring
      _ = a * b := by rw [← hA, ← hD]
      _ = c ^ 2 := h
  have hAD_eq_c : A * D = c :=
    (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) hsq
  exact ⟨A, D, hApos, hDpos, hA, hD, hAD_eq_c.symm⟩

lemma coprime_eight_left_of_odd {n : ℕ} (hn : Odd n) : Nat.Coprime 8 n := by
  have h2 : Nat.Coprime 2 n := Nat.coprime_two_left.mpr hn
  have h23 : Nat.Coprime (2 ^ 3) n := h2.pow_left 3
  simpa using h23

/--
The oriented case: the left factor is the even factor and the right factor is odd.
The `Even m` hypothesis is retained for caller symmetry; the proof only needs `Odd n`
to force all factors of `8` into `m`.
-/
lemma coprime_product_eq_eight_square_split_even_left
    {N m n : ℕ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Nat.Coprime m n)
    (_hm_even : Even m) (hn_odd : Odd n) :
    ∃ A D : ℕ,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ Nat.Coprime A D ∧
      N = A * D ∧
      m = 8 * A ^ 2 ∧ n = D ^ 2 := by
  have h8copn : Nat.Coprime 8 n := Nat.coprime_eight_left_of_odd hn_odd
  have h8dvd_mn : 8 ∣ m * n := by
    rw [hmn]
    exact dvd_mul_right 8 (N ^ 2)
  have h8dvd_m : 8 ∣ m := (h8copn.dvd_mul_right).mp h8dvd_mn
  let M : ℕ := m / 8
  have hm_eq : m = 8 * M := by
    dsimp [M]
    rw [mul_comm, Nat.div_mul_cancel h8dvd_m]
  have hquot : M * n = N ^ 2 := by
    have hmul : 8 * (M * n) = 8 * N ^ 2 := by
      calc
        8 * (M * n) = (8 * M) * n := by ring
        _ = m * n := by rw [← hm_eq]
        _ = 8 * N ^ 2 := hmn
    exact (mul_left_inj' (show (8 : ℕ) ≠ 0 by norm_num)).mp hmul
  have hMpos : 0 < M := by
    by_contra hMnot
    have hM0 : M = 0 := by omega
    have hN0 : N ^ 2 = 0 := by
      rw [← hquot, hM0]
      norm_num
    exact (pow_ne_zero 2 (ne_of_gt hNpos)) hN0
  have hMdvdm : M ∣ m := by
    refine ⟨8, ?_⟩
    rw [hm_eq]
    ring
  have hcopMn : Nat.Coprime M n := hmn_coprime.of_dvd_left hMdvdm
  obtain ⟨A, D, hApos, hDpos, hM, hDsq, hN⟩ :=
    Nat.coprime_mul_eq_square_split hMpos hnpos hcopMn hquot
  have hDodd : Odd D := by
    have hcopD2 : Nat.Coprime D 2 := by
      have hcopDsq2 : Nat.Coprime (D ^ 2) 2 := by
        rw [← hDsq]
        exact Nat.coprime_two_right.mpr hn_odd
      rwa [Nat.coprime_pow_left_iff (by norm_num : (0 : ℕ) < 2)] at hcopDsq2
    exact Nat.coprime_two_right.mp hcopD2
  have hAeven : Even A := by
    have h2dvdAD : 2 ∣ A * D := by
      rw [← hN]
      exact even_iff_two_dvd.mp hNeven
    have hcop2D : Nat.Coprime 2 D := Nat.coprime_two_left.mpr hDodd
    exact even_iff_two_dvd.mpr ((hcop2D.dvd_mul_right).mp h2dvdAD)
  have hcopAD : Nat.Coprime A D := by
    have hcopSquares : Nat.Coprime (A ^ 2) (D ^ 2) := by
      simpa [hM, hDsq] using hcopMn
    rwa [Nat.coprime_pow_left_iff (by norm_num : (0 : ℕ) < 2),
      Nat.coprime_pow_right_iff (by norm_num : (0 : ℕ) < 2)] at hcopSquares
  refine ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, ?_, hDsq⟩
  rw [hm_eq, hM]

/--
Coprime split of a positive product `m*n = 8*N^2`, with the `8` forced onto
whichever factor is even by the supplied parity alternative.
-/
theorem coprime_product_eq_eight_square_split
    {N m n : ℕ}
    (hNpos : 0 < N)
    (hNeven : Even N)
    (hmpos : 0 < m) (hnpos : 0 < n)
    (hmn : m * n = 8 * N ^ 2)
    (hmn_coprime : Nat.Coprime m n)
    (hparity : (Even m ∧ Odd n) ∨ (Odd m ∧ Even n)) :
    ∃ A D : ℕ,
      0 < A ∧ 0 < D ∧ Even A ∧ Odd D ∧ Nat.Coprime A D ∧
      N = A * D ∧
      ((m = 8 * A ^ 2 ∧ n = D ^ 2) ∨
       (m = D ^ 2 ∧ n = 8 * A ^ 2)) := by
  rcases hparity with hleft | hright
  · obtain ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, hm8, hnD⟩ :=
      Nat.coprime_product_eq_eight_square_split_even_left
        (hNpos := hNpos) (hNeven := hNeven)
        (hmpos := hmpos) (hnpos := hnpos)
        (hmn := hmn) (hmn_coprime := hmn_coprime)
        hleft.1 hleft.2
    exact ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, Or.inl ⟨hm8, hnD⟩⟩
  · obtain ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, hn8, hmD⟩ :=
      Nat.coprime_product_eq_eight_square_split_even_left
        (N := N) (m := n) (n := m)
        (hNpos := hNpos) (hNeven := hNeven)
        (hmpos := hnpos) (hnpos := hmpos)
        (hmn := by simpa [mul_comm] using hmn)
        (hmn_coprime := hmn_coprime.symm)
        hright.2 hright.1
    exact ⟨A, D, hApos, hDpos, hAeven, hDodd, hcopAD, hN, Or.inr ⟨hmD, hn8⟩⟩

end Nat
```

## Lemma DAG

The intended dependency graph is:

```text
Nat.exists_sq_of_coprime_mul_eq_sq_left
  uses Int.sq_of_gcd_eq_one

Nat.coprime_mul_eq_square_split
  uses exists_sq_of_coprime_mul_eq_sq_left twice
  uses Nat.pow_left_injective to identify c = A*D

Nat.coprime_eight_left_of_odd
  uses Nat.coprime_two_left and Coprime.pow_left

Nat.coprime_product_eq_eight_square_split_even_left
  uses coprime_eight_left_of_odd to prove 8 | m
  sets M = m / 8
  proves M*n = N^2
  applies coprime_mul_eq_square_split to M and n
  proves Odd D from n = D^2 and Odd n
  proves Even A from N = A*D, Even N, Odd D
  proves Coprime A D by rewriting Coprime (A^2) (D^2)

Nat.coprime_product_eq_eight_square_split
  splits on the parity disjunction
  applies the even-left lemma directly or with m/n swapped
```

If a local Mathlib version has a slightly different method name for the `Nat.Coprime` divisibility helpers, the only expected substitutions are:

```lean
(h8copn.dvd_mul_right).mp h8dvd_mn
-- can be replaced by
h8copn.dvd_of_dvd_mul_right h8dvd_mn
```

and similarly for the line extracting `2 ∣ A` from `2 ∣ A*D`.
