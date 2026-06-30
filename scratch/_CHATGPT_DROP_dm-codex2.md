# Q2505 WeakPrimitiveAPParity Lean route

Use the integer parity route, not `ZMod 4`.  The proof below is meant to be pasted after the current definitions inside the existing namespace

```lean
namespace MazurProof.RationalPointsN12
```

Do not repeat the namespace or the definitions of `rootGCD4` / `WeakPrimitiveAPParity` when pasting into the current file.

Required imports, if the file does not already have them:

```lean
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic
```

Paste-after-definitions code:

```lean
private theorem n12_sq_eq_four_mul_of_even {n : ℤ} (hn : Even n) :
    ∃ k : ℤ, n ^ 2 = 4 * k := by
  rcases hn with ⟨t, rfl⟩
  refine ⟨t ^ 2, ?_⟩
  ring

private theorem n12_sq_eq_four_mul_add_one_of_odd {n : ℤ} (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 4 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  refine ⟨t ^ 2 + t, ?_⟩
  ring

private theorem n12_sq_eq_eight_mul_add_one_of_odd {n : ℤ} (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  rcases Int.two_dvd_mul_add_one t with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
    _ = 4 * (2 * u) + 1 := by rw [hu]
    _ = 8 * u + 1 := by ring

private theorem n12_eight_dvd_sq_sub_sq_of_odd {a b : ℤ}
    (ha : Odd a) (hb : Odd b) :
    (8 : ℤ) ∣ a ^ 2 - b ^ 2 := by
  rcases n12_sq_eq_eight_mul_add_one_of_odd ha with ⟨A, hA⟩
  rcases n12_sq_eq_eight_mul_add_one_of_odd hb with ⟨B, hB⟩
  refine ⟨A - B, ?_⟩
  rw [hA, hB]
  ring

/--
Parity classifier for the midpoint equation of three squares in arithmetic progression.
If `a^2, b^2, c^2` are in arithmetic progression, then `a,b,c` are either all
odd or all even.
-/
private theorem n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq
    {a b c : ℤ}
    (h : a ^ 2 + c ^ 2 = 2 * b ^ 2) :
    (Odd a ∧ Odd b ∧ Odd c) ∨ (Even a ∧ Even b ∧ Even c) := by
  rcases Int.even_or_odd a with haEven | haOdd
  · rcases Int.even_or_odd b with hbEven | hbOdd
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exact Or.inr ⟨haEven, hbEven, hcEven⟩
      · exfalso
        rcases n12_sq_eq_four_mul_of_even haEven with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_of_even hbEven with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hcOdd with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exfalso
        rcases n12_sq_eq_four_mul_of_even haEven with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hbOdd with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_of_even hcEven with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
      · exfalso
        rcases n12_sq_eq_four_mul_of_even haEven with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hbOdd with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hcOdd with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
  · rcases Int.even_or_odd b with hbEven | hbOdd
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exfalso
        rcases n12_sq_eq_four_mul_add_one_of_odd haOdd with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_of_even hbEven with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_of_even hcEven with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
      · exfalso
        rcases n12_sq_eq_four_mul_add_one_of_odd haOdd with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_of_even hbEven with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hcOdd with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
    · rcases Int.even_or_odd c with hcEven | hcOdd
      · exfalso
        rcases n12_sq_eq_four_mul_add_one_of_odd haOdd with ⟨A, hA⟩
        rcases n12_sq_eq_four_mul_add_one_of_odd hbOdd with ⟨B, hB⟩
        rcases n12_sq_eq_four_mul_of_even hcEven with ⟨C, hC⟩
        rw [hA, hB, hC] at h
        omega
      · exact Or.inl ⟨haOdd, hbOdd, hcOdd⟩

private theorem n12_rootGCD4_ne_one_of_all_even {p q r s : ℤ}
    (hp : Even p) (hq : Even q) (hr : Even r) (hs : Even s) :
    rootGCD4 p q r s ≠ 1 := by
  have h2p : 2 ∣ p.natAbs := by
    have hpAbs : Even p.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hpAbs
  have h2q : 2 ∣ q.natAbs := by
    have hqAbs : Even q.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hqAbs
  have h2r : 2 ∣ r.natAbs := by
    have hrAbs : Even r.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hrAbs
  have h2s : 2 ∣ s.natAbs := by
    have hsAbs : Even s.natAbs := by
      rwa [Int.natAbs_even]
    exact even_iff_two_dvd.mp hsAbs
  have h2g : 2 ∣ rootGCD4 p q r s := by
    dsimp [rootGCD4]
    exact Nat.dvd_gcd h2p (Nat.dvd_gcd h2q (Nat.dvd_gcd h2r h2s))
  intro hprim
  have hbad : (2 : ℕ) ∣ 1 := by
    simpa [hprim] using h2g
  norm_num at hbad

/-- Weak primitive four-square APs have odd roots and square gap divisible by `8`. -/
theorem weakPrimitiveAPParity : WeakPrimitiveAPParity := by
  intro p q r s Δ hpq hrq hsr hprim
  have hpqr : p ^ 2 + r ^ 2 = 2 * q ^ 2 := by
    nlinarith [hpq, hrq]
  have hqrs : q ^ 2 + s ^ 2 = 2 * r ^ 2 := by
    nlinarith [hrq, hsr]
  rcases n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq hpqr with hpqrOdd | hpqrEven
  · rcases hpqrOdd with ⟨hpOdd, hqOdd, hrOdd⟩
    rcases n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq hqrs with hqrsOdd | hqrsEven
    · rcases hqrsOdd with ⟨_hqOdd2, _hrOdd2, hsOdd⟩
      have h8 : (8 : ℤ) ∣ Δ := by
        rw [← hpq]
        exact n12_eight_dvd_sq_sub_sq_of_odd hqOdd hpOdd
      exact ⟨Int.odd_iff.mp hpOdd,
        Int.odd_iff.mp hqOdd,
        Int.odd_iff.mp hrOdd,
        Int.odd_iff.mp hsOdd,
        h8⟩
    · rcases hqrsEven with ⟨hqEven2, _hrEven2, _hsEven⟩
      exfalso
      exact (Int.not_even_iff_odd.mpr hqOdd) hqEven2
  · rcases hpqrEven with ⟨hpEven, hqEven, hrEven⟩
    rcases n12_all_odd_or_all_even_of_sq_add_sq_eq_two_sq hqrs with hqrsOdd | hqrsEven
    · rcases hqrsOdd with ⟨hqOdd2, _hrOdd2, _hsOdd⟩
      exfalso
      exact (Int.not_even_iff_odd.mpr hqOdd2) hqEven
    · rcases hqrsEven with ⟨_hqEven2, _hrEven2, hsEven⟩
      exfalso
      exact n12_rootGCD4_ne_one_of_all_even hpEven hqEven hrEven hsEven hprim
```

Why this is preferable to the proposed `ZMod 4` proof: all congruence facts are replaced by explicit integer normal forms

```lean
Even n  -> ∃ k, n^2 = 4*k
Odd n   -> ∃ k, n^2 = 4*k + 1
Odd n   -> ∃ k, n^2 = 8*k + 1
```

and the impossible mixed-parity midpoint cases close by `omega` after rewriting.  The only Mathlib parity APIs used are `Int.even_or_odd`, `Int.natAbs_even`, `Int.odd_iff`, `Int.not_even_iff_odd`, and `Int.two_dvd_mul_add_one`.
