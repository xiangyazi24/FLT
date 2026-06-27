# Q1425 (dm1/dm4): denominator of `u^3 + u^2 - u`

The useful API fact is this actual Mathlib theorem from `Mathlib.Data.Rat.Lemmas`:

```lean
Rat.den_div_eq_of_coprime
  {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
  ((a / b : ℚ).den : ℤ) = b
```

So the denominator theorem should be proved with an integer numerator and a positive integer denominator cast to `ℤ`.  The key coprimality step is exactly the one you described:

```text
N = a^3 + a^2*d - a*d^2
  = a^3 + d*(a^2 - a*d),
```

so `gcd(N,d)=gcd(a^3,d)=1`, and then `gcd(N,d^3)=1`.

Here is the Lean code with the requested import.

```lean
import Mathlib.Data.Rat.Lemmas

namespace DM4

/-- Coprimality of the cubic numerator with the original denominator. -/
lemma cubic_num_coprime_den
    (a : ℤ) (d : ℕ)
    (had : Nat.Coprime a.natAbs d) :
    Nat.Coprime
      (a ^ 3 + a ^ 2 * (d : ℤ) - a * (d : ℤ) ^ 2).natAbs
      (d ^ 3) := by
  let N : ℤ := a ^ 3 + a ^ 2 * (d : ℤ) - a * (d : ℤ) ^ 2

  have had3' : Nat.Coprime ((a.natAbs * a.natAbs) * a.natAbs) d :=
    (had.mul_left had).mul_left had
  have had3 : Nat.Coprime (a.natAbs ^ 3) d := by
    simpa [pow_succ, pow_two, mul_assoc] using had3'

  have hN_rewrite : N = a ^ 3 + (d : ℤ) * (a ^ 2 - a * (d : ℤ)) := by
    dsimp [N]
    simp [mul_sub, pow_two, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_comm, mul_left_comm]

  have hNgcd_d : Int.gcd N (d : ℤ) = 1 := by
    calc
      Int.gcd N (d : ℤ)
          = Int.gcd (a ^ 3 + (d : ℤ) * (a ^ 2 - a * (d : ℤ))) (d : ℤ) := by
              rw [hN_rewrite]
      _ = Int.gcd (a ^ 3) (d : ℤ) := by
              rw [Int.gcd_add_mul_left_left]
      _ = 1 := by
              change Nat.gcd (a ^ 3).natAbs ((d : ℤ).natAbs) = 1
              rw [Int.natAbs_pow]
              simpa using had3

  have hNd : Nat.Coprime N.natAbs d := by
    change Nat.gcd N.natAbs d = 1
    simpa [Int.gcd_def] using hNgcd_d

  have hNd3' : Nat.Coprime N.natAbs ((d * d) * d) :=
    (hNd.mul_right hNd).mul_right hNd
  have hNd3 : Nat.Coprime N.natAbs (d ^ 3) := by
    simpa [pow_succ, pow_two, mul_assoc] using hNd3'

  simpa [N] using hNd3

/-- Main denominator computation. -/
theorem den_cubic_num_den (u : ℚ) :
    (u ^ 3 + u ^ 2 - u).den = u.den ^ 3 := by
  let a : ℤ := u.num
  let d : ℕ := u.den
  let D : ℤ := (d ^ 3 : ℕ)
  let N : ℤ := a ^ 3 + a ^ 2 * (d : ℤ) - a * (d : ℤ) ^ 2

  have hdpos_nat : 0 < d := by
    dsimp [d]
    exact Rat.pos u
  have hdne : (d : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (Nat.ne_of_gt hdpos_nat)
  have hd2ne : ((d ^ 2 : ℕ) : ℤ) ≠ 0 := by
    exact Int.natCast_ne_zero.mpr (pow_ne_zero 2 (Nat.ne_of_gt hdpos_nat))
  have hDpos : 0 < D := by
    dsimp [D]
    exact Int.natCast_pos.mpr (Nat.pow_pos hdpos_nat 3)
  have hDne : D ≠ 0 := ne_of_gt hDpos

  have had : Nat.Coprime a.natAbs d := by
    dsimp [a, d]
    simpa using u.reduced

  have hNd3 : Nat.Coprime N.natAbs (d ^ 3) := by
    dsimp [N]
    exact cubic_num_coprime_den a d had

  have hNd3_D : Nat.Coprime N.natAbs D.natAbs := by
    dsimp [D]
    simpa using hNd3

  have hu : u = a /. (d : ℤ) := by
    dsimp [a, d]
    exact (Rat.num_divInt_den u).symm

  have hu3 : u ^ 3 = a ^ 3 /. D := by
    dsimp [a, d, D]
    simpa using Rat.pow_eq_divInt u 3

  have hu2_raw : u ^ 2 = a ^ 2 /. ((d ^ 2 : ℕ) : ℤ) := by
    dsimp [a, d]
    simpa using Rat.pow_eq_divInt u 2

  have hu2 : u ^ 2 = (a ^ 2 * (d : ℤ)) /. D := by
    rw [hu2_raw]
    apply (Rat.divInt_eq_divInt_iff hd2ne hDne).mpr
    simp [D, Int.natCast_pow, pow_succ, pow_two,
      mul_assoc, mul_comm, mul_left_comm]

  have hu1 : u = (a * (d : ℤ) ^ 2) /. D := by
    rw [hu]
    apply (Rat.divInt_eq_divInt_iff hdne hDne).mpr
    simp [D, Int.natCast_pow, pow_succ, pow_two,
      mul_assoc, mul_comm, mul_left_comm]

  have hrepr : u ^ 3 + u ^ 2 - u = N /. D := by
    rw [hu3, hu2, hu1]
    dsimp [N]
    rw [sub_eq_add_neg, Rat.neg_divInt]
    rw [← Rat.add_divInt, ← Rat.add_divInt]
    simp [sub_eq_add_neg, add_assoc]

  have hden_div : ((N /. D).den : ℤ) = D := by
    rw [← Rat.intCast_div_eq_divInt N D]
    exact Rat.den_div_eq_of_coprime hDpos hNd3_D

  rw [← Int.ofNat_inj]
  change (((u ^ 3 + u ^ 2 - u).den : ℤ) = ((d ^ 3 : ℕ) : ℤ))
  rw [hrepr]
  simpa [D] using hden_div

end DM4
```

If your local goal uses the exact name `den_cubic_num_den`, the theorem above can be pasted as-is and then called as:

```lean
DM4.den_cubic_num_den u
```
