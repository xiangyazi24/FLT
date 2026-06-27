# Q1384 (dm1/dm2): `den_cubic_num_den`

The numerator for

```lean
u ^ 3 + u ^ 2 - u
```

over denominator `u.den^3` is

```lean
u.num ^ 3 + u.num ^ 2 * (u.den : ℤ) - u.num * (u.den : ℤ) ^ 2
```

not the earlier fourth-power expression from the later quartic equation.

Here is the intended Lean proof.  The coprimality is easiest over `IsCoprime` in `ℤ`: first prove the numerator is coprime to `u.den`, then multiply the right side three times.

```lean
import Mathlib

namespace DM2

/-- Numerator of `u^3+u^2-u` over denominator `u.den^3`. -/
def cubicNum (u : ℚ) : ℤ :=
  u.num ^ 3 + u.num ^ 2 * (u.den : ℤ) - u.num * (u.den : ℤ) ^ 2

/-- The cubic numerator is coprime to `u.den`. -/
lemma cubicNum_isCoprime_den (u : ℚ) :
    IsCoprime (cubicNum u) (u.den : ℤ) := by
  let a : ℤ := u.num
  let d : ℤ := u.den

  have had : IsCoprime a d := by
    simpa [a, d] using Rat.isCoprime_num_den u

  have ha2d : IsCoprime (a ^ 2) d := by
    simpa [pow_two] using (had.mul_left had)

  -- `a^2 + a*d - d^2 = a^2 + d*(a-d)`, so it is coprime to `d`.
  have hquad0 : IsCoprime (a ^ 2 + d * (a - d)) d :=
    ha2d.add_mul_left_left (a - d)

  have hquad : IsCoprime (a ^ 2 + a * d - d ^ 2) d := by
    convert hquad0 using 1 <;> ring

  have hprod : IsCoprime (a * (a ^ 2 + a * d - d ^ 2)) d :=
    had.mul_left hquad

  convert hprod using 1 <;> simp [cubicNum, a, d] <;> ring

/-- The cubic numerator is coprime to `u.den^3`, as an integer. -/
lemma cubicNum_isCoprime_den_pow3 (u : ℚ) :
    IsCoprime (cubicNum u) ((u.den : ℤ) ^ 3) := by
  have h1 : IsCoprime (cubicNum u) (u.den : ℤ) :=
    cubicNum_isCoprime_den u
  have h2 : IsCoprime (cubicNum u) ((u.den : ℤ) * (u.den : ℤ)) :=
    h1.mul_right h1
  have h3 :
      IsCoprime (cubicNum u)
        ((u.den : ℤ) * ((u.den : ℤ) * (u.den : ℤ))) :=
    h1.mul_right h2
  convert h3 using 1 <;> ring

/-- The same coprimality in the `Nat.Coprime` form used by `den_div_eq_of_coprime`. -/
lemma cubicNum_natCoprime_den_pow3 (u : ℚ) :
    Nat.Coprime (cubicNum u).natAbs (((u.den : ℤ) ^ 3).natAbs) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg : Int.gcd (cubicNum u) ((u.den : ℤ) ^ 3) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp (cubicNum_isCoprime_den_pow3 u)
  simpa [Int.gcd_def] using hg

/-- Main helper: denominator of `u^3+u^2-u` is `u.den^3`. -/
lemma den_cubic_num_den (u : ℚ) :
    (u ^ 3 + u ^ 2 - u).den = u.den ^ 3 := by
  let N : ℤ := cubicNum u

  have hdq : ((u.den : ℚ) ≠ 0) := by
    exact_mod_cast u.den_ne_zero

  have hdposZ : 0 < ((u.den : ℤ) ^ 3) := by
    have hdpos : 0 < (u.den : ℤ) := by exact_mod_cast u.den_pos
    positivity

  have hrepr :
      u ^ 3 + u ^ 2 - u = N /. ((u.den : ℤ) ^ 3) := by
    rw [← Rat.num_div_den u]
    rw [Rat.divInt_eq_div]
    field_simp [hdq]
    simp [N, cubicNum]
    ring

  rw [hrepr]

  have hcop : Nat.Coprime N.natAbs (((u.den : ℤ) ^ 3).natAbs) := by
    simpa [N] using cubicNum_natCoprime_den_pow3 u

  have hden :=
    Rat.den_div_eq_of_coprime
      (a := N) (b := ((u.den : ℤ) ^ 3)) hdposZ hcop

  have habs : (((u.den : ℤ) ^ 3).natAbs) = u.den ^ 3 := by
    simpa using (Int.natAbs_pow (u.den : ℤ) 3)

  simpa [habs] using hden

end DM2
```

If your local snapshot exposes the final denominator theorem unqualified, replace

```lean
Rat.den_div_eq_of_coprime
```

by

```lean
den_div_eq_of_coprime
```

inside `namespace Rat`; the arguments are the same: numerator, positive integer denominator, and the `Nat.Coprime` proof.
