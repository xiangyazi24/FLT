# Q1409 (dm1/dm3): `quarticPlus_gcd_UV_eq_one`

The right Lean architecture is to prove the gcd statement by excluding common prime divisors of `U` and `V`.

Use this route:

```lean
rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
by_contra hnot
rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with ⟨p, hp, hpU_abs, hpV_abs⟩
```

Then convert `p ∣ U.natAbs`, `p ∣ V.natAbs` to integer divisibility using `Int.natCast_dvd`.

The exact API-heavy lemma to isolate is `quarticPlus_common_prime_UV_false`. Once that lemma is proved, the final theorem is short.

```lean
import Mathlib

namespace DM3

abbrev U (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
abbrev V (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

lemma U_odd_of_B_odd {r B s : ℤ} (hBodd : Odd B) : Odd (U r B s) := by
  dsimp [U]
  have h2r2 : Even (2 * r ^ 2) := (even_two : Even (2 : ℤ)).mul_right (r ^ 2)
  have h2s : Even (2 * s) := (even_two : Even (2 : ℤ)).mul_right s
  have hB2 : Odd (B ^ 2) := hBodd.pow
  exact (h2r2.add_odd hB2).sub_even h2s

lemma V_odd_of_B_odd {r B s : ℤ} (hBodd : Odd B) : Odd (V r B s) := by
  dsimp [V]
  have h2r2 : Even (2 * r ^ 2) := (even_two : Even (2 : ℤ)).mul_right (r ^ 2)
  have h2s : Even (2 * s) := (even_two : Even (2 : ℤ)).mul_right s
  have hB2 : Odd (B ^ 2) := hBodd.pow
  exact (h2r2.add_odd hB2).add_even h2s

/--
Exact local lemma: no prime can divide both `U` and `V`.

Proof outline:
from a common prime divisor get divisibility of `s` and `2*r^2+B^2`; squaring and
subtracting gives divisibility of `5*B^4` by the square of the prime. If the
prime divides `B`, coprimality of `r,B` is contradicted. Otherwise primality
forces the prime to be `5`, and the square divisibility then forces `5 ∣ B`,
again a contradiction.
-/
lemma quarticPlus_common_prime_UV_false
    {r B s : ℤ} {p : ℕ}
    (hp : Nat.Prime p)
    (hpU : (p : ℤ) ∣ U r B s)
    (hpV : (p : ℤ) ∣ V r B s)
    (hgcd : Int.gcd r B = 1)
    (hBodd : Odd B)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    False := by
  -- This is the only remaining non-mechanical proof.
  -- It is a prime-divisor argument in `ℤ`; keep it separate from the wrapper.
  sorry

/-- GCD of the two quartic factors. -/
theorem quarticPlus_gcd_UV_eq_one
    {r B s : ℤ}
    (hUV : U r B s * V r B s = 5 * B ^ 4)
    (hgcd : Int.gcd r B = 1)
    (hr : 0 < r) (hB : 0 < B)
    (hBodd : Odd B)
    (hspos : 0 < s)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    Int.gcd (U r B s) (V r B s) = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one, Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with ⟨p, hp, hpU_abs, hpV_abs⟩

  have hpU : (p : ℤ) ∣ U r B s := by
    exact Int.natCast_dvd.mpr hpU_abs

  have hpV : (p : ℤ) ∣ V r B s := by
    exact Int.natCast_dvd.mpr hpV_abs

  exact quarticPlus_common_prime_UV_false
    (r := r) (B := B) (s := s) hp hpU hpV hgcd hBodd hs

end DM3
```

The final wrapper is the part to use downstream. The isolated lemma `quarticPlus_common_prime_UV_false` is where the exact integer-prime divisibility API work belongs.
