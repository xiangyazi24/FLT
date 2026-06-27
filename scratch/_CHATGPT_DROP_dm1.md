# Q1354 (dm1/dm3): the `U,V` factor lemmas

There are two important corrections.

First, the clean proof of positivity is **not** the analytic estimate for `s`; it is algebraic:

```text
U*V = 5*B^4 > 0,
U+V = 2*(2*r^2+B^2) > 0.
```

A positive product says `U,V` have the same sign; a positive sum rules out both negative.

Second, the gcd proof is the nontrivial part. From a common odd prime divisor you get divisibility of `s` and `2*r^2+B^2`, hence it divides `5*r^4`; then coprimality with `r` leaves only the possible prime `5`, which must be excluded by a mod-5 square-residue argument. Do not expect `ring`/`linarith` to prove the gcd lemma directly.

Below are the mechanical Lean pieces for (a), (b), and (d), plus the correct interface for (c).

```lean
import Mathlib

namespace DM3

abbrev U (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 - 2 * s
abbrev V (r B s : ℤ) : ℤ := 2 * r ^ 2 + B ^ 2 + 2 * s

/-- (a) The basic factor identity. -/
lemma UV_mul_eq_five_mul_B4 {r B s : ℤ}
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    U r B s * V r B s = 5 * B ^ 4 := by
  calc
    U r B s * V r B s = (2 * r ^ 2 + B ^ 2) ^ 2 - (2 * s) ^ 2 := by
      dsimp [U, V]
      ring
    _ = 5 * B ^ 4 := by
      rw [hs]
      ring

lemma UV_add_eq (r B s : ℤ) :
    U r B s + V r B s = 2 * (2 * r ^ 2 + B ^ 2) := by
  dsimp [U, V]
  ring

/-- (b) Positivity of both factors, using product positive plus sum positive. -/
lemma UV_pos {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    0 < U r B s ∧ 0 < V r B s := by
  have hprod : 0 < U r B s * V r B s := by
    rw [UV_mul_eq_five_mul_B4 hs]
    positivity
  have hsum : 0 < U r B s + V r B s := by
    rw [UV_add_eq]
    positivity
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos
  · exfalso
    have hsum_neg : U r B s + V r B s < 0 := add_neg hneg.1 hneg.2
    linarith

/-- (d) The factor `U` is odd. -/
lemma U_odd {r B s : ℤ} (hr_odd : Odd r) (hB_odd : Odd B) :
    Odd (U r B s) := by
  dsimp [U]
  have h2r2 : Even (2 * r ^ 2) := (even_two : Even (2 : ℤ)).mul_right (r ^ 2)
  have h2s : Even (2 * s) := (even_two : Even (2 : ℤ)).mul_right s
  have hB2 : Odd (B ^ 2) := hB_odd.pow
  exact (h2r2.add_odd hB2).sub_even h2s

/-- (d) The factor `V` is odd. -/
lemma V_odd {r B s : ℤ} (hr_odd : Odd r) (hB_odd : Odd B) :
    Odd (V r B s) := by
  dsimp [V]
  have h2r2 : Even (2 * r ^ 2) := (even_two : Even (2 : ℤ)).mul_right (r ^ 2)
  have h2s : Even (2 * s) := (even_two : Even (2 : ℤ)).mul_right s
  have hB2 : Odd (B ^ 2) := hB_odd.pow
  exact (h2r2.add_odd hB2).add_even h2s

end DM3
```

## The missing gcd lemma

The correct lemma to prove separately is:

```lean
namespace DM3

/--
(c) The gcd lemma.  This is the real arithmetic part: it needs the common-prime
argument plus the exclusion of the common prime `5` by a mod-5 square-residue check.
-/
lemma UV_gcd_eq_one
    {r B s : ℤ}
    (hr : 0 < r) (hB : 0 < B)
    (hr_odd : Odd r) (hB_odd : Odd B)
    (hgcd : Int.gcd r B = 1)
    (hs : s ^ 2 = r ^ 4 + r ^ 2 * B ^ 2 - B ^ 4) :
    Int.gcd (U r B s) (V r B s) = 1 := by
  -- Recommended proof structure:
  -- 1. By contradiction, get a prime p dividing gcd(U,V).
  -- 2. Since U,V are odd, prove p ≠ 2.
  -- 3. From p ∣ V-U = 4*s and p ≠ 2, get p ∣ s.
  -- 4. From p ∣ U+V = 2*(2*r^2+B^2) and p ≠ 2, get p ∣ 2*r^2+B^2.
  -- 5. Reduce `hs` modulo p to get p ∣ 5*r^4.
  -- 6. Use `hgcd` to prove p ∤ r, hence p ∣ 5, hence p = 5.
  -- 7. Exclude p = 5: from `5 ∣ 2*r^2+B^2`, with gcd(r,B)=1, get
  --      (B*r^{-1})^2 ≡ -2 ≡ 3 mod 5,
  --    impossible because the nonzero squares mod 5 are only 1 and 4.
  -- This is not a `ring` or `linarith` lemma; make steps 5--7 separate helpers.
  sorry

end DM3
```

Suggested helper names:

```lean
lemma common_prime_dvd_five_of_dvd_UV ... : p ∣ 5
lemma not_five_dvd_common_UV ... : ¬ (5 : ℤ) ∣ Int.gcd (U r B s) (V r B s)
```

Once those are proved, `UV_gcd_eq_one` is short. But the full gcd proof is not available from the hypotheses by a one-line tactic.
