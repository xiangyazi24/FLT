# Lean drop for dm-codex3: denominator residual after `B^2 ∣ (C - z^3) * (C + z^3)`

This is Lean-level guidance for `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.  I am assuming the already-compiled layer described in the prompt, especially that for the produced `z,k` one has

```lean
Int.gcd z B = 1
Int.gcd C B = 1
B ^ 2 ∣ C ^ 2 - z ^ 6
B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)
```

The next useful layer should be an odd-prime splitting layer.  Do not try to prove a global statement like

```lean
B ^ 2 ∣ C - z ^ 3 ∨ B ^ 2 ∣ C + z ^ 3
```

for composite `B`: different odd prime powers of `B` may choose different signs.  Also keep `p = 2` separate; modulo `2^n`, square roots of `1` have the usual extra 2-adic behavior once `n` is large.

## 1. Suggested lemma layer

Here is the layer I would add immediately after the existing `B ^ 2 ∣ (C - z^3) * (C + z^3)` theorem.  The statements are intentionally local and do not mention `k`.

```lean
import Mathlib

namespace FLT
namespace MazurProof

section OddPrimeSplitting

/-!
The key convention is: primes are `p : ℕ`, divisibility of integer
expressions is by `(p : ℤ)`.  This avoids negative integer primes and keeps
`Nat.Prime` available.
-/

theorem int_natPrime_not_dvd_of_dvd_right_of_gcd_eq_one
    {x B : ℤ} {p : ℕ} (hp : p.Prime)
    (hpB : (p : ℤ) ∣ B)
    (hxB : Int.gcd x B = 1) :
    ¬ ((p : ℤ) ∣ x) := by
  intro hpx
  have hpgcdZ : (p : ℤ) ∣ (Int.gcd x B : ℤ) := by
    -- Check the orientation in your Mathlib with:
    --   #check Int.dvd_coe_gcd
    -- In recent Mathlib this is usually the `.mpr` or `.2` direction.
    exact (Int.dvd_coe_gcd).2 ⟨hpx, hpB⟩
  have hpgcdN : p ∣ Int.gcd x B := by
    exact_mod_cast hpgcdZ
  rw [hxB] at hpgcdN
  exact hp.not_dvd_one hpgcdN

/-- Odd prime divisors of `B` cannot divide `2*z^3` when `gcd z B = 1`. -/
theorem odd_natPrime_not_dvd_two_mul_cube_of_gcd_eq_one
    {z B : ℤ} {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hzB : Int.gcd z B = 1) :
    ¬ ((p : ℤ) ∣ 2 * z ^ 3) := by
  intro h
  have hpZ : Prime (p : ℤ) := by
    -- If this exact cast fails, use the local theorem connecting
    -- `Nat.Prime p` with `Prime (p : ℤ)`; common names include
    -- `Int.prime_iff_natAbs_prime` or a `norm_num`/`exact_mod_cast` proof.
    exact_mod_cast hp
  have hz_not : ¬ ((p : ℤ) ∣ z) :=
    int_natPrime_not_dvd_of_dvd_right_of_gcd_eq_one
      (x := z) (B := B) hp hpB hzB
  rcases hpZ.dvd_or_dvd h with h2 | hz3
  · have h2N : p ∣ (2 : ℕ) := by
      exact_mod_cast h2
    have hp_eq_two : p = 2 := by
      -- Depending on Mathlib revision, one of these is usually accepted:
      --   exact hp.eq_of_dvd_of_prime Nat.prime_two h2N
      --   exact (Nat.Prime.dvd_prime hp Nat.prime_two).1 h2N
      exact hp.eq_of_dvd_of_prime Nat.prime_two h2N
    exact hpodd hp_eq_two
  · have hz : (p : ℤ) ∣ z := by
      -- API name is usually `Prime.dvd_of_dvd_pow`.
      exact hpZ.dvd_of_dvd_pow hz3
    exact hz_not hz

/-- An odd prime divisor of `B` cannot divide both linear factors. -/
theorem odd_natPrime_not_dvd_both_pm_of_dvd_B
    {B C z : ℤ} {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hzB : Int.gcd z B = 1) :
    ¬ (((p : ℤ) ∣ C - z ^ 3) ∧ ((p : ℤ) ∣ C + z ^ 3)) := by
  intro hboth
  have hdiff : (p : ℤ) ∣ (C + z ^ 3) - (C - z ^ 3) := by
    exact dvd_sub hboth.2 hboth.1
  have htwoz : (p : ℤ) ∣ 2 * z ^ 3 := by
    convert hdiff using 1
    ring
  exact
    (odd_natPrime_not_dvd_two_mul_cube_of_gcd_eq_one
      (z := z) (B := B) hp hpodd hpB hzB) htwoz

/-- Any prime divisor of `B` divides at least one of the two linear factors. -/
theorem natPrime_dvd_sub_or_add_of_dvd_B_sq_pm_product
    {B C z : ℤ} {p : ℕ} (hp : p.Prime)
    (hpB : (p : ℤ) ∣ B)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ((p : ℤ) ∣ C - z ^ 3) ∨ ((p : ℤ) ∣ C + z ^ 3) := by
  have hpB2 : (p : ℤ) ∣ B ^ 2 := by
    have : (p : ℤ) ∣ B * B := dvd_mul_of_dvd_left hpB B
    simpa [pow_two] using this
  have hprod : (p : ℤ) ∣ (C - z ^ 3) * (C + z ^ 3) :=
    dvd_trans hpB2 hdiv
  have hpZ : Prime (p : ℤ) := by
    exact_mod_cast hp
  exact hpZ.dvd_or_dvd hprod

/-- Combining the previous two lemmas: odd prime divisors of `B` choose exactly one sign. -/
theorem odd_natPrime_dvd_exactly_one_pm_of_dvd_B_sq_pm_product
    {B C z : ℤ} {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hzB : Int.gcd z B = 1)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    (((p : ℤ) ∣ C - z ^ 3) ∧ ¬ ((p : ℤ) ∣ C + z ^ 3)) ∨
      (((p : ℤ) ∣ C + z ^ 3) ∧ ¬ ((p : ℤ) ∣ C - z ^ 3)) := by
  have hchoice :=
    natPrime_dvd_sub_or_add_of_dvd_B_sq_pm_product
      (B := B) (C := C) (z := z) hp hpB hdiv
  have hnotboth :=
    odd_natPrime_not_dvd_both_pm_of_dvd_B
      (B := B) (C := C) (z := z) hp hpodd hpB hzB
  rcases hchoice with hminus | hplus
  · refine Or.inl ⟨hminus, ?_⟩
    intro hplus
    exact hnotboth ⟨hminus, hplus⟩
  · refine Or.inr ⟨hplus, ?_⟩
    intro hminus
    exact hnotboth ⟨hminus, hplus⟩

/--
Prime-power Euclid splitting over `ℤ`.  This is the reusable workhorse for
turning sign choice modulo `p` into a divisibility statement modulo `p^(2e)`.
-/
theorem int_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
    {a b : ℤ} {p n : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ^ n ∣ a * b)
    (hb : ¬ ((p : ℤ) ∣ b)) :
    (p : ℤ) ^ n ∣ a := by
  -- Preferred proof route:
  --   1. get `Prime (p : ℤ)` from `hp`;
  --   2. prove `IsCoprime (p : ℤ) b` from `hb`;
  --   3. use `IsCoprime.pow_left` to get `IsCoprime ((p : ℤ)^n) b`;
  --   4. use `IsCoprime.dvd_of_dvd_mul_right` or its left/right variant.
  -- Alternative robust route: induction on `n`, using `Prime.dvd_or_dvd`
  -- and cancellation after writing `a = p * a'`.
  sorry

/--
If `p^e ∣ B`, then the whole `p^(2e)` contribution to `B^2` lands in the
chosen sign.  This is the main local output of the denominator congruence.
-/
theorem odd_natPrime_pow_dvd_exactly_one_pm_of_pow_dvd_B
    {B C z : ℤ} {p e : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (he : 0 < e)
    (hpBe : (p : ℤ) ^ e ∣ B)
    (hzB : Int.gcd z B = 1)
    (hdiv : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    (((p : ℤ) ^ (2 * e) ∣ C - z ^ 3) ∧ ¬ ((p : ℤ) ∣ C + z ^ 3)) ∨
      (((p : ℤ) ^ (2 * e) ∣ C + z ^ 3) ∧ ¬ ((p : ℤ) ∣ C - z ^ 3)) := by
  have hpB : (p : ℤ) ∣ B := by
    have hp_dvd_pow : (p : ℤ) ∣ (p : ℤ) ^ e := by
      -- `exact dvd_pow_self _ he` may need a variant for semirings/rings.
      exact dvd_pow_self (p : ℤ) he
    exact dvd_trans hp_dvd_pow hpBe
  have hsign :=
    odd_natPrime_dvd_exactly_one_pm_of_dvd_B_sq_pm_product
      (B := B) (C := C) (z := z) hp hpodd hpB hzB hdiv
  have hpowprod : (p : ℤ) ^ (2 * e) ∣ (C - z ^ 3) * (C + z ^ 3) := by
    have hB2 : ((p : ℤ) ^ e) ^ 2 ∣ B ^ 2 := by
      exact pow_dvd_pow_of_dvd hpBe 2
    have hB2' : (p : ℤ) ^ (2 * e) ∣ B ^ 2 := by
      -- `pow_mul`, `pow_two`, and commutativity of multiplication in exponents
      -- are the expected simplifiers here.
      -- One possible proof shape:
      --   simpa [pow_mul, pow_two, Nat.mul_comm, Nat.mul_left_comm,
      --     Nat.mul_assoc] using hB2
      sorry
    exact dvd_trans hB2' hdiv
  rcases hsign with ⟨hminus, hnotplus⟩ | ⟨hplus, hnotminus⟩
  · refine Or.inl ⟨?_, hnotplus⟩
    exact
      int_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
        (a := C - z ^ 3) (b := C + z ^ 3) hp hpowprod hnotplus
  · refine Or.inr ⟨?_, hnotminus⟩
    have hpowprod' : (p : ℤ) ^ (2 * e) ∣ (C + z ^ 3) * (C - z ^ 3) := by
      simpa [mul_comm] using hpowprod
    exact
      int_prime_pow_dvd_left_of_dvd_mul_of_not_dvd_right
        (a := C + z ^ 3) (b := C - z ^ 3) hp hpowprod' hnotminus

end OddPrimeSplitting

end MazurProof
end FLT
```

The first three lemmas are deliberately very small.  The only proof engineering that may need local edits is the exact name and orientation of `Int.dvd_coe_gcd`, and the cast from `Nat.Prime p` to `Prime (p : ℤ)`.

## 2. Useful ZMod normalization layer

This is not a substitute for the prime-power splitting above, but it is a good sanity layer: the divisibility statement is exactly a square-root-of-one statement modulo `B^2`, after inverting `z^3`.

```lean
import Mathlib

namespace FLT
namespace MazurProof

section ZModLayer

/-- The congruence `C^2 ≡ z^6 mod B^2` as a `ZMod` equality. -/
theorem zmod_C_sq_eq_z_six_of_B_sq_dvd
    {B C z : ℤ} (hBpos : 0 < B)
    (hdiv : B ^ 2 ∣ C ^ 2 - z ^ 6) :
    (C : ZMod (B.natAbs ^ 2)) ^ 2 =
      (z : ZMod (B.natAbs ^ 2)) ^ 6 := by
  have hBnat : ((B.natAbs : ℤ) = B) := by
    exact Int.natAbs_ofNonneg (le_of_lt hBpos)
  have hmod :
      ((C ^ 2 - z ^ 6 : ℤ) : ZMod (B.natAbs ^ 2)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [hBnat] using hdiv
  have hsub :
      (C : ZMod (B.natAbs ^ 2)) ^ 2 -
        (z : ZMod (B.natAbs ^ 2)) ^ 6 = 0 := by
    simpa using hmod
  exact sub_eq_zero.mp hsub

/-- `z` is a unit modulo `B^2` if `gcd z B = 1`. -/
theorem zmod_isUnit_z_of_gcd_z_B
    {B z : ℤ} (hBpos : 0 < B)
    (hzB : Int.gcd z B = 1) :
    IsUnit (z : ZMod (B.natAbs ^ 2)) := by
  -- Expected route:
  --   * convert `Int.gcd z B = 1` to `Nat.Coprime z.natAbs B.natAbs`;
  --   * use `Nat.Coprime.pow_right` for modulus `B.natAbs^2`;
  --   * finish with `ZMod.isUnit_iff_coprime`.
  -- This lemma is often easier after proving a reusable bridge:
  --   Int.gcd x B = 1 -> Nat.Coprime x.natAbs B.natAbs
  sorry

/-- Square-root-of-one packaging after inverting `z^3`. -/
theorem zmod_exists_square_root_one_multiplier
    {B C z : ℤ} (hBpos : 0 < B)
    (hzB : Int.gcd z B = 1)
    (hdiv : B ^ 2 ∣ C ^ 2 - z ^ 6) :
    ∃ t : ZMod (B.natAbs ^ 2),
      t ^ 2 = 1 ∧
        (C : ZMod (B.natAbs ^ 2)) =
          t * (z : ZMod (B.natAbs ^ 2)) ^ 3 := by
  -- Let `u` be the unit `(z : ZMod (B.natAbs^2))^3`, and set
  -- `t = C * ↑u⁻¹`.  Then use `zmod_C_sq_eq_z_six_of_B_sq_dvd`.
  -- Do not expect `t = 1 ∨ t = -1` for arbitrary composite `B`; use CRT
  -- or the odd-prime-power splitting lemmas above.
  sorry

end ZModLayer

end MazurProof
end FLT
```

The important API here is `ZMod.intCast_zmod_eq_zero_iff_dvd`.  The modulus must be a `Nat`, so use `B.natAbs ^ 2`, not `B ^ 2`.  Under `1 < B`, the cast bridge is just `Int.natAbs_ofNonneg` plus `ring` or `simpa [pow_two]`.

## 3. The bad prime `2`

Keep a separate small layer for `p = 2`.  The odd-prime lemmas above intentionally exclude it.

```lean
import Mathlib

namespace FLT
namespace MazurProof

section TwoAdic

theorem two_dvd_B_forces_not_two_dvd_z_and_C
    {B C z : ℤ}
    (h2B : (2 : ℤ) ∣ B)
    (hzB : Int.gcd z B = 1)
    (hCB : Int.gcd C B = 1) :
    ¬ ((2 : ℤ) ∣ z) ∧ ¬ ((2 : ℤ) ∣ C) := by
  exact
    ⟨int_natPrime_not_dvd_of_dvd_right_of_gcd_eq_one
        (x := z) (B := B) Nat.prime_two h2B hzB,
      int_natPrime_not_dvd_of_dvd_right_of_gcd_eq_one
        (x := C) (B := B) Nat.prime_two h2B hCB⟩

/-- If `2 ∣ B`, then both signs are even; this is why the odd split cannot include `p=2`. -/
theorem two_dvd_B_forces_two_dvd_both_pm
    {B C z : ℤ}
    (h2B : (2 : ℤ) ∣ B)
    (hzB : Int.gcd z B = 1)
    (hCB : Int.gcd C B = 1) :
    ((2 : ℤ) ∣ C - z ^ 3) ∧ ((2 : ℤ) ∣ C + z ^ 3) := by
  -- Expected route:
  --   * from previous lemma, prove `C` and `z` are odd;
  --   * odd powers are odd;
  --   * odd ± odd is even.
  -- APIs: `Int.even_iff`, `Int.not_even_iff_odd`, `Odd.pow`, `Odd.add_odd`,
  -- or work in `ZMod 2` and use `decide`/`norm_num`.
  sorry

end TwoAdic

end MazurProof
end FLT
```

## 4. API and tactic checklist

For the first odd-prime layer:

- `Int.gcd` returns `Nat`, so bridge with `(Int.gcd x B : ℤ)` and `exact_mod_cast`.  The key lemma is `Int.dvd_coe_gcd`; check its orientation in your Mathlib revision.
- Use `Nat.Prime` for `p`, but use `(p : ℤ) ∣ ...` for integer divisibility.
- For product splitting over `ℤ`, convert `Nat.Prime p` to `Prime (p : ℤ)`, then use `Prime.dvd_or_dvd` and `Prime.dvd_of_dvd_pow`.
- For prime powers, either use `IsCoprime` with `IsCoprime.pow_left` and `IsCoprime.dvd_of_dvd_mul_right`, or do induction on the exponent.  The induction proof is sometimes more robust if Mathlib names move.
- For exponent normalization such as `((p : ℤ)^e)^2 = (p : ℤ)^(2*e)`, prefer `simpa [pow_mul, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]` over `nlinarith`.
- For congruences, use `ZMod.intCast_zmod_eq_zero_iff_dvd`.  The modulus is a `Nat`; with integer `B`, use `B.natAbs ^ 2` and prove `(B.natAbs : ℤ) = B` from `0 < B`.
- `linarith` and `nlinarith` are useful for the existing sign and range side-conditions.  They are not the right tool for prime-power or divisibility splitting.  Use `omega` for final contradictions like `1 < B` and `B = 1`.

## 5. What not to try as the next layer

The local congruence only says that `C * z^{-3}` is a square root of `1` modulo `B^2`.  For each odd prime power dividing `B`, the root is locally `+1` or `-1`, but the sign can vary with the prime.  Therefore a direct global sign statement is too strong.

Also, the full residual

```lean
def N12NoNontrivialSquareDenominatorResidual : Prop :=
  ∀ A B C : ℤ,
    1 < B →
    Int.gcd A B = 1 →
    C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) →
    False
```

is not realistically closed by local gcd/divisibility algebra alone.  It is a rational-points theorem for the elliptic curve

```lean
w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4
```

or an equivalent certified descent/integral-points computation.  The honest boundary should be explicit.

I would leave one of these as the theorem/axiom boundary.

### Boundary option A: denominator-integrality interface over the integer model

```lean
import Mathlib

namespace FLT
namespace MazurProof

/--
External arithmetic boundary: every primitive square-denominator point on the
N=12 curve has trivial denominator.  This should eventually be proved by a
certified rational-points or integral-points theorem, not by local gcd algebra.
-/
axiom n12_square_denominator_trivial
    (A B C : ℤ)
    (hBpos : 0 < B)
    (hcop : Int.gcd A B = 1)
    (hC : C ^ 2 =
      (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    B = 1

/-- Wrapper from the honest boundary to the current target. -/
theorem N12NoNontrivialSquareDenominatorResidual_of_boundary :
    N12NoNontrivialSquareDenominatorResidual := by
  intro A B C hBgt hcop hC
  have hBpos : 0 < B := lt_trans zero_lt_one hBgt
  have hB1 : B = 1 :=
    n12_square_denominator_trivial A B C hBpos hcop hC
  omega

end MazurProof
end FLT
```

This is the easiest interface to use in the current file.

### Boundary option B: rational-coordinate interface

```lean
import Mathlib

namespace FLT
namespace MazurProof

/--
External rational-points boundary: rational points on the affine model have
integral `u`-coordinate.
-/
axiom n12_rational_u_integral
    (u w : ℚ)
    (hcurve : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    ∃ a : ℤ, u = a

/-- The primitive square denominator `A/B^2` is not an integer when `1 < B`. -/
theorem rat_square_denominator_not_int_of_gcd
    (A B : ℤ)
    (hBgt : 1 < B)
    (hcop : Int.gcd A B = 1) :
    ¬ ∃ a : ℤ, (A : ℚ) / (B : ℚ) ^ 2 = a := by
  -- Expected proof route:
  --   * `0 < B`, hence `(B : ℚ) ≠ 0`;
  --   * clear denominators to get `B^2 ∣ A` over `ℤ`;
  --   * since `B ∣ B^2`, get `B ∣ A`;
  --   * use `Int.dvd_coe_gcd` and `hcop` to get `B ∣ 1`;
  --   * contradict `1 < B`.
  -- APIs: `field_simp`, `norm_num`, `Int.dvd_coe_gcd`, `exact_mod_cast`, `omega`.
  sorry

/-- Wrapper shape if you prefer the rational-points boundary. -/
theorem N12NoNontrivialSquareDenominatorResidual_of_rational_boundary :
    N12NoNontrivialSquareDenominatorResidual := by
  intro A B C hBgt hcop hC
  let u : ℚ := (A : ℚ) / (B : ℚ) ^ 2
  let w : ℚ := (C : ℚ) / (B : ℚ) ^ 3
  have hBne : (B : ℚ) ≠ 0 := by
    have hBpos : 0 < B := lt_trans zero_lt_one hBgt
    exact_mod_cast ne_of_gt hBpos
  have hcurve : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 := by
    -- Clear denominators with `field_simp [u, w, hBne]`, then use `hC`.
    -- `ring_nf` normally aligns the polynomial identity.
    sorry
  rcases n12_rational_u_integral u w hcurve with ⟨a, ha⟩
  exact rat_square_denominator_not_int_of_gcd A B hBgt hcop ⟨a, ha⟩

end MazurProof
end FLT
```

Option A is better for this file because it avoids introducing a separate rational-denominator normalization proof before the hard arithmetic theorem exists.

## 6. How this should connect to your existing produced `z,k`

After destructing `square_denominator_nontrivial_primitive_square_model`, keep the following local names:

```lean
rcases square_denominator_nontrivial_primitive_square_model A B C hBgt hcop hC with
  ⟨z, k, hzB, hA, hCzk, hRange, hProdPos⟩

have hCB : Int.gcd C B = 1 :=
  square_denominator_C_coprime_B A B C hcop hC

have hpm : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3) := by
  -- your existing compiled lemma
  exact ...
```

Then for any odd prime divisor of `B`:

```lean
have hlocal :=
  odd_natPrime_dvd_exactly_one_pm_of_dvd_B_sq_pm_product
    (B := B) (C := C) (z := z) hp hpodd hpB hzB hpm
```

and for a prime-power divisor:

```lean
have hlocalPow :=
  odd_natPrime_pow_dvd_exactly_one_pm_of_pow_dvd_B
    (B := B) (C := C) (z := z) hp hpodd he hpBe hzB hpm
```

That is the right modular layer to build before invoking either a CRT/sign-vector descent or the explicit rational-points boundary.