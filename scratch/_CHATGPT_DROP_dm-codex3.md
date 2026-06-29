# Q2185 Lean drop: prime-power splitting after the odd-prime non-common-factor lemma

```lean
import Mathlib

/-!
Paste this after your theorem

  square_denominator_odd_prime_not_common_z_cube_factors

or keep it in the same namespace/section.  The code below uses only prime-power
divisibility.  This is shorter than `multiplicity`/`emultiplicity` for this
local step.
-/

private theorem square_denominator_nat_prime_int_prime {p : ℕ}
    (hp : Nat.Prime p) :
    Prime (p : ℤ) := by
  exact Int.prime_iff_natAbs_prime.mpr (by simpa using hp)

/--
Pure Euclid/prime-power splitting over `ℤ`.

If `p^e ∣ x*y`, `p ∣ x*y`, and `p` does not divide both `x` and `y`, then the
whole `p^e`-divisibility lies in exactly one factor.

This is the reusable core lemma.  It deliberately knows nothing about `B`,
`C`, or `z`.
-/
theorem square_denominator_prime_pow_dvd_one_factor_of_not_common
    (x y : ℤ) {p e : ℕ}
    (hp : Nat.Prime p)
    (hp_prod : (p : ℤ) ∣ x * y)
    (hpow_prod : (p : ℤ) ^ e ∣ x * y)
    (hnotcommon : ¬ (((p : ℤ) ∣ x) ∧ ((p : ℤ) ∣ y))) :
    ((((p : ℤ) ^ e ∣ x) ∧ ¬ ((p : ℤ) ∣ y)) ∨
      (((p : ℤ) ^ e ∣ y) ∧ ¬ ((p : ℤ) ∣ x))) := by
  have hpZ : Prime (p : ℤ) := square_denominator_nat_prime_int_prime hp
  rcases hpZ.dvd_or_dvd hp_prod with hx | hy
  · have hny : ¬ ((p : ℤ) ∣ y) := by
      intro hy
      exact hnotcommon ⟨hx, hy⟩
    refine Or.inl ⟨?_, hny⟩
    -- Mathlib v4.31.0-rc2:
    --   Prime.pow_dvd_of_dvd_mul_right hpZ e hny hpow_prod
    -- means: if `¬ p ∣ y` and `p^e ∣ x*y`, then `p^e ∣ x`.
    exact hpZ.pow_dvd_of_dvd_mul_right e hny hpow_prod
  · have hnx : ¬ ((p : ℤ) ∣ x) := by
      intro hx
      exact hnotcommon ⟨hx, hy⟩
    refine Or.inr ⟨?_, hnx⟩
    -- Mathlib v4.31.0-rc2:
    --   Prime.pow_dvd_of_dvd_mul_left hpZ e hnx hpow_prod
    -- means: if `¬ p ∣ x` and `p^e ∣ x*y`, then `p^e ∣ y`.
    exact hpZ.pow_dvd_of_dvd_mul_left e hnx hpow_prod

/--
Specialized version for the `C ± z^3` factors, assuming the non-common-factor
lemma has already been supplied.

This is the next lemma I would actually add after your current theorem.
The hypothesis `(p : ℤ)^e ∣ B^2` is intentionally not required to be maximal;
for a maximal contribution, choose `e` from a factorization/valuation layer
later.
-/
theorem square_denominator_odd_prime_pow_dvd_one_z_cube_factor_of_not_common
    (B C z : ℤ) {p e : ℕ}
    (hp : Nat.Prime p)
    (hpB : (p : ℤ) ∣ B)
    (hpowBsq : (p : ℤ) ^ e ∣ B ^ 2)
    (hprod : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3))
    (hnotcommon :
      ¬ (((p : ℤ) ∣ C - z ^ 3) ∧ ((p : ℤ) ∣ C + z ^ 3))) :
    ((((p : ℤ) ^ e ∣ C - z ^ 3) ∧ ¬ ((p : ℤ) ∣ C + z ^ 3)) ∨
      (((p : ℤ) ^ e ∣ C + z ^ 3) ∧ ¬ ((p : ℤ) ∣ C - z ^ 3))) := by
  have hpBsq : (p : ℤ) ∣ B ^ 2 := by
    have hBB : (p : ℤ) ∣ B * B := dvd_mul_of_dvd_left hpB B
    simpa [pow_two] using hBB
  have hp_prod : (p : ℤ) ∣ (C - z ^ 3) * (C + z ^ 3) :=
    dvd_trans hpBsq hprod
  have hpow_prod : (p : ℤ) ^ e ∣ (C - z ^ 3) * (C + z ^ 3) :=
    dvd_trans hpowBsq hprod
  exact
    square_denominator_prime_pow_dvd_one_factor_of_not_common
      (x := C - z ^ 3) (y := C + z ^ 3)
      hp hp_prod hpow_prod hnotcommon

/--
The fully bundled version using your existing odd-prime non-common-factor
lemma.  This is probably the best theorem signature for the N=12 file.
-/
theorem square_denominator_odd_prime_pow_dvd_one_z_cube_factor
    (B C z : ℤ) {p e : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hpowBsq : (p : ℤ) ^ e ∣ B ^ 2)
    (hprod : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ((((p : ℤ) ^ e ∣ C - z ^ 3) ∧ ¬ ((p : ℤ) ∣ C + z ^ 3)) ∨
      (((p : ℤ) ^ e ∣ C + z ^ 3) ∧ ¬ ((p : ℤ) ∣ C - z ^ 3))) := by
  exact
    square_denominator_odd_prime_pow_dvd_one_z_cube_factor_of_not_common
      (B := B) (C := C) (z := z)
      hp hpB hpowBsq hprod
      (square_denominator_odd_prime_not_common_z_cube_factors
        B C z hp hpodd hpB hcopC)

/--
Convenience: if your local factorization data gives `(p:ℤ)^e ∣ B`, then it gives
`(p:ℤ)^(2*e) ∣ B^2`.
-/
private theorem square_denominator_prime_pow_sq_dvd_sq_of_pow_dvd
    (B : ℤ) {p e : ℕ}
    (hpeB : (p : ℤ) ^ e ∣ B) :
    (p : ℤ) ^ (2 * e) ∣ B ^ 2 := by
  have hsq : ((p : ℤ) ^ e) ^ 2 ∣ B ^ 2 := by
    exact pow_dvd_pow_of_dvd hpeB 2
  simpa [pow_mul, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsq

/--
Variant to use when the data is `(p:ℤ)^e ∣ B` rather than `(p:ℤ)^e ∣ B^2`.
The conclusion has exponent `2*e`, as expected for `B^2`.
-/
theorem square_denominator_odd_prime_pow_from_B_dvd_one_z_cube_factor
    (B C z : ℤ) {p e : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) (he : 0 < e)
    (hpowB : (p : ℤ) ^ e ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hprod : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ((((p : ℤ) ^ (2 * e) ∣ C - z ^ 3) ∧ ¬ ((p : ℤ) ∣ C + z ^ 3)) ∨
      (((p : ℤ) ^ (2 * e) ∣ C + z ^ 3) ∧ ¬ ((p : ℤ) ∣ C - z ^ 3))) := by
  have hpB : (p : ℤ) ∣ B := by
    have hp_dvd_pe : (p : ℤ) ∣ (p : ℤ) ^ e := by
      exact dvd_pow_self (p : ℤ) (Nat.ne_of_gt he)
    exact dvd_trans hp_dvd_pe hpowB
  have hpowBsq : (p : ℤ) ^ (2 * e) ∣ B ^ 2 :=
    square_denominator_prime_pow_sq_dvd_sq_of_pow_dvd B hpowB
  exact
    square_denominator_odd_prime_pow_dvd_one_z_cube_factor
      (B := B) (C := C) (z := z)
      hp hpodd hpB hcopC hpowBsq hprod
```

```lean
import Mathlib

/-!
A minimal per-prime/per-prime-power sign interface.  This avoids the false
statement that one global sign works for all of `B`.

Paste this after the lemmas above if downstream code wants to carry a sign as
explicit data.
-/

inductive N12LocalSign where
  | minus
  | plus
deriving DecidableEq, Repr

namespace N12LocalSign

/--
`minus` means the local prime-power contribution lands in `C - z^3`.
`plus` means it lands in `C + z^3`.
-/
def Holds (s : N12LocalSign) (C z : ℤ) (p e : ℕ) : Prop :=
  match s with
  | .minus =>
      ((p : ℤ) ^ e ∣ C - z ^ 3) ∧ ¬ ((p : ℤ) ∣ C + z ^ 3)
  | .plus =>
      ((p : ℤ) ^ e ∣ C + z ^ 3) ∧ ¬ ((p : ℤ) ∣ C - z ^ 3)

end N12LocalSign

/--
Existence of a local sign for one odd prime-power contribution.
This is usually enough; do not pick one sign for all primes.
-/
theorem square_denominator_odd_prime_pow_exists_local_sign
    (B C z : ℤ) {p e : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2)
    (hpB : (p : ℤ) ∣ B)
    (hcopC : Int.gcd C B = 1)
    (hpowBsq : (p : ℤ) ^ e ∣ B ^ 2)
    (hprod : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ∃ s : N12LocalSign, s.Holds C z p e := by
  rcases
    square_denominator_odd_prime_pow_dvd_one_z_cube_factor
      (B := B) (C := C) (z := z)
      hp hpodd hpB hcopC hpowBsq hprod with hminus | hplus
  · exact ⟨.minus, hminus⟩
  · exact ⟨.plus, hplus⟩

/--
The global theorem should be this dependent per-prime/per-exponent statement,
not a single global sign statement.
-/
theorem square_denominator_odd_prime_pow_signs
    (B C z : ℤ)
    (hcopC : Int.gcd C B = 1)
    (hprod : B ^ 2 ∣ (C - z ^ 3) * (C + z ^ 3)) :
    ∀ {p e : ℕ},
      Nat.Prime p →
      p ≠ 2 →
      (p : ℤ) ∣ B →
      (p : ℤ) ^ e ∣ B ^ 2 →
      ∃ s : N12LocalSign, s.Holds C z p e := by
  intro p e hp hpodd hpB hpowBsq
  exact
    square_denominator_odd_prime_pow_exists_local_sign
      (B := B) (C := C) (z := z)
      hp hpodd hpB hcopC hpowBsq hprod
```

## API notes for Mathlib v4.31.0-rc2

Use `Prime.pow_dvd_of_dvd_mul_right` and `Prime.pow_dvd_of_dvd_mul_left`; you do **not** need to prove the prime-power splitting by induction unless the local import set somehow fails to expose these lemmas.

The signatures are easy to mix up:

```lean
-- If `¬ p ∣ b` and `p^n ∣ a*b`, then `p^n ∣ a`.
#check Prime.pow_dvd_of_dvd_mul_right
-- Prime.pow_dvd_of_dvd_mul_right {p a b : M} (hp : Prime p)
--   (n : ℕ) (h : ¬ p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a

-- If `¬ p ∣ a` and `p^n ∣ a*b`, then `p^n ∣ b`.
#check Prime.pow_dvd_of_dvd_mul_left
-- Prime.pow_dvd_of_dvd_mul_left {p a b : M} (hp : Prime p)
--   (n : ℕ) (h : ¬ p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b
```

For `p : ℕ`, keep divisibility in `ℤ` but primality in `Nat`:

```lean
have hpZ : Prime (p : ℤ) :=
  Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
```

Your use of `Int.dvd_coe_gcd` is the Mathlib-friendly one in this version:

```lean
have hpG : (p : ℤ) ∣ ((Int.gcd C B : ℕ) : ℤ) :=
  Int.dvd_coe_gcd hpC hpB
```

That avoids the older confusion about whether `Int.dvd_coe_gcd` is an iff or a two-argument constructor-style theorem.

## Why this is the right interface

The local theorem only assigns a sign for one odd prime-power contribution.  That is globally correct: for composite `B`, different odd primes can land in different signs.  A theorem of the form

```lean
B ^ 2 ∣ C - z ^ 3 ∨ B ^ 2 ∣ C + z ^ 3
```

is too strong without extra CRT/sign-vector hypotheses.  The `N12LocalSign` interface records exactly what the congruence proves: for every odd prime-power contribution to `B^2`, there exists a local sign, and the chosen sign may depend on `p` and `e`.

I would postpone `multiplicity` or `emultiplicity` until you need maximal exponents.  The prime-power divisibility API above is shorter and avoids `WithTop ℕ` arithmetic.