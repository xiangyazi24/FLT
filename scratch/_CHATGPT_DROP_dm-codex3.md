# Q2611: `PrimitiveCenteredFourSqAP` big Pythagorean triple gcd layer

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.
Namespace: `MazurProof.RationalPointsN12`.

This is the code-level layer I would add before applying `PythagoreanTriple.coprime_classification'` to

```text
x = S.p * S.q * S.r * S.s,
y = 16 * S.N^2,
z = S.X^2 - 20*S.N^2.
```

The useful Mathlib APIs for the prime-divisor proof are:

```lean
-- Mathlib.Data.Int.NatPrime / Mathlib.RingTheory.Int.Basic
-- Int.Prime.dvd_natAbs_of_coe_dvd_sq
-- Int.Prime.dvd_pow
-- Int.Prime.dvd_pow'
-- Nat.Prime.not_coprime_iff_dvd
-- Int.natCast_dvd
-- Int.isCoprime_iff_gcd_eq_one
-- IsCoprime.mul_right, IsCoprime.mul_left, IsCoprime.pow_left
-- Int.odd_iff, Int.odd_mul, Int.isCoprime_two_left
```

If the current file already imports enough Mathlib, no new import is needed. Otherwise these are the narrow imports that cover the APIs used below:

```lean
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.NatPrime
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
```

## 1. Oddness from `% 2 = 1`, product oddness

```lean
namespace MazurProof.RationalPointsN12

open Int

theorem primitiveCentered_p_odd (S : PrimitiveCenteredFourSqAP) : Odd S.p := by
  exact Int.odd_iff.mpr S.hp_odd

theorem primitiveCentered_q_odd (S : PrimitiveCenteredFourSqAP) : Odd S.q := by
  exact Int.odd_iff.mpr S.hq_odd

theorem primitiveCentered_r_odd (S : PrimitiveCenteredFourSqAP) : Odd S.r := by
  exact Int.odd_iff.mpr S.hr_odd

theorem primitiveCentered_s_odd (S : PrimitiveCenteredFourSqAP) : Odd S.s := by
  exact Int.odd_iff.mpr S.hs_odd

theorem primitiveCentered_root_product_odd (S : PrimitiveCenteredFourSqAP) :
    Odd (S.p * S.q * S.r * S.s) := by
  simpa [Int.odd_mul, mul_assoc] using
    And.intro
      (And.intro
        (And.intro (primitiveCentered_p_odd S) (primitiveCentered_q_odd S))
        (primitiveCentered_r_odd S))
      (primitiveCentered_s_odd S)

theorem primitiveCentered_root_product_mod_two (S : PrimitiveCenteredFourSqAP) :
    (S.p * S.q * S.r * S.s) % 2 = 1 := by
  exact Int.odd_iff.mp (primitiveCentered_root_product_odd S)

end MazurProof.RationalPointsN12
```

## 2. `p_ne_zero`, `6*N < X`, and positivity of the big hypotenuse

The clean route is: `p` is odd, so `p ≠ 0`; then `0 < p^2 = X - 6N`; hence `6N < X`. This also gives `0 < X`, and then

```text
X^2 - 20N^2 > X^2 - 36N^2 = (X-6N)(X+6N) > 0
```

up to the sign of the displayed difference; the snippet below uses `nlinarith` from the positive product.

```lean
namespace MazurProof.RationalPointsN12

theorem primitiveCentered_p_ne_zero (S : PrimitiveCenteredFourSqAP) : S.p ≠ 0 := by
  intro hp0
  have hpodd : Odd S.p := primitiveCentered_p_odd S
  simpa [hp0] using hpodd

theorem primitiveCentered_sixN_lt_X (S : PrimitiveCenteredFourSqAP) :
    6 * S.N < S.X := by
  have hpne : S.p ≠ 0 := primitiveCentered_p_ne_zero S
  have hpsq : 0 < S.p ^ 2 := sq_pos_of_ne_zero hpne
  nlinarith [S.hp]

theorem primitiveCentered_big_hyp_pos (S : PrimitiveCenteredFourSqAP) :
    0 < S.X ^ 2 - 20 * S.N ^ 2 := by
  have hXgt : 6 * S.N < S.X := primitiveCentered_sixN_lt_X S
  have hXm : 0 < S.X - 6 * S.N := by
    nlinarith [hXgt]
  have hXp : 0 < S.X + 6 * S.N := by
    nlinarith [hXgt, S.hNpos]
  have hprod : 0 < (S.X - 6 * S.N) * (S.X + 6 * S.N) := mul_pos hXm hXp
  have hN2 : 0 < S.N ^ 2 := sq_pos_of_ne_zero (ne_of_gt S.hNpos)
  nlinarith [hprod, hN2]

end MazurProof.RationalPointsN12
```

## 3. Adjacent gap gcd helpers: common divisor of root and step is impossible

These two helpers are the reusable core. They work with the already checked gap lemmas:

```lean
-- primitiveCentered_gap_pq : q^2 - p^2 = 4*N
-- primitiveCentered_gap_qr : r^2 - q^2 = 4*N
-- primitiveCentered_gap_rs : s^2 - r^2 = 4*N
```

The proof uses `Nat.Prime.not_coprime_iff_dvd.mp` on `Int.gcd ... ≠ 1`; the resulting divisibilities are on `natAbs`, and `Int.natCast_dvd` converts them to integer divisibility. The square-root step is exactly `Int.Prime.dvd_natAbs_of_coe_dvd_sq`.

```lean
namespace MazurProof.RationalPointsN12

theorem gcd_left_step_of_adjacent_square_gap
    {u v N : Int}
    (huv : Int.gcd u v = 1)
    (hgap : v ^ 2 - u ^ 2 = 4 * N) :
    Int.gcd N u = 1 := by
  by_contra hbad
  obtain ⟨l, hlprime, hlN, hlu⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  have hlN' : (l : Int) ∣ N := by
    rw [Int.natCast_dvd]
    exact hlN
  have hlu' : (l : Int) ∣ u := by
    rw [Int.natCast_dvd]
    exact hlu
  have hlu2 : (l : Int) ∣ u ^ 2 := by
    rw [sq]
    exact hlu'.mul_right u
  have hl4N : (l : Int) ∣ 4 * N := by
    exact hlN'.mul_left 4
  have hv_eq : v ^ 2 = u ^ 2 + 4 * N := by
    nlinarith [hgap]
  have hlv2 : (l : Int) ∣ v ^ 2 := by
    rw [hv_eq]
    exact dvd_add hlu2 hl4N
  have hlv : l ∣ v.natAbs :=
    Int.Prime.dvd_natAbs_of_coe_dvd_sq hlprime v hlv2
  have hlgcd : l ∣ Int.gcd u v := Nat.dvd_gcd hlu hlv
  rw [huv] at hlgcd
  exact hlprime.not_dvd_one hlgcd

theorem gcd_right_step_of_adjacent_square_gap
    {u v N : Int}
    (huv : Int.gcd u v = 1)
    (hgap : v ^ 2 - u ^ 2 = 4 * N) :
    Int.gcd N v = 1 := by
  by_contra hbad
  obtain ⟨l, hlprime, hlN, hlv⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  have hlN' : (l : Int) ∣ N := by
    rw [Int.natCast_dvd]
    exact hlN
  have hlv' : (l : Int) ∣ v := by
    rw [Int.natCast_dvd]
    exact hlv
  have hlv2 : (l : Int) ∣ v ^ 2 := by
    rw [sq]
    exact hlv'.mul_right v
  have hl4N : (l : Int) ∣ 4 * N := by
    exact hlN'.mul_left 4
  have hu_eq : u ^ 2 = v ^ 2 - 4 * N := by
    nlinarith [hgap]
  have hlu2 : (l : Int) ∣ u ^ 2 := by
    rw [hu_eq]
    exact dvd_sub hlv2 hl4N
  have hlu : l ∣ u.natAbs :=
    Int.Prime.dvd_natAbs_of_coe_dvd_sq hlprime u hlu2
  have hlgcd : l ∣ Int.gcd u v := Nat.dvd_gcd hlu hlv
  rw [huv] at hlgcd
  exact hlprime.not_dvd_one hlgcd

end MazurProof.RationalPointsN12
```

## 4. Apply the helpers to `p,q,r,s`

These are the `Int.gcd` versions plus the `IsCoprime` wrappers. The wrappers are what you usually want for multiplicative combination.

```lean
namespace MazurProof.RationalPointsN12

theorem primitiveCentered_N_coprime_p_gcd (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.N S.p = 1 := by
  exact gcd_left_step_of_adjacent_square_gap S.hpq (primitiveCentered_gap_pq S)

theorem primitiveCentered_N_coprime_q_gcd (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.N S.q = 1 := by
  exact gcd_right_step_of_adjacent_square_gap S.hpq (primitiveCentered_gap_pq S)

theorem primitiveCentered_N_coprime_r_gcd (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.N S.r = 1 := by
  exact gcd_right_step_of_adjacent_square_gap S.hqr (primitiveCentered_gap_qr S)

theorem primitiveCentered_N_coprime_s_gcd (S : PrimitiveCenteredFourSqAP) :
    Int.gcd S.N S.s = 1 := by
  exact gcd_right_step_of_adjacent_square_gap S.hrs (primitiveCentered_gap_rs S)

theorem primitiveCentered_N_coprime_p (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.p := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact primitiveCentered_N_coprime_p_gcd S

theorem primitiveCentered_N_coprime_q (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.q := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact primitiveCentered_N_coprime_q_gcd S

theorem primitiveCentered_N_coprime_r (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.r := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact primitiveCentered_N_coprime_r_gcd S

theorem primitiveCentered_N_coprime_s (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N S.s := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact primitiveCentered_N_coprime_s_gcd S

end MazurProof.RationalPointsN12
```

Notes:

* `primitiveCentered_N_coprime_q_gcd` can also be proved from `hqr`; using `hpq` is fine and keeps it adjacent to `p`.
* `primitiveCentered_N_coprime_p_gcd` and `primitiveCentered_N_coprime_q_gcd` use only `hpq`. The `r` and `s` proofs use `hqr` and `hrs`.
* The non-adjacent fields `hpr,hps,hqs` are not needed for this layer.

## 5. Combine to coprimality of the big even leg and odd leg

First combine coprimality of `N` with each root into coprimality with the root product. Then combine coprimality with `N^2` and with `16`.

```lean
namespace MazurProof.RationalPointsN12

theorem primitiveCentered_N_coprime_root_product (S : PrimitiveCenteredFourSqAP) :
    IsCoprime S.N (S.p * S.q * S.r * S.s) := by
  have hp : IsCoprime S.N S.p := primitiveCentered_N_coprime_p S
  have hq : IsCoprime S.N S.q := primitiveCentered_N_coprime_q S
  have hr : IsCoprime S.N S.r := primitiveCentered_N_coprime_r S
  have hs : IsCoprime S.N S.s := primitiveCentered_N_coprime_s S
  have hpq : IsCoprime S.N (S.p * S.q) := hp.mul_right hq
  have hpqr : IsCoprime S.N ((S.p * S.q) * S.r) := hpq.mul_right hr
  have hpqrs : IsCoprime S.N (((S.p * S.q) * S.r) * S.s) := hpqr.mul_right hs
  simpa [mul_assoc] using hpqrs

theorem primitiveCentered_sixteen_Nsq_coprime_root_product
    (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (16 * S.N ^ 2) (S.p * S.q * S.r * S.s) := by
  let Y : Int := S.p * S.q * S.r * S.s
  have hYodd : Odd Y := by
    simpa [Y] using primitiveCentered_root_product_odd S
  have h2 : IsCoprime (2 : Int) Y := by
    exact Int.isCoprime_two_left.mpr hYodd
  have h16 : IsCoprime (16 : Int) Y := by
    have hpow : IsCoprime ((2 : Int) ^ 4) Y := by
      simpa using (h2.pow_left (m := 4))
    norm_num at hpow ⊢
    exact hpow
  have hN : IsCoprime S.N Y := by
    simpa [Y] using primitiveCentered_N_coprime_root_product S
  have hN2 : IsCoprime (S.N ^ 2) Y := by
    simpa using (hN.pow_left (m := 2))
  have hfinal : IsCoprime (16 * S.N ^ 2) Y := h16.mul_left hN2
  simpa [Y] using hfinal

theorem primitiveCentered_root_product_coprime_sixteen_Nsq
    (S : PrimitiveCenteredFourSqAP) :
    IsCoprime (S.p * S.q * S.r * S.s) (16 * S.N ^ 2) := by
  exact (primitiveCentered_sixteen_Nsq_coprime_root_product S).symm

theorem primitiveCentered_big_triple_gcd_eq_one
    (S : PrimitiveCenteredFourSqAP) :
    Int.gcd (S.p * S.q * S.r * S.s) (16 * S.N ^ 2) = 1 := by
  exact Int.isCoprime_iff_gcd_eq_one.mp
    (primitiveCentered_root_product_coprime_sixteen_Nsq S)

end MazurProof.RationalPointsN12
```

## 6. Optional direct Pythagorean triple wrapper

This is not part of the gcd layer, but it is the natural next lemma after `primitiveCentered_big_pyth_identity`.

```lean
namespace MazurProof.RationalPointsN12

theorem primitiveCentered_big_pyth_triple (S : PrimitiveCenteredFourSqAP) :
    PythagoreanTriple
      (S.p * S.q * S.r * S.s)
      (16 * S.N ^ 2)
      (S.X ^ 2 - 20 * S.N ^ 2) := by
  unfold PythagoreanTriple
  have h := primitiveCentered_big_pyth_identity S
  nlinarith [h]

end MazurProof.RationalPointsN12
```

## 7. If one helper fails due to local imports

If the current local file lacks the theorem `Int.isCoprime_iff_gcd_eq_one`, import `Mathlib.RingTheory.Coprime.Lemmas` or replace the wrapper proofs by the generic theorem name already in scope:

```lean
-- alternative wrapper body if only generic gcd API is in scope:
-- simpa [isCoprime_iff_gcd_eq_one] using primitiveCentered_N_coprime_p_gcd S
```

If `nlinarith` does not expand the product in `primitiveCentered_big_hyp_pos`, replace the last line by an explicit ring normalization step:

```lean
-- have hprod' : 0 < S.X ^ 2 - 36 * S.N ^ 2 := by
--   nlinarith [hprod]
-- have hN2 : 0 < S.N ^ 2 := sq_pos_of_ne_zero (ne_of_gt S.hNpos)
-- nlinarith [hprod', hN2]
```

No axioms or `sorry` are needed for this layer; the only delicate part is keeping the divisibility conversions in the `Nat.Prime.not_coprime_iff_dvd` proof in the `natAbs` form until `Int.natCast_dvd` converts them.
