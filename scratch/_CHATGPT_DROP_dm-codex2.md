# Q2608 `EulerSquarePair` signed even/odd parameter wrappers

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.

Target namespace:

```lean
namespace MazurProof.RationalPointsN12.EulerSquarePair
```

This drop assumes the current file already contains the structure `EulerSquarePair` and the checked lemmas named in the prompt:

```lean
D_mod_two_eq_one
D_coprime_twoA
D_coprime_fourA
gcd_D_twoA_eq_one
gcd_D_fourA_eq_one
pythagorean_D_twoA_C
pythagorean_D_fourA_B
pythagorean_D_twoA_C_params
pythagorean_D_fourA_B_params
```

The snippets below do not redefine the structure.  Paste them in the existing namespace.  They use only `Mathlib.NumberTheory.FLT.Four` and `Mathlib.Tactic`.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12.EulerSquarePair

lemma q2608_int_cancel_two_mul {a b : ℤ}
    (h : (2 : ℤ) * a = 2 * b) :
    a = b := by
  exact (mul_left_inj' (show (2 : ℤ) ≠ 0 by norm_num)).mp h

lemma q2608_int_cancel_four_mul {a b : ℤ}
    (h : (4 : ℤ) * a = 4 * b) :
    a = b := by
  exact (mul_left_inj' (show (4 : ℤ) ≠ 0 by norm_num)).mp h

lemma q2608_eq_mul_of_two_mul_eq_two_mul_mul {A m n : ℤ}
    (h : (2 : ℤ) * A = 2 * m * n) :
    A = m * n := by
  apply q2608_int_cancel_two_mul
  calc
    (2 : ℤ) * A = 2 * m * n := h
    _ = 2 * (m * n) := by ring

lemma q2608_two_mul_eq_mul_of_four_mul_eq_two_mul_mul {A m n : ℤ}
    (h : (4 : ℤ) * A = 2 * m * n) :
    (2 : ℤ) * A = m * n := by
  apply q2608_int_cancel_two_mul
  calc
    (2 : ℤ) * (2 * A) = 4 * A := by ring
    _ = 2 * m * n := h
    _ = 2 * (m * n) := by ring

lemma q2608_even_of_emod_two_eq_zero {x : ℤ}
    (hx : x % 2 = 0) :
    Even x := by
  exact even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero hx)

lemma q2608_odd_of_emod_two_eq_one {x : ℤ}
    (hx : x % 2 = 1) :
    Odd x :=
  Int.odd_iff.mpr hx

lemma q2608_even_left_of_even_mul_of_odd_right {a b : ℤ}
    (hab : Even (a * b)) (hb : Odd b) :
    Even a := by
  by_contra haEven
  have haOdd : Odd a := Int.not_even_iff_odd.mp haEven
  have hOdd : Odd (a * b) := Int.odd_mul.mpr ⟨haOdd, hb⟩
  exact (Int.not_odd_iff_even.mpr hab) hOdd

/--
Halve the even parameter in the second Pythagorean parametrization.

Use this with `(R,S) = (m,n)` in the `m`-even branch, and with
`(R,S) = (n,m)` in the `n`-even branch after rewriting
`4*A = 2*m*n` to `4*A = 2*n*m`.

Inputs:
* `0 < A`, `Even A` from the Euler square pair;
* `0 ≤ R`, coming from `0 ≤ m`, or derived for `R = n` in the swapped branch;
* `R % 2 = 0`, `Odd S`;
* `4*A = 2*R*S`.

Outputs:
* `R = 2*Up`;
* `0 < Up`;
* `Even Up`, using `Even A` and oddness of `S`;
* `A = Up*S`.
-/
lemma q2608_halve_even_factor_in_fourA
    {A R S : ℤ}
    (hApos : 0 < A) (hAeven : Even A)
    (hRnonneg : 0 ≤ R) (hReven : R % 2 = 0) (hSodd : Odd S)
    (h4A : (4 : ℤ) * A = 2 * R * S) :
    ∃ Up : ℤ, R = 2 * Up ∧ 0 < Up ∧ Even Up ∧ A = Up * S := by
  rcases Int.dvd_of_emod_eq_zero hReven with ⟨Up, hUp⟩
  have hA : A = Up * S := by
    apply q2608_int_cancel_four_mul
    calc
      (4 : ℤ) * A = 2 * R * S := h4A
      _ = 4 * (Up * S) := by
        rw [hUp]
        ring
  have hUp_nonneg : 0 ≤ Up := by
    omega
  have hUp_ne : Up ≠ 0 := by
    intro h0
    have hA0 : A = 0 := by
      rw [hA, h0, zero_mul]
    exact (ne_of_gt hApos) hA0
  have hUp_pos : 0 < Up :=
    lt_of_le_of_ne hUp_nonneg (Ne.symm hUp_ne)
  have hUpEven : Even Up := by
    apply q2608_even_left_of_even_mul_of_odd_right
    · rw [← hA]
      exact hAeven
    · exact hSodd
  exact ⟨Up, hUp, hUp_pos, hUpEven, hA⟩

/--
Signed even/odd parameters for the `(D, 2*A, C)` Pythagorean triple.

The Mathlib classification returns `D = m^2 - n^2`, `2*A = 2*m*n`,
and exactly one of `m,n` even.  If `m` is even, take `(U,V,eps) = (m,n,1)`.
If `n` is even, take `(U,V,eps) = (n,m,-1)`.
-/
theorem C_signed_even_odd_params (E : EulerSquarePair) :
    ∃ U V eps : ℤ,
      0 < U ∧ 0 < V ∧ IsCoprime U V ∧ Even U ∧ Odd V ∧
      (eps = 1 ∨ eps = -1) ∧
      E.A = U * V ∧
      E.D = eps * (U ^ 2 - V ^ 2) ∧
      E.C = U ^ 2 + V ^ 2 := by
  obtain ⟨m, n, hD, h2A, hC, hgcd, hparity, hm_nonneg⟩ :=
    pythagorean_D_twoA_C_params E
  have hA_mn : E.A = m * n :=
    q2608_eq_mul_of_two_mul_eq_two_mul_mul h2A
  have hcopmn : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  rcases hparity with hmn | hmn
  · -- `m` even, `n` odd: keep Mathlib's orientation.
    have hmEven : Even m := q2608_even_of_emod_two_eq_zero hmn.1
    have hnOdd : Odd n := q2608_odd_of_emod_two_eq_one hmn.2
    have hm_ne : m ≠ 0 := by
      intro hm0
      have hA0 : E.A = 0 := by
        rw [hA_mn, hm0, zero_mul]
      exact (ne_of_gt E.hApos) hA0
    have hm_pos : 0 < m :=
      lt_of_le_of_ne hm_nonneg (Ne.symm hm_ne)
    have hn_pos : 0 < n := by
      have hmn_pos : 0 < m * n := by
        rw [← hA_mn]
        exact E.hApos
      exact (mul_pos_iff_of_pos_left hm_pos).mp hmn_pos
    refine ⟨m, n, 1, hm_pos, hn_pos, hcopmn, hmEven, hnOdd, Or.inl rfl,
      hA_mn, ?_, hC⟩
    rw [hD]
    ring
  · -- `n` even, `m` odd: swap parameters and flip the sign.
    have hmOdd : Odd m := q2608_odd_of_emod_two_eq_one hmn.1
    have hnEven : Even n := q2608_even_of_emod_two_eq_zero hmn.2
    have hm_ne : m ≠ 0 := by
      intro hm0
      have hA0 : E.A = 0 := by
        rw [hA_mn, hm0, zero_mul]
      exact (ne_of_gt E.hApos) hA0
    have hm_pos : 0 < m :=
      lt_of_le_of_ne hm_nonneg (Ne.symm hm_ne)
    have hn_pos : 0 < n := by
      have hmn_pos : 0 < m * n := by
        rw [← hA_mn]
        exact E.hApos
      exact (mul_pos_iff_of_pos_left hm_pos).mp hmn_pos
    refine ⟨n, m, -1, hn_pos, hm_pos, hcopmn.symm, hnEven, hmOdd, Or.inr rfl,
      ?_, ?_, ?_⟩
    · rw [hA_mn]
      ring
    · rw [hD]
      ring
    · rw [hC]
      ring

/--
Signed even/odd parameters for the `(D, 4*A, B)` Pythagorean triple.

The Mathlib classification returns `D = m^2 - n^2`, `4*A = 2*m*n`,
and exactly one of `m,n` even.  If `m` is even, write `m = 2*Up` and
use `(Up,Vp,eps) = (Up,n,1)`.  If `n` is even, write `n = 2*Up` and
use `(Up,Vp,eps) = (Up,m,-1)`.
-/
theorem B_signed_even_odd_params (E : EulerSquarePair) :
    ∃ Up Vp eps : ℤ,
      0 < Up ∧ 0 < Vp ∧ IsCoprime Up Vp ∧ Even Up ∧ Odd Vp ∧
      (eps = 1 ∨ eps = -1) ∧
      E.A = Up * Vp ∧
      E.D = eps * (4 * Up ^ 2 - Vp ^ 2) ∧
      E.B = 4 * Up ^ 2 + Vp ^ 2 := by
  obtain ⟨m, n, hD, h4A, hB, hgcd, hparity, hm_nonneg⟩ :=
    pythagorean_D_fourA_B_params E
  have hcopmn : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hgcd
  rcases hparity with hmn | hmn
  · -- `m` even, `n` odd.
    have hnOdd : Odd n := q2608_odd_of_emod_two_eq_one hmn.2
    obtain ⟨Up, hUp, hUp_pos, hUpEven, hA_Upn⟩ :=
      q2608_halve_even_factor_in_fourA
        (A := E.A) (R := m) (S := n)
        E.hApos E.hAeven hm_nonneg hmn.1 hnOdd h4A
    have hn_pos : 0 < n := by
      have hprod : 0 < Up * n := by
        rw [← hA_Upn]
        exact E.hApos
      exact (mul_pos_iff_of_pos_left hUp_pos).mp hprod
    have hcopUpn : IsCoprime Up n := by
      have hcop2Upn : IsCoprime (2 * Up) n := by
        simpa [hUp] using hcopmn
      exact IsCoprime.of_mul_left_right hcop2Upn
    refine ⟨Up, n, 1, hUp_pos, hn_pos, hcopUpn, hUpEven, hnOdd, Or.inl rfl,
      hA_Upn, ?_, ?_⟩
    · rw [hD, hUp]
      ring
    · rw [hB, hUp]
      ring
  · -- `n` even, `m` odd.
    have hmOdd : Odd m := q2608_odd_of_emod_two_eq_one hmn.1
    have h2A_mn : (2 : ℤ) * E.A = m * n :=
      q2608_two_mul_eq_mul_of_four_mul_eq_two_mul_mul h4A
    have hm_ne : m ≠ 0 := by
      intro hm0
      subst m
      norm_num at hmn
    have hm_pos : 0 < m :=
      lt_of_le_of_ne hm_nonneg (Ne.symm hm_ne)
    have hn_pos : 0 < n := by
      have hmn_pos : 0 < m * n := by
        rw [← h2A_mn]
        exact mul_pos (by norm_num : (0 : ℤ) < 2) E.hApos
      exact (mul_pos_iff_of_pos_left hm_pos).mp hmn_pos
    have h4A_nm : (4 : ℤ) * E.A = 2 * n * m := by
      rw [h4A]
      ring
    obtain ⟨Up, hUp, hUp_pos, hUpEven, hA_Upm⟩ :=
      q2608_halve_even_factor_in_fourA
        (A := E.A) (R := n) (S := m)
        E.hApos E.hAeven (le_of_lt hn_pos) hmn.2 hmOdd h4A_nm
    have hcopUpm : IsCoprime Up m := by
      have hcopm2Up : IsCoprime m (2 * Up) := by
        simpa [hUp] using hcopmn
      exact (IsCoprime.of_mul_right_right hcopm2Up).symm
    refine ⟨Up, m, -1, hUp_pos, hm_pos, hcopUpm, hUpEven, hmOdd, Or.inr rfl,
      hA_Upm, ?_, ?_⟩
    · rw [hD, hUp]
      ring
    · rw [hB, hUp]
      ring

end MazurProof.RationalPointsN12.EulerSquarePair
```

## Implementation notes

* `q2608_eq_mul_of_two_mul_eq_two_mul_mul` handles the `2*A = 2*m*n` cancellation in the `C` wrapper.
* `q2608_two_mul_eq_mul_of_four_mul_eq_two_mul_mul` handles the first cancellation from `4*A = 2*m*n` to `2*A = m*n`; this is useful in the swapped `B` branch to prove the even parameter `n` is positive.
* `q2608_halve_even_factor_in_fourA` is the requested clean lemma for the `B` case: from `R` even, `S` odd, `0 ≤ R`, `Even A`, and `4*A = 2*R*S`, it produces `R = 2*Up`, `0 < Up`, `Even Up`, and `A = Up*S`.
* Positivity is obtained as follows.  In the `C` wrapper, `0 ≤ m` plus `A = m*n` and `A > 0` gives `m > 0`, hence `n > 0`.  In the swapped `C` branch, `m > 0` still comes from `0 ≤ m` and `A > 0`, then `n > 0` follows from `A = m*n`.  In the `B` wrapper, the `m`-even branch gets `Up > 0` from `0 ≤ m`, `m = 2*Up`, and `A = Up*n`; the `n`-even branch first proves `m > 0`, then `n > 0` from `2*A = m*n`, and then applies the halving lemma with `R = n`.
* The sign convention is encoded by the explicit integer `eps`.  Swapping the Pythagorean parameters changes `m^2 - n^2` to `-(n^2 - m^2)`, so the swapped branches use `eps = -1`.
