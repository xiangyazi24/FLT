# Q2604 Lean wrappers for `EulerSquarePairDescent`

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.

The GitHub contents API did not expose the target Lean file on `scratch` during this drop, so the code below is a standalone snippet.  In the real target file, omit the `structure EulerSquarePair` block if it is already present and paste the lemmas into the local namespace.

The important convention is that `PythagoreanTriple.coprime_classification'` must be applied with `x = D`, not with the even leg as `x`, because the theorem requires `x % 2 = 1`.  Thus we classify `(D, 2*A, C)` and `(D, 4*A, B)`.

```lean
import Mathlib

namespace EulerSquarePairDescent

structure EulerSquarePair where
  A D B C : ℤ
  hApos : 0 < A
  hDpos : 0 < D
  hDodd : Odd D
  hAeven : Even A
  hADcop : IsCoprime A D
  hBpos : 0 < B
  hCpos : 0 < C
  hB : B ^ 2 = 16 * A ^ 2 + D ^ 2
  hC : C ^ 2 = 4 * A ^ 2 + D ^ 2

lemma D_mod_two_eq_one (E : EulerSquarePair) : E.D % 2 = 1 :=
  Int.odd_iff.mp E.hDodd

lemma D_coprime_two (E : EulerSquarePair) : IsCoprime E.D (2 : ℤ) := by
  rcases E.hDodd with ⟨k, hk⟩
  refine ⟨1, -k, ?_⟩
  rw [hk]
  ring

lemma gcd_D_twoA_eq_one (E : EulerSquarePair) :
    Int.gcd E.D (2 * E.A) = 1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  exact IsCoprime.mul_right (D_coprime_two E) (isCoprime_comm.mp E.hADcop)

lemma gcd_D_fourA_eq_one (E : EulerSquarePair) :
    Int.gcd E.D (4 * E.A) = 1 := by
  apply Int.isCoprime_iff_gcd_eq_one.mp
  have hD2 : IsCoprime E.D (2 : ℤ) := D_coprime_two E
  have hD4 : IsCoprime E.D (4 : ℤ) := by
    have h : IsCoprime E.D ((2 : ℤ) * (2 : ℤ)) :=
      IsCoprime.mul_right hD2 hD2
    simpa using h
  exact IsCoprime.mul_right hD4 (isCoprime_comm.mp E.hADcop)

lemma pythagorean_D_twoA_C (E : EulerSquarePair) :
    PythagoreanTriple E.D (2 * E.A) E.C := by
  unfold PythagoreanTriple
  calc
    E.D * E.D + (2 * E.A) * (2 * E.A)
        = 4 * E.A ^ 2 + E.D ^ 2 := by ring
    _ = E.C ^ 2 := by rw [← E.hC]
    _ = E.C * E.C := by ring

lemma pythagorean_D_fourA_B (E : EulerSquarePair) :
    PythagoreanTriple E.D (4 * E.A) E.B := by
  unfold PythagoreanTriple
  calc
    E.D * E.D + (4 * E.A) * (4 * E.A)
        = 16 * E.A ^ 2 + E.D ^ 2 := by ring
    _ = E.B ^ 2 := by rw [← E.hB]
    _ = E.B * E.B := by ring

lemma two_mul_left_cancel_int {a b : ℤ} (h : (2 : ℤ) * a = 2 * b) : a = b := by
  exact (mul_left_inj' (show (2 : ℤ) ≠ 0 by norm_num)).mp h

lemma left_mod_two_eq_zero_of_even_mul_of_right_mod_two_eq_one
    {a b : ℤ} (hab : Even (a * b)) (hb : b % 2 = 1) :
    a % 2 = 0 := by
  have hnot : ¬ Odd a := by
    intro ha
    have hbOdd : Odd b := Int.odd_iff.mpr hb
    have hOdd : Odd (a * b) := Int.odd_mul.mpr ⟨ha, hbOdd⟩
    exact (Int.not_odd_iff_even.mpr hab) hOdd
  exact Int.not_odd_iff.mp hnot

/--
Classification of `(D, 2*A, C)`, normalized so the parameter multiplying the odd
parameter is the even one.  The price of this normalization is a signed formula
for the odd leg.
-/
lemma twoA_classification_signed_params (E : EulerSquarePair) :
    ∃ U V : ℤ,
      E.A = U * V ∧
      E.C = U ^ 2 + V ^ 2 ∧
      Int.gcd U V = 1 ∧
      U % 2 = 0 ∧
      V % 2 = 1 ∧
      (E.D = U ^ 2 - V ^ 2 ∨ -E.D = U ^ 2 - V ^ 2) := by
  obtain ⟨m, n, hD, h2A, hCsum, hmn_gcd, hmn_parity, _hm_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      (pythagorean_D_twoA_C E)
      (gcd_D_twoA_eq_one E)
      (D_mod_two_eq_one E)
      E.hCpos
  have hA_mn : E.A = m * n := by
    apply two_mul_left_cancel_int
    calc
      (2 : ℤ) * E.A = 2 * m * n := h2A
      _ = 2 * (m * n) := by ring
  rcases hmn_parity with hmn | hmn
  · refine ⟨m, n, hA_mn, hCsum, hmn_gcd, hmn.1, hmn.2, Or.inl hD⟩
  · refine ⟨n, m, ?_, ?_, ?_, hmn.2, hmn.1, Or.inr ?_⟩
    · calc
        E.A = m * n := hA_mn
        _ = n * m := by ring
    · rw [hCsum]
      ring
    · rw [Int.gcd_comm]
      exact hmn_gcd
    · rw [hD]
      ring

/--
Classification of `(D, 4*A, B)`.  Mathlib gives `4*A = 2*m*n`, hence
`2*A = m*n`.  Since exactly one of `m,n` is even, halve the even parameter.
The resulting `Up` satisfies `A = Up*Vp` and the odd-leg formula is signed:
`D = 4*Up^2 - Vp^2` or `-D = 4*Up^2 - Vp^2`.

The extra conclusion `Up % 2 = 0` uses `E.hAeven` and `Vp % 2 = 1`.
-/
lemma fourA_classification_signed_params (E : EulerSquarePair) :
    ∃ Up Vp : ℤ,
      E.A = Up * Vp ∧
      E.B = 4 * Up ^ 2 + Vp ^ 2 ∧
      Int.gcd Up Vp = 1 ∧
      Up % 2 = 0 ∧
      Vp % 2 = 1 ∧
      (E.D = 4 * Up ^ 2 - Vp ^ 2 ∨ -E.D = 4 * Up ^ 2 - Vp ^ 2) := by
  obtain ⟨m, n, hD, h4A, hBsum, hmn_gcd, hmn_parity, _hm_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      (pythagorean_D_fourA_B E)
      (gcd_D_fourA_eq_one E)
      (D_mod_two_eq_one E)
      E.hBpos
  have h2A_mn : (2 : ℤ) * E.A = m * n := by
    apply two_mul_left_cancel_int
    calc
      (2 : ℤ) * (2 * E.A) = 4 * E.A := by ring
      _ = 2 * m * n := h4A
      _ = 2 * (m * n) := by ring
  have hmn_coprime : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmn_gcd
  rcases hmn_parity with hmn | hmn
  · rcases Int.dvd_of_emod_eq_zero hmn.1 with ⟨Up, hUp⟩
    have hA : E.A = Up * n := by
      apply two_mul_left_cancel_int
      calc
        (2 : ℤ) * E.A = m * n := h2A_mn
        _ = 2 * (Up * n) := by
          rw [hUp]
          ring
    have hB' : E.B = 4 * Up ^ 2 + n ^ 2 := by
      rw [hBsum, hUp]
      ring
    have hD' : E.D = 4 * Up ^ 2 - n ^ 2 := by
      rw [hD, hUp]
      ring
    have hcop : Int.gcd Up n = 1 := by
      have hcop2Upn : IsCoprime (2 * Up) n := by
        simpa [hUp] using hmn_coprime
      have hcopUpn : IsCoprime Up n :=
        IsCoprime.of_mul_left_right hcop2Upn
      exact Int.isCoprime_iff_gcd_eq_one.mp hcopUpn
    have hUpEven : Up % 2 = 0 := by
      apply left_mod_two_eq_zero_of_even_mul_of_right_mod_two_eq_one
      · rw [← hA]
        exact E.hAeven
      · exact hmn.2
    refine ⟨Up, n, hA, hB', hcop, hUpEven, hmn.2, Or.inl hD'⟩
  · rcases Int.dvd_of_emod_eq_zero hmn.2 with ⟨Up, hUp⟩
    have hA : E.A = Up * m := by
      apply two_mul_left_cancel_int
      calc
        (2 : ℤ) * E.A = m * n := h2A_mn
        _ = 2 * (Up * m) := by
          rw [hUp]
          ring
    have hB' : E.B = 4 * Up ^ 2 + m ^ 2 := by
      rw [hBsum, hUp]
      ring
    have hD' : -E.D = 4 * Up ^ 2 - m ^ 2 := by
      rw [hD, hUp]
      ring
    have hcop : Int.gcd Up m = 1 := by
      have hcopm2Up : IsCoprime m (2 * Up) := by
        simpa [hUp] using hmn_coprime
      have hcopmUp : IsCoprime m Up :=
        IsCoprime.of_mul_right_right hcopm2Up
      exact Int.isCoprime_iff_gcd_eq_one.mp hcopmUp.symm
    have hUpEven : Up % 2 = 0 := by
      apply left_mod_two_eq_zero_of_even_mul_of_right_mod_two_eq_one
      · rw [← hA]
        exact E.hAeven
      · exact hmn.1
    refine ⟨Up, m, hA, hB', hcop, hUpEven, hmn.1, Or.inr hD'⟩

end EulerSquarePairDescent
```

## Notes on the wrappers

1. `D_mod_two_eq_one` should use `Int.odd_iff.mp E.hDodd`.  This is exactly the parity hypothesis expected by `PythagoreanTriple.coprime_classification'`.

2. `D_coprime_two` is often the cleanest bridge from oddness to coprimality: if `D = 2*k + 1`, then `1*D + (-k)*2 = 1`.  Then `IsCoprime.mul_right` combines coprimality with `2` or `4` and with `A`.

3. The Pythagorean triples are produced with `unfold PythagoreanTriple` and `ring`, rewriting `E.hC` and `E.hB` in the middle of a `calc`.

4. For `(D, 2*A, C)`, Mathlib gives `2*A = 2*m*n`, so cancellation gives `A = m*n`.  Reordering to make the first parameter even may flip the sign of the odd-leg formula.  This is why the wrapper concludes

```lean
E.D = U ^ 2 - V ^ 2 ∨ -E.D = U ^ 2 - V ^ 2
```

with `U % 2 = 0` and `V % 2 = 1`.

5. For `(D, 4*A, B)`, Mathlib gives `4*A = 2*m*n`, so cancellation gives `2*A = m*n`.  Halving the even one of `m,n` gives `A = Up*Vp` and

```lean
E.D = 4 * Up ^ 2 - Vp ^ 2 ∨ -E.D = 4 * Up ^ 2 - Vp ^ 2
```

The theorem `fourA_classification_signed_params` is the clean post-classification algebra wrapper requested for the second triple.

6. The proof of `Up % 2 = 0` does not come directly from Pythagorean classification.  It uses `E.hAeven`, `A = Up*Vp`, and `Vp % 2 = 1`: if `Up` were odd, then `Up*Vp` would be odd by `Int.odd_mul`, contradicting `Even A`.
