# Q2443 twoA_triangle_param Lean route

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

namespace EulerAux

#check PythagoreanTriple
#check PythagoreanTriple.coprime_classification'

def normOddLeg (D : ℤ) : ℤ := if D % 4 = 3 then D else -D

/-!  GCD/parity bridge lemmas used before calling
`PythagoreanTriple.coprime_classification'`. -/

theorem int_gcd_one_of_natAbs_coprime {x y : ℤ}
    (h : Nat.Coprime x.natAbs y.natAbs) :
    Int.gcd x y = 1 := by
  simpa [Int.gcd, Nat.Coprime] using h

theorem natAbs_coprime_of_int_gcd_eq_one {x y : ℤ}
    (h : Int.gcd x y = 1) :
    Nat.Coprime x.natAbs y.natAbs := by
  simpa [Int.gcd, Nat.Coprime] using h

theorem int_emod_two_eq_one_of_odd {z : ℤ} (hz : Odd z) :
    z % 2 = 1 := by
  -- `Odd z` is the same parity class as `z % 2 = 1` for integer `%`.
  -- Useful APIs: `Int.emod_two_eq_zero_or_one`, `Int.dvd_of_emod_eq_zero`,
  -- `Int.emod_eq_zero_of_dvd`.
  sorry

theorem even_of_int_emod_two_eq_zero {z : ℤ} (hz : z % 2 = 0) :
    Even z := by
  -- Use `Int.dvd_of_emod_eq_zero hz`, then unfold `Even` as divisibility by `2`.
  sorry

theorem odd_of_int_emod_two_eq_one {z : ℤ} (hz : z % 2 = 1) :
    Odd z := by
  -- Write `z = 2 * (z / 2) + z % 2` by Euclidean division and rewrite with `hz`.
  sorry

theorem natAbs_coprime_two_of_odd {D : ℤ} (hOddD : Odd D) :
    Nat.Coprime D.natAbs 2 := by
  -- Equivalent to saying `2 ∤ D.natAbs`; use `int_emod_two_eq_one_of_odd`.
  sorry

theorem natAbs_coprime_two_mul_of_odd
    {A D : ℤ}
    (hOddD : Odd D)
    (hcop : Nat.Coprime A.natAbs D.natAbs) :
    Nat.Coprime D.natAbs (2 * A.natAbs) := by
  -- Combine `Nat.Coprime D.natAbs 2` and `hcop.symm`.
  -- Useful APIs:
  --   `Nat.coprime_mul_iff_right`
  --   `Nat.Coprime.mul_right`
  --   `Nat.Coprime.symm`
  have hD2 : Nat.Coprime D.natAbs 2 := natAbs_coprime_two_of_odd hOddD
  have hDA : Nat.Coprime D.natAbs A.natAbs := hcop.symm
  sorry

theorem twoA_triangle_gcd_eq_one
    {A D : ℤ}
    (hOddD : Odd D)
    (hcop : Nat.Coprime A.natAbs D.natAbs) :
    Int.gcd D (2 * A) = 1 := by
  apply int_gcd_one_of_natAbs_coprime
  have hD2A : Nat.Coprime D.natAbs (2 * A.natAbs) :=
    natAbs_coprime_two_mul_of_odd hOddD hcop
  simpa [Int.natAbs_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hD2A

/-!  Triangle construction with a positive hypotenuse. -/

theorem twoA_triangle_pythagorean_absS
    {A D S : ℤ}
    (hS : S^2 = 4 * A^2 + D^2) :
    PythagoreanTriple D (2 * A) (|S|) := by
  -- Unfold `PythagoreanTriple`; use `abs_mul_abs_self`/`abs_sq`-style simp,
  -- then the equation `hS` and `ring`.
  sorry

theorem twoA_triangle_absS_pos
    {A D S : ℤ}
    (hDne : D ≠ 0)
    (hS : S^2 = 4 * A^2 + D^2) :
    0 < |S| := by
  -- First prove `S ≠ 0`; otherwise `0 = 4*A^2 + D^2`, contradicting
  -- `sq_pos_of_ne_zero hDne` and nonnegativity of `4*A^2`.
  sorry

/-!  Mod-4 sign normalization for the odd leg. -/

theorem emod_four_eq_three_of_sq_sub_sq_even_odd
    {D m n : ℤ}
    (hD : D = m^2 - n^2)
    (hm : m % 2 = 0)
    (hn : n % 2 = 1) :
    D % 4 = 3 := by
  -- Squares of even integers are `0 mod 4`; squares of odd integers are `1 mod 4`.
  -- Then `0 - 1 = 3 mod 4`.
  sorry

theorem emod_four_eq_one_of_sq_sub_sq_odd_even
    {D m n : ℤ}
    (hD : D = m^2 - n^2)
    (hm : m % 2 = 1)
    (hn : n % 2 = 0) :
    D % 4 = 1 := by
  -- Squares of odd integers are `1 mod 4`; squares of even integers are `0 mod 4`.
  sorry

/-!  First EulerAux Pythagorean parametrization helper. -/

theorem twoA_triangle_param
    {A D S : ℤ}
    (hDne : D ≠ 0)
    (hOddD : Odd D)
    (hcop : Nat.Coprime A.natAbs D.natAbs)
    (hS : S^2 = 4*A^2 + D^2) :
    ∃ P Q : ℤ,
      Even P ∧ Odd Q ∧
      Nat.Coprime P.natAbs Q.natAbs ∧
      A = P*Q ∧
      normOddLeg D = P^2 - Q^2 := by
  have hTrip : PythagoreanTriple D (2 * A) (|S|) :=
    twoA_triangle_pythagorean_absS (A := A) (D := D) (S := S) hS
  have hGcd : Int.gcd D (2 * A) = 1 :=
    twoA_triangle_gcd_eq_one (A := A) (D := D) hOddD hcop
  have hDmod2 : D % 2 = 1 := int_emod_two_eq_one_of_odd hOddD
  have hZpos : 0 < |S| :=
    twoA_triangle_absS_pos (A := A) (D := D) (S := S) hDne hS
  rcases PythagoreanTriple.coprime_classification' hTrip hGcd hDmod2 hZpos with
    ⟨m, n, hDmn, h2Amn, _hZmn, hgmn, hparmn, _hm_nonneg⟩
  have hA : A = m * n := by
    nlinarith [h2Amn]
  rcases hparmn with h_even_odd | h_odd_even
  · rcases h_even_odd with ⟨hm2, hn2⟩
    refine ⟨m, n, ?_, ?_, ?_, ?_, ?_⟩
    · exact even_of_int_emod_two_eq_zero hm2
    · exact odd_of_int_emod_two_eq_one hn2
    · exact natAbs_coprime_of_int_gcd_eq_one hgmn
    · exact hA
    · have hDmod4 : D % 4 = 3 :=
        emod_four_eq_three_of_sq_sub_sq_even_odd hDmn hm2 hn2
      calc
        normOddLeg D = D := by
          rw [normOddLeg, if_pos hDmod4]
        _ = m^2 - n^2 := hDmn
  · rcases h_odd_even with ⟨hm2, hn2⟩
    refine ⟨n, m, ?_, ?_, ?_, ?_, ?_⟩
    · exact even_of_int_emod_two_eq_zero hn2
    · exact odd_of_int_emod_two_eq_one hm2
    · exact (natAbs_coprime_of_int_gcd_eq_one hgmn).symm
    · calc
        A = m * n := hA
        _ = n * m := by ring
    · have hDmod4 : D % 4 = 1 :=
        emod_four_eq_one_of_sq_sub_sq_odd_even hDmn hm2 hn2
      have hDnot3 : D % 4 ≠ 3 := by omega
      calc
        normOddLeg D = -D := by
          rw [normOddLeg, if_neg hDnot3]
        _ = n^2 - m^2 := by
          rw [hDmn]
          ring

end EulerAux
```
