# Q2310: `QuarticA` opposite-parity branch

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

lemma quarticA_int_sum_sq_pos_of_mul_ne_zero {u v : ℤ}
    (huv0 : u * v ≠ 0) :
    0 < u ^ 2 + v ^ 2 := by
  have hu0 : u ≠ 0 := left_ne_zero_of_mul huv0
  exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hu0) (sq_nonneg v)

lemma quarticA_even_square_leg_mod_two (v : ℤ) :
    (2 * v ^ 2) % 2 = 0 := by
  simpa using Int.mul_emod_right (2 : ℤ) (v ^ 2)

lemma quarticA_first_leg_mod_two_eq_one_of_second_leg_even
    {x y z : ℤ}
    (htrip : PythagoreanTriple x y z)
    (hcop : Int.gcd x y = 1)
    (hy : y % 2 = 0) :
    x % 2 = 1 := by
  obtain hbad | hgood := htrip.even_odd_of_coprime hcop
  · rw [hy] at hbad
    exact False.elim (zero_ne_one hbad.2)
  · exact hgood.1

/--
The core Pythagorean extraction.  The second leg is `2 * v ^ 2`, and after
primitive classification it is forced to be the even leg `2 * m * n`.
-/
theorem quarticA_evenLegParams_of_pythagorean_leg_coprime
    {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (htrip : PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2))
    (hlegcop : Int.gcd Z (2 * v ^ 2) = 1) :
    ∃ r s : ℤ,
      r * s ≠ 0 ∧ Int.gcd r s = 1 ∧
      r * s = v ^ 2 ∧
      r ^ 2 + s ^ 2 = u ^ 2 + v ^ 2 := by
  have hZmod : Z % 2 = 1 :=
    quarticA_first_leg_mod_two_eq_one_of_second_leg_even
      htrip hlegcop (quarticA_even_square_leg_mod_two v)
  have hsum_pos : 0 < u ^ 2 + v ^ 2 :=
    quarticA_int_sum_sq_pos_of_mul_ne_zero huv0
  obtain ⟨m, n, _hZ, h2v, hsum, hgcd, _hmnpar, _hm_nonneg⟩ :=
    PythagoreanTriple.coprime_classification'
      htrip hlegcop hZmod hsum_pos
  have hprod : m * n = v ^ 2 := by
    have htwo : 2 * (m * n) = 2 * (v ^ 2) := by
      calc
        2 * (m * n) = 2 * m * n := by ring
        _ = 2 * v ^ 2 := h2v.symm
    exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) htwo
  have hmn0 : m * n ≠ 0 := by
    have hv0 : v ≠ 0 := right_ne_zero_of_mul huv0
    have hvsq0 : v ^ 2 ≠ 0 := pow_ne_zero 2 hv0
    simpa [hprod] using hvsq0
  exact ⟨m, n, hmn0, hgcd, hprod, hsum.symm⟩

/--
Same extraction, with the full opposite-parity branch hypotheses in the
interface.  The only extra input is the primitive Pythagorean-leg coprimality
lemma for the QuarticA construction.
-/
theorem quarticA_evenLegParams_of_oppParity_with_leg_coprime
    {u v Z : ℤ}
    (_hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (_hne : u ^ 2 ≠ v ^ 2)
    (_hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z)
    (hlegcop : Int.gcd Z (2 * v ^ 2) = 1) :
    ∃ r s : ℤ,
      r * s ≠ 0 ∧ Int.gcd r s = 1 ∧
      r * s = v ^ 2 ∧
      r ^ 2 + s ^ 2 = u ^ 2 + v ^ 2 := by
  exact quarticA_evenLegParams_of_pythagorean_leg_coprime
    (u := u) (v := v) (Z := Z)
    huv0 (quarticA_pythagoreanTriple hA) hlegcop

theorem quarticA_eisensteinParam_of_oppParity_with_leg_coprime
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hopp : (Odd u ∧ Even v) ∨ (Even u ∧ Odd v))
    (hA : QuarticA u v Z)
    (hlegcop : Int.gcd Z (2 * v ^ 2) = 1) :
    QuarticAEisensteinParam u v := by
  obtain ⟨r, s, hrs0, hrs_coprime, hprod, hhyp⟩ :=
    quarticA_evenLegParams_of_oppParity_with_leg_coprime
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hopp hA hlegcop
  exact quarticA_eisensteinParam_from_evenLegParams
    (u := u) (v := v) (r := r) (s := s)
    hrs0 hrs_coprime hprod hhyp

/--
Small remaining project-specific input, stated as a parameter rather than an
axiom.  If the file already has this under another name, apply this theorem to
that existing lemma.
-/
theorem quarticAOppParityParamBridge_of_leg_coprime
    (hlegcop_of_quarticA :
      ∀ {u v Z : ℤ},
        Int.gcd u v = 1 →
        u * v ≠ 0 →
        u ^ 2 ≠ v ^ 2 →
        ((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) →
        QuarticA u v Z →
        Int.gcd Z (2 * v ^ 2) = 1) :
    QuarticAOppParityParamBridge := by
  dsimp [QuarticAOppParityParamBridge]
  intro u v Z hcop huv0 hne hopp hA
  exact quarticA_eisensteinParam_of_oppParity_with_leg_coprime
    (u := u) (v := v) (Z := Z)
    hcop huv0 hne hopp hA
    (hlegcop_of_quarticA
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hopp hA)

end MazurProof.RationalPointsN12
```

## Answers to the branch questions

1. In the primitive opposite-parity branch, `2 * v ^ 2` is the even leg, so it corresponds to `2 * m * n`, not to `m ^ 2 - n ^ 2`.  The code above uses `PythagoreanTriple.coprime_classification'`, which orients the classification from `Z % 2 = 1` and `0 < u ^ 2 + v ^ 2`; therefore the second-leg equation returned is exactly
   ```lean
   h2v : 2 * v ^ 2 = 2 * m * n
   ```

2. Yes, after that orientation we get `m * n = v ^ 2` exactly by cancelling the nonzero integer factor `2`:
   ```lean
   exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) htwo
   ```
   There is no sign ambiguity at this point.  If one uses `PythagoreanTriple.coprime_classification.mp` directly instead of the primed theorem, the disjunction has an orientation branch where the second leg is `m ^ 2 - n ^ 2`; that branch must be rejected by parity.  The primed theorem packages that rejection.

3. This branch does not need `Z` sign normalization and does not need an explicit `Z ≠ 0` hypothesis.  The only positivity needed for `coprime_classification'` is the hypotenuse positivity
   ```lean
   0 < u ^ 2 + v ^ 2
   ```
   which follows from `u * v ≠ 0`.  The sign of `Z` is allowed to be either sign of `m ^ 2 - n ^ 2`.

4. The one hard project-specific lemma still needed for a closed proof of `QuarticAOppParityParamBridge` is not parity/orientation; it is primitive-leg coprimality for the Pythagorean triple produced by QuarticA.  Exact type:
   ```lean
   ∀ {u v Z : ℤ},
     Int.gcd u v = 1 →
     u * v ≠ 0 →
     u ^ 2 ≠ v ^ 2 →
     ((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) →
     QuarticA u v Z →
     Int.gcd Z (2 * v ^ 2) = 1
   ```
   Once that lemma is available, `quarticAOppParityParamBridge_of_leg_coprime` proves the full bridge.

`u ^ 2 ≠ v ^ 2` and the explicit opposite-parity hypothesis are not used in the local Pythagorean extraction above; they belong naturally in the project-specific leg-coprimality lemma and in the safe bridge interface.
