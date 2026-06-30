# Q2670 normalize bad Eisenstein quartic counterexample

Target file: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`.

The code below is standalone under `import Mathlib.Tactic`.  If the three definitions already exist in the target file, omit the definition block and paste only the private helpers plus `normalizedOfBadStatement`.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- A primitive nontrivial counterexample to the Eisenstein quartic residual. -/
def EisensteinQuarticBad (A N S : ℤ) : Prop :=
  IsCoprime A N ∧ A ≠ 0 ∧ N ≠ 0 ∧ A ^ 2 ≠ N ^ 2 ∧
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Normalized positive counterexample, with `0 < A < N` and `0 < S`. -/
def NormalizedEisensteinBad (A N S : ℤ) : Prop :=
  0 < A ∧ A < N ∧ 0 < S ∧ IsCoprime A N ∧
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Every bad counterexample can be normalized. -/
def NormalizedOfBadStatement : Prop :=
  ∀ {A N S : ℤ}, EisensteinQuarticBad A N S →
    ∃ A0 N0 S0 : ℤ, NormalizedEisensteinBad A0 N0 S0

private lemma q2670_quartic_pos {A N : ℤ}
    (hA : A ≠ 0) (hN : N ≠ 0) :
    0 < A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 := by
  have hA2pos : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hN2pos : 0 < N ^ 2 := sq_pos_of_ne_zero hN
  have hprod : 0 < A ^ 2 * N ^ 2 := mul_pos hA2pos hN2pos
  have hsq : 0 ≤ (A ^ 2 - N ^ 2) ^ 2 := sq_nonneg _
  have hid :
      A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 =
        (A ^ 2 - N ^ 2) ^ 2 + A ^ 2 * N ^ 2 := by
    ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos hsq hprod

private lemma q2670_abs_quartic {A N S : ℤ}
    (hS : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
    |S| ^ 2 = |A| ^ 4 - |A| ^ 2 * |N| ^ 2 + |N| ^ 4 := by
  have hS2 : |S| ^ 2 = S ^ 2 := sq_abs S
  have hA2 : |A| ^ 2 = A ^ 2 := sq_abs A
  have hN2 : |N| ^ 2 = N ^ 2 := sq_abs N
  have hA4 : |A| ^ 4 = A ^ 4 := by
    calc
      |A| ^ 4 = (|A| ^ 2) ^ 2 := by ring
      _ = (A ^ 2) ^ 2 := by rw [hA2]
      _ = A ^ 4 := by ring
  have hN4 : |N| ^ 4 = N ^ 4 := by
    calc
      |N| ^ 4 = (|N| ^ 2) ^ 2 := by ring
      _ = (N ^ 2) ^ 2 := by rw [hN2]
      _ = N ^ 4 := by ring
  calc
    |S| ^ 2 = S ^ 2 := hS2
    _ = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 := hS
    _ = |A| ^ 4 - |A| ^ 2 * |N| ^ 2 + |N| ^ 4 := by
      rw [hA4, hA2, hN2, hN4]

private lemma q2670_abs_coprime {A N : ℤ}
    (hcop : IsCoprime A N) :
    IsCoprime |A| |N| := by
  have hcopNat : Nat.Coprime A.natAbs N.natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hcop
  have hcopCast : IsCoprime (A.natAbs : ℤ) (N.natAbs : ℤ) :=
    Nat.Coprime.isCoprime hcopNat
  simpa only [Nat.cast_natAbs] using hcopCast

private lemma q2670_abs_ne_of_sq_ne {A N : ℤ}
    (hneq : A ^ 2 ≠ N ^ 2) :
    |A| ≠ |N| := by
  intro hAbs
  have hsq : A ^ 2 = N ^ 2 := by
    calc
      A ^ 2 = |A| ^ 2 := (sq_abs A).symm
      _ = |N| ^ 2 := by rw [hAbs]
      _ = N ^ 2 := sq_abs N
  exact hneq hsq

/-- Proof of the normalization statement. -/
theorem normalizedOfBadStatement : NormalizedOfBadStatement := by
  intro A N S hbad
  rcases hbad with ⟨hcop, hAne, hNne, hsq_ne, hS⟩
  have hAabspos : 0 < |A| := abs_pos.mpr hAne
  have hNabspos : 0 < |N| := abs_pos.mpr hNne
  have hSsqpos : 0 < S ^ 2 := by
    rw [hS]
    exact q2670_quartic_pos hAne hNne
  have hSne : S ≠ 0 := by
    intro h0
    rw [h0] at hSsqpos
    norm_num at hSsqpos
  have hSabspos : 0 < |S| := abs_pos.mpr hSne
  have hquartAbs :
      |S| ^ 2 = |A| ^ 4 - |A| ^ 2 * |N| ^ 2 + |N| ^ 4 :=
    q2670_abs_quartic hS
  have hcopAbs : IsCoprime |A| |N| := q2670_abs_coprime hcop
  have hAbs_ne : |A| ≠ |N| := q2670_abs_ne_of_sq_ne hsq_ne
  rcases lt_or_gt_of_ne hAbs_ne with hlt | hgt
  · refine ⟨|A|, |N|, |S|, ?_⟩
    exact ⟨hAabspos, hlt, hSabspos, hcopAbs, hquartAbs⟩
  · refine ⟨|N|, |A|, |S|, ?_⟩
    have hquartSwap :
        |S| ^ 2 = |N| ^ 4 - |N| ^ 2 * |A| ^ 2 + |A| ^ 4 := by
      rw [hquartAbs]
      ring
    exact ⟨hNabspos, hgt, hSabspos, hcopAbs.symm, hquartSwap⟩

-- API checks for the exact names used above.
#check abs_pos
#check sq_abs
#check Int.isCoprime_iff_nat_coprime
#check Nat.Coprime.isCoprime
#check Nat.cast_natAbs
#check lt_or_gt_of_ne

end MazurProof.RationalPointsN12
```

Notes:

* The positivity of `S0` comes from the identity
  `A^4 - A^2*N^2 + N^4 = (A^2 - N^2)^2 + A^2*N^2`, which is positive when `A` and `N` are nonzero.
* `A^2 ≠ N^2` is converted to `|A| ≠ |N|`; linear order then gives either `|A| < |N|` or the swapped case.
* Coprimality is preserved by absolute values via
  `Int.isCoprime_iff_nat_coprime`, `Nat.Coprime.isCoprime`, and `Nat.cast_natAbs`.
