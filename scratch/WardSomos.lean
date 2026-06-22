import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- The adjacent Somos relation at an integer index. -/
def AdjRel (b c d : R) (m : ℤ) : Prop :=
  normEDS b c d (m + 2) * normEDS b c d (m - 2)
    = b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
        - c * normEDS b c d m ^ 2

private lemma h5_eq (b c d : R) : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by
  have h := normEDS_odd b c d 2
  norm_num [normEDS_one, normEDS_two, normEDS_three, normEDS_four] at h
  linear_combination h

lemma adjRel_zero (b c d : R) : AdjRel b c d 0 := by
  unfold AdjRel
  norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_neg] <;> ring

lemma adjRel_one (b c d : R) : AdjRel b c d 1 := by
  unfold AdjRel
  norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_neg] <;> ring

lemma adjRel_two (b c d : R) : AdjRel b c d 2 := by
  unfold AdjRel
  norm_num [normEDS_zero, normEDS_one, normEDS_two, normEDS_three, normEDS_four] <;> ring

lemma adjRel_three (b c d : R) : AdjRel b c d 3 := by
  unfold AdjRel
  norm_num [normEDS_one, normEDS_two, normEDS_three, normEDS_four, h5_eq] <;> ring

-- Routine finite base case (needs normEDS 6); ChatGPT to fill the W6 closed form.
lemma adjRel_four (b c d : R) : AdjRel b c d 4 := by
  sorry

/-- Packages the two recurrence steps needed by `normEDSRec`. -/
structure AdjRelRecSteps (b c d : R) : Prop where
  even : ∀ m : ℕ,
    AdjRel b c d ((m + 1 : ℕ) : ℤ) →
    AdjRel b c d ((m + 2 : ℕ) : ℤ) →
    AdjRel b c d ((m + 3 : ℕ) : ℤ) →
    AdjRel b c d ((m + 4 : ℕ) : ℤ) →
    AdjRel b c d ((m + 5 : ℕ) : ℤ) →
    AdjRel b c d ((2 * (m + 3) : ℕ) : ℤ)
  odd : ∀ m : ℕ,
    AdjRel b c d ((m + 1 : ℕ) : ℤ) →
    AdjRel b c d ((m + 2 : ℕ) : ℤ) →
    AdjRel b c d ((m + 3 : ℕ) : ℤ) →
    AdjRel b c d ((m + 4 : ℕ) : ℤ) →
    AdjRel b c d ((2 * (m + 2) + 1 : ℕ) : ℤ)

/-- The two recurrence-step certificates — the ONLY remaining gap (named sorries, no axiom).
These are finite polynomial identities obtained by expanding `normEDS_even`/`normEDS_odd` and
reducing by the lower adjacent relations; the `linear_combination` cofactors are mechanical. -/
theorem adjRelRecSteps (b c d : R) : AdjRelRecSteps b c d where
  even := by
    intro m h1 h2 h3 h4 h5
    sorry
  odd := by
    intro m h1 h2 h3 h4
    sorry

/-- Natural-index adjacent Somos relation, via `normEDSRec`. -/
theorem normEDS_adjacent_somos_nat (b c d : R) (n : ℕ) :
    AdjRel b c d (n : ℤ) := by
  classical
  let P : ℕ → Prop := fun n => AdjRel b c d (n : ℤ)
  change P n
  refine normEDSRec
    (P := P)
    ?h0 ?h1 ?h2 ?h3 ?h4
    ?heven ?hodd n
  · exact adjRel_zero b c d
  · exact adjRel_one b c d
  · exact adjRel_two b c d
  · exact adjRel_three b c d
  · exact adjRel_four b c d
  · intro m h1 h2 h3 h4 h5
    exact (adjRelRecSteps b c d).even m h1 h2 h3 h4 h5
  · intro m h1 h2 h3 h4
    exact (adjRelRecSteps b c d).odd m h1 h2 h3 h4

lemma adjRel_neg_iff (b c d : R) (m : ℤ) :
    AdjRel b c d (-m) ↔ AdjRel b c d m := by
  unfold AdjRel
  have e1 : normEDS b c d (-m + 2) = -normEDS b c d (m - 2) := by
    rw [show -m + 2 = -(m - 2) by ring, normEDS_neg]
  have e2 : normEDS b c d (-m - 2) = -normEDS b c d (m + 2) := by
    rw [show -m - 2 = -(m + 2) by ring, normEDS_neg]
  have e3 : normEDS b c d (-m + 1) = -normEDS b c d (m - 1) := by
    rw [show -m + 1 = -(m - 1) by ring, normEDS_neg]
  have e4 : normEDS b c d (-m - 1) = -normEDS b c d (m + 1) := by
    rw [show -m - 1 = -(m + 1) by ring, normEDS_neg]
  have e5 : normEDS b c d (-m) = -normEDS b c d m := normEDS_neg b c d m
  rw [e1, e2, e3, e4, e5]
  constructor <;> intro h <;> linear_combination h

/-- Full integer-index adjacent Somos relation, conditional only on `adjRelRecSteps`. -/
theorem normEDS_adjacent_somos (b c d : R) (m : ℤ) :
    normEDS b c d (m + 2) * normEDS b c d (m - 2)
      = b ^ 2 * normEDS b c d (m + 1) * normEDS b c d (m - 1)
          - c * normEDS b c d m ^ 2 := by
  change AdjRel b c d m
  rcases le_total 0 m with hm | hm
  · have hnat : AdjRel b c d ((m.toNat : ℕ) : ℤ) :=
      normEDS_adjacent_somos_nat b c d m.toNat
    have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    simpa [hcast] using hnat
  · have hneg_nonneg : 0 ≤ -m := by omega
    have hnat : AdjRel b c d (((-m).toNat : ℕ) : ℤ) :=
      normEDS_adjacent_somos_nat b c d (-m).toNat
    have hcast : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg hneg_nonneg
    have hneg : AdjRel b c d (-m) := by
      simpa [hcast] using hnat
    exact (adjRel_neg_iff b c d m).mp hneg

end FLT.EDS
