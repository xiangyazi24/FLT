import FLT.Assumptions.MazurProof.N13InverseInfinityWitnessClass
import FLT.Assumptions.MazurProof.N13RationalPicardSpreadExistence

/-!
Source pin: a6290bc36c3549d89239da82b13b1f59ebd0388e.
Candidate only. Lean elaboration / build / axiom checks: NOT RUN.
This repairs degree-zero CLASS realization, not exact normalized raw equality.
It does not assert global specialization or additivity.
-/

namespace MazurProof.N13CoherentDegreeZeroChooser

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Model := N13TwoChartPicardRealization.Model
abbrev Data := N13TwoChartPicardRealization.Data

/-- Data's special class is completely insensitive to the separate generic
orientation. This is a limitation, not a coherence lemma. -/
theorem reorientData_toSpecialPic
    (D : N13Mumford.Mumford N13InfinityBaseChange.Q₂) (R : Data) :
    (N13RationalPicardSpreadExistence.reorientData D R).toSpecialPic =
      R.toSpecialPic := rfl

/-- Extensionality in the three non-proof Mumford fields. -/
theorem mumford_ext {D E : SexticMumford.Mumford Model}
    (hu : D.u = E.u) (hv : D.v = E.v) (hn : D.nInf = E.nInf) : D = E := by
  cases D
  cases E
  simp_all

/-- The three correct degree-zero witnesses, with the nInf=2 witness allowed
to change the raw representative by a principal relation.

The stored chart data are respectively the anchored negative infinity line,
the doubled positive infinity line, and the C+A line. -/
theorem exists_degreeZero_class_data
    (D : SexticMumford.Mumford Model) (hdeg : D.u.natDegree = 0) :
    ∃ R : Data,
      R.toGenericPic =
        SexticMumford.classOf Model
          (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂) D ∧
      N13TwoChartPicardRealization.AffineVerticallySaturated R.charts ∧
      (R = N13InfinityPointPicardRealization.infinityMinusData ∨
       R = N13InfinityPointPicardRealization.infinityPlusData ∨
       R = N13InverseInfinityWitness.inverseInfinityData) := by
  have hu : D.u = 1 := Polynomial.eq_one_of_monic_natDegree_zero D.u_monic hdeg
  have hv : D.v = 0 := by
    have hr := D.v_reduced
    rw [hu] at hr
    simpa using hr.symm
  have hb : D.nInf ≤ 2 := by
    have h := D.infinity_bound
    rw [hdeg] at h
    omega
  interval_cases hn : D.nInf
  · have hD : D = SexticMumford.infinityMinusMumford Model := by
      apply mumford_ext
      · simpa [SexticMumford.infinityMinusMumford] using hu
      · simpa [SexticMumford.infinityMinusMumford] using hv
      · simpa [SexticMumford.infinityMinusMumford] using hn
    subst D
    exact ⟨N13InfinityPointPicardRealization.infinityMinusData,
      N13InfinityPointPicardRealization.infinityMinusData_toGenericPic,
      N13InfinityPointPicardRealization.infinityMinusLine_affineVerticallySaturated,
      Or.inl rfl⟩
  · have hD : D = SexticMumford.zero Model := by
      apply mumford_ext
      · simpa [SexticMumford.zero] using hu
      · simpa [SexticMumford.zero] using hv
      · simpa [SexticMumford.zero] using hn
    subst D
    exact ⟨N13InfinityPointPicardRealization.infinityPlusData,
      N13InfinityPointPicardRealization.infinityPlusData_toGenericPic,
      N13InfinityPointPicardRealization.infinityPlusLine_affineVerticallySaturated,
      Or.inr (Or.inl rfl)⟩
  · have hD : D = N13Arithmetic.oppositeInfinityMumford
        N13TwoChartPicardRealization.Q₂ := by
      apply mumford_ext
      · simpa [N13Arithmetic.oppositeInfinityMumford] using hu
      · simpa [N13Arithmetic.oppositeInfinityMumford] using hv
      · simpa [N13Arithmetic.oppositeInfinityMumford] using hn
    subst D
    exact ⟨N13InverseInfinityWitness.inverseInfinityData,
      N13InverseInfinityWitness.inverseInfinityData_toGenericPic_eq_opposite,
      N13InverseInfinityWitness.inverseInfinityData_affineVerticallySaturated,
      Or.inr (Or.inr rfl)⟩

/-- The same C+A chart line, marked by the standard degree-two raw order -1,
has twice the opposite-infinity class. This follows from proved declarations,
not merely from the explanatory source header. -/
theorem caLine_minus_one_class :
    N13TwoChartPicardRealization.genericClass N13InverseInfinityWitness.caLine (-1) =
      SexticMumford.classOf Model
          (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂)
          (N13Arithmetic.oppositeInfinityMumford N13TwoChartPicardRealization.Q₂) +
        SexticMumford.classOf Model
          (N13Infinity.positiveInfinityOrder N13TwoChartPicardRealization.Q₂)
          (N13Arithmetic.oppositeInfinityMumford N13TwoChartPicardRealization.Q₂) := by
  have h := N13InverseInfinityWitness.inverseInfinityData_toGenericPic
  rw [N13InverseInfinityWitness.inverseInfinityData_toGenericPic_eq_opposite] at h
  exact ((eq_sub_iff_add_eq).mp h).symm

end
end MazurProof.N13CoherentDegreeZeroChooser
