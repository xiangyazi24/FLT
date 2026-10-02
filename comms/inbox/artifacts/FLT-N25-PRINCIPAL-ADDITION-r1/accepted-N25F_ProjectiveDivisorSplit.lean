import FLT.Assumptions.MazurProof.CurveZetaEffectiveDivisors
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointPartition
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective

/-!
# Splitting the characteristic-two N25 projective divisor carrier

The full closed-point atom type is the disjoint sum of the three `W = 0`
boundary atoms and the complement represented by the affine `W = 1` chart.
Reindexing signed-divisor `Finsupp`s along that equivalence splits a full
projective divisor into three boundary coefficients and its chart divisor.
-/

set_option autoImplicit false

noncomputable section

namespace MazurProof.N25F_ProjectiveDivisorSplit

open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
-- The current `...WOpenPrimeSurjective` module exports these declarations
-- in its established namespace.
open RationalPointsN25QuotientTwoWOpenPrimeSurjective

/-! ## The atom partition -/

/-- Every tagged atom is a boundary atom. -/
theorem fullBoundaryAtomOfTag_isFullBoundaryAtom
    (t : FullBoundaryTag25Two) :
    IsFullBoundaryAtom (fullBoundaryAtomOfTag t) := by
  cases t with
  | X =>
      exact Or.inl rfl
  | YZ =>
      exact Or.inr (Or.inl rfl)
  | Z =>
      exact Or.inr (Or.inr rfl)

/-- The three tags exhaust the predicate `IsFullBoundaryAtom`.

This is the exhaustivity half of the partition.  It follows by unfolding the
existing definition; it is not assumed as a new premise. -/
theorem isFullBoundaryAtom_iff_exists_fullBoundaryTag
    (A : FullAtom25Two) :
    IsFullBoundaryAtom A ↔
      ∃ t : FullBoundaryTag25Two, fullBoundaryAtomOfTag t = A := by
  constructor
  · intro hA
    change
      A = fullBoundaryAtomX ∨
        A = fullBoundaryAtomYZ ∨
          A = fullBoundaryAtomZ at hA
    rcases hA with hX | hYZ | hZ
    · exact ⟨.X, hX.symm⟩
    · exact ⟨.YZ, hYZ.symm⟩
    · exact ⟨.Z, hZ.symm⟩
  · rintro ⟨t, ht⟩
    rw [← ht]
    exact fullBoundaryAtomOfTag_isFullBoundaryAtom t

/-- Inclusion of the tagged boundary and the nonboundary complement into the
full atom type. -/
def boundaryNonBoundaryToFullAtom :
    Sum FullBoundaryTag25Two FullNonBoundaryAtom25Two → FullAtom25Two
  | Sum.inl t => fullBoundaryAtomOfTag t
  | Sum.inr A => A.1

/-- The inclusion of the two pieces is injective.

The boundary/boundary case is exactly
`fullBoundaryAtomOfTag_injective`.  A mixed equality would make the
nonboundary atom satisfy `IsFullBoundaryAtom`, contradicting its subtype
certificate. -/
theorem boundaryNonBoundaryToFullAtom_injective :
    Function.Injective boundaryNonBoundaryToFullAtom := by
  intro S T hST
  cases S with
  | inl s =>
      cases T with
      | inl t =>
          change fullBoundaryAtomOfTag s = fullBoundaryAtomOfTag t at hST
          have hst : s = t := fullBoundaryAtomOfTag_injective hST
          subst t
          rfl
      | inr B =>
          exfalso
          apply B.2
          change fullBoundaryAtomOfTag s = B.1 at hST
          exact hST ▸ fullBoundaryAtomOfTag_isFullBoundaryAtom s
  | inr A =>
      cases T with
      | inl t =>
          exfalso
          apply A.2
          change A.1 = fullBoundaryAtomOfTag t at hST
          exact hST.symm ▸ fullBoundaryAtomOfTag_isFullBoundaryAtom t
      | inr B =>
          have hAB : A = B := by
            apply Subtype.ext
            change A.1 = B.1 at hST
            exact hST
          exact congrArg
            (fun C : FullNonBoundaryAtom25Two =>
              (Sum.inr C :
                Sum FullBoundaryTag25Two FullNonBoundaryAtom25Two))
            hAB

/-- Every full atom lies in one of the two pieces. -/
theorem boundaryNonBoundaryToFullAtom_surjective :
    Function.Surjective boundaryNonBoundaryToFullAtom := by
  classical
  intro A
  by_cases hA : IsFullBoundaryAtom A
  · obtain ⟨t, ht⟩ :=
      (isFullBoundaryAtom_iff_exists_fullBoundaryTag A).mp hA
    exact ⟨Sum.inl t, ht⟩
  · exact ⟨Sum.inr ⟨A, hA⟩, rfl⟩

/-- The inverse-oriented atom partition. -/
noncomputable def boundaryNonBoundaryEquivFullAtom :
    Sum FullBoundaryTag25Two FullNonBoundaryAtom25Two ≃ FullAtom25Two :=
  Equiv.ofBijective boundaryNonBoundaryToFullAtom
    ⟨boundaryNonBoundaryToFullAtom_injective,
      boundaryNonBoundaryToFullAtom_surjective⟩

/-- The requested orientation of the atom partition. -/
noncomputable def fullAtomEquivBoundaryNonBoundary :
    FullAtom25Two ≃
      Sum FullBoundaryTag25Two FullNonBoundaryAtom25Two :=
  boundaryNonBoundaryEquivFullAtom.symm

/-! ## Signed-divisor reindexing -/

/-- The actual projective signed-divisor carrier. -/
abbrev ProjectiveDivisor25Two :=
  fullClosedPointGrading25Two.Divisor

/-- Signed coefficients on the three tagged boundary atoms. -/
abbrev BoundaryDivisor25Two :=
  FullBoundaryTag25Two →₀ ℤ

/-- Signed coefficients on full nonboundary atoms. -/
abbrev NonBoundaryDivisor25Two :=
  FullNonBoundaryAtom25Two →₀ ℤ

/-- Signed affine-chart divisors, indexed by maximal ideals of the `W = 1`
chart. -/
abbrev WChartDivisor25Two :=
  WChartMaximalIdeal →₀ ℤ

/-- The boundary coefficient triple, ordered `X`, `YZ`, `Z`. -/
abbrev BoundaryCoefficients25Two :=
  ℤ × (ℤ × ℤ)

/-- First split a projective divisor into its tagged-boundary and nonboundary
parts. -/
noncomputable def fullDivisorEquivBoundaryNonBoundary :
    ProjectiveDivisor25Two ≃+
      (BoundaryDivisor25Two × NonBoundaryDivisor25Two) :=
  (Finsupp.domCongr fullAtomEquivBoundaryNonBoundary).trans
    Finsupp.sumFinsuppAddEquivProdFinsupp

/-- Reindex the nonboundary part by the actual maximal ideals of the affine
`W = 1` chart. -/
noncomputable def nonBoundaryDivisorEquivWChart :
    NonBoundaryDivisor25Two ≃+ WChartDivisor25Two :=
  Finsupp.domCongr fullNonBoundaryAtomEquivMaximalIdeal

/-- Apply the nonboundary/chart equivalence in the second component of a
product. -/
noncomputable def boundaryNonBoundaryDivisorEquivBoundaryChart :
    (BoundaryDivisor25Two × NonBoundaryDivisor25Two) ≃+
      (BoundaryDivisor25Two × WChartDivisor25Two) where
  toFun D :=
    (D.1, nonBoundaryDivisorEquivWChart D.2)
  invFun D :=
    (D.1, (nonBoundaryDivisorEquivWChart).symm D.2)
  left_inv D := by
    rcases D with ⟨B, N⟩
    simp
  right_inv D := by
    rcases D with ⟨B, C⟩
    simp
  map_add' D E := by
    apply Prod.ext
    · rfl
    · simpa using
        (nonBoundaryDivisorEquivWChart).map_add D.2 E.2

/-- Projective signed divisors split into a tagged boundary divisor and the
actual affine-chart divisor. -/
noncomputable def fullDivisorEquivBoundaryChart :
    ProjectiveDivisor25Two ≃+
      (BoundaryDivisor25Two × WChartDivisor25Two) :=
  fullDivisorEquivBoundaryNonBoundary.trans
    boundaryNonBoundaryDivisorEquivBoundaryChart

/-- A signed divisor on the three boundary tags is exactly three integer
coefficients in the order `X`, `YZ`, `Z`. -/
noncomputable def boundaryDivisorEquivCoefficients :
    BoundaryDivisor25Two ≃+ BoundaryCoefficients25Two where
  toFun D :=
    (D .X, (D .YZ, D .Z))
  invFun c :=
    Finsupp.single .X c.1 +
      Finsupp.single .YZ c.2.1 +
        Finsupp.single .Z c.2.2
  left_inv D := by
    ext t
    cases t <;> simp
  right_inv c := by
    apply Prod.ext
    · simp
    · apply Prod.ext <;> simp
  map_add' D E := by
    apply Prod.ext
    · simp
    · apply Prod.ext <;> simp

/-- Apply the explicit boundary-triple equivalence in the first component. -/
noncomputable def boundaryChartDivisorEquivCoefficientsChart :
    (BoundaryDivisor25Two × WChartDivisor25Two) ≃+
      (BoundaryCoefficients25Two × WChartDivisor25Two) where
  toFun D :=
    (boundaryDivisorEquivCoefficients D.1, D.2)
  invFun D :=
    ((boundaryDivisorEquivCoefficients).symm D.1, D.2)
  left_inv D := by
    rcases D with ⟨B, C⟩
    simp
  right_inv D := by
    rcases D with ⟨c, C⟩
    simp
  map_add' D E := by
    apply Prod.ext
    · simpa using
        (boundaryDivisorEquivCoefficients).map_add D.1 E.1
    · rfl

/-- Final carrier split:

* first integer: coefficient at `fullBoundaryAtomX`;
* second integer: coefficient at `fullBoundaryAtomYZ`;
* third integer: coefficient at `fullBoundaryAtomZ`;
* final `Finsupp`: the divisor on maximal ideals of the affine `W = 1` chart.
-/
noncomputable def fullDivisorEquivBoundaryCoefficientsChart :
    ProjectiveDivisor25Two ≃+
      (BoundaryCoefficients25Two × WChartDivisor25Two) :=
  fullDivisorEquivBoundaryChart.trans
    boundaryChartDivisorEquivCoefficientsChart

end MazurProof.N25F_ProjectiveDivisorSplit
