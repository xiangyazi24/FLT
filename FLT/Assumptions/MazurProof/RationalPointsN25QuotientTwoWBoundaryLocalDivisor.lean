import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointPartition
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryArtinLocal
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryYZLocal
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

/-!
# The global `W = 0` boundary divisor

The previously defined degree-six effective boundary cycle is identified here
with the genuine local orders of the section `W` at all three points.  Its
nonzero carrier is exactly the boundary part of the full closed-point grading.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryLocalDivisor

open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWBoundaryArtinLocal
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal

local instance fullAtomDecidableEq : DecidableEq FullAtom25Two :=
  Classical.decEq _

@[simp]
theorem wBoundaryHyperplaneDivisor_apply_X :
    wBoundaryHyperplaneDivisor fullBoundaryAtomX = 3 := by
  simp [wBoundaryHyperplaneDivisor, fullBoundaryAtomX_ne_YZ,
    fullBoundaryAtomX_ne_Z]

@[simp]
theorem wBoundaryHyperplaneDivisor_apply_YZ :
    wBoundaryHyperplaneDivisor fullBoundaryAtomYZ = 1 := by
  simp [wBoundaryHyperplaneDivisor, fullBoundaryAtomX_ne_YZ,
    fullBoundaryAtomYZ_ne_Z]

@[simp]
theorem wBoundaryHyperplaneDivisor_apply_Z :
    wBoundaryHyperplaneDivisor fullBoundaryAtomZ = 2 := by
  simp [wBoundaryHyperplaneDivisor, fullBoundaryAtomX_ne_Z,
    fullBoundaryAtomYZ_ne_Z]

/-- The coefficient at `[1:0:0:0]` is the local order of `W/X`. -/
theorem wBoundaryHyperplaneDivisor_apply_X_eq_ord :
    wBoundaryHyperplaneDivisor fullBoundaryAtomX =
      Ring.ord XLocalRing xWGerm := by
  rw [wBoundaryHyperplaneDivisor_apply_X, xWGerm_ord_eq_three]
  norm_num

/-- The coefficient at `[0:1:1:0]` is the local order of `W/Y`. -/
theorem wBoundaryHyperplaneDivisor_apply_YZ_eq_ord :
    wBoundaryHyperplaneDivisor fullBoundaryAtomYZ =
      Ring.ord YZLocalRing yzWGerm := by
  rw [wBoundaryHyperplaneDivisor_apply_YZ, yzWGerm_ord_eq_one]
  norm_num

/-- The coefficient at `[0:0:1:0]` is the local order of `W/Z`. -/
theorem wBoundaryHyperplaneDivisor_apply_Z_eq_ord :
    wBoundaryHyperplaneDivisor fullBoundaryAtomZ =
      Ring.ord ZLocalRing zWGerm := by
  rw [wBoundaryHyperplaneDivisor_apply_Z, zWGerm_ord_eq_two]
  norm_num

/-- The genuine local order of `W` attached to each boundary tag. -/
noncomputable def wBoundaryLocalOrderOfTag :
    FullBoundaryTag25Two → WithTop ℕ
  | .X => Ring.ord XLocalRing xWGerm
  | .YZ => Ring.ord YZLocalRing yzWGerm
  | .Z => Ring.ord ZLocalRing zWGerm

/-- Uniformly on the three tags, the coefficient of the global boundary
divisor is its genuine local order. -/
theorem wBoundaryHyperplaneDivisor_apply_tag_eq_ord
    (tag : FullBoundaryTag25Two) :
    (wBoundaryHyperplaneDivisor (fullBoundaryAtomOfTag tag) : WithTop ℕ) =
      wBoundaryLocalOrderOfTag tag := by
  cases tag
  · exact wBoundaryHyperplaneDivisor_apply_X_eq_ord
  · exact wBoundaryHyperplaneDivisor_apply_YZ_eq_ord
  · exact wBoundaryHyperplaneDivisor_apply_Z_eq_ord

/-- The explicit effective divisor has nonzero coefficient exactly at the
three closed points on `W = 0`. -/
theorem wBoundaryHyperplaneDivisor_ne_zero_iff
    (A : FullAtom25Two) :
    wBoundaryHyperplaneDivisor A ≠ 0 ↔ IsFullBoundaryAtom A := by
  constructor
  · intro hA
    by_contra hboundary
    have hX : A ≠ fullBoundaryAtomX := by
      intro h
      exact hboundary (Or.inl h)
    have hYZ : A ≠ fullBoundaryAtomYZ := by
      intro h
      exact hboundary (Or.inr (Or.inl h))
    have hZ : A ≠ fullBoundaryAtomZ := by
      intro h
      exact hboundary (Or.inr (Or.inr h))
    exact hA (by
      simp [wBoundaryHyperplaneDivisor, hX, hYZ, hZ])
  · intro hA
    rcases hA with rfl | rfl | rfl
    · simp
    · simp
    · simp

/-- The finite support of the divisor is the image of the three boundary
tags in the full closed-point grading. -/
theorem wBoundaryHyperplaneDivisor_support :
    wBoundaryHyperplaneDivisor.support =
      Finset.univ.image fullBoundaryAtomOfTag := by
  classical
  ext A
  rw [Finsupp.mem_support_iff, wBoundaryHyperplaneDivisor_ne_zero_iff]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (hX | hYZ | hZ)
    · exact ⟨FullBoundaryTag25Two.X, hX.symm⟩
    · exact ⟨FullBoundaryTag25Two.YZ, hYZ.symm⟩
    · exact ⟨FullBoundaryTag25Two.Z, hZ.symm⟩
  · rintro ⟨tag, rfl⟩
    cases tag <;> simp [IsFullBoundaryAtom, fullBoundaryAtomOfTag]

end MazurProof.RationalPointsN25QuotientTwoWBoundaryLocalDivisor
