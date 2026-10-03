import FLT.Assumptions.MazurProof.N25F_EffectiveAffineIdeal
import FLT.Assumptions.MazurProof.N25F_AffineNonpositiveRepresentative

/-! Actual W-chart adapter. NOT COMPILED in the full FLT project. -/
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_ShiftedAffineIdeal
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_AffineNonpositiveRepresentative N25F_EffectiveAffineIdeal
local notation "K" => FractionRing W

private def affinePart (E : ProjectiveDivisor25Two) : WHeightOne →₀ ℤ :=
  Finsupp.comapDomain (fun v => (fullNonBoundaryAtomEquivHeightOne.symm v).1) E
    (Subtype.coe_injective.comp fullNonBoundaryAtomEquivHeightOne.symm.injective).injOn

/-- Exact affine ideal for the actual principal-shifted divisor. -/
theorem exists_shifted_affine_ideal (D : ProjectiveDivisor25Two) :
    ∃ I : Ideal W, I ≠ ⊥ ∧
      (∀ A : FullNonBoundaryAtom25Two,
        FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
          (I : FractionalIdeal W⁰ K) = -affineNonpositiveRepresentative25Two D A.1) ∧
      ∀ f : K, f ∈ (I : FractionalIdeal W⁰ K) ↔
        f = 0 ∨ ∀ A : FullNonBoundaryAtom25Two,
          0 ≤ affineNonpositiveRepresentative25Two D A.1 +
            FractionalIdeal.count K (fullNonBoundaryAtomEquivHeightOne A)
              (FractionalIdeal.spanSingleton W⁰ f) := by
  let E := affineNonpositiveRepresentative25Two D
  have hd : ∀ v, affinePart E v ≤ 0 := by
    intro v
    exact affineNonpositiveRepresentative25Two_nonBoundary D
      (fullNonBoundaryAtomEquivHeightOne.symm v)
  obtain ⟨I, hI, hc, hm⟩ := exists_ideal_for_nonpositive_divisor (K := K) (affinePart E) hd
  refine ⟨I, hI, ?_, ?_⟩
  · intro A
    simpa only [affinePart, Finsupp.comapDomain_apply, Equiv.symm_apply_apply] using
      hc (fullNonBoundaryAtomEquivHeightOne A)
  · intro f
    rw [hm]
    apply or_congr_right
    constructor
    · intro h A
      simpa only [affinePart, Finsupp.comapDomain_apply, Equiv.symm_apply_apply] using
        h (fullNonBoundaryAtomEquivHeightOne A)
    · intro h v
      simpa only [affinePart, Finsupp.comapDomain_apply, Equiv.apply_symm_apply] using
        h (fullNonBoundaryAtomEquivHeightOne.symm v)

#print axioms exists_shifted_affine_ideal
end MazurProof.N25F_ShiftedAffineIdeal
