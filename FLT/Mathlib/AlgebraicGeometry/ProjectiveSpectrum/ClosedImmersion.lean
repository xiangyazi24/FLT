import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions from surjective graded ring maps

A surjective graded ring map induces a closed immersion in the opposite
direction on projective spectra.  Mathlib already supplies the affine charts,
their functoriality, and Zariski locality of closed immersions.  The algebraic
point established here is that surjectivity survives degree-zero homogeneous
localization.
-/

noncomputable section

open DirectSum
open Graded
open HomogeneousIdeal
open HomogeneousLocalization
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

variable {A B σ τ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
variable [GradedRing 𝒜] [GradedRing ℬ]

namespace GradedRingHom

/-- A surjective graded ring map is surjective on each homogeneous piece.
An arbitrary preimage is replaced by its component in the required degree. -/
theorem gradedAddHom_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) (i : ℕ) :
    Function.Surjective (f.gradedAddHom i) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hf y
  refine ⟨DirectSum.decompose 𝒜 x i, ?_⟩
  apply Subtype.ext
  change f (DirectSum.decompose 𝒜 x i) = y
  rw [GradedRingHom.map_directSumDecompose, hx,
    DirectSum.decompose_of_mem_same ℬ hy]

end GradedRingHom

namespace HomogeneousLocalization.Away

/-- Homogeneous localization on a projective basic open preserves
surjectivity of a graded ring map.  The numerator is lifted in its prescribed
degree, while the denominator remains the same power of the chart element. -/
theorem map_surjective (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective ℬ (map_mem f hs) z
  obtain ⟨x, hx⟩ :=
    GradedRingHom.gradedAddHom_surjective f hf (n • d) ⟨y, hy⟩
  refine ⟨Away.mk 𝒜 hs n x x.2, ?_⟩
  rw [Away.map_mk]
  congr 1
  exact congrArg Subtype.val hx

end HomogeneousLocalization.Away

namespace AlgebraicGeometry.Proj

/-- A graded projective morphism is a closed immersion when its ring maps on
all positive-degree homogeneous basic-open charts are surjective. -/
theorem isClosedImmersion_map_of_away_surjective
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hAway : ∀ {i : ℕ} (_hi : 0 < i) (s : A) (_hs : s ∈ 𝒜 i),
      Function.Surjective (Away.map f s)) :
    IsClosedImmersion (Proj.map f hf) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsClosedImmersion) (Proj.affineOpenCover 𝒜).openCover]
  intro s
  have hpbAway : IsPullback
      (Proj.awayι ℬ (f s.2.1) (f.2 s.2.2) s.1.2)
      (Spec.map (CommRingCat.ofHom (Away.map f s.2.1)))
      (Proj.map f hf)
      (Proj.awayι 𝒜 s.2.1 s.2.2 s.1.2) := by
    exact (IsOpenImmersion.isPullback
      (Spec.map (CommRingCat.ofHom (Away.map f s.2.1)))
      (Proj.awayι ℬ (f s.2.1) (f.2 s.2.2) s.1.2)
      (Proj.awayι 𝒜 s.2.1 s.2.2 s.1.2)
      (Proj.map f hf)
      (Proj.awayι_comp_map f hf s.1.2 s.2.1 s.2.2)
      (by simp [Proj.opensRange_awayι,
        Proj.map_preimage_basicOpen])).flip
  have hclosed : IsClosedImmersion
      (pullback.snd (Proj.map f hf)
        (Proj.awayι 𝒜 s.2.1 s.2.2 s.1.2)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso
      @IsClosedImmersion hpbAway.isoPullback.hom]
    rw [hpbAway.isoPullback_hom_snd]
    exact IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Away.map f s.2.1))
      (hAway s.1.2 s.2.1 s.2.2)
  simpa [Scheme.Cover.pullbackHom,
    Scheme.AffineOpenCover.openCover, Scheme.AffineCover.cover,
    Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁,
    Proj.affineOpenCover, Proj.affineOpenCoverOfIrrelevantLESpan] using hclosed

/-- A surjective graded quotient satisfying the irrelevant-ideal condition
induces a closed immersion on projective spectra. -/
theorem isClosedImmersion_map_of_surjective
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (hfs : Function.Surjective f) :
    IsClosedImmersion (Proj.map f hf) := by
  apply isClosedImmersion_map_of_away_surjective f hf
  intro i hi s hs
  exact Away.map_surjective f hfs s hs

end AlgebraicGeometry.Proj
