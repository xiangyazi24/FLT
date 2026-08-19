import FLT.Assumptions.MazurProof.N13RationalPicardEndpoint
import FLT.Assumptions.MazurProof.N13QuadraticTwoChartSpreadSaturation

/-!
# Direct construction of CanonicalMappedSpecialFamily for the trivial kernel

This file proves the contraction-to-specialIdeal equality for kernel = ⊥
WITHOUT using `class_eq_iff`, breaking the circularity in the N13 wiring.

The key chain:
1. baseLine is vertically saturated (pairLine_affineVerticallySaturated)
2. contractIdeal(graphIdeal of mapMumford rationalBaseMumford) = baseLine.affineIdeal
   (saturation retract)
3. map reduceCoordinate (baseLine.affineIdeal) = specialIdeal
   (restrict_baseLine_affineIdeal + specialBaseDivisor_affineIdeal)
-/

namespace MazurProof.N13TrivialKernelFamily

noncomputable section

open N13RationalPicardEndpoint
open N13RationalPicardSpreadExistence
open N13RationalAbelChartBase
open N13RationalKernelDoublingAdapter

private abbrev G := N13RationalPointEndgame.G

/-- baseLine is vertically saturated because it is a pairLine. -/
private theorem baseLine_affineVerticallySaturated :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      N13RationalAbelChartBase.baseLine :=
  N13QuadraticTwoChartSpreadSaturation.pairLine_affineVerticallySaturated
    0 0 (-1) 0
    N13RationalAbelChartBase.zero_onCurve
    N13RationalAbelChartBase.negOne_onCurve

/-- The contraction of the graph ideal of the mapped base Mumford datum
equals baseLine's affine ideal. This is the saturation retract: localize
baseLine.affineIdeal to get the graph ideal, contract back to get baseLine.affineIdeal. -/
private theorem contractIdeal_graphIdeal_base_eq_baseLine :
    N13IntegralModelContraction.contractIdeal
        (N13CanonicalContractionQuotient.graphIdeal
          (mapMumford rationalBaseMumford).toSemi) =
      baseLine.affineIdeal := by
  apply N13IntegralInfinityGraphSaturation.contractIdeal_eq_of_map_eq_of_scalarSaturated
  · change
      Ideal.map N13IntegralFractionalHull.integralToRational
          baseLine.affineIdeal =
        N13CanonicalContractionQuotient.graphIdeal
          (mapMumford rationalBaseMumford).toSemi
    exact map_baseLine_affineIdeal
  · exact baseLine_affineVerticallySaturated

/-- Reducing baseLine's affine ideal gives specialIdeal. -/
private theorem reduce_baseLine_eq_specialIdeal :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        baseLine.affineIdeal =
      N13SpecialQuotientBasis.specialIdeal := by
  calc
    Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          baseLine.affineIdeal =
        (N13TwoChartSpecialRestriction.restrict baseLine).affineIdeal := rfl
    _ = (N13SpecialDivisorCharts.ofDivisor
          N13AbelChartBase.specialBaseDivisor).affineIdeal :=
      restrict_baseLine_affineIdeal
    _ = N13SpecialQuotientBasis.specialIdeal :=
      specialBaseDivisor_affineIdeal

/-- The full contraction-reduction chain for the base Mumford datum. -/
theorem contraction_base_eq_specialIdeal :
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal
            (mapMumford rationalBaseMumford).toSemi)) =
      N13SpecialQuotientBasis.specialIdeal := by
  rw [contractIdeal_graphIdeal_base_eq_baseLine]
  exact reduce_baseLine_eq_specialIdeal

/-- CanonicalMappedSpecialFamily for the trivial kernel ⊥.

For the only element z = 0 of ⊥:
- canonicalMappedSpecialMumford(subgroupToPic ⊥ 0) = mapMumford rationalBaseMumford
  (via canonicalMappedSpecialMumford_subgroup_eq_mapMumford + normalizedMumford_rationalBasePic)
- The contraction-reduction of its graph ideal = specialIdeal
  (via baseLine saturation retract)
-/
def trivialKernelFamily :
    CanonicalMappedSpecialFamily (⊥ : AddSubgroup G) where
  map_contract_eq_special := by
    intro ⟨z, hz⟩
    have hz0 : z = 0 := by
      rwa [AddSubgroup.mem_bot] at hz
    subst hz0
    rw [canonicalMappedSpecialMumford_subgroup_eq_mapMumford]
    simp only [zero_add]
    rw [normalizedMumford_rationalBasePic]
    exact contraction_base_eq_specialIdeal

/-- The pair recovered at z = 0 is basePair, by centeredPic injectivity. -/
private theorem trivialKernelFamily_pair_zero :
    trivialKernelFamily.toNearBaseFamily.pair ⟨0, AddSubgroup.zero_mem ⊥⟩ =
      N13TwoAdicAbelChartData.basePair := by
  apply N13TwoAdicAbelChartPic.DiskPair.centeredPic_injective
  rw [NearBaseFamily.realize trivialKernelFamily.toNearBaseFamily,
    N13TwoAdicAbelChartSection.subgroupToPic, AddMonoidHom.comp_apply,
    AddSubgroup.coe_subtype, AddSubgroup.coe_mk,
    map_zero, N13TwoAdicAbelChartPic.DiskPair.centeredPic_basePair]

/-- coord at z = 0 is the zero function. -/
private theorem trivialKernelFamily_coord_zero :
    trivialKernelFamily.toNearBaseFamily.coord ⟨0, AddSubgroup.zero_mem ⊥⟩ = 0 := by
  simp only [NearBaseFamily.coord, trivialKernelFamily_pair_zero,
    N13TwoAdicAbelChartData.DiskPair.coord_basePair]

/-- FirstJetDoublingCompatibility for the trivial kernel family.

For ⊥, z ranges only over {0}. At z = 0: coord 0 = 0, coordIdeal 0 = ⊥,
and 0 ∈ ⊥ * ⊥ = ⊥. -/
def trivialKernelFirstJetCompat :
    FirstJetDoublingCompatibility trivialKernelFamily.toNearBaseFamily where
  compare := by
    intro ⟨z, hz⟩ i
    have hz0 : z = 0 := by rwa [AddSubgroup.mem_bot] at hz
    subst hz0
    let F := trivialKernelFamily.toNearBaseFamily
    let z₀ : (⊥ : AddSubgroup G) := ⟨0, AddSubgroup.zero_mem ⊥⟩
    show F.coord (2 • z₀) i - F.squareJet z₀ i ∈
      N13TwoAdicKernelChart.coordIdeal F.coord z₀ *
        N13TwoAdicKernelChart.coordIdeal F.coord z₀
    have hcoord : F.coord z₀ = 0 := trivialKernelFamily_coord_zero
    have hspan : N13TwoAdicKernelChart.coordIdeal F.coord z₀ =
        (⊥ : Ideal N13TwoAdicKernelChart.R₂) := by
      rw [N13TwoAdicKernelChart.coordIdeal, hcoord, Ideal.span_eq_bot]
      intro x hx
      obtain ⟨j, rfl⟩ := hx
      exact Pi.zero_apply j
    rw [hspan, Ideal.bot_mul]
    have h2z : 2 • z₀ = z₀ := by
      simp [z₀, two_nsmul]
    rw [h2z, hcoord, Pi.zero_apply]
    have h := NearBaseFamily.squareJet_sub_double_coord_mem_sq F z₀ i
    rw [hspan, Ideal.bot_mul] at h
    rw [hcoord, Pi.zero_apply, add_zero, sub_zero] at h
    simpa using h

/-- NSeparated for the trivial kernel follows from the family and FJDC. -/
theorem trivialKernel_separated :
    N18RouteC.Separated.NSeparated (⊥ : AddSubgroup G) 2 :=
  trivialKernelFamily.separated trivialKernelFirstJetCompat

end

end MazurProof.N13TrivialKernelFamily
