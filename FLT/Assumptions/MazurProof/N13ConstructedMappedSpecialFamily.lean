import FLT.Assumptions.MazurProof.N13KernelBasePic

/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K1. Source candidate; Lean and axiom checks NOT RUN.

Construct the adapter's exact MappedSpecialFamily for the actual additive
specialization kernel. No mapped-special, near-base, or compatibility
assumption is an input. FirstJetDoublingCompatibility remains separate.
-/

namespace MazurProof.N13ConstructedMappedSpecialFamily

noncomputable section
open N13KernelBaseDivisor N13KernelInfinityMultiplicity N13KernelGraphContraction
open N13KernelBasePic N13TwoChartPicardRealization N13EffectiveGraphData
open N13RationalKernelDoublingAdapter
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem representative_nonempty (z : Kernel) :
    Nonempty (MappedSpecialRepresentative
      (N13TwoAdicAbelChartSection.subgroupToPic Kernel z)) := by
  let D := N13CalibratedChooser.choose
    ((z : N13ConstructedSpecialization.G) + baseTranslate)
  obtain ⟨E, he, _, hn, hr, hs⟩ := chosen_translated_finite_graph z
  refine ⟨{ mumford := balancedGraph E he.1
            class_eq := ?_
            map_contract_eq_special := ?_ }⟩
  · rw [balancedGraph_class D E he.1 hn hr]
    rw [show D.toGenericPic = N13InfinityBaseChange.picMapRatToQ₂
      ((z : N13ConstructedSpecialization.G) + baseTranslate) from
        N13CalibratedChooser.choose_generic _]
    rw [map_add, basePic_eq_translated_twist]
    change N13InfinityBaseChange.picMapRatToQ₂ (z : N13ConstructedSpecialization.G) +
      N13InfinityBaseChange.picMapRatToQ₂ baseTranslate + infinityShift =
        N13InfinityBaseChange.picMapRatToQ₂ (z : N13ConstructedSpecialization.G) +
          (N13InfinityBaseChange.picMapRatToQ₂ baseTranslate + infinityShift)
    exact add_assoc _ _ _
  · exact balancedGraph_map_contract D E he.1 hr hs (chosen_translated_divisor z)

/-- K1 for the constructed specialization's actual kernel. -/
def mappedSpecialFamily : MappedSpecialFamily Kernel where
  representative z := Classical.choice (representative_nonempty z)

/-- Existing exact Hensel graph recovery supplies the centered family. -/
def nearBaseFamily : NearBaseFamily Kernel := mappedSpecialFamily.toNearBaseFamily

theorem nearBaseFamily_realizes (z : Kernel) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic (nearBaseFamily.pair z) =
      N13TwoAdicAbelChartSection.subgroupToPic Kernel z :=
  nearBaseFamily.realize z

end
end MazurProof.N13ConstructedMappedSpecialFamily
