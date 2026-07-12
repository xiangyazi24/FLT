import FLT.Assumptions.MazurProof.N18MumfordGroup
import FLT.Assumptions.MazurProof.N18MumfordBaseChange
import FLT.Assumptions.MazurProof.N18RouteC_Curve

/-!
# Transporting N18 Picard base change through balanced representatives

The project-specific ideal-extension compatibility is isolated in
`BaseChangeData.class_map`.  Everything after that seam—including injectivity,
annihilator descent, and finiteness transport—is inherited group algebra.
-/

namespace MazurProof.N18RouteC.BaseChange

noncomputable section

open N18Mumford

variable [NormalFormData ℚ] [NormalFormData L]

structure Data where
  picMap : ConcretePic ℚ →+ ConcretePic L
  class_map : ∀ M : Mumford ℚ,
    classOf L (mapQToL M) = picMap (classOf ℚ M)

namespace Data

variable (D : Data)

def mumfordMap : Mumford ℚ →+ Mumford L :=
  (classEquiv L).symm.toAddMonoidHom.comp
    (D.picMap.comp (classEquiv ℚ).toAddMonoidHom)

@[simp]
theorem mumfordMap_apply (M : Mumford ℚ) :
    D.mumfordMap M = mapQToL M := by
  apply (classEquiv L).injective
  simpa [mumfordMap, classEquiv_apply] using (D.class_map M).symm

theorem mumfordMap_injective : Function.Injective D.mumfordMap := by
  intro M N hMN
  apply mapQToL_injective
  simpa only [mumfordMap_apply] using hMN

theorem picMap_injective : Function.Injective D.picMap := by
  intro x y hxy
  have hM :
      D.mumfordMap ((classEquiv ℚ).symm x) =
        D.mumfordMap ((classEquiv ℚ).symm y) := by
    apply (classEquiv L).injective
    simpa [mumfordMap] using hxy
  exact (classEquiv ℚ).symm.injective (mumfordMap_injective D hM)

theorem annihilator_descends (D : Data) (n : ℕ)
    (hL : ∀ y : ConcretePic L, n • y = 0) :
    ∀ x : ConcretePic ℚ, n • x = 0 := by
  intro x
  apply picMap_injective D
  simpa only [map_nsmul, map_zero] using hL (D.picMap x)

@[reducible] noncomputable def finitePicQ (D : Data)
    [Finite (ConcretePic L)] :
    Finite (ConcretePic ℚ) :=
  Finite.of_injective D.picMap (picMap_injective D)

@[reducible] noncomputable def finiteCurveQ
    (D : Data)
    [Finite (ConcretePic L)]
    (abelJacobi : CurvePointQ → ConcretePic ℚ)
    (hAJ : Function.Injective abelJacobi) : Finite CurvePointQ := by
  letI : Finite (ConcretePic ℚ) := finitePicQ D
  exact Finite.of_injective abelJacobi hAJ

end Data

end

end MazurProof.N18RouteC.BaseChange
