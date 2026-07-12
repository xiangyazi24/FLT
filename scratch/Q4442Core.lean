import Mathlib

set_option autoImplicit false

namespace FLT.CyclicExclusion.N18.BaseChangeReference

section Generic

variable {MQ ML JQ JL : Type*}
variable [AddCommGroup MQ] [AddCommGroup ML]
variable [AddCommGroup JQ] [AddCommGroup JL]

/--
Minimal interface exported by the concrete oriented-Mumford implementation.
The coefficient map need not be proved additive directly: additivity is obtained
by transport through the oriented class groups.
-/
structure Data (MQ ML JQ JL : Type*)
    [AddCommGroup MQ] [AddCommGroup ML]
    [AddCommGroup JQ] [AddCommGroup JL] where
  classQ : MQ ≃+ JQ
  classL : ML ≃+ JL
  mapCoeffs : MQ → ML
  mapCoeffs_injective : Function.Injective mapCoeffs
  orientedClassBaseChange : JQ →+ JL
  class_mapCoeffs : ∀ M : MQ,
    classL (mapCoeffs M) = orientedClassBaseChange (classQ M)

namespace Data

variable (d : Data MQ ML JQ JL)

/-- Additive base change on reduced Mumford forms, transported from the
oriented-class base-change homomorphism. -/
noncomputable def baseChangeMumford : MQ →+ ML :=
  d.classL.symm.toAddMonoidHom.comp
    (d.orientedClassBaseChange.comp d.classQ.toAddMonoidHom)

@[simp] theorem baseChangeMumford_apply (M : MQ) :
    d.baseChangeMumford M = d.mapCoeffs M := by
  apply d.classL.injective
  change d.orientedClassBaseChange (d.classQ M) = d.classL (d.mapCoeffs M)
  exact (d.class_mapCoeffs M).symm

/-- The induced map on `Pic^0`; this is exactly the oriented quotient map. -/
noncomputable abbrev baseChangePic : JQ →+ JL :=
  d.orientedClassBaseChange

/-- Compatibility with the class of a Mumford representative. -/
@[simp] theorem class_baseChangeMumford (M : MQ) :
    d.classL (d.baseChangeMumford M) =
      d.baseChangePic (d.classQ M) := by
  simpa only [baseChangeMumford_apply] using d.class_mapCoeffs M

/-- Coefficient extension on reduced Mumford forms is injective. -/
theorem baseChangeMumford_injective :
    Function.Injective d.baseChangeMumford := by
  intro x y hxy
  apply d.mapCoeffs_injective
  simpa only [baseChangeMumford_apply] using hxy

/-- Injectivity of base change on `Pic^0`, derived from unique reduced Mumford forms. -/
theorem baseChangePic_injective : Function.Injective d.baseChangePic := by
  intro x y hxy
  have hM : d.baseChangeMumford (d.classQ.symm x) =
      d.baseChangeMumford (d.classQ.symm y) := by
    apply d.classL.injective
    change d.baseChangePic (d.classQ (d.classQ.symm x)) =
      d.baseChangePic (d.classQ (d.classQ.symm y))
    simpa using hxy
  exact d.classQ.symm.injective (d.baseChangeMumford_injective hM)

/-- A uniform annihilator over the extension field descends to the ground field. -/
theorem annihilator_descends (n : ℕ)
    (hL : ∀ y : JL, n • y = 0) (x : JQ) :
    n • x = 0 := by
  apply baseChangePic_injective d
  rw [map_nsmul, hL, map_zero]

/-- Finiteness descends along an injective base-change map. -/
@[reducible] noncomputable def finite_source_of_finite_target [Finite JL] : Finite JQ :=
  Finite.of_injective d.baseChangePic (baseChangePic_injective d)

/-- If Abel--Jacobi is injective and the extension-field Picard group is finite,
then the set of ground-field curve points is finite. -/
@[reducible] noncomputable def finite_curvePoints_of_finite_pic
    {CPoint : Type*} [Finite JL]
    (abelJacobi : CPoint → JQ)
    (hAJ : Function.Injective abelJacobi) : Finite CPoint := by
  letI : Finite JQ := d.finite_source_of_finite_target
  exact Finite.of_injective abelJacobi hAJ

end Data

end Generic

end FLT.CyclicExclusion.N18.BaseChangeReference
