import Mathlib

set_option autoImplicit false

namespace FLT.CyclicExclusion.N18.BaseChangeReference

section Generic

variable {MQ ML JQ JL : Type*}
variable [AddCommGroup MQ] [AddCommGroup ML]
variable [AddCommGroup JQ] [AddCommGroup JL]

/--
The interface exported by the concrete oriented-Mumford implementation.
`classQ` and `classL` are the canonical reduced-Mumford equivalences.
`baseChangeMumford` is coefficient extension on reduced triples.
-/
structure Data (MQ ML JQ JL : Type*)
    [AddCommGroup MQ] [AddCommGroup ML]
    [AddCommGroup JQ] [AddCommGroup JL] where
  classQ : MQ ≃+ JQ
  classL : ML ≃+ JL
  baseChangeMumford : MQ →+ ML
  baseChangeMumford_injective : Function.Injective baseChangeMumford

namespace Data

variable (d : Data MQ ML JQ JL)

/-- The induced base-change map on `Pic^0`, transported through reduced Mumford forms. -/
noncomputable def baseChangePic : JQ →+ JL :=
  d.classL.toAddMonoidHom.comp
    (d.baseChangeMumford.comp d.classQ.symm.toAddMonoidHom)

@[simp] theorem baseChangePic_apply (D : JQ) :
    d.baseChangePic D =
      d.classL (d.baseChangeMumford (d.classQ.symm D)) := rfl

/-- Compatibility with the class of a Mumford representative. -/
@[simp] theorem class_baseChangeMumford (M : MQ) :
    d.classL (d.baseChangeMumford M) =
      d.baseChangePic (d.classQ M) := by
  simp [baseChangePic]

/-- Injectivity follows from uniqueness of reduced Mumford forms and injectivity
of coefficient extension.  This is the lightweight replacement for a direct
Hilbert-90 proof on the oriented ideal quotient. -/
theorem baseChangePic_injective : Function.Injective d.baseChangePic := by
  intro x y hxy
  apply d.classQ.symm.injective
  apply d.baseChangeMumford_injective
  apply d.classL.injective
  simpa [baseChangePic] using hxy

/-- A uniform annihilator over the extension field descends to the ground field. -/
theorem annihilator_descends (n : ℕ)
    (hL : ∀ y : JL, n • y = 0) (x : JQ) :
    n • x = 0 := by
  apply d.baseChangePic_injective
  simpa using hL (d.baseChangePic x)

/-- Finiteness descends along an injective base-change map. -/
noncomputable def finite_source_of_finite_target [Finite JL] : Finite JQ :=
  Finite.of_injective d.baseChangePic d.baseChangePic_injective

/-- If Abel--Jacobi is injective and the extension-field Picard group is finite,
then the set of ground-field curve points is finite. -/
noncomputable def finite_curvePoints_of_finite_pic
    {CPoint : Type*} [Finite JL]
    (abelJacobi : CPoint → JQ)
    (hAJ : Function.Injective abelJacobi) : Finite CPoint := by
  letI : Finite JQ := d.finite_source_of_finite_target
  exact Finite.of_injective abelJacobi hAJ

end Data

end Generic

end FLT.CyclicExclusion.N18.BaseChangeReference
