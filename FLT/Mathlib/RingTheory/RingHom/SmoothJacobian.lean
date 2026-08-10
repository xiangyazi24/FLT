import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# Structural smoothness from selected Jacobian minors

This module supplies the generic bridge needed by affine complete
intersections such as the N25 charts.  It contains no equation-specific
computation: the only input is a finite pre-submersive presentation and,
globally, a family of its selected Jacobians spanning the unit ideal.
-/

noncomputable section

universe u

namespace Algebra.PreSubmersivePresentation

/-- Localizing the target at a selected Jacobian makes a finite
pre-submersive presentation smooth.  The localization presentation adds one
inverse variable and one relation; the composite selected Jacobian is the
square of the localized original Jacobian. -/
theorem smooth_localizationAway_jacobian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.PreSubmersivePresentation R S ι σ) :
    RingHom.Smooth
      ((algebraMap S (Localization.Away P.jacobian)).comp
        (algebraMap R S)) := by
  let T := Localization.Away P.jacobian
  let f : R →+* T := (algebraMap S T).comp (algebraMap R S)
  change RingHom.Smooth f
  letI : IsScalarTower R S T :=
    IsScalarTower.of_algebraMap_eq' rfl
  let Q : Algebra.PreSubmersivePresentation S T Unit Unit :=
    Algebra.PreSubmersivePresentation.localizationAway T P.jacobian
  let C : Algebra.PreSubmersivePresentation
      R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    Q.comp P
  have hJacobian : IsUnit (algebraMap S T P.jacobian) :=
    IsLocalization.map_units T
      (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
  let SP : Algebra.SubmersivePresentation
      R T (Unit ⊕ ι) (Unit ⊕ σ) :=
    { __ := C
      jacobian_isUnit := by
        dsimp [C, Q]
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.PreSubmersivePresentation.localizationAway_jacobian]
        simpa only [Algebra.smul_def] using hJacobian.mul hJacobian }
  have hStandard : RingHom.IsStandardSmooth (algebraMap R T) :=
    RingHom.isStandardSmooth_algebraMap.mpr SP.isStandardSmooth
  exact hStandard.smooth

end Algebra.PreSubmersivePresentation

namespace RingHom

/-- If a family of finite selected presentations has Jacobians spanning the
unit ideal in the target, smoothness follows by target-localization locality. -/
theorem Smooth.of_jacobian_span
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {E ι σ : Type*} [_root_.Finite ι] [_root_.Finite σ]
    (P : E → Algebra.PreSubmersivePresentation R S ι σ)
    (hspan : Ideal.span (Set.range fun e ↦ (P e).jacobian) = ⊤) :
    RingHom.Smooth (algebraMap R S) := by
  refine RingHom.Smooth.ofLocalizationSpanTarget
    (algebraMap R S) (Set.range fun e ↦ (P e).jacobian) hspan ?_
  rintro ⟨_, ⟨e, rfl⟩⟩
  exact (P e).smooth_localizationAway_jacobian

end RingHom
