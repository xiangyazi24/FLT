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

/-- Localizing the target at a selected Jacobian gives a standard-smooth
presentation with the same relative dimension as the original finite
presentation.  The added inverse variable and its defining relation
contribute zero to the presentation dimension. -/
theorem isStandardSmoothOfRelativeDimension_localizationAway_jacobian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {ι σ : Type*} [Finite ι] [Finite σ]
    (P : Algebra.PreSubmersivePresentation R S ι σ) {n : ℕ}
    (hP : P.dimension = n) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap S (Localization.Away P.jacobian)).comp
        (algebraMap R S)) := by
  let T := Localization.Away P.jacobian
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
  change RingHom.IsStandardSmoothOfRelativeDimension n (algebraMap R T)
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  apply SP.isStandardSmoothOfRelativeDimension
  change C.dimension = n
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  change (Algebra.Presentation.localizationAway T P.jacobian).dimension +
      P.dimension = n
  rw [Algebra.Presentation.localizationAway_dimension_zero, zero_add, hP]

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
  exact
    (P.isStandardSmoothOfRelativeDimension_localizationAway_jacobian
      (n := P.dimension) rfl).isStandardSmooth.smooth

end Algebra.PreSubmersivePresentation

namespace RingHom

/-- If equal-dimensional finite selected presentations have Jacobians
spanning the unit ideal, the map is locally standard smooth in that relative
dimension. -/
theorem Locally.isStandardSmoothOfRelativeDimension_of_jacobian_span
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {E ι σ : Type*} [_root_.Finite ι] [_root_.Finite σ]
    (P : E → Algebra.PreSubmersivePresentation R S ι σ) {n : ℕ}
    (hDimension : ∀ e, (P e).dimension = n)
    (hspan : Ideal.span (Set.range fun e ↦ (P e).jacobian) = ⊤) :
    Locally (IsStandardSmoothOfRelativeDimension n) (algebraMap R S) := by
  refine ⟨Set.range fun e ↦ (P e).jacobian, hspan, ?_⟩
  rintro _ ⟨e, rfl⟩
  exact (P e).isStandardSmoothOfRelativeDimension_localizationAway_jacobian
    (hDimension e)

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
