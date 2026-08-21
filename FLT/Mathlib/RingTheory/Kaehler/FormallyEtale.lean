import Mathlib.RingTheory.Etale.Kaehler

/-!
# Coordinates on Kahler differentials after formally etale base change

A chosen coordinate on a relative Kahler differential module transports
canonically through a formally etale algebra map.  Localization maps are the
main application.
-/

set_option autoImplicit false

noncomputable section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

namespace KaehlerDifferential

/-- A coordinate equivalence on relative differentials base-changes through
a formally etale algebra map. -/
def coordinateEquivOfFormallyEtale [Algebra.FormallyEtale S T]
    (e : Ω[S⁄R] ≃ₗ[S] S) : Ω[T⁄R] ≃ₗ[T] T :=
  (tensorKaehlerEquivOfFormallyEtale R S T).symm |>.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) e).trans
      (TensorProduct.AlgebraTensorModule.rid S T T))

/-- The base-changed coordinate of a differential from the source is the
image of its original coordinate. -/
theorem coordinateEquivOfFormallyEtale_map
    [Algebra.FormallyEtale S T] (e : Ω[S⁄R] ≃ₗ[S] S) (x : Ω[S⁄R]) :
    coordinateEquivOfFormallyEtale e (map R R S T x) =
      algebraMap S T (e x) := by
  change
    TensorProduct.AlgebraTensorModule.rid S T T
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) e
        ((tensorKaehlerEquivOfFormallyEtale R S T).symm
          (map R R S T x))) = _
  have h :
      (tensorKaehlerEquivOfFormallyEtale R S T).symm (map R R S T x) =
        1 ⊗ₜ[S] x := by
    rw [LinearEquiv.symm_apply_eq]
    simp [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
  rw [h]
  simp [Algebra.smul_def]

/-- The formally étale base-change equivalence expressed through a chosen
coordinate on the source and its induced coordinate on the target. -/
def coordinateBaseChangeEquiv [Algebra.FormallyEtale S T]
    (e : Ω[S⁄R] ≃ₗ[S] S) :
    TensorProduct S T Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl T T) e).trans
    ((TensorProduct.AlgebraTensorModule.rid S T T).trans
      (coordinateEquivOfFormallyEtale e).symm)

/-- Canonical formally étale base change agrees with the construction through
any chosen coordinate. -/
theorem tensorKaehlerEquivOfFormallyEtale_eq_coordinateBaseChange
    [Algebra.FormallyEtale S T] (e : Ω[S⁄R] ≃ₗ[S] S) :
    tensorKaehlerEquivOfFormallyEtale R S T =
      coordinateBaseChangeEquiv e := by
  apply LinearEquiv.ext
  intro z
  simp [coordinateBaseChangeEquiv, coordinateEquivOfFormallyEtale]

end KaehlerDifferential
