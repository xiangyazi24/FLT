import FLT.Assumptions.MazurProof.N25F_XSectionFiltration
import FLT.Assumptions.MazurProof.N25F_XInfinityGerm
import FLT.Assumptions.MazurProof.N25F_DVRIntegralLift

/-! The actual leading residue at X: scale by the established uniformizer
W/Z, recover the unique X-local germ, and apply its genuine binary residue. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_XSectionResidue
open CurveZetaEffectiveDivisors RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryXLocal
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_RiemannRochSpace
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder N25F_InfinityResidueFields
open N25F_XInfinityGerm N25F_XSectionFiltration N25F_DVRIntegralLift
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
local notation "XPoint" => fullBoundaryAtomOfTag .X

private def xSectionScale (D : ProjectiveDivisor25Two) : CurveField :=
  (xLocalToFraction xInverseZGerm) ^ (D XPoint)

private theorem xSectionScale_ne_zero (D : ProjectiveDivisor25Two) : xSectionScale D ≠ 0 :=
  zpow_ne_zero _ ((map_ne_zero_iff _ xLocalToFraction_injective).mpr xInverseZGerm_ne_zero)

private theorem xSectionScale_order (D : ProjectiveDivisor25Two) :
    WithZero.log (xLocalFractionOrder (xSectionScale D)) = D XPoint := by
  have ht : xLocalFractionOrder (xLocalToFraction xInverseZGerm) = WithZero.exp (1 : ℤ) := by
    letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
    letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
    change Ring.ordFrac XLocalRing (algebraMap XLocalRing CurveField xInverseZGerm) = _
    rw [Ring.ordFrac_eq_ord XLocalRing xInverseZGerm_ne_zero,
      Ring.ordMonoidWithZeroHom_eq_coe XLocalRing
        (mem_nonZeroDivisors_iff_ne_zero.mpr xInverseZGerm_ne_zero) xInverseZGerm_ord_eq_one]
    rfl
  change WithZero.log (xLocalFractionOrder
    ((xLocalToFraction xInverseZGerm) ^ (D XPoint))) = D XPoint
  rw [map_zpow₀, WithZero.log_zpow, ht, WithZero.log_exp]
  simp

private theorem scaled_section_nonneg (D : ProjectiveDivisor25Two)
    (f : fullRiemannRochSpace25Two D) :
    xSectionScale D * (f : CurveField) = 0 ∨
      0 ≤ WithZero.log (xLocalFractionOrder (xSectionScale D * (f : CurveField))) := by
  rcases f.property with hzero | ⟨hf, hb⟩
  · exact Or.inl (by rw [hzero, mul_zero])
  right
  have hs : xLocalFractionOrder (xSectionScale D) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr (xSectionScale_ne_zero D)).map xLocalFractionOrder).ne_zero
  have hv : xLocalFractionOrder (f : CurveField) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hf).map xLocalFractionOrder).ne_zero
  rw [map_mul, WithZero.log_mul hs hv, xSectionScale_order]
  have hx := hb XPoint
  rw [projectivePrincipalDivisor_apply_X] at hx
  exact hx

private theorem xScaledSection_has_germ (D : ProjectiveDivisor25Two)
    (f : fullRiemannRochSpace25Two D) :
    ∃! a : XLocalRing, xLocalToFraction a = xSectionScale D * (f : CurveField) := by
  letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
  exact existsUnique_algebraMap_eq_of_log_nonneg _ (scaled_section_nonneg D f)

/-- The unique actual X-local germ of (W/Z)^D(X) times a section. -/
def xScaledSectionGerm25Two (D : ProjectiveDivisor25Two)
    (f : fullRiemannRochSpace25Two D) : XLocalRing :=
  Classical.choose (xScaledSection_has_germ D f)

@[simp]
theorem xLocalToFraction_xScaledSectionGerm25Two (D : ProjectiveDivisor25Two)
    (f : fullRiemannRochSpace25Two D) :
    xLocalToFraction (xScaledSectionGerm25Two D f) =
      (xLocalToFraction xInverseZGerm) ^ (D XPoint) * (f : CurveField) :=
  (Classical.choose_spec (xScaledSection_has_germ D f)).1

private theorem xScaledSectionGerm_zero (D : ProjectiveDivisor25Two) :
    xScaledSectionGerm25Two D 0 = 0 := by
  apply xLocalToFraction_injective
  rw [xLocalToFraction_xScaledSectionGerm25Two, map_zero]
  exact mul_zero _

theorem xScaledSectionGerm25Two_add (D : ProjectiveDivisor25Two)
    (f g : fullRiemannRochSpace25Two D) :
    xScaledSectionGerm25Two D (f + g) =
      xScaledSectionGerm25Two D f + xScaledSectionGerm25Two D g := by
  apply xLocalToFraction_injective
  simp only [map_add, xLocalToFraction_xScaledSectionGerm25Two, Submodule.coe_add, mul_add]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have hc : a.val = 0 ∨ a.val = 1 := by omega
  rcases hc with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h

/-- The genuine uniformizer-scaled residue, as an F2-linear functional on L(D). -/
def xLeadingResidue25Two (D : ProjectiveDivisor25Two) :
    fullRiemannRochSpace25Two D →ₗ[ZMod 2] ZMod 2 where
  toFun f := xLocalResidueRingEquivF2 (IsLocalRing.residue XLocalRing (xScaledSectionGerm25Two D f))
  map_add' f g := by rw [xScaledSectionGerm25Two_add, map_add, map_add]
  map_smul' r f := by
    rcases zmod_two_cases r with rfl | rfl
    · simp only [zero_smul, xScaledSectionGerm_zero, map_zero]
    · simp only [map_one, one_smul]

/-- Vanishing of the actual leading residue means exactly one extra zero at X. -/
theorem xLeadingResidue25Two_eq_zero_iff (D : ProjectiveDivisor25Two)
    (f : fullRiemannRochSpace25Two D) :
    xLeadingResidue25Two D f = 0 ↔
      (f : CurveField) ∈ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1) := by
  by_cases hf : (f : CurveField) = 0
  · have hf0 : f = 0 := Subtype.ext hf
    rw [hf0, map_zero]
    simp only [Submodule.coe_zero, zero_mem, iff_self]
  letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
  letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
  have hg : xScaledSectionGerm25Two D f ≠ 0 := by
    intro h
    have hm := xLocalToFraction_xScaledSectionGerm25Two D f
    rw [h, map_zero] at hm
    exact (mul_ne_zero (xSectionScale_ne_zero D) hf) hm.symm
  change xLocalResidueRingEquivF2
    (IsLocalRing.residue XLocalRing (xScaledSectionGerm25Two D f)) = 0 ↔ _
  rw [map_eq_zero_iff _ xLocalResidueRingEquivF2.injective,
    residue_eq_zero_iff_eq_zero_or_log_pos (L := CurveField), or_iff_right hg]
  have hs : xLocalFractionOrder (xSectionScale D) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr (xSectionScale_ne_zero D)).map xLocalFractionOrder).ne_zero
  have hv : xLocalFractionOrder (f : CurveField) ≠ 0 :=
    ((isUnit_iff_ne_zero.mpr hf).map xLocalFractionOrder).ne_zero
  change 0 < WithZero.log (xLocalFractionOrder
    (xLocalToFraction (xScaledSectionGerm25Two D f))) ↔ _
  rw [xLocalToFraction_xScaledSectionGerm25Two]
  change 0 < WithZero.log (xLocalFractionOrder (xSectionScale D * (f : CurveField))) ↔ _
  rw [map_mul, WithZero.log_mul hs hv, xSectionScale_order]
  have hm := mem_fullRiemannRochSpace25Two_sub_X_iff D
    (Additive.ofMul (Units.mk0 (f : CurveField) hf)) f.property
  change ((f : CurveField) ∈ fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1) ↔
    -D XPoint < WithZero.log (xLocalFractionOrder (f : CurveField))) at hm
  rw [hm]
  omega

/-- The exact kernel of the genuine leading-residue functional is L(D-X). -/
theorem ker_xLeadingResidue25Two (D : ProjectiveDivisor25Two) :
    LinearMap.ker (xLeadingResidue25Two D) =
      (fullRiemannRochSpace25Two (D - Finsupp.single XPoint 1)).submoduleOf
        (fullRiemannRochSpace25Two D) := by
  ext f
  exact xLeadingResidue25Two_eq_zero_iff D f

end MazurProof.N25F_XSectionResidue
