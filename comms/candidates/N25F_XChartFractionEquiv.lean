import FLT.Assumptions.MazurProof.N25F_XChartFractionInjective

/-!
# The coordinate-rigid equivalence of the actual X and W function fields

The injective X-chart map extends to fraction fields. Its field range contains
`qx`, as the inverse of the image of `xW`, and then `qy` and `qz`, using the
images of `xY` and `xZ`. Induction on the actual W-chart polynomial quotient
and the fraction representation therefore proves surjectivity. No generation
or surjectivity premise is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_XChartFractionEquiv

open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryChartArtin
open N25F_XChartFractionMap N25F_XChartWChartEquiv N25F_XChartFractionInjective

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W

/-- The coordinate-rigid extension of the actual X-chart map to its fraction field. -/
def xFractionToFraction : FractionRing XChartRing →ₐ[ZMod 2] FractionRing W :=
  IsFractionRing.liftAlgHom
    (R := ZMod 2) (A := XChartRing) (K := FractionRing XChartRing)
    (L := FractionRing W) (g := xChartToFraction) xChartToFraction_injective

@[simp]
theorem xFractionToFraction_algebraMap (r : XChartRing) :
    xFractionToFraction (algebraMap XChartRing (FractionRing XChartRing) r) =
      xChartToFraction r := by
  simp [xFractionToFraction]

private abbrev xFractionRange : Subfield (FractionRing W) :=
  RingHom.fieldRange (K := FractionRing XChartRing) xFractionToFraction.toRingHom

private theorem xChartToFraction_mem_range (r : XChartRing) :
    xChartToFraction r ∈ xFractionRange := by
  exact ⟨algebraMap XChartRing (FractionRing XChartRing) r,
    xFractionToFraction_algebraMap r⟩

/-- The actual W-chart X coordinate lies in the range of the fraction-field lift. -/
theorem fraction_qx_mem_range :
    algebraMap W (FractionRing W) qx ∈ RingHom.fieldRange (K := FractionRing XChartRing) xFractionToFraction.toRingHom := by
  have h := xFractionRange.inv_mem (xChartToFraction_mem_range xW)
  simpa only [xChartToFraction_xW, one_div, inv_inv] using h

/-- The actual W-chart Y coordinate lies in the range of the fraction-field lift. -/
theorem fraction_qy_mem_range :
    algebraMap W (FractionRing W) qy ∈ RingHom.fieldRange (K := FractionRing XChartRing) xFractionToFraction.toRingHom := by
  have h := xFractionRange.mul_mem (xChartToFraction_mem_range xY) fraction_qx_mem_range
  simpa only [xChartToFraction_xY, div_mul_cancel₀ _ fraction_qx_ne_zero] using h

/-- The actual W-chart Z coordinate lies in the range of the fraction-field lift. -/
theorem fraction_qz_mem_range :
    algebraMap W (FractionRing W) qz ∈ RingHom.fieldRange (K := FractionRing XChartRing) xFractionToFraction.toRingHom := by
  have h := xFractionRange.mul_mem (xChartToFraction_mem_range xZ) fraction_qx_mem_range
  simpa only [xChartToFraction_xZ, div_mul_cancel₀ _ fraction_qx_ne_zero] using h

/-- Every element of the actual W-chart quotient lies in the field range. -/
theorem wChart_algebraMap_mem_range (w : W) :
    algebraMap W (FractionRing W) w ∈ RingHom.fieldRange (K := FractionRing XChartRing) xFractionToFraction.toRingHom := by
  have hX : ∀ j : OtherCoordinate (3 : Fin 4),
      algebraMap W (FractionRing W)
        (Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4)) (MvPolynomial.X j))
        ∈ xFractionRange := by
    rintro ⟨j, hj⟩
    fin_cases j
    · exact fraction_qx_mem_range
    · exact fraction_qy_mem_range
    · exact fraction_qz_mem_range
    · exact (hj rfl).elim
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction p using MvPolynomial.induction_on with
  | C c =>
      change algebraMap W (FractionRing W) (algebraMap (ZMod 2) W c) ∈ xFractionRange
      rw [← IsScalarTower.algebraMap_apply (ZMod 2) W (FractionRing W)]
      exact ⟨algebraMap (ZMod 2) (FractionRing XChartRing) c,
        xFractionToFraction.commutes c⟩
  | add p q hp hq =>
      simpa only [map_add] using xFractionRange.add_mem hp hq
  | mul_X p j hp =>
      simpa only [map_mul] using xFractionRange.mul_mem hp (hX j)

/-- Surjectivity of the coordinate-rigid map on the actual fraction fields. -/
theorem xFractionToFraction_surjective : Function.Surjective xFractionToFraction := by
  intro z
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective W z
  exact xFractionRange.div_mem (wChart_algebraMap_mem_range a)
    (wChart_algebraMap_mem_range b)

/-- The fraction-field lift is injective. -/
theorem xFractionToFraction_injective : Function.Injective xFractionToFraction := by
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h := congrArg xFractionToFraction (inv_mul_cancel₀ hsub)
  rw [map_mul, map_sub, hab, sub_self, mul_zero, map_one] at h
  exact zero_ne_one h

/-- The coordinate-rigid equivalence between the actual X and W function fields. -/
def xChartFractionAlgEquiv : FractionRing XChartRing ≃ₐ[ZMod 2] FractionRing W :=
  AlgEquiv.ofBijective xFractionToFraction
    ⟨xFractionToFraction_injective, xFractionToFraction_surjective⟩

@[simp]
theorem xChartFractionAlgEquiv_algebraMap (r : XChartRing) :
    xChartFractionAlgEquiv (algebraMap XChartRing (FractionRing XChartRing) r) =
      xChartToFraction r :=
  xFractionToFraction_algebraMap r

/-- The fixed W-chart function field is a fraction field of the actual X-chart
ring for the coordinate-rigid algebra structure. The algebra structure is kept
explicit to avoid choosing a global competing scalar action. -/
theorem xChartToFraction_isFractionRing :
    letI : Algebra XChartRing (FractionRing W) := xChartToFraction.toRingHom.toAlgebra
    IsFractionRing XChartRing (FractionRing W) := by
  letI : Algebra XChartRing (FractionRing W) := xChartToFraction.toRingHom.toAlgebra
  letI : FaithfulSMul XChartRing (FractionRing W) :=
    (faithfulSMul_iff_algebraMap_injective XChartRing (FractionRing W)).2
      xChartToFraction_injective
  apply IsFractionRing.of_field
  intro z
  obtain ⟨u, rfl⟩ := xFractionToFraction_surjective z
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective XChartRing u
  refine ⟨a, b, ?_⟩
  change xFractionToFraction
      (algebraMap XChartRing (FractionRing XChartRing) a /
        algebraMap XChartRing (FractionRing XChartRing) b) =
    xChartToFraction a / xChartToFraction b
  rw [map_div₀, xFractionToFraction_algebraMap, xFractionToFraction_algebraMap]

end MazurProof.N25F_XChartFractionEquiv
