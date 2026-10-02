import ZChartInjectiveCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ZChartFractionEquiv

open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_ZChartFractionMap N25F_ZChartWChartEquiv N25F_ZChartFractionInjective

local notation "W" => N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree (Polynomial (ZMod 2)) W] [IsDedekindDomain W]

/-- The coordinate-rigid extension of the actual Z-chart map to its fraction field. -/
def zFractionToFraction : FractionRing ZChartRing →ₐ[ZMod 2] FractionRing W :=
  IsFractionRing.liftAlgHom
    (R := ZMod 2) (A := ZChartRing) (K := FractionRing ZChartRing)
    (L := FractionRing W) (g := zChartToFraction) zChartToFraction_injective

@[simp]
theorem zFractionToFraction_algebraMap (r : ZChartRing) :
    zFractionToFraction (algebraMap ZChartRing (FractionRing ZChartRing) r) =
      zChartToFraction r := by
  simp [zFractionToFraction]

private abbrev zFractionRange : Subfield (FractionRing W) :=
  RingHom.fieldRange (K := FractionRing ZChartRing) zFractionToFraction.toRingHom

private theorem zChartToFraction_mem_range (r : ZChartRing) :
    zChartToFraction r ∈ zFractionRange := by
  exact ⟨algebraMap ZChartRing (FractionRing ZChartRing) r,
    zFractionToFraction_algebraMap r⟩

/-- The actual W-chart Z coordinate lies in the range of the fraction-field lift. -/
theorem fraction_qz_mem_range :
    algebraMap W (FractionRing W) qz ∈
      RingHom.fieldRange (K := FractionRing ZChartRing) zFractionToFraction.toRingHom := by
  have h := zFractionRange.inv_mem (zChartToFraction_mem_range zW)
  simpa only [zChartToFraction_zW, one_div, inv_inv] using h

/-- The actual W-chart X coordinate lies in the range of the fraction-field lift. -/
theorem fraction_qx_mem_range :
    algebraMap W (FractionRing W) qx ∈
      RingHom.fieldRange (K := FractionRing ZChartRing) zFractionToFraction.toRingHom := by
  have h := zFractionRange.mul_mem (zChartToFraction_mem_range zX) fraction_qz_mem_range
  simpa only [zChartToFraction_zX, div_mul_cancel₀ _ fraction_qz_ne_zero] using h

/-- The actual W-chart Y coordinate lies in the range of the fraction-field lift. -/
theorem fraction_qy_mem_range :
    algebraMap W (FractionRing W) qy ∈
      RingHom.fieldRange (K := FractionRing ZChartRing) zFractionToFraction.toRingHom := by
  have h := zFractionRange.mul_mem (zChartToFraction_mem_range zY) fraction_qz_mem_range
  simpa only [zChartToFraction_zY, div_mul_cancel₀ _ fraction_qz_ne_zero] using h

/-- Every element of the actual W-chart quotient lies in the field range. -/
theorem wChart_algebraMap_mem_range (w : W) :
    algebraMap W (FractionRing W) w ∈ RingHom.fieldRange (K := FractionRing ZChartRing) zFractionToFraction.toRingHom := by
  have hX : ∀ j : OtherCoordinate (3 : Fin 4),
      algebraMap W (FractionRing W)
        (Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4)) (MvPolynomial.X j))
        ∈ zFractionRange := by
    rintro ⟨j, hj⟩
    fin_cases j
    · exact fraction_qx_mem_range
    · exact fraction_qy_mem_range
    · exact fraction_qz_mem_range
    · exact (hj rfl).elim
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction p using MvPolynomial.induction_on with
  | C c =>
      change algebraMap W (FractionRing W) (algebraMap (ZMod 2) W c) ∈ zFractionRange
      rw [← IsScalarTower.algebraMap_apply (ZMod 2) W (FractionRing W)]
      exact ⟨algebraMap (ZMod 2) (FractionRing ZChartRing) c,
        zFractionToFraction.commutes c⟩
  | add p q hp hq =>
      simpa only [map_add] using zFractionRange.add_mem hp hq
  | mul_X p j hp =>
      simpa only [map_mul] using zFractionRange.mul_mem hp (hX j)

/-- Surjectivity of the coordinate-rigid map on the actual fraction fields. -/
theorem zFractionToFraction_surjective : Function.Surjective zFractionToFraction := by
  intro z
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective W z
  exact zFractionRange.div_mem (wChart_algebraMap_mem_range a)
    (wChart_algebraMap_mem_range b)

/-- The fraction-field lift is injective. -/
theorem zFractionToFraction_injective : Function.Injective zFractionToFraction := by
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h := congrArg zFractionToFraction (inv_mul_cancel₀ hsub)
  rw [map_mul, map_sub, hab, sub_self, mul_zero, map_one] at h
  exact zero_ne_one h

/-- The coordinate-rigid equivalence between the actual Z and W function fields. -/
def zChartFractionAlgEquiv : FractionRing ZChartRing ≃ₐ[ZMod 2] FractionRing W :=
  AlgEquiv.ofBijective zFractionToFraction
    ⟨zFractionToFraction_injective, zFractionToFraction_surjective⟩

@[simp]
theorem zChartFractionAlgEquiv_algebraMap (r : ZChartRing) :
    zChartFractionAlgEquiv (algebraMap ZChartRing (FractionRing ZChartRing) r) =
      zChartToFraction r :=
  zFractionToFraction_algebraMap r

/-- The fixed W-chart function field is a fraction field of the actual Z-chart
ring for the coordinate-rigid algebra structure. The algebra structure is kept
explicit to avoid choosing a global competing scalar action. -/
theorem zChartToFraction_isFractionRing :
    letI : Algebra ZChartRing (FractionRing W) := zChartToFraction.toRingHom.toAlgebra
    IsFractionRing ZChartRing (FractionRing W) := by
  letI : Algebra ZChartRing (FractionRing W) := zChartToFraction.toRingHom.toAlgebra
  letI : FaithfulSMul ZChartRing (FractionRing W) :=
    (faithfulSMul_iff_algebraMap_injective ZChartRing (FractionRing W)).2
      zChartToFraction_injective
  apply IsFractionRing.of_field
  intro z
  obtain ⟨u, rfl⟩ := zFractionToFraction_surjective z
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective ZChartRing u
  refine ⟨a, b, ?_⟩
  change zFractionToFraction
      (algebraMap ZChartRing (FractionRing ZChartRing) a /
        algebraMap ZChartRing (FractionRing ZChartRing) b) =
    zChartToFraction a / zChartToFraction b
  rw [map_div₀, zFractionToFraction_algebraMap, zFractionToFraction_algebraMap]

end MazurProof.N25F_ZChartFractionEquiv

#check @MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction
#print axioms MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction
#check @MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction_algebraMap
#print axioms MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction_algebraMap
#check @MazurProof.N25F_ZChartFractionEquiv.fraction_qz_mem_range
#print axioms MazurProof.N25F_ZChartFractionEquiv.fraction_qz_mem_range
#check @MazurProof.N25F_ZChartFractionEquiv.fraction_qx_mem_range
#print axioms MazurProof.N25F_ZChartFractionEquiv.fraction_qx_mem_range
#check @MazurProof.N25F_ZChartFractionEquiv.fraction_qy_mem_range
#print axioms MazurProof.N25F_ZChartFractionEquiv.fraction_qy_mem_range
#check @MazurProof.N25F_ZChartFractionEquiv.wChart_algebraMap_mem_range
#print axioms MazurProof.N25F_ZChartFractionEquiv.wChart_algebraMap_mem_range
#check @MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction_surjective
#print axioms MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction_surjective
#check @MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction_injective
#print axioms MazurProof.N25F_ZChartFractionEquiv.zFractionToFraction_injective
#check @MazurProof.N25F_ZChartFractionEquiv.zChartFractionAlgEquiv
#print axioms MazurProof.N25F_ZChartFractionEquiv.zChartFractionAlgEquiv
#check @MazurProof.N25F_ZChartFractionEquiv.zChartFractionAlgEquiv_algebraMap
#print axioms MazurProof.N25F_ZChartFractionEquiv.zChartFractionAlgEquiv_algebraMap
#check @MazurProof.N25F_ZChartFractionEquiv.zChartToFraction_isFractionRing
#print axioms MazurProof.N25F_ZChartFractionEquiv.zChartToFraction_isFractionRing
