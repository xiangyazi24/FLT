import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! Factor the actual integral-closure inclusion through an integrally closed
ring with the same fraction field. No factor map is assumed. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace MazurProof.N25F_IntegralBoundaryFactor

variable {A R K : Type*} [CommRing A] [CommRing R] [Field K]
  [Algebra A R] [Algebra A K] [Algebra R K] [IsScalarTower A R K]
  [IsFractionRing R K] [IsIntegrallyClosed R]

/-- Every element of the normalization is represented by a boundary-ring element. -/
theorem exists_preimage (x : integralClosure A K) :
    ∃ r : R, algebraMap R K r = (x : K) :=
  IsIntegrallyClosed.isIntegral_iff.mp (x.property.tower_top (A := R))

/-- The actual factorization of the normalization inclusion, constructed by
integrality and integral closedness of the boundary ring. -/
def integralClosureToRing : integralClosure A K →ₐ[A] R where
  toFun x := Classical.choose (exists_preimage (R := R) x)
  map_zero' := by
    apply IsFractionRing.injective R K
    simpa only [map_zero, Subalgebra.coe_zero] using Classical.choose_spec (exists_preimage (R := R) (0 : integralClosure A K))
  map_one' := by
    apply IsFractionRing.injective R K
    simpa only [map_one, Subalgebra.coe_one] using Classical.choose_spec (exists_preimage (R := R) (1 : integralClosure A K))
  map_add' x y := by
    apply IsFractionRing.injective R K
    simp only [map_add, Subalgebra.coe_add, Classical.choose_spec (exists_preimage (R := R) (x + y)),
      Classical.choose_spec (exists_preimage (R := R) x),
      Classical.choose_spec (exists_preimage (R := R) y)]
  map_mul' x y := by
    apply IsFractionRing.injective R K
    simp only [map_mul, Subalgebra.coe_mul, Classical.choose_spec (exists_preimage (R := R) (x * y)),
      Classical.choose_spec (exists_preimage (R := R) x),
      Classical.choose_spec (exists_preimage (R := R) y)]
  commutes' a := by
    apply IsFractionRing.injective R K
    rw [Classical.choose_spec (exists_preimage (R := R) (algebraMap A (integralClosure A K) a)),
      ← IsScalarTower.algebraMap_apply A R K]
    rfl

@[simp]
theorem algebraMap_integralClosureToRing (x : integralClosure A K) :
    algebraMap R K (integralClosureToRing (R := R) x) = (x : K) :=
  Classical.choose_spec (exists_preimage (R := R) x)

/-- The composite is exactly the canonical inclusion, as an A-algebra map. -/
theorem toAlgHom_comp_integralClosureToRing :
    (IsScalarTower.toAlgHom A R K).comp (integralClosureToRing (A := A) (R := R)) =
      (integralClosure A K).val := by
  ext x
  exact algebraMap_integralClosureToRing x

/-- The normalization map into the boundary ring is injective. -/
theorem integralClosureToRing_injective :
    Function.Injective (integralClosureToRing (A := A) (R := R) (K := K)) := by
  intro x y h
  apply Subtype.ext
  have hh := congrArg (algebraMap R K) h
  simpa only [algebraMap_integralClosureToRing] using hh

/-- Compatibility with the fixed inclusion determines the map uniquely. -/
theorem integralClosureToRing_unique (f : integralClosure A K →ₐ[A] R)
    (hf : ∀ x, algebraMap R K (f x) = (x : K)) :
    f = integralClosureToRing := by
  ext x
  apply IsFractionRing.injective R K
  rw [hf, algebraMap_integralClosureToRing]

end MazurProof.N25F_IntegralBoundaryFactor

#print axioms MazurProof.N25F_IntegralBoundaryFactor.exists_preimage
#print axioms MazurProof.N25F_IntegralBoundaryFactor.integralClosureToRing
#print axioms MazurProof.N25F_IntegralBoundaryFactor.algebraMap_integralClosureToRing
#print axioms MazurProof.N25F_IntegralBoundaryFactor.toAlgHom_comp_integralClosureToRing
#print axioms MazurProof.N25F_IntegralBoundaryFactor.integralClosureToRing_injective
#print axioms MazurProof.N25F_IntegralBoundaryFactor.integralClosureToRing_unique
