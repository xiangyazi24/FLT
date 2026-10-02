import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.FreeModule.Norm
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25BaseNormCheck

variable {k S F L : Type*} [Field k] [CommRing S] [IsDomain S]
  [Field F] [Field L]
  [Algebra (Polynomial k) S] [Module.Finite (Polynomial k) S]
  [Module.IsTorsionFree (Polynomial k) S]
  [Algebra (Polynomial k) F] [IsFractionRing (Polynomial k) F]
  [Algebra (Polynomial k) L] [Algebra S L] [IsFractionRing S L]
  [Algebra F L] [IsScalarTower (Polynomial k) F L] [IsScalarTower (Polynomial k) S L]

 theorem finrank_eq_four (hdegree : Module.finrank F L = 4) :
    Module.finrank (Polynomial k) S = 4 := by
  letI : Algebra.IsAlgebraic (Polynomial k) S := Algebra.IsAlgebraic.of_finite _ _
  rw [← Algebra.IsAlgebraic.finrank_of_isFractionRing (Polynomial k) F S L]
  exact hdegree

theorem norm_algebraMap_eq_pow_four (hdegree : Module.finrank F L = 4)
    (p : Polynomial k) : Algebra.norm (Polynomial k) (algebraMap (Polynomial k) S p) = p ^ 4 := by
  letI : Module.Free (Polynomial k) S := Module.free_of_finite_type_torsion_free'
  rw [Algebra.norm_algebraMap, finrank_eq_four hdegree]


variable [Algebra k S] [IsScalarTower k (Polynomial k) S]

theorem quotient_finrank_base_polynomial (hdegree : Module.finrank F L = 4)
    (p : Polynomial k) (hp : p ≠ 0) :
    Module.finrank k (S ⧸ Ideal.span ({algebraMap (Polynomial k) S p} : Set S)) =
      4 * p.natDegree := by
  letI : Module.Free (Polynomial k) S := Module.free_of_finite_type_torsion_free'
  have hmap : algebraMap (Polynomial k) S p ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (Polynomial k) S)).mpr hp
  rw [finrank_quotient_span_eq_natDegree_norm (F := k)
    (Module.Free.chooseBasis (Polynomial k) S) hmap,
    norm_algebraMap_eq_pow_four hdegree, Polynomial.natDegree_pow]

#print axioms quotient_finrank_base_polynomial

#print axioms finrank_eq_four
#print axioms norm_algebraMap_eq_pow_four
end N25BaseNormCheck
