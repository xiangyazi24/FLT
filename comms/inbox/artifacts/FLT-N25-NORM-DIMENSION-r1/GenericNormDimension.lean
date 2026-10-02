import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace N25NormDimensionCheck

variable {S : Type*} [CommRing S] [IsDomain S]
  [Algebra (ZMod 2) S] [Algebra (Polynomial (ZMod 2)) S]
  [Module.Finite (Polynomial (ZMod 2)) S]
  [Module.IsTorsionFree (Polynomial (ZMod 2)) S]

theorem binary_quotient_finrank_eq_natDegree_norm (a : S) (ha : a ≠ 0) :
    Module.finrank (ZMod 2) (S ⧸ Ideal.span ({a} : Set S)) =
      (Algebra.norm (Polynomial (ZMod 2)) a).natDegree := by
  letI : IsScalarTower (ZMod 2) (Polynomial (ZMod 2)) S :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : Module.Free (Polynomial (ZMod 2)) S :=
    Module.free_of_finite_type_torsion_free'
  exact finrank_quotient_span_eq_natDegree_norm (F := ZMod 2)
    (Module.Free.chooseBasis (Polynomial (ZMod 2)) S) ha

#print axioms binary_quotient_finrank_eq_natDegree_norm

end N25NormDimensionCheck
