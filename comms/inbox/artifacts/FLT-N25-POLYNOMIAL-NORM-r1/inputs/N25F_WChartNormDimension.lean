import FLT.Assumptions.MazurProof.N25F_WChartQuotientFinite
import Mathlib.LinearAlgebra.FreeModule.Norm
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace MazurProof.N25F_NonBoundaryPrincipalDivisor

/-- The binary dimension of the zero-scheme of a nonzero regular function
on the actual W-chart is the degree of its norm to the existing polynomial
base `F₂[z]`. Finiteness and torsion-freeness of the chart over that base
supply the finite basis required by the norm formula. -/
theorem wChart_quotient_finrank_eq_natDegree_norm (a : W) (ha : a ≠ 0) :
    Module.finrank (ZMod 2) (W ⧸ Ideal.span ({a} : Set W)) =
      (Algebra.norm (Polynomial (ZMod 2)) a).natDegree := by
  letI : IsScalarTower (ZMod 2) (Polynomial (ZMod 2)) W :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : Module.Free (Polynomial (ZMod 2)) W :=
    Module.free_of_finite_type_torsion_free'
  exact finrank_quotient_span_eq_natDegree_norm (F := ZMod 2)
    (Module.Free.chooseBasis (Polynomial (ZMod 2)) W) ha

end MazurProof.N25F_NonBoundaryPrincipalDivisor
