import FLT.Assumptions.MazurProof.N25F_InfinityPrimeContraction
import FLT.Assumptions.MazurProof.N25F_InfinityParameterOrders
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.OrderOfVanishing.Basic

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityRamificationIndices

/-- A principal contracted prime computes ramification by the actual order
of its parameter in the source localization. -/
theorem ramificationIdx_eq_of_parameter_order {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (q : Ideal B) [q.IsPrime] (a : A) (n : ℕ)
    (hunder : q.under A = Ideal.span {a})
    (horder : Ring.ord (Localization.AtPrime q)
      (algebraMap B (Localization.AtPrime q) (algebraMap A B a)) = n) :
    q.ramificationIdx' A = n := by
  rw [Ideal.ramificationIdx'_def, hunder, Ideal.map_span, Set.image_singleton]
  change (Ring.ord (Localization.AtPrime q)
    (algebraMap A (Localization.AtPrime q) a)).toNat = n
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q), horder]
  exact ENat.toNat_coe n


open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityBoundaryCenters N25F_InfinityPrimeContraction
open N25F_InfinityParameterOrders N25F_InfinityBoundaryAlgebras
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra

/-- The actual X center has ramification index 1 over the reciprocal base. -/
theorem xInfinityPrime_ramificationIdx_eq_one :
    xInfinityPrime.ramificationIdx' BasePolynomial = 1 :=
  ramificationIdx_eq_of_parameter_order xInfinityPrime Polynomial.X 1
    xInfinityPrime_under xInfinityParameter_order

/-- The actual YZ center has ramification index 1 over the reciprocal base. -/
theorem yzInfinityPrime_ramificationIdx_eq_one :
    yzInfinityPrime.ramificationIdx' BasePolynomial = 1 :=
  ramificationIdx_eq_of_parameter_order yzInfinityPrime Polynomial.X 1
    yzInfinityPrime_under yzInfinityParameter_order

/-- The actual Z center has ramification index 2 over the reciprocal base. -/
theorem zInfinityPrime_ramificationIdx_eq_two :
    zInfinityPrime.ramificationIdx' BasePolynomial = 2 :=
  ramificationIdx_eq_of_parameter_order zInfinityPrime Polynomial.X 2
    zInfinityPrime_under zInfinityParameter_order

end MazurProof.N25F_InfinityRamificationIndices
