import FLT.Assumptions.MazurProof.N25F_PolynomialBoundaryOrders
import FLT.Assumptions.MazurProof.N25F_WChartBaseNorm
import FLT.Assumptions.MazurProof.N25F_WChartPrincipalDegree
import Mathlib.Algebra.Group.Prod

/-! Assemble the genuine three boundary orders with the existing affine
principal divisor. Prove degree zero for nonzero base polynomials. The
arbitrary-function projective product formula remains a separate target. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_ProjectivePrincipalDivisor

open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_NonBoundaryPrincipalDivisor N25F_ProjectiveDivisorSplit
open N25F_ProjectiveDivisorDegree N25F_PolynomialBoundaryOrders
open N25F_XBoundaryOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_ZChartFractionMap

local notation "K" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The three genuine local orders, in the existing X,YZ,Z coefficient order. -/
def boundaryPrincipalOrders : Additive Kˣ →+ BoundaryCoefficients25Two :=
  xBoundaryOrder.prod (yzBoundaryOrder.prod zBoundaryOrder)

/-- The actual principal divisor, including all boundary and nonboundary atoms.
Its definition does not assume the general degree-zero product formula. -/
def projectivePrincipalDivisor : Additive Kˣ →+ ProjectiveDivisor25Two :=
  fullDivisorEquivBoundaryCoefficientsChart.symm.toAddMonoidHom.comp
    (boundaryPrincipalOrders.prod
      (nonBoundaryDivisorEquivWChart.toAddMonoidHom.comp nonBoundaryPrincipalDivisor))

@[simp]
theorem projectivePrincipalDivisor_split (f : Additive Kˣ) :
    fullDivisorEquivBoundaryCoefficientsChart (projectivePrincipalDivisor f) =
      ((xBoundaryOrder f, (yzBoundaryOrder f, zBoundaryOrder f)),
        nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) := by
  change fullDivisorEquivBoundaryCoefficientsChart
    (fullDivisorEquivBoundaryCoefficientsChart.symm _) = _
  exact fullDivisorEquivBoundaryCoefficientsChart.apply_symm_apply _

/-- Exact degree of the constructed actual principal divisor, before invoking
any product formula. -/
theorem projectivePrincipalDivisor_degree (f : Additive Kˣ) :
    fullClosedPointGrading25Two.divisorDegree (projectivePrincipalDivisor f) =
      xBoundaryOrder f + yzBoundaryOrder f + zBoundaryOrder f +
        wChartDivisorDegree
          (nonBoundaryDivisorEquivWChart (nonBoundaryPrincipalDivisor f)) := by
  rw [divisorDegree_eq_splitDegree, projectivePrincipalDivisor_split,
    splitDegree_apply_components, boundaryCoefficientDegree_apply]

/-- The fixed normalization coefficient map is evaluation at the actual
common-field coordinate qz, not at a renamed or independent variable. -/
theorem basePolynomial_inFunctionField (p : Polynomial (ZMod 2)) :
    algebraMap N25F_NonBoundaryPrincipalDivisor.W K (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W p) =
      p.aeval (algebraMap N25F_NonBoundaryPrincipalDivisor.W K qz) := by
  have h : (algebraMap N25F_NonBoundaryPrincipalDivisor.W K).comp (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W) =
      (Polynomial.aeval (algebraMap N25F_NonBoundaryPrincipalDivisor.W K qz)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_zmod _ _
    · change algebraMap N25F_NonBoundaryPrincipalDivisor.W K
        (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W Polynomial.X) =
        (Polynomial.aeval (algebraMap N25F_NonBoundaryPrincipalDivisor.W K qz)) Polynomial.X
      rw [Polynomial.aeval_X, algebraMap_Rz_X]
  exact congrArg (fun h : Polynomial (ZMod 2) →+* K => h p) h

/-- The genuine projective principal divisor has degree zero on every nonzero
base polynomial. The same function and actual coefficient map are retained. -/
theorem projectivePrincipalDivisor_degree_base_polynomial
    (p : Polynomial (ZMod 2)) (hp : p ≠ 0) (f : Additive Kˣ)
    (hf : (f.toMul : K) =
      algebraMap N25F_NonBoundaryPrincipalDivisor.W K (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W p)) :
    fullClosedPointGrading25Two.divisorDegree (projectivePrincipalDivisor f) = 0 := by
  have heval : (f.toMul : K) = p.aeval (algebraMap N25F_NonBoundaryPrincipalDivisor.W K qz) :=
    hf.trans (basePolynomial_inFunctionField p)
  have hx : xBoundaryOrder f = -(1 * p.natDegree : ℤ) := by
    change WithZero.log (xLocalFractionOrder (f.toMul : K)) = _
    rw [heval, xLocalFractionOrder_aeval_qz p hp, WithZero.log_exp]
  have hyz : yzBoundaryOrder f = -(1 * p.natDegree : ℤ) := by
    change WithZero.log (yzLocalFractionOrder (f.toMul : K)) = _
    rw [heval, yzLocalFractionOrder_aeval_qz p hp, WithZero.log_exp]
  have hz : zBoundaryOrder f = -(2 * p.natDegree : ℤ) := by
    change WithZero.log (zLocalFractionOrder (f.toMul : K)) = _
    rw [heval, zLocalFractionOrder_aeval_qz p hp, WithZero.log_exp]
  have hmap : algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W p ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W)).mpr hp
  have haff := wChart_principal_degree_eq_quotient_finrank
    (algebraMap (Polynomial (ZMod 2)) N25F_NonBoundaryPrincipalDivisor.W p) hmap f hf
  rw [wChart_quotient_finrank_base_polynomial p hp] at haff
  rw [projectivePrincipalDivisor_degree, hx, hyz, hz, haff]
  push_cast
  ring

end MazurProof.N25F_ProjectivePrincipalDivisor
