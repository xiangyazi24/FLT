import ScopeAlgebraExports
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25ScopeRegression

/-- The exporter did not install its selected polynomial action globally. -/
example : True := by
  fail_if_success have : Algebra BasePolynomial Boundary := inferInstance
  trivial

attribute [local instance] boundaryBaseAlgebra boundaryNormalizationAlgebra

/-- The required actions can be selected in a fresh importing module. -/
example : Algebra BasePolynomial Boundary := inferInstance
example : Algebra Normalization Boundary := inferInstance
#check normalizationMap.toRingHom

theorem normalizationMap_coefficient (p : BasePolynomial) :
    normalizationMap (algebraMap BasePolynomial Normalization p) =
      algebraMap BasePolynomial Boundary p := normalizationMap.commutes p
#print axioms normalizationMap_coefficient
end N25ScopeRegression
