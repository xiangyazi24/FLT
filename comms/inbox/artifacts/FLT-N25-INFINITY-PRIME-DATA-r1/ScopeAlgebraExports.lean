import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace N25ScopeRegression
abbrev BasePolynomial := Polynomial (ZMod 2)
abbrev Normalization := Polynomial BasePolynomial
abbrev Boundary := ZMod 2

def baseMap : BasePolynomial →ₐ[ZMod 2] Boundary := Polynomial.aeval 0
abbrev boundaryBaseAlgebra : Algebra BasePolynomial Boundary := baseMap.toRingHom.toAlgebra
attribute [local instance] boundaryBaseAlgebra

def normalizationMap : Normalization →ₐ[BasePolynomial] Boundary := Polynomial.aeval 0
abbrev boundaryNormalizationAlgebra : Algebra Normalization Boundary :=
  normalizationMap.toRingHom.toAlgebra
end N25ScopeRegression
