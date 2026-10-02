import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Field.ZMod
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
namespace N25PolynomialMapBridge

theorem polynomial_map_aeval
    {S T : Type*} [CommRing S] [CommRing T] [Algebra (ZMod 2) T]
    (f : Polynomial (ZMod 2) →+* S) (g : S →+* T) (z : S)
    (hX : f Polynomial.X = z) (p : Polynomial (ZMod 2)) :
    g (f p) = p.aeval (g z) := by
  have h : g.comp f = (Polynomial.aeval (g z)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_zmod _ _
    · change g (f Polynomial.X) = (Polynomial.aeval (g z)) Polynomial.X
      rw [Polynomial.aeval_X]
      exact congrArg g hX
  exact congrArg (fun h : Polynomial (ZMod 2) →+* T => h p) h

#print axioms polynomial_map_aeval
end N25PolynomialMapBridge
