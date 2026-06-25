/-
# Wiring: FormalGroupW → FormalNsmulDirect → tangent bridge

Connects the Weierstrass formal group law (FormalGroupW.lean) to the
tangent-at-origin theorem (FormalNsmulDirect.lean). Once FormalGroupW
provides formalGroupLaw with its three properties (constantCoeff=0,
lin_coeff_X=1, lin_coeff_Y=1), this file gives:

  formalNsmulF_coeff_one W.formalGroupLaw n = (n : R)

i.e., the tangent map of formal [n] is n.
-/

import scratch.FormalGroupW
import scratch.FormalNsmulDirect

namespace WeierstrassCurve.FormalGroupWiring

variable {R : Type*} [CommRing R]

/-- The tangent map of [n] on the Weierstrass formal group is n. -/
theorem formalNsmul_tangent (W : WeierstrassCurve R) (n : ℕ) :
    PowerSeries.coeff (R := R) 1
      (FormalNsmulDirect.formalNsmulF W.formalGroupLaw n) = (n : R) :=
  FormalNsmulDirect.formalNsmulF_coeff_one
    W.formalGroupLaw
    W.formalGroupLaw_constantCoeff
    W.formalGroupLaw_lin_coeff_X
    W.formalGroupLaw_lin_coeff_Y
    n

end WeierstrassCurve.FormalGroupWiring
