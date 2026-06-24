import Mathlib
open Polynomial WeierstrassCurve

namespace DiagTest

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable def dupNumP (P Q : R[X]) : R[X] :=
  P ^ 4 - C W.b₄ * P ^ 2 * Q ^ 2 - C (2 * W.b₆) * P * Q ^ 3 - C W.b₈ * Q ^ 4

noncomputable def dupDenP (P Q : R[X]) : R[X] :=
  C 4 * P ^ 3 * Q + C W.b₂ * P ^ 2 * Q ^ 2 + C (2 * W.b₄) * P * Q ^ 3 + C W.b₆ * Q ^ 4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- Diagnostic: the doubling cross-identity at the CONCRETE 2m=4, via Mathlib's proven
Φ_four/ΨSq_four (independent of my general-m recurrence rewrites). -/
theorem diag_2m4 :
    W.Φ 4 * dupDenP W (W.Φ 2) (W.ΨSq 2)
      = W.ΨSq 4 * dupNumP W (W.Φ 2) (W.ΨSq 2) := by
  rw [ΨSq_four, Φ_four, ΨSq_two, Φ_two, dupNumP, dupDenP]
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

end DiagTest
