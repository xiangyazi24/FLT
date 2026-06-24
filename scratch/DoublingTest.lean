import Mathlib
open Polynomial WeierstrassCurve

namespace DoublingTest

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable def dupNumP (P Q : R[X]) : R[X] :=
  P ^ 4 - C W.b₄ * P ^ 2 * Q ^ 2 - C (2 * W.b₆) * P * Q ^ 3 - C W.b₈ * Q ^ 4

noncomputable def dupDenP (P Q : R[X]) : R[X] :=
  C 4 * P ^ 3 * Q + C W.b₂ * P ^ 2 * Q ^ 2 + C (2 * W.b₄) * P * Q ^ 3 + C W.b₆ * Q ^ 4

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem dup_doubling_cross (m : ℤ) :
    W.Φ (2 * m) * dupDenP W (W.Φ m) (W.ΨSq m)
      = W.ΨSq (2 * m) * dupNumP W (W.Φ m) (W.ΨSq m) := by
  have hΦ2m : W.Φ (2 * m) = X * W.ΨSq (2 * m)
      - W.preΨ (2 * m + 1) * W.preΨ (2 * m - 1) := by
    rw [WeierstrassCurve.Φ, if_pos (even_two_mul m), mul_one]
  have h2m1 : (2 * m - 1 : ℤ) = 2 * (m - 1) + 1 := by ring
  rw [hΦ2m, W.ΨSq_even m, W.preΨ_odd m, h2m1, W.preΨ_odd (m - 1)]
  simp only [WeierstrassCurve.Φ, WeierstrassCurve.ΨSq, dupNumP, dupDenP,
    WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  rcases Int.even_or_odd m with hm | hm
  · have hm1 : ¬ Even (m - 1) := by
      rcases hm with ⟨t, rfl⟩; intro h; rw [Int.even_iff] at h; omega
    simp only [if_pos hm, if_neg hm1]
    ring
  · have hm0 : ¬ Even m := Int.not_even_iff_odd.mpr hm
    have hm1 : Even (m - 1) := by rcases hm with ⟨t, rfl⟩; exact ⟨t, by ring⟩
    simp only [if_neg hm0, if_pos hm1]
    ring

end DoublingTest
