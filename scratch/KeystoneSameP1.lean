import scratch.KeystoneLadder
import scratch.KeystoneDoubling
import scratch.KeystoneDoublingCert

open Polynomial WeierstrassCurve

namespace KeystoneLadder

variable {k : Type*} [Field k]

/-- The x-coordinate doubling fact: `doubleVec (xPair m) ~ xPair (2m)` projectively (c = 1),
from the proven polynomial doubling identities `Φ_two_mul`/`ΨSq_two_mul` evaluated at `x`. -/
lemma xPair_double_sameP1 (W : WeierstrassCurve k) (m : ℤ) (x : k)
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0) :
    SameP1Vec (XOnly.doubleVec (E := W⁄k) (xPair W m x)) (xPair W (2 * m) x) := by
  refine ⟨1, one_ne_zero, ?_⟩
  funext i
  fin_cases i <;>
    simp only [Pi.smul_apply, smul_eq_mul, one_mul, xPair, XOnly.doubleVec, XOnly.X, XOnly.Z,
      Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  · rw [W.Φ_two_mul h4 hψ_ne hc3 m, W.dupNumP_eval]
    simp only [XOnly.dupNumH, WeierstrassCurve.baseChange, WeierstrassCurve.map_b₄,
      WeierstrassCurve.map_b₆, WeierstrassCurve.map_b₈, Algebra.algebraMap_self_apply]
  · rw [W.ΨSq_two_mul h4 hψ_ne hc3 m, W.dupDenP_eval]
    simp only [XOnly.dupDenH, WeierstrassCurve.baseChange, WeierstrassCurve.map_b₂,
      WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, Algebra.algebraMap_self_apply]

end KeystoneLadder
