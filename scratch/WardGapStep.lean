import scratch.WardEllSequence
import scratch.WardInvariant

/-!
# Ward gap step — building blocks (van der Poorten–Swart Thm 3, eqs 13–15)

The mutual gap induction `(GapRel k, OffRel k) ⟹ (GapRel (k+1), OffRel (k+1))` is driven by two
regrouping tautologies on the "gap products" `U_k(m) = W(m+k)W(m-k)` and the off-by-one
`V_k(m) = W(2)·W(m+k+1)W(m-k)`. This file states those building blocks; the gap steps then close
from `OffRel`/`GapRel` at `k`, the adjacent Somos, and `Trel_zero`, cancelling over the domain.

`GapRel k m` is `AddRel` (already in WardEllSequence); the code is ours, route is vdPS Thm 3 / cf. PR #13155.
-/

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- Gap product `U_k(m) = W(m+k) W(m-k)`. -/
def Useq (W : ℤ → R) (k m : ℤ) : R := W (m + k) * W (m - k)

/-- Off-by-one gap product `V_k(m) = W(2) · W(m+k+1) W(m-k)`. -/
def Vseq (W : ℤ → R) (k m : ℤ) : R := W 2 * W (m + k + 1) * W (m - k)

/-- Driving tautology for the gap step (eq. before (13)): a pure regrouping identity. -/
lemma Vseq_mul_Vseq (W : ℤ → R) (k m : ℤ) :
    Vseq W k m * Vseq W k (m - 1) = (W 2) ^ 2 * Useq W (k + 1) m * Useq W k m := by
  unfold Useq Vseq
  simp only [show (m - 1) + k + 1 = m + k by ring, show (m - 1) - k = m - k - 1 by ring,
    show m + (k + 1) = m + k + 1 by ring, show m - (k + 1) = m - k - 1 by ring]
  ring

end FLT.EDS
