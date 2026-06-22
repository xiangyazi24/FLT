import scratch.WardEllSequence
import scratch.WardInvariant

/-!
# Ward gap induction — `normEDS_addRel` via the mutual `(GapRel, OffRel)` induction

Route: van der Poorten–Swart Thm 3 (cf. Mathlib PR #13155, alreadydone). Every cofactor below was
sympy-verified (free-`W`, exact 0); see `WARD_FULL_DOCTRINE.md`. The code is ours.

`GapRel b c d k m := AddRel (normEDS b c d) m k`  (so `GapRel 2 m` is the adjacent Somos).
`OffRel` is the off-diagonal `b·W(m+k+1)W(m-k) = W(m+2)W(m-1)W(k+1)W(k) − W(k+2)W(k-1)W(m+1)W(m)`.
-/

namespace FLT.EDS

variable {R : Type*} [CommRing R]

/-- Gap relation `U_k(m) = B(m)W(k)² − B(k)W(m)²` (= `AddRel` with the gap as second argument). -/
def GapRel (b c d : R) (k m : ℤ) : Prop := AddRel (normEDS b c d) m k

/-- Off-diagonal relation. -/
def OffRel (b c d : R) (k m : ℤ) : Prop :=
  b * normEDS b c d (m + k + 1) * normEDS b c d (m - k)
    = normEDS b c d (m + 2) * normEDS b c d (m - 1) * normEDS b c d (k + 1) * normEDS b c d k
      - normEDS b c d (k + 2) * normEDS b c d (k - 1) * normEDS b c d (m + 1) * normEDS b c d m

/-- Base case `GapRel 0 m`: `W(m)² = W(m)²` (trivial via `W 0 = 0`). -/
lemma gapRel_zero (b c d : R) (m : ℤ) : GapRel b c d 0 m := by
  unfold GapRel AddRel
  simp only [add_zero, sub_zero, show (0:ℤ)+1 = 1 by ring, show (0:ℤ)-1 = -1 by ring]
  simp [normEDS_zero, normEDS_one, normEDS_neg]
  ring

/-- Base case `OffRel 0 m`: `b·W(m+1)W(m) = b·W(m+1)W(m)` (trivial via `W 0 = 0`). -/
lemma offRel_zero (b c d : R) (m : ℤ) : OffRel b c d 0 m := by
  unfold OffRel
  simp only [add_zero, sub_zero, show m+0+1 = m+1 by ring, show (0:ℤ)+1 = 1 by ring,
    show (0:ℤ)+2 = 2 by ring, show (0:ℤ)-1 = -1 by ring]
  simp [normEDS_zero, normEDS_one, normEDS_two, normEDS_neg]

end FLT.EDS
