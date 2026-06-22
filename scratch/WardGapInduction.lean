import scratch.WardEllSequence
import scratch.WardInvariant

/-!
# Ward gap induction — `normEDS_addRel` via the mutual `(GapRel, OffRel)` induction

Route: van der Poorten–Swart Thm 3 (cf. Mathlib PR #13155, alreadydone). Every cofactor below was
sympy-verified (free-`W`, exact 0); see `WARD_FULL_DOCTRINE.md`. The code is ours.

`GapRel b c d k m := AddRel (normEDS b c d) m k`  (so `GapRel 2 m` is the adjacent Somos).
`OffRel` is the off-diagonal `b·W(m+k+1)W(m-k) = W(m+2)W(m-1)W(k+1)W(k) − W(k+2)W(k-1)W(m+1)W(m)`
(= Stange elliptic-net `EN(m,k,1,1)`).
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

/-- **G-step (multiplied form).** `b²·U_k(m)·(GapRel(k+1,m) residual) = 0`, the sympy-verified
linear combination of `GapRel k`, `OffRel k m`, `OffRel k (m-1)`, the two adjacent Somos, and `Trel`.
Cancelling the factor `b²·W(m+k)·W(m-k)` (nonzero off `m=±k`) gives `GapRel (k+1) m`. -/
lemma gStep_mul [IsDomain R] (b c d : R) (hc : c ≠ 0)
    (hne : ∀ j : ℤ, j ≠ 0 → normEDS b c d j ≠ 0) (k m : ℤ)
    (hG : GapRel b c d k m) (hO : OffRel b c d k m) (hO1 : OffRel b c d k (m - 1)) :
    b ^ 2 * normEDS b c d (m + k) * normEDS b c d (m - k) *
      (normEDS b c d (m + (k + 1)) * normEDS b c d (m - (k + 1))
        - (normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d (k + 1) ^ 2
           - normEDS b c d (k + 1 + 1) * normEDS b c d (k + 1 - 1) * normEDS b c d m ^ 2)) = 0 := by
  unfold GapRel AddRel at hG
  unfold OffRel at hO hO1
  have hsm := normEDS_adjacent_somos b c d m
  have hsk := normEDS_adjacent_somos b c d k
  have htrel := Trel_zero b c d hc hne k m
  unfold Nseq Dseq at htrel
  simp only [show m + (k + 1) = m + k + 1 by ring, show m - (k + 1) = m - k - 1 by ring,
    show k + 1 + 1 = k + 2 by ring, show k + 1 - 1 = k by ring,
    show (m - 1) + k + 1 = m + k by ring, show (m - 1) - k = m - k - 1 by ring,
    show (m - 1) + 2 = m + 1 by ring, show (m - 1) - 1 = m - 2 by ring,
    show (m - 1) + 1 = m by ring] at hG hO hO1 hsm hsk htrel ⊢
  linear_combination
    (-(b ^ 2) * (normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d (k + 1) ^ 2
        - normEDS b c d (k + 2) * normEDS b c d k * normEDS b c d m ^ 2)) * hG
    + (b * normEDS b c d (m + k) * normEDS b c d (m - k - 1)) * hO
    + (normEDS b c d (m + 2) * normEDS b c d (m - 1) * normEDS b c d (k + 1) * normEDS b c d k
        - normEDS b c d (k + 2) * normEDS b c d (k - 1) * normEDS b c d (m + 1) * normEDS b c d m) * hO1
    + (normEDS b c d k ^ 2 * normEDS b c d (k + 1) ^ 2 * normEDS b c d (m + 1)
        * normEDS b c d (m - 1)) * hsm
    + (-(normEDS b c d m ^ 2 * normEDS b c d (k + 1) ^ 2 * normEDS b c d (m + 1)
        * normEDS b c d (m - 1))) * hsk
    + (normEDS b c d m * normEDS b c d (k + 2)) * htrel

/-- **H-step (multiplied form).** `V_k(m)·(OffRel(k+1,m) residual) = 0`, the sympy-verified linear
combination of `GapRel (k+1) m`, `GapRel (k+1) (m+1)`, `OffRel k m`, `Trel (k+1) m`, and the two Somos
(`@m`, `@(k+1)`). Cancelling `V_k(m) = b·W(m+k+1)W(m-k)` (nonzero) gives `OffRel (k+1) m`. -/
lemma hStep_mul [IsDomain R] (b c d : R) (hc : c ≠ 0)
    (hne : ∀ j : ℤ, j ≠ 0 → normEDS b c d j ≠ 0) (k m : ℤ)
    (hG1 : GapRel b c d (k + 1) m) (hG2 : GapRel b c d (k + 1) (m + 1)) (hO : OffRel b c d k m) :
    (b * normEDS b c d (m + k + 1) * normEDS b c d (m - k)) *
      (b * normEDS b c d (m + k + 2) * normEDS b c d (m - k - 1)
        - (normEDS b c d (m + 2) * normEDS b c d (m - 1) * normEDS b c d (k + 2) * normEDS b c d (k + 1)
           - normEDS b c d (k + 3) * normEDS b c d k * normEDS b c d (m + 1) * normEDS b c d m)) = 0 := by
  unfold GapRel AddRel at hG1 hG2
  unfold OffRel at hO
  have hsm := normEDS_adjacent_somos b c d m
  have hsk1 := normEDS_adjacent_somos b c d (k + 1)
  have htrel := Trel_zero b c d hc hne (k + 1) m
  unfold Nseq Dseq at htrel
  simp only [show m + (k + 1) + 1 = m + k + 2 by ring, show m - (k + 1) = m - k - 1 by ring,
    show m + (k + 1) = m + k + 1 by ring, show k + 1 + 1 = k + 2 by ring, show k + 1 - 1 = k by ring,
    show (m + 1) + (k + 1) = m + k + 2 by ring, show (m + 1) - (k + 1) = m - k by ring,
    show (m + 1) + 1 = m + 2 by ring, show (m + 1) - 1 = m by ring,
    show (k + 1) + 2 = k + 3 by ring, show (k + 1) - 2 = k - 1 by ring,
    show (k + 1) + 1 = k + 2 by ring, show (k + 1) - 1 = k by ring] at hG1 hG2 hO hsm hsk1 htrel ⊢
  linear_combination
    (b ^ 2 * (normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d (k + 1) ^ 2
        - normEDS b c d (k + 2) * normEDS b c d k * normEDS b c d m ^ 2)) * hG2
    + (b ^ 2 * normEDS b c d (m + k + 2) * normEDS b c d (m - k)) * hG1
    + (-(normEDS b c d (m + 2) * normEDS b c d (m - 1) * normEDS b c d (k + 2) * normEDS b c d (k + 1)
        - normEDS b c d (k + 3) * normEDS b c d k * normEDS b c d (m + 1) * normEDS b c d m)) * hO
    + (normEDS b c d (m + 2) * normEDS b c d (k + 1)) * htrel
    + (normEDS b c d k * normEDS b c d (k + 1) ^ 2 * normEDS b c d (k + 2) * normEDS b c d (m + 1) ^ 2) * hsm
    + (-(normEDS b c d k * normEDS b c d (k + 2) * normEDS b c d m ^ 2 * normEDS b c d (m + 1) ^ 2)) * hsk1

/-- **Diagonal** `GapRel (k+1) k` (= `AddRel k (k+1)`): the odd-index recurrence, where the G-step
cancellation factor `b²W(m+k)W(m-k)` vanishes (`m=k ⇒ W(0)=0`). Direct from Mathlib `normEDS_odd`. -/
lemma gapRel_diag (b c d : R) (k : ℤ) : GapRel b c d (k + 1) k := by
  unfold GapRel AddRel
  have hodd := normEDS_odd b c d k
  simp only [show k + (k + 1) = 2 * k + 1 by ring, show k - (k + 1) = -1 by ring,
    show (k + 1) + 1 = k + 2 by ring, show (k + 1) - 1 = k by ring]
  rw [hodd, show (-1 : ℤ) = -(1) by ring, normEDS_neg, normEDS_one]
  ring

end FLT.EDS
