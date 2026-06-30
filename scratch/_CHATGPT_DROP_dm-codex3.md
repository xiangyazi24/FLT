# Q2624 / Q2621: positive coprime product square extraction over `Int`

Target file: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.
Namespace for the Euler wrapper: `MazurProof.RationalPointsN12`.

The robust route is to prove the integer extraction theorem directly from `Int.sq_of_isCoprime`, calling it once for the left factor and once for the right factor. Positivity eliminates the negative-square branch, and then `abs` gives a positive root.

For the Euler wrapper, the only nontrivial inputs are positivity of the two cofactors and the already-proved `euler_cofactor_coprime`. The positivity goals are immediate from `D ^ 2 > 0` and nonnegativity of squares.

```lean
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace Int

theorem exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    {x y z : Int}
    (hx : 0 < x) (hy : 0 < y)
    (hxy : IsCoprime x y)
    (h : z ^ 2 = x * y) :
    exists r s : Int,
      0 < r /\ 0 < s /\ r ^ 2 = x /\ s ^ 2 = y := by
  have hmul : x * y = z ^ 2 := h.symm
  rcases Int.sq_of_isCoprime hxy hmul with ⟨r, hr | hr⟩
  · rcases Int.sq_of_isCoprime hxy.symm (by simpa [mul_comm] using hmul) with
      ⟨s, hs | hs⟩
    · refine ⟨|r|, |s|, ?_, ?_, ?_, ?_⟩
      · exact abs_pos.mpr (by
          intro hr0
          have hx0 : x = 0 := by simpa [hr0] using hr
          exact (ne_of_gt hx) hx0)
      · exact abs_pos.mpr (by
          intro hs0
          have hy0 : y = 0 := by simpa [hs0] using hs
          exact (ne_of_gt hy) hy0)
      · calc
          |r| ^ 2 = r ^ 2 := by simpa using (sq_abs r)
          _ = x := hr.symm
      · calc
          |s| ^ 2 = s ^ 2 := by simpa using (sq_abs s)
          _ = y := hs.symm
    · exfalso
      have hsq_nonneg : 0 ≤ s ^ 2 := sq_nonneg s
      have hy_nonpos : y ≤ 0 := by
        rw [hs]
        exact neg_nonpos.mpr hsq_nonneg
      exact (not_lt_of_ge hy_nonpos) hy
  · exfalso
    have hsq_nonneg : 0 ≤ r ^ 2 := sq_nonneg r
    have hx_nonpos : x ≤ 0 := by
      rw [hr]
      exact neg_nonpos.mpr hsq_nonneg
    exact (not_lt_of_ge hx_nonpos) hx

end Int

namespace MazurProof.RationalPointsN12

theorem euler_cofactors_are_squares_of_center_square
    {A D X : Int}
    (hApos : 0 < A) (hDpos : 0 < D)
    (hDodd : Odd D) (hAD : IsCoprime A D)
    (hXsq : X ^ 2 = (16 * A ^ 2 + D ^ 2) * (4 * A ^ 2 + D ^ 2)) :
    exists B C : Int, 0 < B /\ 0 < C /\
      B ^ 2 = 16 * A ^ 2 + D ^ 2 /\ C ^ 2 = 4 * A ^ 2 + D ^ 2 := by
  have hleft_pos : 0 < 16 * A ^ 2 + D ^ 2 := by
    have hDsq_pos : 0 < D ^ 2 := sq_pos_of_ne_zero (ne_of_gt hDpos)
    have hAsq_nonneg : 0 ≤ A ^ 2 := sq_nonneg A
    nlinarith
  have hright_pos : 0 < 4 * A ^ 2 + D ^ 2 := by
    have hDsq_pos : 0 < D ^ 2 := sq_pos_of_ne_zero (ne_of_gt hDpos)
    have hAsq_nonneg : 0 ≤ A ^ 2 := sq_nonneg A
    nlinarith
  have hcop : IsCoprime (16 * A ^ 2 + D ^ 2) (4 * A ^ 2 + D ^ 2) := by
    simpa using euler_cofactor_coprime (A := A) (D := D) hDodd hAD
  exact Int.exists_pos_sq_and_sq_of_mul_eq_sq_of_pos_of_isCoprime
    hleft_pos hright_pos hcop hXsq

end MazurProof.RationalPointsN12
```

If the target file is already inside `namespace MazurProof.RationalPointsN12`, put the `namespace Int ... end Int` block outside that namespace, then paste only the body of the Euler wrapper where the project theorem belongs.
