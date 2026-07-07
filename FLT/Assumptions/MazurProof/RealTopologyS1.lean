import FLT.Assumptions.MazurProof.RealTopologyS3

/-!
# Real topology route, S1: algebraic root facts

This file records the root-order facts needed by S3 in a factored form.  The
analytic/topological route can later supply the factorization and ordering for
the rightmost real branch point `e`.
-/

namespace MazurProof.RealTopology

/--
For a factored monic cubic with rightmost simple root `e`, the derivative at
`e` is positive.  This is the S1 input consumed by `componentBitHom`.
-/
theorem shortCubicDeriv_pos_of_ordered_roots
    {A B r s e : ℝ}
    (hA : A = -(e + r + s))
    (hB : B = e * r + e * s + r * s)
    (hr : r < e) (hs : s < e) :
    0 < shortCubicDeriv A B e := by
  have her : 0 < e - r := sub_pos.mpr hr
  have hes : 0 < e - s := sub_pos.mpr hs
  have hprod : 0 < (e - r) * (e - s) := mul_pos her hes
  rw [hA, hB, shortCubicDeriv]
  nlinarith

/-- A monic cubic factored by three roots is positive to the right of the largest root. -/
theorem shortCubic_pos_right_of_ordered_roots
    {A B r s e x : ℝ}
    (hfactor : ∀ u : ℝ, shortCubic A B u = (u - r) * (u - s) * (u - e))
    (hr : r < e) (hs : s < e) (hx : e < x) :
    0 < shortCubic A B x := by
  have hxr : 0 < x - r := sub_pos.mpr (lt_trans hr hx)
  have hxs : 0 < x - s := sub_pos.mpr (lt_trans hs hx)
  have hxe : 0 < x - e := sub_pos.mpr hx
  rw [hfactor x]
  exact mul_pos (mul_pos hxr hxs) hxe

/-- Nonnegativity on the closed ray to the right of the largest root. -/
theorem shortCubic_nonneg_right_of_ordered_roots
    {A B r s e x : ℝ}
    (hfactor : ∀ u : ℝ, shortCubic A B u = (u - r) * (u - s) * (u - e))
    (hr : r < e) (hs : s < e) (hx : e ≤ x) :
    0 ≤ shortCubic A B x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · rw [hfactor e]
    simp
  · exact (shortCubic_pos_right_of_ordered_roots hfactor hr hs hxlt).le

end MazurProof.RealTopology
