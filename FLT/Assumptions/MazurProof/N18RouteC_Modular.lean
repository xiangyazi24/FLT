import FLT.Assumptions.MazurProof.N18RouteC_Curve
import FLT.Assumptions.MazurProof.TateOrder18
import FLT.Assumptions.MazurProof.RationalPointsN18

/-!
# Exact order 18 gives a noncuspidal point on the Route C sextic

This reuses the repository's axiom-free order-`9` Tate-normal-form bridge.
Its standard hyperelliptic coordinate `U` is related to the Route C coordinate
by `x = -U`.
-/

namespace MazurProof.N18RouteC.Modular

noncomputable section

theorem curvePolynomial_neg_eq_hyperellipticF18 (U : ℚ) :
    curvePolynomial (-U) = RationalPointsN18.hyperellipticF18 U := by
  unfold curvePolynomial RationalPointsN18.hyperellipticF18
  ring

theorem exactOrder18_to_noncusp
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h18 : HasRationalPointOfOrder E 18) :
    ∃ P : CurvePointQ, ¬ CurvePoint.IsCusp P := by
  obtain ⟨b, c, X, hb, hF9, hT2⟩ :=
    TateOrder18.order18_to_tate_obstruction E h18
  obtain ⟨U, Y, hU0, hU1, hY⟩ :=
    RationalPointsN18.obstruction_to_hyperelliptic hb hF9 hT2
  have hcurve : Y ^ 2 = curvePolynomial (-U) := by
    rw [curvePolynomial_neg_eq_hyperellipticF18]
    exact hY
  refine ⟨.affine (-U) Y hcurve,
    CurvePoint.affine_not_cusp_of_x_ne ?_ ?_⟩
  · exact neg_ne_zero.mpr hU0
  · intro hneg
    apply hU1
    linarith

end

end MazurProof.N18RouteC.Modular
