import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.TateOrder13
import FLT.Assumptions.MazurProof.N13CurveModel

/-!
# Cyclic order 13 exclusion

The modular curve `X₁(13)` has genus 2, Jacobian of rank 0 over `ℚ` with
`J(ℚ) ≅ ℤ/19ℤ`.  Its rational points are all cusps (corresponding to
degenerate Tate parameters `b = 0`).

## Strategy

1. `TateOrder13.exists_tate_parameters_of_order_thirteen` reduces a rational
   order-13 point to the condition `F₁₃(b,c) = 0` with `b ≠ 0`.
2. `N13TateBridge.exists_C13Opt_point_of_tateF13` sends such a solution to the
   noncuspidal affine locus of the optimized genus-two model of `X₁(13)`.
3. The remaining arithmetic input says that this locus has no rational point.

## References

* Ogg, "Rational points on certain elliptic modular curves", 1973
* Mazur, "Modular curves and the Eisenstein ideal", 1978
* Kubert, "Universal bounds on the torsion of elliptic curves", 1976
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

namespace CyclicExclusion13

/-- The arithmetic core: every rational point on the optimized model of
`X₁(13)` is a cusp.  The Tate and birational reductions are proved separately
in `N13TateBridge`. -/
axiom C13Sextic_affine_x_is_cuspidal :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y → X = 0 ∨ X = -1

/-- The sextic rational-point theorem rules out the noncuspidal open of the
optimized model. -/
theorem C13Opt_rational_points_are_cuspidal :
    ∀ x y : ℚ, N13TateBridge.C13OptEq x y →
      ¬N13TateBridge.OptNonCusp13 x y := by
  intro x y hcurve hnon
  obtain ⟨hsextic, hX0, hXneg⟩ :=
    N13CurveModel.optToSextic_nonexceptional hcurve hnon
  rcases C13Sextic_affine_x_is_cuspidal
      (N13CurveModel.optToSexticX x)
      (N13CurveModel.optToSexticY x y) hsextic with h | h
  · exact hX0 h
  · exact hXneg h

/-- The old Tate-polynomial boundary follows from the structural modular-curve
bridge and the fixed rational-point theorem. -/
theorem no_F13_rational_solution :
    ∀ b c : ℚ, b ≠ 0 → TateNFDivision.F13 b c ≠ 0 := by
  intro b c hb hF
  obtain ⟨x, y, hcurve, hnoncusp⟩ :=
    N13TateBridge.exists_C13Opt_point_of_tateF13 hb hF
  exact C13Opt_rational_points_are_cuspidal x y hcurve hnoncusp

end CyclicExclusion13

/-- No elliptic curve over `ℚ` has a rational point of exact order `13`. -/
theorem no_rational_point_of_order_13
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 13 := by
  intro ⟨P, hP⟩
  obtain ⟨b, c, _, _, hb, hF13⟩ :=
    TateOrder13.exists_tate_parameters_of_order_thirteen E P hP
  exact CyclicExclusion13.no_F13_rational_solution b c hb hF13

end MazurProof
