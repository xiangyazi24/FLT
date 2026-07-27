import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.TateOrder13

/-!
# Cyclic order 13 exclusion

The modular curve `X₁(13)` has genus 2, Jacobian of rank 0 over `ℚ` with
`J(ℚ) ≅ ℤ/19ℤ`.  Its rational points are all cusps (corresponding to
degenerate Tate parameters `b = 0`).

## Strategy

1. `TateOrder13.exists_tate_parameters_of_order_thirteen` reduces a rational
   order-13 point to the Diophantine condition `F₁₃(b,c) = 0` with `b ≠ 0`.
2. `no_F13_rational_solution` asserts this Diophantine equation has no rational
   solution — equivalently, every rational point on `X₁(13)` is a cusp.
3. The two together give `no_rational_point_of_order_13`.

## References

* Ogg, "Rational points on certain elliptic modular curves", 1973
* Mazur, "Modular curves and the Eisenstein ideal", 1978
* Kubert, "Universal bounds on the torsion of elliptic curves", 1976
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

namespace CyclicExclusion13

/-- The Diophantine core: `F₁₃(b,c) = 0` has no rational solution with `b ≠ 0`.
Equivalently, every rational point on `X₁(13)` is a cusp. -/
axiom no_F13_rational_solution :
    ∀ b c : ℚ, b ≠ 0 → TateNFDivision.F13 b c ≠ 0

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
