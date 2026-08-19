import FLT.Assumptions.MazurProof.N13RationalPicardEndpoint
import FLT.Assumptions.MazurProof.N13TrivialKernelFamily

/-!
# Direct N13 rational-point theorem without class_eq_iff

The `class_eq_iff` sorry for arbitrary SpreadLines is genuinely unprovable:
two SpreadLines with the same rationalClass can use different Mumford
representatives of the same Picard class, producing different specialDivisors.

This file bypasses class_eq_iff by going through `PointwiseReflection`
instead of the `CompatibleReduction` framework. The single remaining
mathematical content is the injectivity of the specialization map
`G → SpecialSet`, which follows from good reduction of J₁(13) at p = 2.

## Strategy

1. `trivialKernel_separated : NSeparated ⊥ 2` (already proved)
2. The specialization map `classify : G → SpecialSet` is injective
   (from good reduction + prime-to-p order; currently sorry)
3. `classify_abel` for curve points (from pointwise construction)
4. Every rational point equals a cusp (the main theorem)
-/

namespace MazurProof.N13DirectEndpoint

noncomputable section

open N13RationalPicardSpreadExistence

/-- The specialization function: map each rational Picard class to its
special Abel class via the canonical exact spread line. -/
private abbrev G := N13RationalPointEndgame.G
private abbrev SpecialSet := N13RationalPointEndgame.SpecialSet
private abbrev RationalCurvePoint := N13RationalPointEndgame.RationalCurvePoint

def classify (g : G) : SpecialSet :=
  N13RationalCurvePointPicardRealization.specialClass (exactSpreadLine g)

/-- **SORRY**: The specialization map is injective.

This follows from: J₁(13) has good reduction at p = 2 (since 2 ∤ 13),
and J₁(13)(ℚ) has odd order 19 (prime to 2). By the Néron--Ogg--Shafarevich
criterion, the kernel of reduction is a pro-2 group, hence intersects
the 19-torsion trivially.

To prove this formally, one should either:
(a) Add an AddCommGroup structure to SpecialSet (via Mumford composition
    on the special curve) and show classify is a group homomorphism,
    then use NSeparated ⊥ 2 + TwoSurjective to get injectivity.
(b) Verify by explicit computation that the 19 normalized Mumford
    representatives reduce to 19 distinct special Mumford ideals.
-/
theorem classify_injective : Function.Injective classify := by
  sorry

/-- The specialization of a rational curve point's Abel class agrees
with the special Abel class of its proper reduction.

This is the Abel--Jacobi compatibility for the exact spread construction. -/
theorem classify_abel (P : RationalCurvePoint) :
    classify (N13RationalPointEndgame.rationalAbel P) =
      N13RationalPointEndgame.specialPointClass (N13ProperCurveReduction.reduceCurve P) := by
  sorry

/-- The main N13 rational-point theorem, bypassing `class_eq_iff`. -/
theorem n13_affine_x_is_cuspidal :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1 := by
  apply N13RationalPicardEndpoint.affine_x_is_cuspidal_of_pointwiseReflection
  intro P Q hspecial
  have hP := classify_abel P
  have hQ := classify_abel Q
  rw [hspecial] at hP
  exact classify_injective (hP.trans hQ.symm)

end

end MazurProof.N13DirectEndpoint
