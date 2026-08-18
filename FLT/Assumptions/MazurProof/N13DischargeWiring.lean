import FLT.Assumptions.MazurProof.N13RationalPicardEndpoint
import FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingAdapter
import FLT.Assumptions.MazurProof.CyclicExclusion13

/-!
# N13 axiom discharge — wiring attempt

This file attempts to discharge `C13Sextic_affine_x_is_cuspidal` by wiring
the existing 283-file infrastructure through the rational Picard endpoint.

## Strategy

Choose `kernel = ⊥` (trivial subgroup). Since `J₁(13)(ℚ) ≅ ℤ/19ℤ` has no
2-torsion, the kernel of `J(ℚ) → J(𝔽₂)` is trivial, so:
- `class_eq_iff`: special class equality ↔ rational class equality (injectivity)
- `FirstJetDoublingCompatibility`: trivially satisfied at the single element `z = 0`

## Current status

This file has a single `sorry` for `class_eq_iff`, which requires proving that
the special-class assignment on spread lines is injective (faithfully reflects
rational Picard classes when the kernel is trivial).
-/

namespace MazurProof.N13DischargeWiring

noncomputable section

/-- The trivial kernel: since J₁(13)(ℚ) ≅ ℤ/19ℤ has no 2-torsion, the kernel
of reduction J(ℚ) → J(𝔽₂) is trivial. -/
def n13Kernel : AddSubgroup N13RationalPointEndgame.G := ⊥

/-- **SORRY**: The only remaining gap. For trivial kernel, this says: two spread lines
have the same special class iff they have the same rational Picard class.

This follows from:
1. J(ℚ) → J(𝔽₂) is injective (Z/19Z has no 2-torsion)
2. The specialization of spread lines is compatible with Jacobian reduction
3. The set-valued classifier on the special fiber is faithful

All three should follow from the existing 283-file infrastructure. -/
theorem n13_class_eq_iff :
    ∀ L M : N13RationalCurvePointPicardRealization.SpreadLine,
      N13RationalCurvePointPicardRealization.specialClass L =
          N13RationalCurvePointPicardRealization.specialClass M ↔
        N13RationalCurvePointPicardRealization.genericClass n13Kernel L =
          N13RationalCurvePointPicardRealization.genericClass n13Kernel M := by
  sorry

end

end MazurProof.N13DischargeWiring
