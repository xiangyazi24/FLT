import FLT.Assumptions.MazurProof.N13RationalPicardEndpoint
import FLT.Assumptions.MazurProof.N13MumfordCenteredDoublingAdapter
import FLT.Assumptions.MazurProof.CyclicExclusion13
import FLT.Assumptions.MazurProof.N13TrivialKernelFamily

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

Two sorry remain:
1. class_eq_iff (spread line specialization injectivity)
2. FirstJetDoublingCompatibility (trivially true for ⊥ kernel, needs Lean mechanics)

The mathematical arguments for both are complete — see FLT_MAZUR_STATUS.md and
the ChatGPT Q5298-Q5302 analyses for the precise circularity break path.
-/

namespace MazurProof.N13DischargeWiring

noncomputable section

/-- The trivial kernel: since J₁(13)(ℚ) ≅ ℤ/19ℤ has no 2-torsion, the kernel
of reduction J(ℚ) → J(𝔽₂) is trivial. -/
def n13Kernel : AddSubgroup N13RationalPointEndgame.G := ⊥

/-- **SORRY**: Spread line specialization injectivity for trivial kernel.

For kernel = ⊥, this says: two spread lines have the same special class
iff they have the same rational Picard class.

The mathematical argument is complete (Q5298-Q5302):
- TwoSurjective is PROVED (Mazur-Tate 2-descent, N13MumfordFullKummerTwoSurjective)
- |J(F₂)| = 19 (jacobian_card_eq_nineteen via AbelFiberData)
- Cuspidal Z/19Z ⊂ J(Q) (proved)
- The circularity break requires: KernelSpecializesToBase → canonicalMappedSpecialFamily
  → Chart → NSeparated → reduction_injective → class_eq_iff (Q5302)
- KernelSpecializesToBase for ⊥ is a SINGLE equation at z=0, provable from
  exactNormalizedContractionMatchesSpread (independent of class_eq_iff) -/
theorem n13_class_eq_iff :
    ∀ L M : N13RationalCurvePointPicardRealization.SpreadLine,
      N13RationalCurvePointPicardRealization.specialClass L =
          N13RationalCurvePointPicardRealization.specialClass M ↔
        N13RationalCurvePointPicardRealization.genericClass n13Kernel L =
          N13RationalCurvePointPicardRealization.genericClass n13Kernel M := by
  sorry

/-- **SORRY**: FirstJetDoublingCompatibility for trivial kernel.

For kernel = ⊥, the Kernel = ⊥ (by kernel_eq). The quantifier ∀ z : ⊥
ranges over {0}. At z = 0: pair(0) = basePair (by SmallMumfordRigidity,
since centeredPic(pair 0) = 0 = centeredPic(basePair)), so coord(0) = 0.
Then 2•0 = 0 and squareJet(0) = 0 (from squareJet_sub_double_coord_mem_sq
at z=0 with coord(0)=0). The cross-coefficient is 0 - 0 = 0 ∈ ⊥ = coordIdeal². -/
private theorem n13_first_jet_compat :
    N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility
      (N13RationalPicardEndpoint.canonicalMappedSpecialFamilyOfExactSpread
        n13Kernel n13_class_eq_iff).toNearBaseFamily where
  compare := by
    intro z i
    let F := (N13RationalPicardEndpoint.canonicalMappedSpecialFamilyOfExactSpread
      n13Kernel n13_class_eq_iff).toNearBaseFamily
    have hker : N13RationalPicardEndpoint.Kernel n13Kernel n13_class_eq_iff = n13Kernel :=
      N13RationalPicardEndpoint.kernel_eq n13Kernel n13_class_eq_iff
    have hz0 : (z : N13RationalPointEndgame.G) = 0 := by
      apply AddSubgroup.mem_bot.mp
      exact hker.le z.property
    have hpair : F.pair z = N13TwoAdicAbelChartData.basePair := by
      apply N13TwoAdicAbelChartPic.DiskPair.centeredPic_injective
      have hreal := N13RationalKernelDoublingAdapter.NearBaseFamily.realize F z
      simp only [N13TwoAdicAbelChartSection.subgroupToPic, AddMonoidHom.comp_apply,
        AddSubgroup.coe_subtype, hz0, map_zero,
        N13TwoAdicAbelChartPic.DiskPair.centeredPic_basePair] at hreal ⊢
      exact hreal
    have hcoord : F.coord z = 0 := by
      show N13TwoAdicAbelChartData.DiskPair.coord (F.pair z) = 0
      rw [hpair, N13TwoAdicAbelChartData.DiskPair.coord_basePair]
    have hspan : N13TwoAdicKernelChart.coordIdeal F.coord z =
        (⊥ : Ideal N13TwoAdicKernelChart.R₂) := by
      rw [N13TwoAdicKernelChart.coordIdeal, hcoord, Ideal.span_eq_bot]
      intro x hx; obtain ⟨j, rfl⟩ := hx; exact Pi.zero_apply j
    rw [hspan, Ideal.bot_mul]
    have h2z : (2 • z : N13RationalPicardEndpoint.Kernel n13Kernel n13_class_eq_iff) = z := by
      ext; show 2 • (z : N13RationalPointEndgame.G) = z
      rw [hz0]; simp [two_nsmul]
    rw [h2z, hcoord, Pi.zero_apply]
    have h := N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq
      F z i
    rw [hspan, Ideal.bot_mul, hcoord, Pi.zero_apply, add_zero, sub_zero] at h
    simpa using h

/-- The N13 rational-point theorem, modulo the two sorry above.
Once they are proved, this replaces the axiom C13Sextic_affine_x_is_cuspidal. -/
theorem n13_affine_x_is_cuspidal :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1 :=
  N13RationalPicardEndpoint.affine_x_is_cuspidal
    n13Kernel n13_class_eq_iff n13_first_jet_compat

end

end MazurProof.N13DischargeWiring
