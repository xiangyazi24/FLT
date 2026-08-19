import FLT.Assumptions.MazurProof.N13RationalPicardSpreadExistence
import FLT.Assumptions.MazurProof.N13RationalAbelChartBase
import FLT.Assumptions.MazurProof.N13TrivialKernelFamily

/-!
# Proof of `class_eq_iff` for the trivial kernel

For kernel = ⊥, the class_eq_iff theorem states that two spread lines
have the same special class iff they have the same rational class.

The key insight is that every SpreadLine's affine ideal is *automatically*
the saturated contraction of its generic Mumford ideal. This follows from
a degree argument: the generic and special fibres both have rank 2, so
the integral model cannot carry 2-torsion.
-/

namespace MazurProof.N13ClassEqIff

noncomputable section

open N13RationalPicardSpreadExistence
open N13RationalCurvePointPicardRealization
open N13RationalAbelChartBase

private abbrev G := N13RationalPointEndgame.G

/-!
## Step 1: Well-definedness for vertically saturated SpreadLines

Two vertically saturated SpreadLines with the same rational class have
the same integral affine ideal (by contraction retract), hence the same
special restriction, hence the same Abel class.
-/

/-- Two vertically saturated SpreadLines with the same rational class
and the same generic Mumford ideal have the same special class.

Proof outline:
1. Both saturated + same generic → same contraction → same integral affine ideal
2. Same integral affine ideal → same restrict.affineIdeal
3. Same restrict gives same ofDivisor(specialDivisor) on the affine chart
4. ChartPair overlap_eq + affine equality → abel equality
-/
theorem specialClass_eq_of_rationalClass_eq_of_saturated
    (L M : SpreadLine)
    (hrational : L.rationalClass = M.rationalClass)
    (hLsat : N13TwoChartPicardRealization.AffineVerticallySaturated
      L.realization.charts)
    (hMsat : N13TwoChartPicardRealization.AffineVerticallySaturated
      M.realization.charts) :
    specialClass L = specialClass M := by
  -- Both have the same generic fiber
  have hgenericL := L.generic_eq
  have hgenericM := M.generic_eq
  rw [hrational] at hgenericL
  -- So their generic Picard classes agree
  have hpic : L.realization.toGenericPic = M.realization.toGenericPic := by
    rw [hgenericL, hgenericM]
  -- The affine ideals, when localized, give the same generic Mumford ideal.
  -- By contraction retract (both saturated), the integral affine ideals match.
  -- From there: same restrict.affineIdeal → same ofDivisor affineIdeal →
  -- same Abel class.
  sorry

/-!
## Step 2: Every SpreadLine is automatically vertically saturated

The argument: the affine ideal I of a SpreadLine satisfies
- I[1/2] = generic Mumford ideal J_gen (from generic_eq)
- I mod 2 = special Mumford ideal I₀ (from special_affine)

From I₀, lift to an integral Mumford ideal J = (u, Y-v) over ℤ₂.
Then J ⊂ I (both generators are in I) and J is saturated.
Since I ⊂ contractIdeal(I[1/2]) = contractIdeal(J[1/2]) = J,
we get I = J.

The key step: u_gen (from J_gen) has ℤ₂-integral coefficients,
because any non-integral coefficient would produce a low-degree
element in I[1/2], contradicting rank(R/I) = 2.
-/

/-- Every SpreadLine's realization has vertically saturated affine charts. -/
theorem spreadLine_affineVerticallySaturated (L : SpreadLine) :
    N13TwoChartPicardRealization.AffineVerticallySaturated
      L.realization.charts := by
  sorry

/-!
## Step 3: class_eq_iff for kernel = ⊥

Combining Steps 1 and 2: same rationalClass → same specialClass (← direction).
For the → direction: classify = specialClass ∘ exactSpreadLine is well-defined
(by ←), and surjective (every Abel class has a spread line representative
by regular_fiber_nonempty + the construction). Since |G| = |SpecialSet| = 19,
surjectivity gives injectivity, hence the → direction.
-/

/-- The (←) direction: equal rational classes imply equal special classes. -/
theorem specialClass_eq_of_rationalClass_eq
    (L M : SpreadLine)
    (hrational : L.rationalClass = M.rationalClass) :
    specialClass L = specialClass M :=
  specialClass_eq_of_rationalClass_eq_of_saturated L M hrational
    (spreadLine_affineVerticallySaturated L)
    (spreadLine_affineVerticallySaturated M)

/-- The class_eq_iff for the trivial kernel. -/
theorem n13_class_eq_iff :
    ∀ L M : SpreadLine,
      specialClass L = specialClass M ↔
        genericClass (⊥ : AddSubgroup G) L =
          genericClass (⊥ : AddSubgroup G) M := by
  intro L M
  constructor
  · -- (→): same specialClass → same rationalClass
    intro hspecial
    -- Well-definedness gives: specialClass = classify ∘ rationalClass
    -- Classify is injective (19 = 19 + surjectivity)
    sorry
  · -- (←): same genericClass (mod ⊥) → same specialClass
    intro hgeneric
    have hrational : L.rationalClass = M.rationalClass := by
      simp only [genericClass] at hgeneric
      rwa [QuotientAddGroup.mk'_eq_mk', AddSubgroup.mem_bot, sub_eq_zero] at hgeneric
    exact specialClass_eq_of_rationalClass_eq L M hrational

end

end MazurProof.N13ClassEqIff
