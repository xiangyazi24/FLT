import FLT.Assumptions.MazurProof.N25F_PicardZeroFinite
import FLT.Assumptions.MazurProof.N25F_SectionPrincipalTransport
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoMiddleRiemannRoch

/-!
# The binary class number of the actual N25 curve from degree-four Riemann--Roch

On the full closed-point divisor group modulo actual principal divisors, the
existing class-number consumer
`picardZero_card_eq_seventy_one_of_two_full_closed_points_and_middle_rr` has
four kinds of input.  This file discharges all but the Riemann--Roch one:

* `Pic⁰` is finite (`N25F_PicardZeroFinite.picDegreeZero_finite`);
* `Pic⁴ ≃ Pic⁰` by translation by the degree-one boundary class;
* each effective fibre over a class `c` of degree `n` has `2^ℓ(c) - 1`
  elements, where `ℓ(c)` is the dimension of the actual Riemann--Roch space
  (`fullEffectiveClassFiber25Two_card`, transported along the class);
* the residual map is `c ↦ K - c` for a degree-six class `K`.

The single remaining hypothesis is the genus-four Riemann--Roch identity
`ℓ(c) = ℓ(K - c) + 1` for classes `c` of degree four, for the chosen
degree-six class `K`.  It is a visible hypothesis, not proved here.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.N25F_ClassNumberFromRR

open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_RiemannRochSpace N25F_FullPicardDegree
open N25F_SectionClassFiber N25F_SectionPrincipalTransport N25F_PicardZeroFinite
open RationalPointsN25QuotientMiddleRiemannRoch

/-- Over `F₂` a projective space of rank `r` has `2^r - 1` points. -/
theorem linearSystemCard_two (r : ℕ) :
    CurveZetaClassNumber.linearSystemCard 2 r = 2 ^ r - 1 := by
  unfold CurveZetaClassNumber.linearSystemCard
  rw [Nat.geomSum_eq (le_refl 2)]
  simp

/-- The effective fibre over a degree-`n` class, written with the fixed
index `n`, is the same set as the class fibre of any signed representative. -/
def effectiveFiberEquiv (n : ℕ) (D : ProjectiveDivisor25Two)
    (hD : fullClosedPointGrading25Two.divisorDegree D = n) :
    {E : fullClosedPointGrading25Two.EffDivOfDegree n //
        (fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
          fullProjectivePrincipalSubgroup25Two_le_degree_ker n E).1 =
        fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D} ≃
      FullEffectiveClassFiber25Two D where
  toFun E := ⟨⟨E.1.1, E.1.2.trans (by rw [hD]; simp)⟩, E.2⟩
  invFun E := ⟨⟨E.1.1, E.1.2.trans (by rw [hD]; simp)⟩, E.2⟩
  left_inv E := rfl
  right_inv E := rfl

/-- Cardinality of the effective fibre over an actual Picard class of degree `n`. -/
theorem effectiveClass_fiber_card (n : ℕ)
    (c : fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker n) :
    Nat.card {E : fullClosedPointGrading25Two.EffDivOfDegree n //
        fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
          fullProjectivePrincipalSubgroup25Two_le_degree_ker n E = c} =
      CurveZetaClassNumber.linearSystemCard 2 (fullClassSectionRank25Two c.1) := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective fullProjectivePrincipalSubgroup25Two c
  have hD : fullClosedPointGrading25Two.divisorDegree D = n := hc
  have hsub : ∀ E : fullClosedPointGrading25Two.EffDivOfDegree n,
      (fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
          fullProjectivePrincipalSubgroup25Two_le_degree_ker n E = ⟨_, hc⟩) ↔
      ((fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
          fullProjectivePrincipalSubgroup25Two_le_degree_ker n E).1 =
        fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D) :=
    fun E => Subtype.ext_iff
  rw [Nat.card_congr (Equiv.subtypeEquivRight hsub),
    Nat.card_congr (effectiveFiberEquiv n D hD), fullEffectiveClassFiber25Two_card,
    linearSystemCard_two]
  rfl

/-- **Class number from Riemann--Roch.**  If a degree-six class `K` satisfies
the genus-four Riemann--Roch identity `ℓ(c) = ℓ(K - c) + 1` on all degree-four
classes, then the degree-zero Picard group of the actual N25 curve over `F₂`
has exactly `71` elements. -/
theorem picDegreeZero_card_eq_seventy_one_of_rr
    (K : fullClosedPointGrading25Two.DivisorClass fullProjectivePrincipalSubgroup25Two)
    (hK : fullProjectiveClassDegree25Two K = 6)
    (hRR : ∀ c : fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker 4,
      fullClassSectionRank25Two c.1 = fullClassSectionRank25Two (K - c.1) + 1) :
    Fintype.card (fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker 0) = 71 := by
  classical
  letI : Fintype (fullClosedPointGrading25Two.PicDegree fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker 4) :=
    Fintype.ofEquiv _
      (fullClosedPointGrading25Two.picDegreeEquivZero fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker boundaryXClass25Two
        boundaryXClass25Two_degree 4).symm
  exact picardZero_card_eq_seventy_one_of_two_full_closed_points_and_middle_rr
    (fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker 4)
    (fullClosedPointGrading25Two.effectiveClass fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker 2)
    (fullClosedPointGrading25Two.residualDegreeFourTwo fullProjectivePrincipalSubgroup25Two
      fullProjectivePrincipalSubgroup25Two_le_degree_ker K hK)
    (fun c => fullClassSectionRank25Two c.1) (fun c => fullClassSectionRank25Two c.1)
    (effectiveClass_fiber_card 4) (effectiveClass_fiber_card 2) hRR
    (Fintype.card_congr
      (fullClosedPointGrading25Two.picDegreeEquivZero fullProjectivePrincipalSubgroup25Two
        fullProjectivePrincipalSubgroup25Two_le_degree_ker boundaryXClass25Two
        boundaryXClass25Two_degree 4))

end MazurProof.N25F_ClassNumberFromRR
