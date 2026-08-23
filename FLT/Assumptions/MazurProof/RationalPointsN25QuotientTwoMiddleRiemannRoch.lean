import FLT.Assumptions.MazurProof.CurveZetaEulerRecurrence
import FLT.Assumptions.MazurProof.CurveZetaMiddleRiemannRoch
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoFullClosedPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoCanonicalDivisor

/-!
# The characteristic-two middle Riemann--Roch class-number route

The structural Frobenius bridge turns the semantic point counts
`5,5,20,29` into the first four ghost coefficients of an honest closed-point
grading.  The marked-divisor Euler recurrence then gives

`A_2 = 15`, `A_4 = 101`.

For the genus-four binary fibre, summed Riemann--Roch in degree four gives

`A_4 = 2 A_2 + #Pic^0`.

Consequently `#Pic^0 = 101 - 30 = 71`.  The remaining inputs of the final
theorem are precisely divisor classes, complete-linear-system fibres, the
residual equivalence, and the Riemann--Roch rank identity.
-/

namespace MazurProof.RationalPointsN25QuotientMiddleRiemannRoch

open CurveZetaEulerRecurrence
open CurveZetaMiddleRiemannRoch
open CurveZetaPointOrbitClassification
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoCanonicalDivisor
open scoped LinearAlgebra.Projectivization

namespace ClosedPointBridge25TwoLE4

variable {C : CurveZetaEffectiveDivisors.ClosedPointGrading}

/-- The degree-one intrinsic ghost count is the semantic binary prime-field
point count. -/
theorem ghostCount_one (B : ClosedPointBridge25TwoLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 1 =
      extensionPointCount25Two 1 := by
  simpa [ExtensionIndex25Two.exponent, ExtensionIndex25Two.pointType,
    extensionPointCount25Two] using
      (B.pointNatCard_eq_ghostCount ExtensionIndex25Two.degreeOne).symm

/-- The degree-two intrinsic ghost count is the semantic quadratic-extension
point count. -/
theorem ghostCount_two (B : ClosedPointBridge25TwoLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 2 =
      extensionPointCount25Two 2 := by
  simpa [ExtensionIndex25Two.exponent, ExtensionIndex25Two.pointType,
    extensionPointCount25Two] using
      (B.pointNatCard_eq_ghostCount ExtensionIndex25Two.degreeTwo).symm

/-- The degree-three intrinsic ghost count is the semantic cubic-extension
point count. -/
theorem ghostCount_three (B : ClosedPointBridge25TwoLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 3 =
      extensionPointCount25Two 3 := by
  simpa [ExtensionIndex25Two.exponent, ExtensionIndex25Two.pointType,
    extensionPointCount25Two] using
      (B.pointNatCard_eq_ghostCount ExtensionIndex25Two.degreeThree).symm

/-- The degree-four intrinsic ghost count is the semantic quartic-extension
point count. -/
theorem ghostCount_four (B : ClosedPointBridge25TwoLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 4 =
      extensionPointCount25Two 4 := by
  simpa [ExtensionIndex25Two.exponent, ExtensionIndex25Two.pointType,
    extensionPointCount25Two] using
      (B.pointNatCard_eq_ghostCount ExtensionIndex25Two.degreeFour).symm

end ClosedPointBridge25TwoLE4

/-- The characteristic-two class-number calculation from an arbitrary
closed-point bridge through degree four and the middle-degree geometric
Riemann--Roch data. -/
theorem picardZero_card_eq_seventy_one_of_two_closed_points_and_middle_rr
    (C : CurveZetaEffectiveDivisors.ClosedPointGrading)
    (B : ClosedPointBridge25TwoLE4 C)
    {PicZero PicFour PicTwo : Type*}
    [Fintype PicZero] [Fintype PicFour]
    (classFour : C.EffDivOfDegree 4 → PicFour)
    (classTwo : C.EffDivOfDegree 2 → PicTwo)
    (residual : PicFour ≃ PicTwo)
    (rankFour : PicFour → ℕ) (rankTwo : PicTwo → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : C.EffDivOfDegree 4 // classFour D = c} =
        CurveZetaClassNumber.linearSystemCard 2 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : C.EffDivOfDegree 2 // classTwo D = c} =
        CurveZetaClassNumber.linearSystemCard 2 (rankTwo c))
    (hRR : ∀ c, rankFour c = rankTwo (residual c) + 1)
    (hPicard : Fintype.card PicFour = Fintype.card PicZero) :
    Fintype.card PicZero = 71 := by
  letI : ∀ n, Fintype (C.EffDivOfDegree n) :=
    fun n => Fintype.ofFinite (C.EffDivOfDegree n)
  have hEuler :=
    CurveZetaMarkedDivisors.ClosedPointGrading.effectiveCount_satisfiesEulerRecurrence C
  have hN1 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 1 = 5 :=
    B.ghostCount_one.trans extensionPointCount25Two_one
  have hN2 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 2 = 5 :=
    B.ghostCount_two.trans extensionPointCount25Two_two
  have hN3 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 3 = 20 :=
    B.ghostCount_three.trans extensionPointCount25Two_three
  have hN4 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 4 = 29 :=
    B.ghostCount_four.trans extensionPointCount25Two_four
  obtain ⟨hA2, hA4⟩ := effective_counts_two_and_four_of_n25_binary_data
    C.effectiveCount
    (CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C)
    hEuler hN1 hN2 hN3 hN4
  have hMiddle := effective_card_middle_degree_picardZero
    classFour classTwo residual rankFour rankTwo 2 hFourFiber hTwoFiber hRR
    hPicard
  have hA2' : Fintype.card (C.EffDivOfDegree 2) = 15 := by
    simpa [CurveZetaEffectiveDivisors.ClosedPointGrading.effectiveCount,
      Nat.card_eq_fintype_card] using hA2
  have hA4' : Fintype.card (C.EffDivOfDegree 4) = 101 := by
    simpa [CurveZetaEffectiveDivisors.ClosedPointGrading.effectiveCount,
      Nat.card_eq_fintype_card] using hA4
  rw [hA2', hA4'] at hMiddle
  omega

/-- The binary N25 class-number conclusion after the new common-field
Frobenius orbit construction has discharged all closed-point classification
inputs through degree four. -/
theorem picardZero_card_eq_seventy_one_of_two_frobenius_and_middle_rr
    {PicZero PicFour PicTwo : Type*}
    [Fintype PicZero] [Fintype PicFour]
    (classFour : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 4 → PicFour)
    (classTwo : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 2 → PicTwo)
    (residual : PicFour ≃ PicTwo)
    (rankFour : PicFour → ℕ) (rankTwo : PicTwo → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 4 //
        classFour D = c} =
          CurveZetaClassNumber.linearSystemCard 2 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 2 //
        classTwo D = c} =
          CurveZetaClassNumber.linearSystemCard 2 (rankTwo c))
    (hRR : ∀ c, rankFour c = rankTwo (residual c) + 1)
    (hPicard : Fintype.card PicFour = Fintype.card PicZero) :
    Fintype.card PicZero = 71 := by
  exact picardZero_card_eq_seventy_one_of_two_closed_points_and_middle_rr
    frobeniusOrbitGrading25TwoLE4 frobeniusClosedPointBridge25TwoLE4
    classFour classTwo residual rankFour rankTwo hFourFiber hTwoFiber hRR
    hPicard

/-- The binary N25 class-number conclusion on the full degreewise
closed-point grading.  Unlike the common degree-twelve carrier, this grading
contains closed points in every residue degree and can therefore support the
eventual global divisor theory. -/
theorem picardZero_card_eq_seventy_one_of_two_full_closed_points_and_middle_rr
    {PicZero PicFour PicTwo : Type*}
    [Fintype PicZero] [Fintype PicFour]
    (classFour : fullClosedPointGrading25Two.EffDivOfDegree 4 → PicFour)
    (classTwo : fullClosedPointGrading25Two.EffDivOfDegree 2 → PicTwo)
    (residual : PicFour ≃ PicTwo)
    (rankFour : PicFour → ℕ) (rankTwo : PicTwo → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : fullClosedPointGrading25Two.EffDivOfDegree 4 //
        classFour D = c} =
          CurveZetaClassNumber.linearSystemCard 2 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : fullClosedPointGrading25Two.EffDivOfDegree 2 //
        classTwo D = c} =
          CurveZetaClassNumber.linearSystemCard 2 (rankTwo c))
    (hRR : ∀ c, rankFour c = rankTwo (residual c) + 1)
    (hPicard : Fintype.card PicFour = Fintype.card PicZero) :
    Fintype.card PicZero = 71 := by
  exact picardZero_card_eq_seventy_one_of_two_closed_points_and_middle_rr
    fullClosedPointGrading25Two fullClosedPointBridge25TwoLE4
    classFour classTwo residual rankFour rankTwo hFourFiber hTwoFiber hRR
    hPicard

/-- The characteristic-two class-number conclusion on the actual divisor
class quotient of the Frobenius closed-point grading.

The principal subgroup, its degree-zero theorem, and the chosen base and
canonical classes are now visible geometric inputs.  In particular, no
arbitrary finite type can be substituted for a Picard degree.  The only
remaining deep hypotheses are the two complete-linear-system fibre formulas
and the genus-four Riemann--Roch rank identity. -/
theorem picardZero_card_eq_seventy_one_of_two_divisorPicard
    (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
    (hPrincipal :
      Principal ≤ frobeniusOrbitGrading25TwoLE4.divisorDegree.ker)
    (base canonical :
      frobeniusOrbitGrading25TwoLE4.DivisorClass Principal)
    (hbase :
      frobeniusOrbitGrading25TwoLE4.classDegree Principal hPrincipal base = 1)
    (hcanonical :
      frobeniusOrbitGrading25TwoLE4.classDegree Principal hPrincipal
        canonical = 6)
    [Fintype
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0)]
    (rankFour :
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 4 → ℕ)
    (rankTwo :
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 2 → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 4 //
        frobeniusOrbitGrading25TwoLE4.effectiveClass
          Principal hPrincipal 4 D = c} =
        CurveZetaClassNumber.linearSystemCard 2 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 2 //
        frobeniusOrbitGrading25TwoLE4.effectiveClass
          Principal hPrincipal 2 D = c} =
        CurveZetaClassNumber.linearSystemCard 2 (rankTwo c))
    (hRR : ∀ c,
      rankFour c = rankTwo
        (frobeniusOrbitGrading25TwoLE4.residualDegreeFourTwo
          Principal hPrincipal canonical hcanonical c) + 1) :
    Fintype.card
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0) = 71 := by
  classical
  letI : Fintype
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 4) :=
    Fintype.ofEquiv
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0)
      (frobeniusOrbitGrading25TwoLE4.picDegreeEquivZero
        Principal hPrincipal base hbase 4).symm
  exact picardZero_card_eq_seventy_one_of_two_frobenius_and_middle_rr
    (PicZero :=
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0)
    (PicFour :=
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 4)
    (PicTwo :=
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 2)
    (frobeniusOrbitGrading25TwoLE4.effectiveClass
      Principal hPrincipal 4)
    (frobeniusOrbitGrading25TwoLE4.effectiveClass
      Principal hPrincipal 2)
    (frobeniusOrbitGrading25TwoLE4.residualDegreeFourTwo
      Principal hPrincipal canonical hcanonical)
    rankFour rankTwo hFourFiber hTwoFiber hRR
    (Fintype.card_congr
      (frobeniusOrbitGrading25TwoLE4.picDegreeEquivZero
        Principal hPrincipal base hbase 4))

/-- The characteristic-two consumer with the degree-one base and degree-six
residual class fixed to the explicit `x=0` hyperplane section.

After this specialization, the remaining concrete geometry is sharply
localized: construct the principal-divisor subgroup, prove finiteness of its
degree-zero quotient, identify complete-linear-system fibres, and prove the
Riemann--Roch rank identity for the displayed hyperplane residual. -/
theorem picardZero_card_eq_seventy_one_of_two_hyperplane_rr
    (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
    (hPrincipal :
      Principal ≤ frobeniusOrbitGrading25TwoLE4.divisorDegree.ker)
    [Fintype
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0)]
    (rankFour :
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 4 → ℕ)
    (rankTwo :
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 2 → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 4 //
        frobeniusOrbitGrading25TwoLE4.effectiveClass
          Principal hPrincipal 4 D = c} =
        CurveZetaClassNumber.linearSystemCard 2 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 2 //
        frobeniusOrbitGrading25TwoLE4.effectiveClass
          Principal hPrincipal 2 D = c} =
        CurveZetaClassNumber.linearSystemCard 2 (rankTwo c))
    (hRR : ∀ c,
      rankFour c = rankTwo
        (frobeniusOrbitGrading25TwoLE4.residualDegreeFourTwo
          Principal hPrincipal
          (hyperplaneSectionClass Principal hPrincipal)
          (hyperplaneSectionClass_degree Principal hPrincipal) c) + 1) :
    Fintype.card
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0) = 71 := by
  exact picardZero_card_eq_seventy_one_of_two_divisorPicard
    Principal hPrincipal
    (basePointClass Principal hPrincipal)
    (hyperplaneSectionClass Principal hPrincipal)
    (basePointClass_degree Principal hPrincipal)
    (hyperplaneSectionClass_degree Principal hPrincipal)
    rankFour rankTwo hFourFiber hTwoFiber hRR

/-- The binary hyperplane consumer with complete linear systems presented as
projectivizations of their section spaces.  The cardinality of each fibre is
therefore a theorem of finite-field linear algebra rather than a separate
geometric hypothesis. -/
theorem picardZero_card_eq_seventy_one_of_two_hyperplane_sections
    (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
    (hPrincipal :
      Principal ≤ frobeniusOrbitGrading25TwoLE4.divisorDegree.ker)
    [Fintype
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0)]
    (SectionsFour :
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 4 → Type*)
    (SectionsTwo :
      frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 2 → Type*)
    [∀ c, AddCommGroup (SectionsFour c)]
    [∀ c, Module (ZMod 2) (SectionsFour c)]
    [∀ c, AddCommGroup (SectionsTwo c)]
    [∀ c, Module (ZMod 2) (SectionsTwo c)]
    (completeFour : ∀ c,
      {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 4 //
        frobeniusOrbitGrading25TwoLE4.effectiveClass
          Principal hPrincipal 4 D = c} ≃ ℙ (ZMod 2) (SectionsFour c))
    (completeTwo : ∀ c,
      {D : frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 2 //
        frobeniusOrbitGrading25TwoLE4.effectiveClass
          Principal hPrincipal 2 D = c} ≃ ℙ (ZMod 2) (SectionsTwo c))
    (hRR : ∀ c,
      Module.finrank (ZMod 2) (SectionsFour c) =
        Module.finrank (ZMod 2)
          (SectionsTwo
            (frobeniusOrbitGrading25TwoLE4.residualDegreeFourTwo
              Principal hPrincipal
              (hyperplaneSectionClass Principal hPrincipal)
              (hyperplaneSectionClass_degree Principal hPrincipal) c)) + 1) :
    Fintype.card
      (frobeniusOrbitGrading25TwoLE4.PicDegree Principal hPrincipal 0) = 71 := by
  apply picardZero_card_eq_seventy_one_of_two_hyperplane_rr
    Principal hPrincipal
    (fun c ↦ Module.finrank (ZMod 2) (SectionsFour c))
    (fun c ↦ Module.finrank (ZMod 2) (SectionsTwo c))
  · intro c
    exact fiber_card_eq_linearSystemCard_of_equiv_projectivization
      _ c (completeFour c) 2 (Module.finrank (ZMod 2) (SectionsFour c))
      (by simp) rfl
  · intro c
    exact fiber_card_eq_linearSystemCard_of_equiv_projectivization
      _ c (completeTwo c) 2 (Module.finrank (ZMod 2) (SectionsTwo c))
      (by simp) rfl
  · exact hRR

end MazurProof.RationalPointsN25QuotientMiddleRiemannRoch
