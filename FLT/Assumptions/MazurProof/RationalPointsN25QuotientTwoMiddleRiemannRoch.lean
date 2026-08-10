import FLT.Assumptions.MazurProof.CurveZetaEulerRecurrence
import FLT.Assumptions.MazurProof.CurveZetaMiddleRiemannRoch
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoFrobeniusOrbits

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

end MazurProof.RationalPointsN25QuotientMiddleRiemannRoch
