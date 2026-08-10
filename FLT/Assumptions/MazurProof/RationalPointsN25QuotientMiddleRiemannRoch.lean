import FLT.Assumptions.MazurProof.CurveZetaEulerRecurrence
import FLT.Assumptions.MazurProof.CurveZetaMiddleRiemannRoch
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientFrobeniusOrbits

/-!
# The short N25 class-number route through middle-degree Riemann--Roch

For the characteristic-three genus-four fibre, only effective divisors of
degrees two and four are needed.  The first four semantic extension-field
point counts and the closed-point Euler recurrence give

`A_2 = 15`, `A_4 = 116`.

Summed Riemann--Roch in degree four gives

`A_4 = 3 A_2 + #Pic^0`.

Therefore `#Pic^0 = 116 - 45 = 71`.  Compared with the full formal zeta
consumer, this route asks geometry only for the Euler recurrence through
degree four and the degree-four/degree-two Riemann--Roch pairing.
-/

namespace MazurProof.RationalPointsN25QuotientMiddleRiemannRoch

open CurveZetaClassNumber
open CurveZetaEulerRecurrence
open CurveZetaMiddleRiemannRoch
open CurveZetaPointOrbitClassification
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientWeilThree
open RationalPointsN25QuotientKummerThreeProjective
open RationalPointsN25QuotientSmallThreeSemantic
open RationalPointsN25QuotientZetaThree
open RationalPointsN25QuotientFrobeniusOrbits

namespace ClosedPointBridge25ThreeLE4

variable {C : CurveZetaEffectiveDivisors.ClosedPointGrading}

/-- The degree-one intrinsic ghost coefficient is the semantic ground-field
point count. -/
theorem ghostCount_one (B : ClosedPointBridge25ThreeLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 1 =
      extensionPointCount25Three 1 := by
  simpa [ExtensionIndex25Three.exponent, ExtensionIndex25Three.pointType,
    extensionPointCount25Three] using
      (B.pointNatCard_eq_ghostCount
        ExtensionIndex25Three.degreeOne).symm

/-- The degree-two intrinsic ghost coefficient is the semantic quadratic
extension point count. -/
theorem ghostCount_two (B : ClosedPointBridge25ThreeLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 2 =
      extensionPointCount25Three 2 := by
  simpa [ExtensionIndex25Three.exponent, ExtensionIndex25Three.pointType,
    extensionPointCount25Three] using
      (B.pointNatCard_eq_ghostCount
        ExtensionIndex25Three.degreeTwo).symm

/-- The degree-three intrinsic ghost coefficient is the semantic cubic
extension point count. -/
theorem ghostCount_three (B : ClosedPointBridge25ThreeLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 3 =
      extensionPointCount25Three 3 := by
  simpa [ExtensionIndex25Three.exponent, ExtensionIndex25Three.pointType,
    extensionPointCount25Three] using
      (B.pointNatCard_eq_ghostCount
        ExtensionIndex25Three.degreeThree).symm

/-- The degree-four intrinsic ghost coefficient is the semantic quartic
extension point count. -/
theorem ghostCount_four (B : ClosedPointBridge25ThreeLE4 C) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 4 =
      extensionPointCount25Three 4 := by
  simpa [ExtensionIndex25Three.exponent, ExtensionIndex25Three.pointType,
    extensionPointCount25Three] using
      (B.pointNatCard_eq_ghostCount
        ExtensionIndex25Three.degreeFour).symm

end ClosedPointBridge25ThreeLE4

/-! ## The class-number consumer -/

/-- The short semantic consumer for the characteristic-three N25 fibre.

The fibre hypotheses say that effective divisors in a Picard class form the
appropriate complete linear system.  `hRR` is degree-four Riemann--Roch,
`residual` is `c ↦ K-c`, and `hPicard` translates `Pic^4` to `Pic^0`.
The generic `hEuler` argument makes this consumer reusable with any effective
divisor model.  The concrete closed-point theorem below discharges it by the
marked-divisor double count. -/
theorem picardZero_card_eq_seventy_one_of_middle_rr
    {PicZero PicFour PicTwo : Type*}
    [Fintype PicZero] [Fintype PicFour]
    (Effective : ℕ → Type*) [∀ n, Fintype (Effective n)]
    (classFour : Effective 4 → PicFour)
    (classTwo : Effective 2 → PicTwo)
    (residual : PicFour ≃ PicTwo)
    (rankFour : PicFour → ℕ) (rankTwo : PicTwo → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : Effective 4 // classFour D = c} =
        linearSystemCard 3 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : Effective 2 // classTwo D = c} =
        linearSystemCard 3 (rankTwo c))
    (hRR : ∀ c, rankFour c = rankTwo (residual c) + 1)
    (hPicard : Fintype.card PicFour = Fintype.card PicZero)
    (hEuler : SatisfiesEulerRecurrence
      (fun n => Fintype.card (Effective n)) extensionPointCount25Three) :
    Fintype.card PicZero = 71 := by
  obtain ⟨hA2, hA4⟩ := effective_counts_two_and_four_of_n25_data
    (fun n => Fintype.card (Effective n)) extensionPointCount25Three hEuler
    extensionPointCount25Three_one extensionPointCount25Three_two
    extensionPointCount25Three_three extensionPointCount25Three_four
  have hMiddle := effective_card_middle_degree_picardZero classFour classTwo
    residual rankFour rankTwo 3 hFourFiber hTwoFiber hRR hPicard
  rw [hA2, hA4] at hMiddle
  omega

/-- The N25 class-number calculation with the Euler recurrence discharged by
the marked-divisor theorem.

The remaining geometric inputs are exactly the closed-point classification
of the four semantic extension-point types and the degree-four/degree-two
Picard and Riemann--Roch data. -/
theorem picardZero_card_eq_seventy_one_of_closed_points_and_middle_rr
    (C : CurveZetaEffectiveDivisors.ClosedPointGrading)
    (B : ClosedPointBridge25ThreeLE4 C)
    {PicZero PicFour PicTwo : Type*}
    [Fintype PicZero] [Fintype PicFour]
    (classFour : C.EffDivOfDegree 4 → PicFour)
    (classTwo : C.EffDivOfDegree 2 → PicTwo)
    (residual : PicFour ≃ PicTwo)
    (rankFour : PicFour → ℕ) (rankTwo : PicTwo → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : C.EffDivOfDegree 4 // classFour D = c} =
        linearSystemCard 3 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : C.EffDivOfDegree 2 // classTwo D = c} =
        linearSystemCard 3 (rankTwo c))
    (hRR : ∀ c, rankFour c = rankTwo (residual c) + 1)
    (hPicard : Fintype.card PicFour = Fintype.card PicZero) :
    Fintype.card PicZero = 71 := by
  letI : ∀ n, Fintype (C.EffDivOfDegree n) :=
    fun n => Fintype.ofFinite (C.EffDivOfDegree n)
  have hEuler :=
    CurveZetaMarkedDivisors.ClosedPointGrading.effectiveCount_satisfiesEulerRecurrence C
  have hN1 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 1 = 5 :=
    B.ghostCount_one.trans extensionPointCount25Three_one
  have hN2 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 2 = 5 :=
    B.ghostCount_two.trans extensionPointCount25Three_two
  have hN3 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 3 = 20 :=
    B.ghostCount_three.trans extensionPointCount25Three_three
  have hN4 :
      CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C 4 = 89 :=
    B.ghostCount_four.trans extensionPointCount25Three_four
  obtain ⟨hA2, hA4⟩ := effective_counts_two_and_four_of_n25_data
    C.effectiveCount
    (CurveZetaMarkedDivisors.ClosedPointGrading.ghostCount C)
    hEuler hN1 hN2 hN3 hN4
  have hMiddle := effective_card_middle_degree_picardZero
    classFour classTwo residual rankFour rankTwo 3 hFourFiber hTwoFiber hRR
    hPicard
  have hA2' : Fintype.card (C.EffDivOfDegree 2) = 15 := by
    simpa [CurveZetaEffectiveDivisors.ClosedPointGrading.effectiveCount,
      Nat.card_eq_fintype_card] using hA2
  have hA4' : Fintype.card (C.EffDivOfDegree 4) = 116 := by
    simpa [CurveZetaEffectiveDivisors.ClosedPointGrading.effectiveCount,
      Nat.card_eq_fintype_card] using hA4
  rw [hA2', hA4'] at hMiddle
  omega

/-- The characteristic-three N25 class-number calculation after Frobenius
orbit geometry has been discharged.

Arithmetic Frobenius on the canonical curve over `𝔽_(3^12)` supplies the
closed-point grading and classifies the semantic points over the first four
extensions.  Consequently the only remaining inputs are the actual
degree-two and degree-four Picard classes, their complete-linear-system
fibres, and genus-four Riemann--Roch. -/
theorem picardZero_card_eq_seventy_one_of_frobenius_and_middle_rr
    {PicZero PicFour PicTwo : Type*}
    [Fintype PicZero] [Fintype PicFour]
    (classFour : frobeniusOrbitGrading25ThreeLE4.EffDivOfDegree 4 → PicFour)
    (classTwo : frobeniusOrbitGrading25ThreeLE4.EffDivOfDegree 2 → PicTwo)
    (residual : PicFour ≃ PicTwo)
    (rankFour : PicFour → ℕ) (rankTwo : PicTwo → ℕ)
    (hFourFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25ThreeLE4.EffDivOfDegree 4 //
        classFour D = c} = linearSystemCard 3 (rankFour c))
    (hTwoFiber : ∀ c,
      Nat.card {D : frobeniusOrbitGrading25ThreeLE4.EffDivOfDegree 2 //
        classTwo D = c} = linearSystemCard 3 (rankTwo c))
    (hRR : ∀ c, rankFour c = rankTwo (residual c) + 1)
    (hPicard : Fintype.card PicFour = Fintype.card PicZero) :
    Fintype.card PicZero = 71 := by
  exact picardZero_card_eq_seventy_one_of_closed_points_and_middle_rr
    frobeniusOrbitGrading25ThreeLE4
    frobeniusClosedPointBridge25ThreeLE4 classFour classTwo residual
    rankFour rankTwo hFourFiber hTwoFiber hRR hPicard

end MazurProof.RationalPointsN25QuotientMiddleRiemannRoch
