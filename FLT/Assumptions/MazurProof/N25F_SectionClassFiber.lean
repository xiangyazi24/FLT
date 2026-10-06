import FLT.Assumptions.MazurProof.N25F_SectionFiniteness
import FLT.Assumptions.MazurProof.N25F_FullPicardDegree
import Mathlib.FieldTheory.Finiteness
import Mathlib.SetTheory.Cardinal.NatCard

/-! Exact fibres of the full effective-divisor class map, using actual
nonzero bounded-pole functions over F2. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_SectionClassFiber
open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_RiemannRochSpace N25F_SectionFiniteness N25F_FullPicardDegree
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- Effective full divisors whose class is the class of the actual signed divisor D. -/
abbrev FullEffectiveClassFiber25Two (D : ProjectiveDivisor25Two) :=
  {E : fullClosedPointGrading25Two.EffDivOfDegree
      (fullClosedPointGrading25Two.divisorDegree D).toNat //
    fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two
      (fullClosedPointGrading25Two.effectiveToDivisor E.1) =
    fullClosedPointGrading25Two.classOf fullProjectivePrincipalSubgroup25Two D}

/-- The actual section-to-divisor map lands in the correct full Picard fibre. -/
def nonzeroSectionToFullClassFiber25Two (D : ProjectiveDivisor25Two)
    (f : NonzeroSection25Two D) : FullEffectiveClassFiber25Two D := by
  refine ⟨effectiveDivisorOfNonzeroSection25Two D f, ?_⟩
  rw [fullProjectiveClassOf_eq_iff_exists_principal]
  have hf : (f.1 : CurveField) ≠ 0 := fun h => f.2 (Subtype.ext h)
  refine ⟨Additive.ofMul (Units.mk0 (f.1 : CurveField) hf), ?_⟩
  rw [effectiveDivisorOfNonzeroSection25Two_cast]
  simp only [add_sub_cancel_left]

theorem nonzeroSectionToFullClassFiber25Two_injective (D : ProjectiveDivisor25Two) :
    Function.Injective (nonzeroSectionToFullClassFiber25Two D) := by
  intro f g h
  exact effectiveDivisorOfNonzeroSection25Two_injective D (congrArg Subtype.val h)

/-- A genuine principal representative of a class equality produces a section. -/
theorem nonzeroSectionToFullClassFiber25Two_surjective (D : ProjectiveDivisor25Two) :
    Function.Surjective (nonzeroSectionToFullClassFiber25Two D) := by
  intro E
  obtain ⟨f, hfdiv⟩ := (fullProjectiveClassOf_eq_iff_exists_principal _ _).mp E.2
  have hrepr : D + projectivePrincipalDivisor f =
      fullClosedPointGrading25Two.effectiveToDivisor E.1.1 :=
    (add_comm D _).trans (eq_sub_iff_add_eq.mp hfdiv)
  have hf : (f.toMul : CurveField) ≠ 0 := Units.ne_zero f.toMul
  have hunit : Additive.ofMul (Units.mk0 (f.toMul : CurveField) hf) = f := by
    change Units.mk0 (f.toMul : CurveField) hf = f.toMul
    exact Units.ext rfl
  have hmem : (f.toMul : CurveField) ∈ fullRiemannRochSpace25Two D := by
    refine Or.inr ⟨hf, ?_⟩
    intro A
    rw [hunit]
    change 0 ≤ (D + projectivePrincipalDivisor f) A
    rw [hrepr]
    exact Int.natCast_nonneg _
  let g : NonzeroSection25Two D :=
    ⟨⟨(f.toMul : CurveField), hmem⟩, fun h => hf (congrArg Subtype.val h)⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he : fullClosedPointGrading25Two.effectiveToDivisor
      (effectiveDivisorOfNonzeroSection25Two D g).1 =
      fullClosedPointGrading25Two.effectiveToDivisor E.1.1 := by
    rw [effectiveDivisorOfNonzeroSection25Two_cast]
    change D + projectivePrincipalDivisor (Additive.ofMul (Units.mk0 (f.toMul : CurveField) hf)) = _
    rw [hunit, hrepr]
  ext A
  exact Int.ofNat_inj.mp (congrArg (fun H => H A) he)

/-- Over F2 the actual nonzero sections are exactly the effective class fibre. -/
def nonzeroSectionEquivFullClassFiber25Two (D : ProjectiveDivisor25Two) :
    NonzeroSection25Two D ≃ FullEffectiveClassFiber25Two D :=
  Equiv.ofBijective (nonzeroSectionToFullClassFiber25Two D)
    ⟨nonzeroSectionToFullClassFiber25Two_injective D,
      nonzeroSectionToFullClassFiber25Two_surjective D⟩

theorem fullRiemannRochSpace25Two_card (D : ProjectiveDivisor25Two) :
    Nat.card (fullRiemannRochSpace25Two D) =
      2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) := by
  simpa only [Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fullRiemannRochSpace25Two D))

theorem nonzeroSection25Two_card (D : ProjectiveDivisor25Two) :
    Nat.card (NonzeroSection25Two D) =
      2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) - 1 := by
  classical
  have h := Nat.card_congr (Equiv.optionSubtypeNe (0 : fullRiemannRochSpace25Two D))
  rw [Finite.card_option, fullRiemannRochSpace25Two_card] at h
  change Nat.card (NonzeroSection25Two D) + 1 =
    2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) at h
  exact Nat.eq_sub_of_add_eq h

/-- The exact finite class-fibre cardinality, with the genuine section-space rank. -/
theorem fullEffectiveClassFiber25Two_card (D : ProjectiveDivisor25Two) :
    Nat.card (FullEffectiveClassFiber25Two D) =
      2 ^ Module.finrank (ZMod 2) (fullRiemannRochSpace25Two D) - 1 := by
  rw [← Nat.card_congr (nonzeroSectionEquivFullClassFiber25Two D), nonzeroSection25Two_card]

end MazurProof.N25F_SectionClassFiber
