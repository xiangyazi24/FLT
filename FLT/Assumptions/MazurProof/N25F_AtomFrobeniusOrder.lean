import FLT.Assumptions.MazurProof.N25F_FrobeniusDVROrder
import FLT.Assumptions.MazurProof.N25F_ProjectivePrincipalAddition
import FLT.Assumptions.MazurProof.N25F_InfinityResidueFields
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Orders of `f ^ 8 - f` at the closed points of the N25 curve

For a nonzero function `f` on the genus-four N25 quotient curve over `F₂` and a
closed point `A` of the full projective grading, write `ord_A` for the actual
coefficient of the projective principal divisor.  With `g = f ^ 8 - f ≠ 0`:

* at a pole of `f`, `ord_A g = 8 · ord_A f`;
* where `f` is regular, `g` is regular;
* where `f` is regular and `deg A ∣ 3`, `g` vanishes, since the residue field
  has `2` or `8` elements and so satisfies `x ^ 8 = x`.

Each statement is the corresponding local fact of `N25F_FrobeniusDVROrder`
applied in the genuine local ring of `A`: the three boundary local rings with
their binary residue fields, or the localisation of the affine W-chart at the
height-one prime of a nonboundary atom.
-/

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_AtomFrobeniusOrder
open N25F_FrobeniusDVROrder
open N25F_ProjectiveDivisorSplit N25F_ProjectivePrincipalDivisor
open N25F_ProjectivePrincipalCoefficients N25F_PrincipalOrderAddition
open N25F_NonBoundaryPrincipalDivisor
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal
open N25F_XLocalFractionEmbedding N25F_XBoundaryOrder
open N25F_YZLocalFractionEmbedding N25F_YZBoundaryOrder N25F_ZBoundaryOrder
open N25F_InfinityResidueFields
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W

/-- The three Frobenius facts in one DVR, with the vanishing statement gated by
a proposition `P` that supplies the residue identity `x ^ 8 = x`. -/
private theorem frobenius_local {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Algebra R CurveField] [IsFractionRing R CurveField]
    (P : Prop) (hres : P → ∀ x : IsLocalRing.ResidueField R, x ^ 8 = x)
    (f g : CurveField) (hf : f ≠ 0) (hg0 : g ≠ 0) (hg : g = f ^ 8 - f) :
    (WithZero.log (Ring.ordFrac R f) < 0 →
        WithZero.log (Ring.ordFrac R g) = 8 * WithZero.log (Ring.ordFrac R f)) ∧
      (0 ≤ WithZero.log (Ring.ordFrac R f) → 0 ≤ WithZero.log (Ring.ordFrac R g)) ∧
      (P → 0 ≤ WithZero.log (Ring.ordFrac R f) → 0 < WithZero.log (Ring.ordFrac R g)) := by
  subst hg
  refine ⟨fun h => ?_, fun h => log_ordFrac_pow_sub_self_nonneg 8 f hf h hg0,
    fun hP h => log_ordFrac_pow_sub_self_pos 8 f hf h hg0 (hres hP)⟩
  simpa using log_ordFrac_pow_sub_self_of_neg (R := R) 8 (by norm_num) f hf h hg0

/-- A binary residue field satisfies `x ^ 8 = x`. -/
private theorem pow_eight_of_equiv_zmod_two {F : Type*} [CommRing F] (e : F ≃+* ZMod 2)
    (x : F) : x ^ 8 = x := by
  apply e.injective
  rw [map_pow]
  exact pow_eight_eq_self_of_card 1 (by simp) (one_dvd 3) (e x)

/-- A finite field with `2 ^ d` elements, `d ∣ 3`, satisfies `x ^ 8 = x`. -/
private theorem pow_eight_of_natCard {F : Type*} [Field F] (d : ℕ) (hcard : Nat.card F = 2 ^ d)
    (hd : d ∣ 3) (x : F) : x ^ 8 = x := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype F := Fintype.ofFinite F
  exact pow_eight_eq_self_of_card d (by rw [← Nat.card_eq_fintype_card, hcard]) hd x

/-- The local Frobenius facts at every closed point of the full grading. -/
theorem projectivePrincipalDivisor_frobenius
    (f g : Additive CurveFieldˣ)
    (hg : (g.toMul : CurveField) = (f.toMul : CurveField) ^ 8 - (f.toMul : CurveField))
    (A : fullClosedPointGrading25Two.Atom) :
    (projectivePrincipalDivisor f A < 0 →
        projectivePrincipalDivisor g A = 8 * projectivePrincipalDivisor f A) ∧
      (0 ≤ projectivePrincipalDivisor f A → 0 ≤ projectivePrincipalDivisor g A) ∧
      (fullClosedPointGrading25Two.atomDegree A ∣ 3 →
        0 ≤ projectivePrincipalDivisor f A → 0 < projectivePrincipalDivisor g A) := by
  obtain ⟨s, rfl⟩ := boundaryNonBoundaryToFullAtom_surjective A
  cases s with
  | inl t =>
      cases t with
      | X =>
          simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_X]
          letI : Algebra XLocalRing CurveField := xLocalToFraction.toRingHom.toAlgebra
          letI : IsFractionRing XLocalRing CurveField := xLocalToFraction_isFractionRing
          exact frobenius_local (R := XLocalRing) _
            (fun _ => pow_eight_of_equiv_zmod_two xLocalResidueRingEquivF2)
            _ _ f.toMul.ne_zero g.toMul.ne_zero hg
      | YZ =>
          simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_YZ]
          letI : Algebra YZLocalRing CurveField := yzLocalToFraction.toRingHom.toAlgebra
          letI : IsFractionRing YZLocalRing CurveField := yzLocalToFraction_isFractionRing
          exact frobenius_local (R := YZLocalRing) _
            (fun _ => pow_eight_of_equiv_zmod_two yzLocalResidueRingEquivF2)
            _ _ f.toMul.ne_zero g.toMul.ne_zero hg
      | Z =>
          simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_Z]
          letI : Algebra ZLocalRing CurveField := zLocalToFraction.toRingHom.toAlgebra
          letI : IsFractionRing ZLocalRing CurveField := zLocalToFraction_isFractionRing
          exact frobenius_local (R := ZLocalRing) _
            (fun _ => pow_eight_of_equiv_zmod_two zLocalResidueRingEquivF2)
            _ _ f.toMul.ne_zero g.toMul.ne_zero hg
  | inr B =>
      simp only [boundaryNonBoundaryToFullAtom, projectivePrincipalDivisor_apply_nonBoundary,
        nonBoundaryPrincipalDivisor_apply]
      let v := fullNonBoundaryAtomEquivHeightOne B
      letI : IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ v.ne_bot
          (Localization.AtPrime v.asIdeal)
      change (FractionalIdeal.count CurveField v
          (FractionalIdeal.spanSingleton W⁰ (f.toMul : CurveField)) < 0 → _) ∧ _
      change _ ∧ _ ∧ _
      have hcf := count_spanSingleton_eq_log_ordFrac v (f.toMul : CurveField) f.toMul.ne_zero
      have hcg := count_spanSingleton_eq_log_ordFrac v (g.toMul : CurveField) g.toMul.ne_zero
      change (FractionalIdeal.count CurveField v
          (FractionalIdeal.spanSingleton W⁰ (f.toMul : CurveField)) < 0 →
            FractionalIdeal.count CurveField v
              (FractionalIdeal.spanSingleton W⁰ (g.toMul : CurveField)) =
            8 * FractionalIdeal.count CurveField v
              (FractionalIdeal.spanSingleton W⁰ (f.toMul : CurveField))) ∧
        (0 ≤ FractionalIdeal.count CurveField v
          (FractionalIdeal.spanSingleton W⁰ (f.toMul : CurveField)) →
            0 ≤ FractionalIdeal.count CurveField v
              (FractionalIdeal.spanSingleton W⁰ (g.toMul : CurveField))) ∧
        (fullClosedPointGrading25Two.atomDegree B.1 ∣ 3 →
          0 ≤ FractionalIdeal.count CurveField v
            (FractionalIdeal.spanSingleton W⁰ (f.toMul : CurveField)) →
          0 < FractionalIdeal.count CurveField v
            (FractionalIdeal.spanSingleton W⁰ (g.toMul : CurveField)))
      rw [hcf, hcg]
      have hvB : v.asIdeal = fullNonBoundaryPrimeIdeal B := rfl
      have hres : fullClosedPointGrading25Two.atomDegree B.1 ∣ 3 →
          ∀ x : IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal), x ^ 8 = x := by
        intro hd x
        have hmax : v.asIdeal.IsMaximal := IsDedekindDomain.HeightOneSpectrum.isMaximal v
        have hcard : Nat.card (IsLocalRing.ResidueField (Localization.AtPrime v.asIdeal)) =
            2 ^ fullClosedPointGrading25Two.atomDegree B.1 := by
          rw [← fullNonBoundaryPrimeIdeal_residue_card B]
          exact (Nat.card_congr (Equiv.ofBijective _
            (Ideal.bijective_algebraMap_quotient_residueField v.asIdeal))).symm
        exact pow_eight_of_natCard _ hcard hd x
      exact frobenius_local (R := Localization.AtPrime v.asIdeal) _ hres
        _ _ f.toMul.ne_zero g.toMul.ne_zero hg

end MazurProof.N25F_AtomFrobeniusOrder
