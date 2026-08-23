import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoHyperplaneArtinKernel
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPolynomial.Ideal
import FLT.Assumptions.MazurProof.CurveLocalIntersectionLength

/-!
# Principal-open presentations of the binary hyperplane-section Artin factors

The affine kernel calculations identify the double and triple normal forms
before localization.  This file performs the remaining scheme-local step.
It maps the actual chart equations into the principal opens isolating the two
nonreduced points, proves the localized equation ideals equal the corresponding
normal ideals, and uses the general theorem that localization commutes with
kernels to identify both ideals as exact kernels of the Artin evaluations.

Thus the principal-open quotient rings themselves, rather than merely their
closed points or vector-space dimensions, have the required length-two and
length-three Artin presentations.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin

open RationalPointsN25QuotientF2

/-- A ring equivalence between rings of characteristic `n` is linear over
`ZMod n`; additive maps commute with the canonical `ZMod` scalar action. -/
private def zmodLinearEquivOfRingEquiv
    {n : ℕ} {A B : Type*} [Ring A] [Ring B]
    [Module (ZMod n) A] [Module (ZMod n) B]
    (e : A ≃+* B) : A ≃ₗ[ZMod n] B :=
  { e.toAddEquiv with
    map_smul' := fun c x ↦ ZMod.map_smul e.toAddEquiv c x }

/-! ## Exact kernels after inverting one element -/

/-- Extending a ring map across a principal open set localizes its kernel,
provided the chosen denominator already maps to a unit.  This packages the
general Mathlib theorem that localization commutes with kernels in the exact
form needed by the two Artin evaluations below. -/
theorem awayLift_ker
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (hr : IsUnit (f r)) :
    RingHom.ker (Localization.awayLift f r hr) =
      Ideal.map (algebraMap R (Localization.Away r)) (RingHom.ker f) := by
  letI : IsLocalization.Away (f r) S :=
    IsLocalization.away_of_isUnit_of_bijective S hr Function.bijective_id
  rw [show Localization.awayLift f r hr =
      IsLocalization.Away.map (Localization.Away r) S f r from
    IsLocalization.ringHom_ext (.powers r) (by
      ext x
      simp [IsLocalization.Away.map])]
  exact IsLocalization.ker_map S f (Submonoid.map_powers f r)

/-- The local equation ideal on `D(y+z+1)` is the doubled triangular ideal. -/
theorem wLocalized_intersectionIdeal_eq_normalForm :
    Ideal.span
        {(algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
              (MvPolynomial.X 0)) ^ 2 +
            algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                (MvPolynomial.X 0) *
              algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                (MvPolynomial.X 1) +
            algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
              (MvPolynomial.X 1),
          algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
              (MvPolynomial.X 1) *
            (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                  (MvPolynomial.X 0) +
                algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
                  (MvPolynomial.X 1) + 1)} =
      Ideal.span
        {(algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
            (MvPolynomial.X 0)) ^ 2,
          algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
            (MvPolynomial.X 1)} := by
  exact wChart_intersectionIdeal_eq_normalForm
      (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
        (MvPolynomial.X 0))
      (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator)
        (MvPolynomial.X 1))
      (by
        let f := algebraMap BinaryAffinePlane
          (Localization.Away wChartDenominator)
        change IsUnit (f (MvPolynomial.X 0) + f (MvPolynomial.X 1) + 1)
        rw [← map_one f, ← map_add, ← map_add]
        exact IsLocalization.Away.algebraMap_isUnit wChartDenominator)

/-- The local equation ideal on `D(1+b)` is the tripled triangular ideal. -/
theorem yzLocalized_intersectionIdeal_eq_normalForm :
    Ideal.span
        {algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 0) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 1) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 0) *
              algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 1),
          (1 + algebraMap BinaryAffinePlane
                (Localization.Away yzChartDenominator) (MvPolynomial.X 0)) *
              algebraMap BinaryAffinePlane
                (Localization.Away yzChartDenominator) (MvPolynomial.X 1) *
            (algebraMap BinaryAffinePlane
                  (Localization.Away yzChartDenominator) (MvPolynomial.X 0) +
              algebraMap BinaryAffinePlane
                (Localization.Away yzChartDenominator) (MvPolynomial.X 1))} =
      Ideal.span
        {algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 0) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
              (MvPolynomial.X 1) +
            algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 0) *
              algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
                (MvPolynomial.X 1),
          (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
            (MvPolynomial.X 1)) ^ 3} := by
  exact yzChart_intersectionIdeal_eq_normalForm
      (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
        (MvPolynomial.X 0))
      (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator)
        (MvPolynomial.X 1))
      (by
        have htwoCoeff : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
        have htwoSource : (2 : BinaryAffinePlane) = 0 := by
          change MvPolynomial.C (2 : ZMod 2) = 0
          rw [htwoCoeff, map_zero]
        simpa only [map_ofNat, map_zero] using congrArg
          (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
          htwoSource)
      (by
        let f := algebraMap BinaryAffinePlane
          (Localization.Away yzChartDenominator)
        change IsUnit (1 + f (MvPolynomial.X 1))
        rw [← map_one f, ← map_add]
        exact IsLocalization.Away.algebraMap_isUnit yzChartDenominator)

/-! ## Exact local Artin presentations -/

/-- Mapping the two chart equations into `D(y+z+1)` gives exactly the mapped
double-point normal ideal. -/
theorem wLocalized_chartIdeal_eq_normalIdeal :
    Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial}) =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        doubleNormalIdeal := by
  simpa [wChartQuadricPolynomial, wChartCubicPolynomial, doubleNormalIdeal,
    Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using
    wLocalized_intersectionIdeal_eq_normalForm

/-- Mapping the translated chart equations into `D(1+b)` gives exactly the
mapped triple-point normal ideal. -/
theorem yzLocalized_chartIdeal_eq_normalIdeal :
    Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial}) =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        tripleNormalIdeal := by
  simpa [yzChartQuadricPolynomial, yzChartCubicPolynomial, tripleNormalIdeal,
    Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using
    yzLocalized_intersectionIdeal_eq_normalForm

/-- The kernel of the doubled evaluation on the principal open set is the
extension of the doubled normal ideal. -/
theorem doubleLocalizedEvaluation_ker :
    RingHom.ker doubleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        doubleNormalIdeal := by
  rw [doubleLocalizedEvaluation, awayLift_ker, doubleEvaluation_ker]

/-- The kernel of the tripled evaluation on the principal open set is the
extension of the tripled normal ideal. -/
theorem tripleLocalizedEvaluation_ker :
    RingHom.ker tripleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        tripleNormalIdeal := by
  rw [tripleLocalizedEvaluation, awayLift_ker, tripleEvaluation_ker]

/-- On `D(y+z+1)`, the actual chart equations cut out precisely the kernel of
the evaluation to `F₂[t]/(t²)`. -/
theorem doubleLocalizedEvaluation_ker_eq_chartIdeal :
    RingHom.ker doubleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial}) := by
  rw [doubleLocalizedEvaluation_ker, wLocalized_chartIdeal_eq_normalIdeal]

/-- On `D(1+b)`, the actual translated chart equations cut out precisely the
kernel of the evaluation to `F₂[t]/(t³)`. -/
theorem tripleLocalizedEvaluation_ker_eq_chartIdeal :
    RingHom.ker tripleLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial}) := by
  rw [tripleLocalizedEvaluation_ker, yzLocalized_chartIdeal_eq_normalIdeal]

/-! ## Quotient-ring presentations -/

/-- The localized doubled evaluation remains surjective because every target
element already has a preimage before the denominator is inverted. -/
theorem doubleLocalizedEvaluation_surjective :
    Function.Surjective doubleLocalizedEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := doubleEvaluation_surjective x
  refine ⟨algebraMap BinaryAffinePlane
    (Localization.Away wChartDenominator) p, ?_⟩
  exact IsLocalization.Away.lift_eq
    wChartDenominator doubleEvaluation_denominator_isUnit p

/-- The localized tripled evaluation remains surjective for the same
structural reason. -/
theorem tripleLocalizedEvaluation_surjective :
    Function.Surjective tripleLocalizedEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := tripleEvaluation_surjective x
  refine ⟨algebraMap BinaryAffinePlane
    (Localization.Away yzChartDenominator) p, ?_⟩
  exact IsLocalization.Away.lift_eq
    yzChartDenominator tripleEvaluation_denominator_isUnit p

/-- The actual local equation quotient on `D(y+z+1)` is the doubled Artin
ring `F₂[t]/(t²)`.  This is the first isomorphism theorem applied to the
exact localized kernel calculation above. -/
noncomputable def doubleLocalizedChartQuotientEquiv :
    (Localization.Away wChartDenominator ⧸
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
        (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial})) ≃+*
      DoubleArtin :=
  (Ideal.quotEquivOfEq doubleLocalizedEvaluation_ker_eq_chartIdeal.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      doubleLocalizedEvaluation_surjective)

/-- The actual local equation quotient on `D(1+b)` is the tripled Artin ring
`F₂[t]/(t³)`. -/
noncomputable def tripleLocalizedChartQuotientEquiv :
    (Localization.Away yzChartDenominator ⧸
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
        (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial})) ≃+*
      TripleArtin :=
  (Ideal.quotEquivOfEq tripleLocalizedEvaluation_ker_eq_chartIdeal.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      tripleLocalizedEvaluation_surjective)

/-! ## The reduced point on the `z=1` chart -/

/-- On the `z=1` chart of `x=0`, the quadric is `y²+y+w`. -/
theorem zChart_quadric
    {K : Type*} [CommRing K] (y w : K) :
    canonicalQuadric25Over (⟨0, y, 1, w⟩ : Coordinates4 K) = y ^ 2 + y + w := by
  dsimp [canonicalQuadric25Over]
  ring

/-- In characteristic two, the cubic on the same chart is
`w*(y+w+1)`. -/
theorem zChart_cubic
    {K : Type*} [CommRing K] [CharP K 2] (y w : K) :
    canonicalCubic25Over (⟨0, y, 1, w⟩ : Coordinates4 K) =
      w * (y + w + 1) := by
  rw [cubic_x_zero_factor]
  ring

/-- After isolating the origin by inverting `y+w+1` and `y+1`, the two
chart equations generate the reduced maximal ideal `(y,w)`. -/
theorem zChart_intersectionIdeal_eq_normalForm
    {R : Type*} [CommRing R] (y w : R)
    (hu : IsUnit (y + w + 1)) (hv : IsUnit (y + 1)) :
    Ideal.span {y ^ 2 + y + w, w * (y + w + 1)} =
      Ideal.span {y, w} := by
  let uInv : R := ↑hu.unit⁻¹
  let vInv : R := ↑hv.unit⁻¹
  have hU : uInv * (y + w + 1) = 1 := hu.val_inv_mul
  have hV : vInv * (y + 1) = 1 := hv.val_inv_mul
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨y + 1, 1, by ring⟩
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨0, y + w + 1, by ring⟩
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨vInv, -(vInv * uInv), by
        calc
          vInv * (y ^ 2 + y + w) + -(vInv * uInv) * (w * (y + w + 1)) =
              vInv * (y * (y + 1)) + vInv * w *
                (1 - uInv * (y + w + 1)) := by ring
          _ = y * (vInv * (y + 1)) := by rw [hU]; ring
          _ = y := by rw [hV, mul_one]⟩
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨0, uInv, by
        calc
          0 * (y ^ 2 + y + w) + uInv * (w * (y + w + 1)) =
              w * (uInv * (y + w + 1)) := by ring
          _ = w := by rw [hU, mul_one]⟩

/-- The quadric equation on the reduced `z=1` chart. -/
noncomputable def zChartQuadricPolynomial : BinaryAffinePlane :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 + MvPolynomial.X 1

/-- The cubic equation on the reduced `z=1` chart. -/
noncomputable def zChartCubicPolynomial : BinaryAffinePlane :=
  MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1 + 1)

/-- A principal-open denominator isolating `(y,w)=(0,0)` and making both
linear factors used in the normal-form calculation invertible. -/
noncomputable def zChartDenominator : BinaryAffinePlane :=
  (MvPolynomial.X 0 + MvPolynomial.X 1 + 1) * (MvPolynomial.X 0 + 1)

/-- Evaluation at the reduced point `(y,w)=(0,0)`. -/
noncomputable def zReducedEvaluation : BinaryAffinePlane →ₐ[ZMod 2] ZMod 2 :=
  MvPolynomial.aeval ![0, 0]

/-- The maximal ideal of the reduced origin. -/
def zReducedNormalIdeal : Ideal BinaryAffinePlane :=
  Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}

/-- For two variables, the displayed maximal ideal is the ideal generated by
all variables. -/
theorem zReducedNormalIdeal_eq_idealOfVars :
    zReducedNormalIdeal = MvPolynomial.idealOfVars (Fin 2) (ZMod 2) := by
  apply congrArg Ideal.span
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-- Evaluation at the origin has kernel exactly the ideal generated by the
two affine variables. -/
theorem zReducedEvaluation_ker :
    RingHom.ker zReducedEvaluation.toRingHom = zReducedNormalIdeal := by
  rw [zReducedNormalIdeal_eq_idealOfVars]
  ext p
  rw [RingHom.mem_ker]
  have hz : (![0, 0] : Fin 2 → ZMod 2) = 0 := by
    funext i
    fin_cases i <;> simp
  rw [zReducedEvaluation, hz]
  change MvPolynomial.aeval (0 : Fin 2 → ZMod 2) p = 0 ↔ _
  rw [MvPolynomial.aeval_zero]
  simp only [map_eq_zero]
  unfold MvPolynomial.idealOfVars
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro hp m hm
    by_contra hnone
    push Not at hnone
    have hmzero : m = 0 := by
      ext i
      exact hnone i (Set.mem_univ i)
    subst m
    have hcoeff : p.coeff 0 ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    exact hcoeff (by simpa [MvPolynomial.constantCoeff_eq] using hp)
  · intro hsupport
    by_contra hp
    have hcoeff : p.coeff 0 ≠ 0 := by
      simpa [MvPolynomial.constantCoeff_eq] using hp
    obtain ⟨i, -, hi⟩ :=
      hsupport 0 (MvPolynomial.mem_support_iff.mpr hcoeff)
    exact hi rfl

/-- On the chosen principal open, the actual reduced chart ideal is the
mapped maximal ideal of the origin. -/
theorem zLocalized_chartIdeal_eq_normalIdeal :
    Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away zChartDenominator))
        (Ideal.span {zChartQuadricPolynomial, zChartCubicPolynomial}) =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away zChartDenominator))
        zReducedNormalIdeal := by
  let f := algebraMap BinaryAffinePlane (Localization.Away zChartDenominator)
  have hprod : IsUnit
      (f (MvPolynomial.X 0 + MvPolynomial.X 1 + 1) *
        f (MvPolynomial.X 0 + 1)) := by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit zChartDenominator
  have hparts := IsUnit.mul_iff.mp hprod
  simpa [zChartQuadricPolynomial, zChartCubicPolynomial,
    zReducedNormalIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton] using
    zChart_intersectionIdeal_eq_normalForm
      (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1))
      (by simpa only [map_add, map_one] using hparts.1)
      (by simpa only [map_add, map_one] using hparts.2)

/-- The isolating denominator evaluates to one at the reduced point. -/
theorem zReducedEvaluation_denominator_isUnit :
    IsUnit (zReducedEvaluation zChartDenominator) := by
  rw [show zReducedEvaluation zChartDenominator = 1 by
    simp [zReducedEvaluation, zChartDenominator]]
  exact isUnit_one

/-- Evaluation at the reduced point extended over its isolating principal
open set. -/
noncomputable def zReducedLocalizedEvaluation :
    Localization.Away zChartDenominator →+* ZMod 2 :=
  Localization.awayLift zReducedEvaluation.toRingHom zChartDenominator
    zReducedEvaluation_denominator_isUnit

/-- The localized evaluation kernel is the mapped maximal ideal. -/
theorem zReducedLocalizedEvaluation_ker :
    RingHom.ker zReducedLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away zChartDenominator))
        zReducedNormalIdeal := by
  rw [zReducedLocalizedEvaluation, awayLift_ker, zReducedEvaluation_ker]

/-- The same kernel is generated by the actual localized chart equations. -/
theorem zReducedLocalizedEvaluation_ker_eq_chartIdeal :
    RingHom.ker zReducedLocalizedEvaluation =
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away zChartDenominator))
        (Ideal.span {zChartQuadricPolynomial, zChartCubicPolynomial}) := by
  rw [zReducedLocalizedEvaluation_ker, zLocalized_chartIdeal_eq_normalIdeal.symm]

/-- Evaluation at the reduced point is onto the binary ground field. -/
theorem zReducedEvaluation_surjective :
    Function.Surjective zReducedEvaluation := by
  intro x
  refine ⟨MvPolynomial.C x, ?_⟩
  simp [zReducedEvaluation]

/-- Localizing the source preserves surjectivity of the reduced evaluation. -/
theorem zReducedLocalizedEvaluation_surjective :
    Function.Surjective zReducedLocalizedEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := zReducedEvaluation_surjective x
  refine ⟨algebraMap BinaryAffinePlane
    (Localization.Away zChartDenominator) p, ?_⟩
  exact IsLocalization.Away.lift_eq
    zChartDenominator zReducedEvaluation_denominator_isUnit p

/-- The isolated reduced local factor is exactly `F₂`. -/
noncomputable def zReducedLocalizedChartQuotientEquiv :
    (Localization.Away zChartDenominator ⧸
      Ideal.map
        (algebraMap BinaryAffinePlane (Localization.Away zChartDenominator))
        (Ideal.span {zChartQuadricPolynomial, zChartCubicPolynomial})) ≃+*
      ZMod 2 :=
  (Ideal.quotEquivOfEq zReducedLocalizedEvaluation_ker_eq_chartIdeal.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      zReducedLocalizedEvaluation_surjective)

/-! ## Lengths over the binary ground field -/

/-- The quotient cut out by the actual equations on `D(y+z+1)` has
`F₂`-module length two.  This is a ground-field length statement; comparison
with length over the curve's local ring requires a separate stalk and residue
field argument. -/
theorem doubleLocalizedChartQuotient_f2_length :
    Module.length (ZMod 2)
      (Localization.Away wChartDenominator ⧸
        Ideal.map
          (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
          (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial})) = 2 := by
  let e :
      (Localization.Away wChartDenominator ⧸
        Ideal.map
          (algebraMap BinaryAffinePlane (Localization.Away wChartDenominator))
          (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial}))
        ≃ₗ[ZMod 2] DoubleArtin :=
    zmodLinearEquivOfRingEquiv doubleLocalizedChartQuotientEquiv
  rw [e.length_eq]
  letI : Module.Finite (ZMod 2) DoubleArtin :=
    (Polynomial.monic_X_pow 2).finite_adjoinRoot
  rw [Module.length_eq_finrank, doubleArtin_finrank]
  norm_num

/-- The quotient cut out by the translated equations on `D(1+b)` has
`F₂`-module length three.  As in the doubled case, this does not identify the
chart ring with the local ring at the supported point. -/
theorem tripleLocalizedChartQuotient_f2_length :
    Module.length (ZMod 2)
      (Localization.Away yzChartDenominator ⧸
        Ideal.map
          (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
          (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial})) = 3 := by
  let e :
      (Localization.Away yzChartDenominator ⧸
        Ideal.map
          (algebraMap BinaryAffinePlane (Localization.Away yzChartDenominator))
          (Ideal.span {yzChartQuadricPolynomial, yzChartCubicPolynomial}))
        ≃ₗ[ZMod 2] TripleArtin :=
    zmodLinearEquivOfRingEquiv tripleLocalizedChartQuotientEquiv
  rw [e.length_eq]
  letI : Module.Finite (ZMod 2) TripleArtin :=
    (Polynomial.monic_X_pow 3).finite_adjoinRoot
  rw [Module.length_eq_finrank, tripleArtin_finrank]
  norm_num

/-- The isolated reduced factor has `F₂`-module length one. -/
theorem zReducedLocalizedChartQuotient_f2_length :
    Module.length (ZMod 2)
      (Localization.Away zChartDenominator ⧸
        Ideal.map
          (algebraMap BinaryAffinePlane (Localization.Away zChartDenominator))
          (Ideal.span {zChartQuadricPolynomial, zChartCubicPolynomial})) = 1 := by
  let e :
      (Localization.Away zChartDenominator ⧸
        Ideal.map
          (algebraMap BinaryAffinePlane (Localization.Away zChartDenominator))
          (Ideal.span {zChartQuadricPolynomial, zChartCubicPolynomial}))
        ≃ₗ[ZMod 2] ZMod 2 :=
    zmodLinearEquivOfRingEquiv zReducedLocalizedChartQuotientEquiv
  rw [e.length_eq, Module.length_eq_one]

end MazurProof.RationalPointsN25QuotientTwoHyperplaneArtin
