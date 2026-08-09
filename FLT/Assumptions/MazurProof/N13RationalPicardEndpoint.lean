import FLT.Assumptions.MazurProof.N13RationalPicardSpreadExistence
import FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter
import FLT.Assumptions.MazurProof.N13RationalAbelChartBase

/-!
# Exact remaining interface for the rational N13 endpoint

Global existence of rational spread lines and compatibility with rational
Abel--Jacobi points are now theorems.  Consequently a concrete reduction
classifier needs only an equality theorem for specializations of spread
lines.  Once that classifier kernel is represented in the two-adic Abel
chart with the unary first-jet doubling law, the existing formal-kernel
argument proves that every rational point of the N13 curve is cuspidal.

This file performs only the final assembly.  It deliberately leaves the two
remaining geometric statements visible in the theorem signature: equality
reflection for spread lines, and first-order compatibility of the canonical
near-base representatives under doubling.
-/

namespace MazurProof.N13RationalPicardEndpoint

noncomputable section

universe u

/-- The rational oriented Picard group used throughout the N13 endgame. -/
abbrev G : Type :=
  N13RationalPointEndgame.G

/-- Concrete proper spread lines carrying both generic and special classes. -/
abbrev SpreadLine : Type :=
  N13RationalCurvePointPicardRealization.SpreadLine

/-!
## The pointwise formulation

One may avoid a global classifier by asking only that equality of anchored
special Abel classes reflect equality of rational Abel--Jacobi classes for
curve points.  Because both Abel maps used here are injective on points, this
condition is exactly injectivity of proper reduction on rational curve
points.  The equivalence below records that this is a weaker interface, but
not an independent shortcut around the rational-point theorem.
-/

/-- Equality after anchored special reduction reflects equality of the
rational Abel--Jacobi classes of two rational curve points. -/
def PointwiseReflection : Prop :=
  ∀ P Q : N13RationalPointEndgame.RationalCurvePoint,
    N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve P) =
        N13RationalPointEndgame.specialPointClass
          (N13ProperCurveReduction.reduceCurve Q) →
      N13RationalPointEndgame.rationalAbel P =
        N13RationalPointEndgame.rationalAbel Q

/-- Pointwise Abel reflection is equivalent to injectivity of proper
reduction on rational N13 curve points: the rational Abel--Jacobi map and the
anchored special Abel map are both injective. -/
theorem pointwiseReflection_iff_reduceCurve_injective :
    PointwiseReflection ↔
      Function.Injective N13ProperCurveReduction.reduceCurve := by
  constructor
  · intro hreflect P Q hreduce
    -- Equal reduced points have equal anchored special classes; reflection
    -- and rational Abel--Jacobi injectivity then recover the rational points.
    apply N13MumfordAbelJacobi.abelJacobi_injective ℚ
    exact hreflect P Q (congrArg
      N13RationalPointEndgame.specialPointClass hreduce)
  · intro hreduce P Q hspecial
    -- Injectivity of the anchored special Abel map first recovers equality of
    -- reductions, after which the assumed reduction injectivity gives `P=Q`.
    exact congrArg N13RationalPointEndgame.rationalAbel
      (hreduce
        (N13InfinitySpecialPointClass.specialPointClass_injective hspecial))

/-- Pointwise reflection already classifies every rational projective point
as one of the six cusps, because those cusps reduce bijectively to the six
points of the special curve. -/
theorem curvePoint_eq_cusp_of_pointwiseReflection
    (hreflect : PointwiseReflection)
    (P : N13RationalPointEndgame.RationalCurvePoint) :
    ∃ c : N13Mumford.Cusp13,
      P = N13Mumford.cuspPoint c := by
  have hreduce :
      Function.Injective N13ProperCurveReduction.reduceCurve :=
    pointwiseReflection_iff_reduceCurve_injective.mp hreflect
  obtain ⟨c, hc⟩ :=
    N13SpecialCuspReduction.specialCuspEquiv_surjective
      (N13ProperCurveReduction.reduceCurve P)
  refine ⟨c, hreduce ?_⟩
  rw [N13ProperCurveReduction.reduceCurve_cusp]
  exact hc.symm

/-- The affine first coordinate, undefined at the two projective infinity
points; this lets equality with a named cusp expose the two possible affine
cusp coordinates. -/
private def affineX? :
    N13RationalPointEndgame.RationalCurvePoint → Option ℚ
  | .infinityPlus => none
  | .infinityMinus => none
  | .affine x _ _ => some x

/-- The pointwise reflection formulation implies the exact affine theorem
consumed by the primitive order-thirteen exclusion. -/
theorem affine_x_is_cuspidal_of_pointwiseReflection
    (hreflect : PointwiseReflection) :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1 := by
  intro X Y hcurve
  let P : N13RationalPointEndgame.RationalCurvePoint :=
    N13Mumford.affineCurvePoint X Y hcurve
  obtain ⟨c, hPc⟩ :=
    curvePoint_eq_cusp_of_pointwiseReflection hreflect P
  -- Applying the partial affine-coordinate projection excludes both points
  -- at infinity and reads off `0` or `-1` from the four affine cusps.
  have hx := congrArg affineX? hPc
  cases c with
  | infinityPlus =>
      simp [P, affineX?, N13Mumford.affineCurvePoint,
        N13Mumford.cuspPoint] at hx
  | infinityMinus =>
      simp [P, affineX?, N13Mumford.affineCurvePoint,
        N13Mumford.cuspPoint] at hx
  | zeroPlus =>
      exact Or.inl (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | zeroMinus =>
      exact Or.inl (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | negOnePlus =>
      exact Or.inr (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)
  | negOneMinus =>
      exact Or.inr (by
        simpa [P, affineX?, N13Mumford.affineCurvePoint,
          N13Mumford.cuspPoint] using hx)

/-!
## The reduction classifier

The balanced-Mumford exhaustion supplies a spread for every rational class,
and the pointwise constructions supply Abel compatibility.  Thus the sole
input to the relation-first classifier is the theorem that its special-class
fibres are exactly the cosets of the proposed kernel.
-/

/-- Assemble rational-point reduction from a proposed kernel and the exact
generic-versus-special equality theorem for concrete spread lines. -/
def reductionData
    (kernel : AddSubgroup G)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M) :
    N13SpreadRationalPointReduction.Data SpreadLine :=
  N13RationalCurvePointPicardRealization.rationalPointReductionData
    kernel
    (N13RationalPicardSpreadExistence.exists_spread kernel)
    class_eq_iff

/-- On the exact normalized spreads chosen above, special equality is
literally the coset relation of the proposed kernel.

Unlike the abstract `class_eq_iff` input, these two lines carry raw generic
data equal to the coefficient-extended balanced Mumford normal forms.  This
specialization of the relation therefore provides the representative-level
starting point for constructing the canonical mapped-special family. -/
theorem exactSpreadLine_special_eq_iff_sub_mem
    (kernel : AddSubgroup G)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M)
    (P Q : G) :
    N13RationalCurvePointPicardRealization.specialClass
          (N13RationalPicardSpreadExistence.exactSpreadLine P) =
        N13RationalCurvePointPicardRealization.specialClass
          (N13RationalPicardSpreadExistence.exactSpreadLine Q) ↔
      P - Q ∈ kernel := by
  rw [class_eq_iff]
  simp only [N13RationalCurvePointPicardRealization.genericClass,
    N13RationalPicardSpreadExistence.exactSpreadLine_rationalClass]
  exact QuotientAddGroup.eq_iff_sub_mem

/-- The literal classifier kernel produced by `reductionData`.  Naming this
subgroup keeps the two-adic representative hypotheses tied to the exact
kernel consumed by the rational-point endpoint. -/
abbrev Kernel
    (kernel : AddSubgroup G)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M) :
    AddSubgroup G :=
  N13RationalKernelDoublingAdapter.Concrete.Kernel
    (reductionData kernel class_eq_iff)

/-- The assembled classifier introduces no hidden subgroup: its reduction
kernel is exactly the subgroup appearing in `class_eq_iff`. -/
theorem kernel_eq
    (kernel : AddSubgroup G)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M) :
    Kernel kernel class_eq_iff = kernel := by
  calc
    Kernel kernel class_eq_iff =
        (reductionData kernel class_eq_iff).spread.kernel :=
      N13RationalKernelDoublingAdapter.Concrete.kernel_eq_spreadKernel
        (reductionData kernel class_eq_iff)
    _ = kernel := rfl

/-!
## Comparing canonical contraction with an actual rational spread

The exact normalized spread of `z + rationalBasePic` supplies a proper
integral line with the correct generic Mumford representative.  The
remaining representative-level input is vertical saturation of that actual
line.  Localization then identifies it with the canonical contraction.
Once this equality is known, the global specialization relation forces
the line's stored divisor to be the literal Abel-chart base divisor, whose
affine ideal is already proved to be `specialIdeal`.
-/

/-- The affine ideal of every translated exact spread is saturated against
all nonzero vertical scalars from `ℤ₂`.

This rules out precisely the ambiguity invisible on the generic fibre: an
integral lattice cannot differ from the canonical contraction by an extra
vertical component or scalar twist.  The statement concerns only the
explicit spreads selected by balanced degree exhaustion, not arbitrary
proper spread lines. -/
def ExactSpreadAffineVerticallySaturated
    (kernel : AddSubgroup G) : Prop :=
  ∀ z : kernel,
    N13TwoChartPicardRealization.AffineVerticallySaturated
      (N13RationalPicardSpreadExistence.exactSpreadLine
        ((z : G) +
          N13RationalAbelChartBase.rationalBasePic)).realization.charts

/-- The contraction of each mapped normalized rational representative agrees
with the affine special restriction of its exact normalized rational spread.

The preceding base-change theorem identifies this Mumford datum with the
canonical two-adic representative.  Thus this is strictly a comparison
between two integral models of the same literal generic datum.  It does not
assume that either side is the fixed special ideal and therefore isolates the
remaining lattice/contraction compatibility below the former
`CanonicalMappedSpecialFamily` input. -/
def ExactNormalizedContractionMatchesSpread
    (kernel : AddSubgroup G) : Prop :=
  ∀ z : kernel,
    Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate
        (N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal
            (N13RationalPicardSpreadExistence.mapMumford
              (N13RationalPicardSpreadExistence.normalizedMumford
                ((z : G) +
                  N13RationalAbelChartBase.rationalBasePic))).toSemi)) =
      (N13TwoChartSpecialRestriction.restrict
        (N13RationalPicardSpreadExistence.exactSpreadLine
          ((z : G) +
            N13RationalAbelChartBase.rationalBasePic)).realization.charts).affineIdeal

/-- Vertical saturation of the exact spread lattice forces the canonical
contraction comparison.

The raw generic equality supplies equality after inverting the nonzero
`ℤ₂` scalars.  The existing localization theorem says that a vertically
saturated integral ideal is recovered exactly by contraction; applying
special reduction to that integral equality gives the displayed comparison. -/
theorem exactNormalizedContractionMatchesSpread_of_verticalSaturated
    (kernel : AddSubgroup G)
    (hsaturated : ExactSpreadAffineVerticallySaturated kernel) :
    ExactNormalizedContractionMatchesSpread kernel := by
  intro z
  let P : G :=
    (z : G) + N13RationalAbelChartBase.rationalBasePic
  have hcontract :
      N13IntegralModelContraction.contractIdeal
          (N13CanonicalContractionQuotient.graphIdeal
            (N13RationalPicardSpreadExistence.mapMumford
              (N13RationalPicardSpreadExistence.normalizedMumford P)).toSemi) =
        (N13RationalPicardSpreadExistence.exactSpreadLine
          P).realization.charts.affineIdeal := by
    apply
      N13IntegralInfinityGraphSaturation.contractIdeal_eq_of_map_eq_of_scalarSaturated
    · exact
        N13RationalPicardSpreadExistence.exactSpreadLine_map_affineIdeal P
    · exact hsaturated z
  change
    Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal
              (N13RationalPicardSpreadExistence.mapMumford
                (N13RationalPicardSpreadExistence.normalizedMumford P)).toSemi)) =
      Ideal.map N13GeneralizedMumfordReduction.reduceCoordinate
        (N13RationalPicardSpreadExistence.exactSpreadLine
          P).realization.charts.affineIdeal
  rw [hcontract]

/-- Construct the canonical mapped-special family from vertical saturation
of the exact normalized spread lattices.

The contraction comparison is first derived by localization.  The global
`class_eq_iff` theorem is used only afterward: it sends the translated exact
spread to the same special Abel class as the explicit base spread.  Regularity
then identifies the stored divisor literally, and the special graph-divisor
theorem identifies its affine ideal with the fixed special ideal. -/
def canonicalMappedSpecialFamilyOfExactSpread
    (kernel : AddSubgroup G)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M)
    (hsaturated : ExactSpreadAffineVerticallySaturated kernel) :
    N13RationalKernelDoublingAdapter.CanonicalMappedSpecialFamily
      (Kernel kernel class_eq_iff) := by
  rw [kernel_eq kernel class_eq_iff]
  refine ⟨?_⟩
  intro z
  calc
    Ideal.map
          N13GeneralizedMumfordReduction.reduceCoordinate
          (N13IntegralModelContraction.contractIdeal
            (N13CanonicalContractionQuotient.graphIdeal
              (N13RationalKernelDoublingAdapter.canonicalMappedSpecialMumford
                (N13TwoAdicAbelChartSection.subgroupToPic kernel z)).toSemi)) =
        (N13TwoChartSpecialRestriction.restrict
          (N13RationalPicardSpreadExistence.exactSpreadLine
            ((z : G) +
              N13RationalAbelChartBase.rationalBasePic)).realization.charts).affineIdeal :=
      by
        rw [N13RationalAbelChartBase.canonicalMappedSpecialMumford_subgroup_eq_mapMumford]
        exact
          exactNormalizedContractionMatchesSpread_of_verticalSaturated
            kernel hsaturated z
    _ = (N13SpecialDivisorCharts.ofDivisor
          (N13RationalPicardSpreadExistence.exactSpreadLine
            ((z : G) +
              N13RationalAbelChartBase.rationalBasePic)).realization.specialDivisor).affineIdeal :=
      (N13RationalPicardSpreadExistence.exactSpreadLine
        ((z : G) +
          N13RationalAbelChartBase.rationalBasePic)).realization.special_affine
    _ = (N13SpecialDivisorCharts.ofDivisor
          N13AbelChartBase.specialBaseDivisor).affineIdeal := by
      rw [N13RationalAbelChartBase.exactTranslated_specialDivisor_eq_base
        kernel class_eq_iff z]
    _ = N13SpecialQuotientBasis.specialIdeal :=
      N13RationalAbelChartBase.specialBaseDivisor_affineIdeal

/-!
## Endpoint assembly

Canonical mapped-special representatives recover a centered two-disk pair
for every kernel element.  The transition-square estimate is already proved;
the remaining comparison says that the representative selected for `2z` has
the same first jet as the square of the representative selected for `z`.
Together these facts make the classifier kernel two-adically separated.
-/

/-- Equality reflection for rational spreads, vertical saturation of the
exact normalized spreads, and first-jet doubling compatibility imply the
primitive N13 rational-point theorem required by Mazur's bound. -/
theorem affine_x_is_cuspidal
    (kernel : AddSubgroup G)
    (class_eq_iff :
      ∀ L M : SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M)
    (hsaturated : ExactSpreadAffineVerticallySaturated kernel)
    (C :
      N13RationalKernelDoublingAdapter.FirstJetDoublingCompatibility
        (canonicalMappedSpecialFamilyOfExactSpread
          kernel class_eq_iff hsaturated).toNearBaseFamily) :
    ∀ X Y : ℚ, N13CurveModel.C13SexticEq X Y →
      X = 0 ∨ X = -1 := by
  -- The canonical family and first-jet comparison give separatedness of the
  -- exact subgroup defined by the assembled relation-first classifier.
  have hseparated :
      N18RouteC.Separated.NSeparated
        (Kernel kernel class_eq_iff) 2 :=
    (canonicalMappedSpecialFamilyOfExactSpread
      kernel class_eq_iff hsaturated).separated C
  -- All other fields of rational-point reduction are supplied by the global
  -- spread and pointwise realization theorems used in `reductionData`.
  exact
    (reductionData kernel class_eq_iff).affine_x_is_cuspidal
      hseparated

end

end MazurProof.N13RationalPicardEndpoint
