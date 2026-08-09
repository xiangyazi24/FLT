import FLT.Assumptions.MazurProof.N13RationalPicardSpreadExistence
import FLT.Assumptions.MazurProof.N13RationalKernelDoublingAdapter
import FLT.Assumptions.MazurProof.N13SplitQuadraticPicardRealization
import FLT.Assumptions.MazurProof.N13SpecialGraphDivisorCharts

/-!
# A rational lift of the N13 two-adic Abel-chart base

The formal two-adic chart is centred at the good-model divisor
`(0,0)+(-1,0)`.  In the standard sextic coordinate the same divisor has
Mumford data `u = X^2 + X`, `v = 2X + 1`, and zero infinity orientation.  This
file records that rational datum and proves that coefficient extension sends
it literally to the distinguished two-adic disk-pair representative.

Naming the rational lift is essential for the specialization argument: a
rational kernel class is translated by this base class before its canonical
balanced representative is contracted and compared with the fixed special
graph.
-/

open Polynomial

namespace MazurProof.N13RationalAbelChartBase

noncomputable section

/-! ## The balanced rational base representative -/

/-- Rational balanced Mumford data of the nonspecial Abel-chart base.

The two good-model ordinates are both zero.  Completing the square sends
their graph to the reduced sextic polynomial `2X+1`; replacing it by the
constant `1` would select the wrong sheet above `x=-1`.  The displayed
quotient certifies the Mumford divisibility condition directly over `ℚ`. -/
def rationalBaseMumford : N13Mumford.Mumford ℚ where
  u := X ^ 2 + X
  v := 2 * X + 1
  nInf := 0
  u_monic := by
    simpa [N13FormalAbelLinearization.uBase] using
      (N13FormalAbelLinearization.uBase_monic (R := ℚ))
  deg_u := by
    have hdeg : (X ^ 2 + X : ℚ[X]).natDegree = 2 := by
      simpa [N13FormalAbelLinearization.uBase] using
        (N13FormalAbelLinearization.uBase_natDegree (R := ℚ))
    exact hdeg.le
  v_reduced := by
    have hu : (X ^ 2 + X : ℚ[X]).Monic := by
      simpa [N13FormalAbelLinearization.uBase] using
        (N13FormalAbelLinearization.uBase_monic (R := ℚ))
    apply (Polynomial.mod_eq_self_iff hu.ne_zero).2
    rw [degree_eq_natDegree hu.ne_zero]
    have hdeg : (X ^ 2 + X : ℚ[X]).natDegree = 2 := by
      simpa [N13FormalAbelLinearization.uBase] using
        (N13FormalAbelLinearization.uBase_natDegree (R := ℚ))
    rw [hdeg]
    simpa [Polynomial.C_ofNat] using
      (Polynomial.degree_linear_lt (R := ℚ) (a := 2) (b := 1))
  curve_dvd := by
    refine ⟨X ^ 4 + 3 * X ^ 3 + 3 * X ^ 2 - X - 2, ?_⟩
    simp only [N13Mumford.model_f, N13Mumford.f]
    ring
  infinity_bound := by
    norm_num
    compute_degree

/-- Two Mumford structures with identical polynomial and orientation data
are equal; proof certificates in the remaining fields are propositions.

This extensionality bridge is used only to compare two independently
constructed concrete representatives, not to identify Picard classes. -/
theorem mumford_eq_of_u_v_nInf
    {D E : N13Mumford.Mumford N13InfinityBaseChange.Q₂}
    (hu : D.u = E.u) (hv : D.v = E.v) (hn : D.nInf = E.nInf) :
    D = E := by
  cases D
  cases E
  simp_all

/-- Coefficient extension of the rational base datum is literally the
balanced Mumford representative attached to the distinguished disk pair.

The proof unfolds the good-to-sextic coordinate conversion.  This exact
representative equality is stronger than equality of their Picard classes
and prevents a later normalization argument from losing the chosen frame. -/
@[simp] theorem mapMumford_rationalBaseMumford :
    N13RationalPicardSpreadExistence.mapMumford rationalBaseMumford =
      N13TwoAdicAbelChartPic.DiskPair.mumford
        N13TwoAdicAbelChartData.basePair := by
  apply mumford_eq_of_u_v_nInf
  · simp [N13RationalPicardSpreadExistence.mapMumford,
      rationalBaseMumford,
      N13TwoAdicAbelChartPic.DiskPair.mumford,
      N13TwoAdicAbelChartData.DiskPair.u,
      N13TwoAdicAbelChartData.basePair,
      N13TwoAdicMumfordTransport.mapPoly,
      N13TwoAdicMumfordTransport.coeffMap]
    ring
  · simp [N13RationalPicardSpreadExistence.mapMumford,
      rationalBaseMumford,
      N13TwoAdicAbelChartPic.DiskPair.mumford,
      N13TwoAdicAbelChartData.DiskPair.smoothMumford,
      N13TwoAdicAbelChartData.DiskPair.w,
      N13GoodSexticMumfordTransport.reducedCompletedGraph,
      N13GoodSexticMumfordTransport.completedGraph,
      N13GeneralizedMumfordIntegral.hPoly,
      N13FormalAbelLinearization.uBase,
      N13TwoAdicMumfordTransport.mapPoly,
      N13TwoAdicMumfordTransport.coeffMap]
    symm
    calc
      (X ^ 3 + X + 1 : N13InfinityBaseChange.Q₂[X]) %
            (X ^ 2 + X) =
          (2 * X + 1) % (X ^ 2 + X) := by
        apply Polynomial.mod_eq_of_dvd_sub
        refine ⟨X - 1, ?_⟩
        ring
      _ = 2 * X + 1 := by
        have hu :
            (X ^ 2 + X : N13InfinityBaseChange.Q₂[X]).Monic := by
          simpa [N13FormalAbelLinearization.uBase] using
            (N13FormalAbelLinearization.uBase_monic
              (R := N13InfinityBaseChange.Q₂))
        apply (Polynomial.mod_eq_self_iff hu.ne_zero).2
        rw [degree_eq_natDegree hu.ne_zero]
        have hdeg :
            (X ^ 2 + X : N13InfinityBaseChange.Q₂[X]).natDegree = 2 := by
          simpa [N13FormalAbelLinearization.uBase] using
            (N13FormalAbelLinearization.uBase_natDegree
              (R := N13InfinityBaseChange.Q₂))
        rw [hdeg]
        simpa [Polynomial.C_ofNat] using
          (Polynomial.degree_linear_lt
            (R := N13InfinityBaseChange.Q₂) (a := 2) (b := 1))
  · rfl

/-! ## The rational Picard base class -/

/-- The rational oriented Picard class represented by the lifted base
divisor.  Translating a rational kernel element by this class matches the
centering convention of the two-adic disk-pair chart. -/
def rationalBasePic : N13RationalPointEndgame.G :=
  SexticMumford.classOf
    (N13Mumford.model ℚ)
    (N13Infinity.positiveInfinityOrder ℚ)
    rationalBaseMumford

/-- Rational-to-two-adic Picard base change sends the lifted rational class
to the exact base class used by the kernel-doubling adapter.

This follows from naturality of `classOf` together with the literal Mumford
representative equality above. -/
@[simp] theorem picMapRatToQ₂_rationalBasePic :
    N13InfinityBaseChange.picMapRatToQ₂ rationalBasePic =
      N13RationalKernelDoublingAdapter.basePic := by
  calc
    N13InfinityBaseChange.picMapRatToQ₂ rationalBasePic =
        SexticMumford.classOf
          (N13Mumford.model N13InfinityBaseChange.Q₂)
          (N13Infinity.positiveInfinityOrder
            N13InfinityBaseChange.Q₂)
          (N13RationalPicardSpreadExistence.mapMumford
            rationalBaseMumford) :=
      N13InfinityBaseChange.picMapRatToQ₂_classOf
        rationalBaseMumford
    _ = N13RationalKernelDoublingAdapter.basePic := by
      rw [mapMumford_rationalBaseMumford]
      rfl

/-- Normalizing the rational base class returns the explicit lifted datum.

Both sides are balanced representatives of the same oriented Picard class;
normal-form uniqueness therefore identifies them.  This equality connects
the exact-spread choice to the base datum used in the Abel chart. -/
theorem normalizedMumford_rationalBasePic :
    N13RationalPicardSpreadExistence.normalizedMumford rationalBasePic =
      rationalBaseMumford := by
  apply SexticMumford.normalize_eq_of_class
  rfl

/-- The canonical two-adic representative of a centered rational subgroup
class is exactly the coefficient extension of the normalized rational
representative after translation by the lifted Abel-chart base.

This removes all quotient-level ambiguity before integral contraction is
compared with a proper spread line: both constructions start from the same
literal balanced Mumford datum on the generic fibre. -/
theorem canonicalMappedSpecialMumford_subgroup_eq_mapMumford
    (kernel : AddSubgroup N13RationalPointEndgame.G)
    (z : kernel) :
    N13RationalKernelDoublingAdapter.canonicalMappedSpecialMumford
        (N13TwoAdicAbelChartSection.subgroupToPic kernel z) =
      N13RationalPicardSpreadExistence.mapMumford
        (N13RationalPicardSpreadExistence.normalizedMumford
          ((z : N13RationalPointEndgame.G) + rationalBasePic)) := by
  calc
    N13RationalKernelDoublingAdapter.canonicalMappedSpecialMumford
          (N13TwoAdicAbelChartSection.subgroupToPic kernel z) =
        SexticMumford.normalize
          (N13Mumford.model N13InfinityBaseChange.Q₂)
          (N13Infinity.positiveInfinityOrder
            N13InfinityBaseChange.Q₂)
          (N13InfinityBaseChange.picMapRatToQ₂
              (z : N13RationalPointEndgame.G) +
            N13InfinityBaseChange.picMapRatToQ₂ rationalBasePic) := by
      rw [N13RationalKernelDoublingAdapter.canonicalMappedSpecialMumford,
        N13TwoAdicAbelChartSection.subgroupToPic,
        picMapRatToQ₂_rationalBasePic]
      rfl
    _ = SexticMumford.normalize
          (N13Mumford.model N13InfinityBaseChange.Q₂)
          (N13Infinity.positiveInfinityOrder
            N13InfinityBaseChange.Q₂)
          (N13InfinityBaseChange.picMapRatToQ₂
            ((z : N13RationalPointEndgame.G) + rationalBasePic)) := by
      rw [map_add]
    _ = N13RationalPicardSpreadExistence.mapMumford
          (N13RationalPicardSpreadExistence.normalizedMumford
            ((z : N13RationalPointEndgame.G) + rationalBasePic)) := by
      exact N13InfinityBaseChange.normalize_picMapRatToQ₂
        ((z : N13RationalPointEndgame.G) + rationalBasePic)

/-!
## A literal two-chart spread of the base divisor

The good-model points `(0,0)` and `(-1,0)` are integral, so their explicit
proper point lines may be tensored.  The resulting line has the mapped
rational Mumford graph on the generic fibre and the named divisor
`p00+p10` literally on the special fibre.
-/

/-- The good-model origin lies on the two-adic N13 curve. -/
theorem zero_onCurve :
    N13GoodModelTwo.AffineEquation
      (0 : N13InfinityBaseChange.Q₂) 0 := by
  exact (N13FormalAbelLinearization.base_points_on_curve
    (R := N13InfinityBaseChange.Q₂)).1

/-- The point with horizontal coordinate `-1` and ordinate zero is the
second integral base point on the good model. -/
theorem negOne_onCurve :
    N13GoodModelTwo.AffineEquation
      (-1 : N13InfinityBaseChange.Q₂) 0 := by
  exact (N13FormalAbelLinearization.base_points_on_curve
    (R := N13InfinityBaseChange.Q₂)).2

/-- The proper two-chart line obtained by tensoring the point lines through
the two rational base points.  It is the geometric spread underlying the
rational lift of the Abel-chart origin. -/
def baseLine : N13TwoChartPicardRealization.Line :=
  N13QuadraticTwoChartSpread.pairLine
    0 0 (-1) 0 zero_onCurve negOne_onCurve

/-- Proper reduction of the two integral base points gives exactly the named
nonspecial divisor `p00+p10`, with no appeal to Abel-class equality. -/
theorem reducedPairDivisor_base :
    N13SplitQuadraticSpecialRestriction.reducedPairDivisor
        0 0 (-1) 0 zero_onCurve negOne_onCurve =
      N13AbelChartBase.specialBaseDivisor := by
  simp [N13SplitQuadraticSpecialRestriction.reducedPairDivisor,
    N13SplitQuadraticSpecialRestriction.reducedPoint,
    N13IntegralAffinePointSpecialClass.reducedPoint,
    N13ProperCurveReduction.integralAffineLift,
    N13AbelChartBase.specialBaseDivisor,
    N13AbelChartBase.p00,
    N13AbelChartBase.p10,
    N13AbelFiberTwoModel.curvePointEquiv]

/-- The affine-chart restriction of `baseLine` is the canonical affine ideal
of the literal special base divisor.  This is the special-fibre half of the
two-chart realization on the ordinary chart. -/
theorem restrict_baseLine_affineIdeal :
    (N13TwoChartSpecialRestriction.restrict baseLine).affineIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        N13AbelChartBase.specialBaseDivisor).affineIdeal := by
  calc
    (N13TwoChartSpecialRestriction.restrict baseLine).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor
          (N13SplitQuadraticSpecialRestriction.reducedPairDivisor
            0 0 (-1) 0 zero_onCurve negOne_onCurve)).affineIdeal := by
      exact N13SplitQuadraticSpecialRestriction.restrict_pairLine_affineIdeal
        0 0 (-1) 0 zero_onCurve negOne_onCurve
    _ = (N13SpecialDivisorCharts.ofDivisor
          N13AbelChartBase.specialBaseDivisor).affineIdeal := by
      rw [reducedPairDivisor_base]

/-- The infinity-chart restriction of `baseLine` is the canonical infinity
ideal of the same literal special divisor.  Together with the affine theorem
this fixes the complete special two-chart frame. -/
theorem restrict_baseLine_infinityIdeal :
    (N13TwoChartSpecialRestriction.restrict baseLine).infinityIdeal =
      (N13SpecialDivisorCharts.ofDivisor
        N13AbelChartBase.specialBaseDivisor).infinityIdeal := by
  calc
    (N13TwoChartSpecialRestriction.restrict baseLine).infinityIdeal =
        (N13SpecialDivisorCharts.ofDivisor
          (N13SplitQuadraticSpecialRestriction.reducedPairDivisor
            0 0 (-1) 0 zero_onCurve negOne_onCurve)).infinityIdeal := by
      exact N13SplitQuadraticSpecialRestriction.restrict_pairLine_infinityIdeal
        0 0 (-1) 0 zero_onCurve negOne_onCurve
    _ = (N13SpecialDivisorCharts.ofDivisor
          N13AbelChartBase.specialBaseDivisor).infinityIdeal := by
      rw [reducedPairDivisor_base]

/-- The mapped rational base polynomial splits at the two good-model base
coordinates.  This factorization feeds the exact product-of-point-ideals
theorem for the generic fibre. -/
theorem mappedBase_u_factor :
    (N13RationalPicardSpreadExistence.mapMumford
        rationalBaseMumford).u =
      (X - C (0 : N13InfinityBaseChange.Q₂)) *
        (X - C (-1 : N13InfinityBaseChange.Q₂)) := by
  simp [N13RationalPicardSpreadExistence.mapMumford,
    rationalBaseMumford]
  ring

/-- The mapped rational base datum retains horizontal degree two. -/
theorem mappedBase_u_natDegree :
    (N13RationalPicardSpreadExistence.mapMumford
        rationalBaseMumford).u.natDegree = 2 := by
  rw [mapMumford_rationalBaseMumford]
  simpa [N13TwoAdicAbelChartPic.DiskPair.mumford] using
    (N13TwoAdicAbelChartPic.DiskPair.sexticSemi_u_natDegree
      N13TwoAdicAbelChartData.basePair)

/-- The generic affine ideal of `baseLine` is literally the Mumford ideal of
the coefficient-extended rational base datum.

The proof identifies the completed-square ordinates of the two point lines
with the evaluations of `2X+1`, then applies the split quadratic product
formula. -/
theorem map_baseLine_affineIdeal :
    Ideal.map
        N13IntegralFractionalHull.integralToRational
        baseLine.affineIdeal =
      SexticMumford.mumfordIdeal
        N13RationalPicardSpreadExistence.Model₂
        (N13RationalPicardSpreadExistence.mapMumford
          rationalBaseMumford).u
        (N13RationalPicardSpreadExistence.mapMumford
          rationalBaseMumford).v := by
  change
    Ideal.map
        N13TwoAdicCoordinateBaseChange.integralToSextic
        baseLine.affineIdeal =
      SexticMumford.mumfordIdeal
        N13RationalPicardSpreadExistence.Model₂
        (N13RationalPicardSpreadExistence.mapMumford
          rationalBaseMumford).u
        (N13RationalPicardSpreadExistence.mapMumford
          rationalBaseMumford).v
  rw [baseLine,
    N13QuadraticTwoChartSpread.map_pairLine_affineIdeal]
  have hv₀ :
      N13EscapingDegreeOneSpread.pointY 0 0 =
        (N13RationalPicardSpreadExistence.mapMumford
          rationalBaseMumford).v.eval 0 := by
    simp [N13EscapingDegreeOneSpread.pointY,
      N13GoodModelTwo.h,
      N13RationalPicardSpreadExistence.mapMumford,
      rationalBaseMumford]
  have hv₁ :
      N13EscapingDegreeOneSpread.pointY (-1) 0 =
        (N13RationalPicardSpreadExistence.mapMumford
          rationalBaseMumford).v.eval (-1) := by
    simp [N13EscapingDegreeOneSpread.pointY,
      N13GoodModelTwo.h,
      N13RationalPicardSpreadExistence.mapMumford,
      rationalBaseMumford]
    ring
  rw [hv₀, hv₁]
  exact
    N13TwoChartLineTensor.mumfordIdeal_eq_pointIdeal_mul_of_split
      (N13RationalPicardSpreadExistence.mapMumford
        rationalBaseMumford)
      mappedBase_u_natDegree 0 (-1) mappedBase_u_factor (by norm_num)

/-- Complete two-fibre Picard data for the rational base divisor.  Its
generic representative and both special chart ideals are fixed literally,
so no quotient-level choice remains in this base case. -/
def baseRealization : N13TwoChartPicardRealization.Data :=
  N13SplitQuadraticPicardRealization.dataOfSpecialRealization
    (N13RationalPicardSpreadExistence.mapMumford rationalBaseMumford)
    baseLine
    N13AbelChartBase.specialBaseDivisor
    restrict_baseLine_affineIdeal
    restrict_baseLine_infinityIdeal

/-- The raw generic datum of the explicit base realization is exactly the
mapped rational Mumford datum, including zero infinity orientation. -/
theorem baseRealization_genericRaw :
    N13TwoChartPicardRealization.genericRaw
        baseRealization.charts baseRealization.infinityOrder =
      SexticMumford.mumfordRaw
        N13RationalPicardSpreadExistence.Model₂
        (N13RationalPicardSpreadExistence.mapMumford
          rationalBaseMumford) := by
  exact
    N13SplitQuadraticPicardRealization.dataOfSpecialRealization_genericRaw_eq_mumfordRaw
        (N13RationalPicardSpreadExistence.mapMumford rationalBaseMumford)
        baseLine N13AbelChartBase.specialBaseDivisor
        restrict_baseLine_affineIdeal restrict_baseLine_infinityIdeal
        map_baseLine_affineIdeal

/-- The generic Picard class of the explicit base realization is the
two-adic base change of the rational base class. -/
theorem baseRealization_toGenericPic :
    baseRealization.toGenericPic =
      N13InfinityBaseChange.picMapRatToQ₂ rationalBasePic := by
  calc
    baseRealization.toGenericPic =
        SexticMumford.classOf
          N13RationalPicardSpreadExistence.Model₂
          (N13Infinity.positiveInfinityOrder
            N13InfinityBaseChange.Q₂)
          (N13RationalPicardSpreadExistence.mapMumford
            rationalBaseMumford) := by
      exact
        N13SplitQuadraticPicardRealization.dataOfSpecialRealization_toGenericPic_eq_classOf
            (N13RationalPicardSpreadExistence.mapMumford
              rationalBaseMumford)
            baseLine N13AbelChartBase.specialBaseDivisor
            restrict_baseLine_affineIdeal restrict_baseLine_infinityIdeal
            map_baseLine_affineIdeal
    _ = N13RationalKernelDoublingAdapter.basePic := by
      rw [mapMumford_rationalBaseMumford]
      rfl
    _ = N13InfinityBaseChange.picMapRatToQ₂ rationalBasePic :=
      picMapRatToQ₂_rationalBasePic.symm

/-- A concrete rational spread line for the Abel-chart base whose special
divisor is stored literally as `specialBaseDivisor`. -/
def baseSpreadLine :
    N13RationalCurvePointPicardRealization.SpreadLine where
  rationalClass := rationalBasePic
  realization := baseRealization
  generic_eq := baseRealization_toGenericPic

@[simp] theorem baseSpreadLine_rationalClass :
    baseSpreadLine.rationalClass = rationalBasePic :=
  rfl

/-- The special class of the explicit base spread is the regular Abel class
of the named nonspecial base divisor. -/
theorem baseSpreadLine_specialClass :
    N13RationalCurvePointPicardRealization.specialClass baseSpreadLine =
      N13AbelFiberTwoModel.abel
        N13AbelChartBase.specialBaseDivisor :=
  rfl

/-- The affine chart of the literal nonspecial base divisor is the fixed
special graph ideal used by canonical contraction.

The proof passes through the existing quadratic graph-divisor theorem for
the reduced smooth base Mumford datum.  Thus the equality is a consequence
of the special-fibre geometry, not a new choice of coordinates or an
assumption about rational specialization. -/
theorem specialBaseDivisor_affineIdeal :
    (N13SpecialDivisorCharts.ofDivisor
        N13AbelChartBase.specialBaseDivisor).affineIdeal =
      N13SpecialQuotientBasis.specialIdeal := by
  have hgraph :
      N13SpecialGraphDivisor.graphDivisor
          N13SpecialQuotientBasis.specialData
          N13SpecialQuotientBasis.specialData_u_natDegree =
        N13AbelChartBase.specialBaseDivisor := by
    apply
      N13SpecialGraphDivisor.graphDivisor_eq_special_of_mumfordIdeal_eq
    rfl
  calc
    (N13SpecialDivisorCharts.ofDivisor
          N13AbelChartBase.specialBaseDivisor).affineIdeal =
        (N13SpecialDivisorCharts.ofDivisor
          (N13SpecialGraphDivisor.graphDivisor
            N13SpecialQuotientBasis.specialData
            N13SpecialQuotientBasis.specialData_u_natDegree)).affineIdeal := by
      rw [hgraph]
    _ = N13GoodCoordinateRingTwo.mumfordIdeal
          N13SpecialQuotientBasis.specialData.u
          N13SpecialQuotientBasis.specialData.v :=
      N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_affineIdeal
        N13SpecialQuotientBasis.specialData
        N13SpecialQuotientBasis.specialData_u_natDegree
    _ = N13SpecialQuotientBasis.specialIdeal := rfl

/-! ## Translating kernel classes to the literal base fibre -/

/-- Abel equality with the nonspecial base divisor forces literal equality
of degree-two divisors.  The only alternative fibre allowed by the special
Abel model is the canonical pencil, which cannot contain the base divisor. -/
theorem divisor_eq_base_of_abel_eq
    {Δ : N13SymmetricSquareTwo.EffectiveDivisorTwo}
    (h : N13AbelFiberTwoModel.abel Δ =
      N13AbelFiberTwoModel.abel N13AbelChartBase.specialBaseDivisor) :
    Δ = N13AbelChartBase.specialBaseDivisor := by
  rcases (N13AbelFiberTwoModel.abel_eq_iff
    Δ N13AbelChartBase.specialBaseDivisor).mp h with hEq | hcanonical
  · exact hEq
  · exact (N13AbelChartBase.specialBaseDivisor_not_canonical
      hcanonical.2).elim

/-- Under the global specialization relation, translating a kernel element
by the rational base class produces an exact normalized spread with the same
special class as the explicit base spread.

This is quotient algebra only; it does not prove the global relation itself.
Its role is to feed canonical translated representatives into the later
literal-special-fibre argument. -/
theorem exactTranslated_special_eq_base
    (kernel : AddSubgroup N13RationalPointEndgame.G)
    (class_eq_iff :
      ∀ L M : N13RationalCurvePointPicardRealization.SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M)
    (z : kernel) :
    N13RationalCurvePointPicardRealization.specialClass
          (N13RationalPicardSpreadExistence.exactSpreadLine
            ((z : N13RationalPointEndgame.G) + rationalBasePic)) =
        N13RationalCurvePointPicardRealization.specialClass
          baseSpreadLine := by
  apply (class_eq_iff _ _).2
  simp only [N13RationalCurvePointPicardRealization.genericClass,
    N13RationalPicardSpreadExistence.exactSpreadLine_rationalClass,
    baseSpreadLine_rationalClass]
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  simpa only [add_sub_cancel_right] using z.property

/-- The exact normalized spread of a translated kernel element stores the
literal special base divisor, not merely its Abel class.

The previous theorem gives equality of special Abel classes; regularity of
the selected base fibre upgrades it to equality of the stored effective
divisors. -/
theorem exactTranslated_specialDivisor_eq_base
    (kernel : AddSubgroup N13RationalPointEndgame.G)
    (class_eq_iff :
      ∀ L M : N13RationalCurvePointPicardRealization.SpreadLine,
        N13RationalCurvePointPicardRealization.specialClass L =
            N13RationalCurvePointPicardRealization.specialClass M ↔
          N13RationalCurvePointPicardRealization.genericClass kernel L =
            N13RationalCurvePointPicardRealization.genericClass kernel M)
    (z : kernel) :
    ((N13RationalPicardSpreadExistence.exactSpreadLine
      ((z : N13RationalPointEndgame.G) + rationalBasePic)).realization).specialDivisor =
      N13AbelChartBase.specialBaseDivisor := by
  apply divisor_eq_base_of_abel_eq
  exact exactTranslated_special_eq_base kernel class_eq_iff z

end

end MazurProof.N13RationalAbelChartBase
