import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointEvaluation
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryClosedPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryXLocal

/-!
# The Z-boundary quotient in the local curve ring

On the standard `Z != 0` chart, imposing `W/Z = 0` leaves the equation
`y^2 (y + 1) = 0`.  The chart contains both boundary points with `Z != 0`.
At `[0:0:1:0]`, however, `y + 1` is invertible, so the local quotient has
`y^2 = 0` and is the length-two Artin algebra `F₂[t]/(t²)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

open Polynomial
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoCanonicalDivisor
open RationalPointsN25QuotientTwoClosedPointEvaluation
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoHyperplaneArtin
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWBoundaryXLocal

local notation "k₂" => ZMod 2

/-- The actual curve coordinate ring on the standard projective `Z` chart. -/
abbrev ZChartRing := ChartQuotient (2 : Fin 4)

private def zX : ZChartRing := chartMap 2 (MvPolynomial.X 0)
private def zY : ZChartRing := chartMap 2 (MvPolynomial.X 1)
/-- The restriction `W/Z` of the homogeneous coordinate `W`. -/
def zW : ZChartRing := chartMap 2 (MvPolynomial.X 3)

private theorem z_quadric_relation :
    zX + zX * zW + zY ^ 2 + zY + zW = 0 := by
  have h := chartQuotientPoint_quadric (2 : Fin 4)
  simpa [canonicalQuadric25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, zX, zY, zW, chartMap_X_pivot] using h

private theorem z_cubic_relation :
    zX ^ 2 * zW + zX * zY + zX * zY * zW + zX * zW +
      zY * zW + zW + zW ^ 2 = 0 := by
  have h := chartQuotientPoint_cubic (2 : Fin 4)
  simpa [canonicalCubic25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, zX, zY, zW, chartMap_X_pivot] using h

private def zArtinCoordinates : Coordinates4 DoubleArtin :=
  ⟨doubleRoot, doubleRoot, 1, 0⟩

private def zArtinAffineEval :
    AffineChart (2 : Fin 4) →ₐ[k₂] DoubleArtin :=
  MvPolynomial.aeval
    (fun j => coordinates4ToFun zArtinCoordinates j.1)

private theorem zArtinAffineEval_comp_dehomogenize :
    zArtinAffineEval.toRingHom.comp (ambientDehomogenize 2) =
      MvPolynomial.eval₂Hom (algebraMap k₂ DoubleArtin)
        (coordinates4ToFun zArtinCoordinates) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [zArtinAffineEval, ambientDehomogenize]
  · intro j
    fin_cases j <;>
      simp [zArtinAffineEval, ambientDehomogenize,
        dehomogenizedVariable, zArtinCoordinates, coordinates4ToFun]

private theorem mappedAmbientPoint_zArtinEval :
    mappedAmbientPoint
        (MvPolynomial.eval₂Hom (algebraMap k₂ DoubleArtin)
          (coordinates4ToFun zArtinCoordinates)) =
      zArtinCoordinates := by
  simp [mappedAmbientPoint, zArtinCoordinates, coordinates4ToFun]

private theorem zArtinAffineEval_quadric :
    zArtinAffineEval (chartAffineQuadric 2) = 0 := by
  change (zArtinAffineEval.toRingHom.comp (ambientDehomogenize 2))
    canonicalQuadricPolynomial25Two = 0
  rw [zArtinAffineEval_comp_dehomogenize, map_canonicalQuadric,
    mappedAmbientPoint_zArtinEval]
  dsimp [canonicalQuadric25CharTwo, zArtinCoordinates]
  have htwo : (2 : DoubleArtin) = 0 := CharP.cast_eq_zero DoubleArtin 2
  linear_combination doubleRoot_sq + doubleRoot * htwo

private theorem zArtinAffineEval_cubic :
    zArtinAffineEval (chartAffineCubic 2) = 0 := by
  change (zArtinAffineEval.toRingHom.comp (ambientDehomogenize 2))
    canonicalCubicPolynomial25Two = 0
  rw [zArtinAffineEval_comp_dehomogenize, map_canonicalCubic,
    mappedAmbientPoint_zArtinEval]
  dsimp [canonicalCubic25CharTwo, zArtinCoordinates]
  linear_combination doubleRoot_sq

private theorem zEquationIdeal_le_artinKer :
    chartAffineEquationIdeal 2 ≤
      RingHom.ker zArtinAffineEval.toRingHom := by
  rw [chartAffineEquationIdeal, chartAffineRelation_range]
  refine Ideal.span_le.2 ?_
  intro p hp
  rcases hp with rfl | rfl
  · exact zArtinAffineEval_quadric
  · exact zArtinAffineEval_cubic

private noncomputable def zChartToDouble :
    ZChartRing →ₐ[k₂] DoubleArtin :=
  Ideal.Quotient.liftₐ (chartAffineEquationIdeal 2) zArtinAffineEval
    (fun _ hp => RingHom.mem_ker.mp (zEquationIdeal_le_artinKer hp))

@[simp]
private theorem zChartToDouble_zX : zChartToDouble zX = doubleRoot := by
  simp [zChartToDouble, zX, chartMap, zArtinAffineEval,
    ambientDehomogenize, dehomogenizedVariable, zArtinCoordinates,
    coordinates4ToFun]

@[simp]
private theorem zChartToDouble_zY : zChartToDouble zY = doubleRoot := by
  simp [zChartToDouble, zY, chartMap, zArtinAffineEval,
    ambientDehomogenize, dehomogenizedVariable, zArtinCoordinates,
    coordinates4ToFun]

@[simp]
private theorem zChartToDouble_zW : zChartToDouble zW = 0 := by
  simp [zChartToDouble, zW, chartMap, zArtinAffineEval,
    ambientDehomogenize, dehomogenizedVariable, zArtinCoordinates,
    coordinates4ToFun]

private def zChartPoint : CurvePointOnChart (2 : Fin 4) k₂ :=
  ⟨hyperplanePointZ, rfl⟩

/-- Evaluation of the actual `Z` chart at `[0:0:1:0]`. -/
noncomputable def zPointEval : ZChartRing →ₐ[k₂] k₂ :=
  chartQuotientEvalAlgHom 2 zChartPoint

theorem zPointEval_surjective : Function.Surjective zPointEval := by
  intro c
  refine ⟨algebraMap k₂ ZChartRing c, ?_⟩
  exact zPointEval.commutes c

/-- The maximal ideal of `[0:0:1:0]` in the actual `Z` chart. -/
def zPrime : Ideal ZChartRing := RingHom.ker zPointEval.toRingHom

theorem zPrime_isMaximal : zPrime.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    zPointEval.toRingHom zPointEval_surjective

local instance : zPrime.IsMaximal := zPrime_isMaximal
local instance : zPrime.IsPrime := zPrime_isMaximal.isPrime

@[simp]
private theorem zPointEval_zX : zPointEval zX = 0 := by
  rw [zPointEval, zX, chartMap]
  change chartPointAffineEval 2 zChartPoint
    (ambientDehomogenize 2 (MvPolynomial.X 0)) = 0
  simp [ambientDehomogenize, dehomogenizedVariable, chartPointAffineEval,
    zChartPoint, hyperplanePointZ, coordinates4ToFun,
    normalizedCoordinates25, NormalizedProjective4.coordinates,
    fieldBinaryOperations]

@[simp]
private theorem zPointEval_zY : zPointEval zY = 0 := by
  rw [zPointEval, zY, chartMap]
  change chartPointAffineEval 2 zChartPoint
    (ambientDehomogenize 2 (MvPolynomial.X 1)) = 0
  simp [ambientDehomogenize, dehomogenizedVariable, chartPointAffineEval,
    zChartPoint, hyperplanePointZ, coordinates4ToFun,
    normalizedCoordinates25, NormalizedProjective4.coordinates,
    fieldBinaryOperations]

@[simp]
private theorem zPointEval_zW : zPointEval zW = 0 := by
  rw [zPointEval, zW, chartMap]
  change chartPointAffineEval 2 zChartPoint
    (ambientDehomogenize 2 (MvPolynomial.X 3)) = 0
  simp [ambientDehomogenize, dehomogenizedVariable, chartPointAffineEval,
    zChartPoint, hyperplanePointZ, coordinates4ToFun,
    normalizedCoordinates25, NormalizedProjective4.coordinates,
    fieldBinaryOperations]

private theorem doublePolynomialIdeal_le_evalKer :
    Ideal.span {(Polynomial.X : k₂[X]) ^ 2} ≤
      RingHom.ker (Polynomial.evalRingHom 0) := by
  refine Ideal.span_le.2 ?_
  intro p hp
  simp only [Set.mem_singleton_iff] at hp
  subst p
  simp [RingHom.mem_ker]

private noncomputable def doubleResidue : DoubleArtin →+* k₂ :=
  Ideal.Quotient.lift
    (Ideal.span {(Polynomial.X : k₂[X]) ^ 2})
    (Polynomial.evalRingHom 0)
    (fun _ hp => RingHom.mem_ker.mp (doublePolynomialIdeal_le_evalKer hp))

private noncomputable def doubleResidueAlg : DoubleArtin →ₐ[k₂] k₂ where
  __ := doubleResidue
  commutes' c := by
    change Polynomial.eval 0 (Polynomial.C c) = c
    simp

@[simp]
private theorem doubleResidueAlg_doubleRoot :
    doubleResidueAlg doubleRoot = 0 := by
  change Polynomial.eval 0 Polynomial.X = 0
  simp

private theorem doubleResidue_ker :
    RingHom.ker doubleResidue = Ideal.span {doubleRoot} := by
  change RingHom.ker
    (Ideal.Quotient.lift
      (Ideal.span {(Polynomial.X : k₂[X]) ^ 2})
      (Polynomial.evalRingHom 0) _) = _
  rw [Ideal.ker_quotient_lift, Polynomial.ker_evalRingHom]
  simp only [Ideal.map_span, Set.image_singleton]
  simp [doubleRoot, AdjoinRoot.root, AdjoinRoot.mk]
  rfl

private theorem doubleRootIdeal_isNilpotent
    {a : DoubleArtin} (ha : a ∈ Ideal.span {doubleRoot}) :
    IsNilpotent a := by
  rw [Ideal.mem_span_singleton] at ha
  rcases ha with ⟨b, rfl⟩
  refine ⟨2, ?_⟩
  rw [mul_pow, doubleRoot_sq, zero_mul]

private theorem doubleResidueAlg_comp_zChartToDouble :
    doubleResidueAlg.comp zChartToDouble = zPointEval := by
  apply Ideal.Quotient.algHom_ext
  ext j
  rcases j with ⟨j, hj⟩
  fin_cases j
  · simp only [AlgHom.comp_apply]
    simp [zChartToDouble, zArtinAffineEval, zArtinCoordinates,
      zPointEval, zChartPoint, chartQuotientEvalAlgHom,
      chartQuotientEval, chartPointAffineEval, hyperplanePointZ,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      fieldBinaryOperations, coordinates4ToFun]
  · simp only [AlgHom.comp_apply]
    simp [zChartToDouble, zArtinAffineEval, zArtinCoordinates,
      zPointEval, zChartPoint, chartQuotientEvalAlgHom,
      chartQuotientEval, chartPointAffineEval, hyperplanePointZ,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      fieldBinaryOperations, coordinates4ToFun]
  · exact (hj rfl).elim
  · simp only [AlgHom.comp_apply]
    simp [zChartToDouble, zArtinAffineEval, zArtinCoordinates,
      zPointEval, zChartPoint, chartQuotientEvalAlgHom,
      chartQuotientEval, chartPointAffineEval, hyperplanePointZ,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      fieldBinaryOperations, coordinates4ToFun]

private theorem zChartToDouble_isUnit_of_primeCompl
    (s : zPrime.primeCompl) :
    IsUnit (zChartToDouble (s : ZChartRing)) := by
  have hsnot : (s : ZChartRing) ∉ zPrime :=
    Ideal.mem_primeCompl_iff.mp s.2
  have hres_ne : zPointEval (s : ZChartRing) ≠ 0 := by
    intro hzero
    exact hsnot (RingHom.mem_ker.mpr hzero)
  let u : DoubleArtin :=
    algebraMap k₂ DoubleArtin (zPointEval (s : ZChartRing))
  have hu : IsUnit u :=
    (isUnit_iff_ne_zero.mpr hres_ne).map
      (algebraMap k₂ DoubleArtin : k₂ →+* DoubleArtin)
  have hdiff : zChartToDouble (s : ZChartRing) - u ∈
      Ideal.span {doubleRoot} := by
    rw [← doubleResidue_ker, RingHom.mem_ker]
    change doubleResidueAlg (zChartToDouble (s : ZChartRing) - u) = 0
    rw [map_sub]
    have hcomp := DFunLike.congr_fun
      doubleResidueAlg_comp_zChartToDouble (s : ZChartRing)
    change doubleResidueAlg (zChartToDouble (s : ZChartRing)) =
      zPointEval (s : ZChartRing) at hcomp
    rw [hcomp]
    change zPointEval (s : ZChartRing) -
      doubleResidueAlg
        (algebraMap k₂ DoubleArtin (zPointEval (s : ZChartRing))) = 0
    rw [doubleResidueAlg.commutes]
    exact sub_self _
  have hnil : IsNilpotent (zChartToDouble (s : ZChartRing) - u) :=
    doubleRootIdeal_isNilpotent hdiff
  have hunit : IsUnit (u + (zChartToDouble (s : ZChartRing) - u)) :=
    hnil.isUnit_add_left_of_commute hu
      (Commute.all (zChartToDouble (s : ZChartRing) - u) u)
  convert hunit using 1
  ring

/-- The local ring of the actual `Z` chart at `[0:0:1:0]`. -/
abbrev ZLocalRing := Localization.AtPrime zPrime

local instance zLocalRingCommRing : CommRing ZLocalRing :=
  OreLocalization.instCommRing

private noncomputable def zLocalToDouble :
    ZLocalRing →ₐ[k₂] DoubleArtin :=
  IsLocalization.liftAlgHom
    (A := k₂) (R := ZChartRing) (S := ZLocalRing)
    (P := DoubleArtin) (f := zChartToDouble)
    zChartToDouble_isUnit_of_primeCompl

/-- The germ of `W/Z` in the local curve ring. -/
noncomputable def zWGerm : ZLocalRing :=
  algebraMap ZChartRing ZLocalRing zW

/-- The principal ideal generated by the germ of `W/Z`. -/
def zWGermIdeal : Ideal ZLocalRing := Ideal.span {zWGerm}

private theorem zWGerm_mem_localToDouble_ker :
    zWGerm ∈ RingHom.ker zLocalToDouble.toRingHom := by
  rw [RingHom.mem_ker]
  simp [zWGerm, zLocalToDouble]

private theorem zWGermIdeal_le_localToDouble_ker :
    zWGermIdeal ≤ RingHom.ker zLocalToDouble.toRingHom := by
  rw [zWGermIdeal, Ideal.span_le]
  intro a ha
  simp only [Set.mem_singleton_iff] at ha
  subst a
  exact zWGerm_mem_localToDouble_ker

/-- The induced map from the local quotient by the germ of `W/Z`. -/
noncomputable def zLocalBoundaryToDouble :
    (ZLocalRing ⧸ zWGermIdeal) →ₐ[k₂] DoubleArtin :=
  Ideal.Quotient.liftₐ zWGermIdeal zLocalToDouble
    (fun _ ha => RingHom.mem_ker.mp (zWGermIdeal_le_localToDouble_ker ha))

private noncomputable def zLocalBoundaryQuot :
    ZLocalRing →ₐ[k₂] (ZLocalRing ⧸ zWGermIdeal) :=
  Ideal.Quotient.mkₐ k₂ zWGermIdeal

private def qX : ZLocalRing ⧸ zWGermIdeal :=
  Ideal.Quotient.mk zWGermIdeal (algebraMap ZChartRing ZLocalRing zX)

private def qY : ZLocalRing ⧸ zWGermIdeal :=
  Ideal.Quotient.mk zWGermIdeal (algebraMap ZChartRing ZLocalRing zY)

private def qW : ZLocalRing ⧸ zWGermIdeal :=
  Ideal.Quotient.mk zWGermIdeal (algebraMap ZChartRing ZLocalRing zW)

private theorem qW_eq_zero : qW = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton zWGerm)

private theorem q_quadric_relation : qX + qY ^ 2 + qY = 0 := by
  have h := congrArg
    (fun a : ZChartRing => zLocalBoundaryQuot
      (algebraMap ZChartRing ZLocalRing a)) z_quadric_relation
  simp only [map_add, map_mul, map_pow, map_zero] at h
  change qX + qX * qW + qY ^ 2 + qY + qW = 0 at h
  rw [qW_eq_zero] at h
  linear_combination h

private theorem q_cubic_relation : qX * qY = 0 := by
  have h := congrArg
    (fun a : ZChartRing => zLocalBoundaryQuot
      (algebraMap ZChartRing ZLocalRing a)) z_cubic_relation
  simp only [map_add, map_mul, map_pow, map_zero] at h
  change qX ^ 2 * qW + qX * qY + qX * qY * qW + qX * qW +
    qY * qW + qW + qW ^ 2 = 0 at h
  rw [qW_eq_zero] at h
  linear_combination h

private theorem qY_sq_mul_add_one : qY ^ 2 * (qY + 1) = 0 := by
  linear_combination qY * q_quadric_relation - q_cubic_relation

private theorem zY_add_one_not_mem_zPrime : zY + 1 ∉ zPrime := by
  rw [zPrime, RingHom.mem_ker]
  simp

private theorem qY_add_one_isUnit : IsUnit (qY + 1) := by
  let s : zPrime.primeCompl :=
    ⟨zY + 1, zY_add_one_not_mem_zPrime⟩
  have hs : IsUnit (algebraMap ZChartRing ZLocalRing (zY + 1)) :=
    IsLocalization.map_units ZLocalRing s
  have hmap := hs.map zLocalBoundaryQuot.toRingHom
  change IsUnit (zLocalBoundaryQuot
    (algebraMap ZChartRing ZLocalRing (zY + 1))) at hmap
  have heq : zLocalBoundaryQuot
      (algebraMap ZChartRing ZLocalRing (zY + 1)) = qY + 1 := by
    simp [zLocalBoundaryQuot, qY]
  rw [heq] at hmap
  exact hmap

private theorem qY_sq : qY ^ 2 = 0 :=
  (IsUnit.mul_left_eq_zero qY_add_one_isUnit).1 qY_sq_mul_add_one

private theorem qX_eq_qY : qX = qY := by
  have hsum : qX + qY = 0 := by
    linear_combination q_quadric_relation - qY_sq
  have htwoCoeff : (2 : k₂) = 0 := CharP.cast_eq_zero k₂ 2
  have htwoBoundary : (2 : ZLocalRing ⧸ zWGermIdeal) = 0 := by
    calc
      (2 : ZLocalRing ⧸ zWGermIdeal) =
          algebraMap k₂ (ZLocalRing ⧸ zWGermIdeal) (2 : k₂) := by
            rw [map_ofNat]
      _ = algebraMap k₂ (ZLocalRing ⧸ zWGermIdeal) 0 := by
        rw [htwoCoeff]
      _ = 0 := map_zero _
  have hself : qY + qY = 0 := by
    linear_combination htwoBoundary * qY
  exact (eq_neg_of_add_eq_zero_left hsum).trans
    (neg_eq_iff_add_eq_zero.mpr hself)

@[simp]
private theorem zLocalBoundaryToDouble_qX :
    zLocalBoundaryToDouble qX = doubleRoot := by
  change zLocalToDouble (algebraMap ZChartRing ZLocalRing zX) = doubleRoot
  rw [zLocalToDouble, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  exact zChartToDouble_zX

@[simp]
private theorem zLocalBoundaryToDouble_qY :
    zLocalBoundaryToDouble qY = doubleRoot := by
  change zLocalToDouble (algebraMap ZChartRing ZLocalRing zY) = doubleRoot
  rw [zLocalToDouble, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  exact zChartToDouble_zY

@[simp]
private theorem zLocalBoundaryToDouble_qW :
    zLocalBoundaryToDouble qW = 0 := by
  change zLocalToDouble (algebraMap ZChartRing ZLocalRing zW) = 0
  rw [zLocalToDouble, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  exact zChartToDouble_zW

private noncomputable def doubleArtinToZLocalBoundary :
    DoubleArtin →ₐ[k₂] (ZLocalRing ⧸ zWGermIdeal) :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : k₂[X]) ^ 2)
    (Algebra.ofId k₂ (ZLocalRing ⧸ zWGermIdeal))
    qY (by simpa using qY_sq)

@[simp]
private theorem doubleArtinToZLocalBoundary_doubleRoot :
    doubleArtinToZLocalBoundary doubleRoot = qY := by
  rw [doubleArtinToZLocalBoundary, doubleRoot,
    AdjoinRoot.liftAlgHom_root]

private theorem zLocalBoundaryToDouble_comp_doubleArtinToZLocalBoundary :
    zLocalBoundaryToDouble.comp doubleArtinToZLocalBoundary =
      AlgHom.id k₂ DoubleArtin := by
  apply AdjoinRoot.algHom_ext
  change zLocalBoundaryToDouble
    (doubleArtinToZLocalBoundary doubleRoot) = doubleRoot
  rw [doubleArtinToZLocalBoundary_doubleRoot,
    zLocalBoundaryToDouble_qY]

private theorem otherCoordinate_two_cases (j : OtherCoordinate (2 : Fin 4)) :
    j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ ∨
      j = ⟨3, by decide⟩ := by
  rcases j with ⟨j, hj⟩
  fin_cases j
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Or.inl (Subtype.ext rfl))
  · exact (hj rfl).elim
  · exact Or.inr (Or.inr (Subtype.ext rfl))

private theorem doubleArtinToZLocalBoundary_comp_zLocalBoundaryToDouble :
    doubleArtinToZLocalBoundary.comp zLocalBoundaryToDouble =
      AlgHom.id k₂ (ZLocalRing ⧸ zWGermIdeal) := by
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (R := k₂) (A := ZChartRing)
    (W := zPrime.primeCompl)
  apply Ideal.Quotient.algHom_ext
  ext j
  rcases otherCoordinate_two_cases j with rfl | rfl | rfl
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ zWGermIdeal)
            ((Algebra.algHom k₂ ZChartRing ZLocalRing)
              ((Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 2))
                (MvPolynomial.X (⟨0, by decide⟩ : OtherCoordinate 2)))) = qX := by
      simp [qX, zX, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
      exact (IsScalarTower.algebraMap_apply ZChartRing ZLocalRing
        (ZLocalRing ⧸ zWGermIdeal) _).symm
    rw [hgen, zLocalBoundaryToDouble_qX,
      doubleArtinToZLocalBoundary_doubleRoot]
    exact qX_eq_qY.symm
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ zWGermIdeal)
            ((Algebra.algHom k₂ ZChartRing ZLocalRing)
              ((Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 2))
                (MvPolynomial.X (⟨1, by decide⟩ : OtherCoordinate 2)))) = qY := by
      simp [qY, zY, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
      exact (IsScalarTower.algebraMap_apply ZChartRing ZLocalRing
        (ZLocalRing ⧸ zWGermIdeal) _).symm
    rw [hgen, zLocalBoundaryToDouble_qY,
      doubleArtinToZLocalBoundary_doubleRoot]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ zWGermIdeal)
            ((Algebra.algHom k₂ ZChartRing ZLocalRing)
              ((Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 2))
                (MvPolynomial.X (⟨3, by decide⟩ : OtherCoordinate 2)))) = qW := by
      simp [qW, zW, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
      exact (IsScalarTower.algebraMap_apply ZChartRing ZLocalRing
        (ZLocalRing ⧸ zWGermIdeal) _).symm
    rw [hgen, zLocalBoundaryToDouble_qW, map_zero, qW_eq_zero]

/-- The quotient of the point local ring by `W/Z` is `F₂[t]/(t²)`. -/
noncomputable def zLocalBoundaryAlgEquivDoubleArtin :
    (ZLocalRing ⧸ zWGermIdeal) ≃ₐ[k₂] DoubleArtin :=
  AlgEquiv.ofAlgHom zLocalBoundaryToDouble
    doubleArtinToZLocalBoundary
    zLocalBoundaryToDouble_comp_doubleArtinToZLocalBoundary
    doubleArtinToZLocalBoundary_comp_zLocalBoundaryToDouble

/-- The local quotient has `F₂`-length two. -/
theorem zLocalBoundary_f2_length :
    Module.length k₂ (ZLocalRing ⧸ zWGermIdeal) = 2 := by
  rw [zLocalBoundaryAlgEquivDoubleArtin.toLinearEquiv.length_eq]
  letI : Module.Finite k₂ DoubleArtin :=
    (Polynomial.monic_X_pow 2).finite_adjoinRoot
  rw [Module.length_eq_finrank, doubleArtin_finrank]
  norm_num

private noncomputable def zPrimeQuotientAlgEquivF2 :
    (ZChartRing ⧸ zPrime) ≃ₐ[k₂] k₂ := by
  change (ZChartRing ⧸ RingHom.ker zPointEval.toRingHom) ≃ₐ[k₂] k₂
  exact Ideal.quotientKerAlgEquivOfSurjective zPointEval_surjective

private noncomputable def zPrimeLocalResidueAlgEquiv :
    (ZChartRing ⧸ zPrime) ≃ₐ[k₂]
      IsLocalRing.ResidueField ZLocalRing := by
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal zPrime ZLocalRing
  exact
    { e with
      commutes' := by
        intro c
        change e (Ideal.Quotient.mk zPrime
          (algebraMap k₂ ZChartRing c)) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal ZLocalRing)
              (algebraMap k₂ ZLocalRing c)
        rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
        rfl }

private noncomputable def zLocalResidueAlgEquivF2 :
    IsLocalRing.ResidueField ZLocalRing ≃ₐ[k₂] k₂ :=
  zPrimeLocalResidueAlgEquiv.symm.trans zPrimeQuotientAlgEquivF2

private theorem zLocalResidue_algebraMap_surjective :
    Function.Surjective
      (algebraMap k₂ (IsLocalRing.ResidueField ZLocalRing)) := by
  intro y
  refine ⟨zLocalResidueAlgEquivF2 y, ?_⟩
  apply zLocalResidueAlgEquivF2.injective
  simp

private theorem zResidueExtension_algebraMap_surjective :
    Function.Surjective
      (algebraMap (IsLocalRing.ResidueField k₂)
        (IsLocalRing.ResidueField ZLocalRing)) := by
  intro y
  obtain ⟨c, rfl⟩ := zLocalResidue_algebraMap_surjective y
  refine ⟨algebraMap k₂ (IsLocalRing.ResidueField k₂) c, ?_⟩
  exact IsScalarTower.algebraMap_apply k₂
    (IsLocalRing.ResidueField k₂)
    (IsLocalRing.ResidueField ZLocalRing) c

private theorem zResidueExtension_length_one :
    Module.length (IsLocalRing.ResidueField k₂)
      (IsLocalRing.ResidueField ZLocalRing) = 1 := by
  let e : IsLocalRing.ResidueField k₂ ≃ₐ[IsLocalRing.ResidueField k₂]
      IsLocalRing.ResidueField ZLocalRing :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨RingHom.injective _, zResidueExtension_algebraMap_surjective⟩
  exact e.toLinearEquiv.length_eq.symm.trans (Module.length_eq_one _ _)

/-- The quotient by the germ of `W/Z` has local-ring length two. -/
theorem zLocalBoundary_local_length :
    Module.length ZLocalRing (ZLocalRing ⧸ zWGermIdeal) = 2 := by
  have h := IsLocalRing.length_restrictScalars
    k₂ ZLocalRing (ZLocalRing ⧸ zWGermIdeal)
  rw [zResidueExtension_length_one, mul_one] at h
  exact h.symm.trans zLocalBoundary_f2_length

/-- The order of vanishing of `W` at `[0:0:1:0]` is two. -/
theorem zWGerm_ord_eq_two : Ring.ord ZLocalRing zWGerm = 2 := by
  unfold Ring.ord
  change Module.length ZLocalRing (ZLocalRing ⧸ zWGermIdeal) = 2
  exact zLocalBoundary_local_length

end MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal
