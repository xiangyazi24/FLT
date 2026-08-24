import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointPartition
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryYZLocal
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryZLocal

/-!
# The pole order of `Z/W` at the X-boundary point

At `[1:0:0:0]`, the affine coordinate `Z/X` vanishes to order two.  Setting
`Z/X = 0` in the actual X-chart local ring makes `Y/X + 1` a unit; the curve
relations then force `W/X = 0` and `(Y/X)^2 = 0`.  Thus the local quotient is
the double Artin algebra `F₂[t]/(t²)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoZProjectionXLocal

open Polynomial
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoHyperplaneArtin
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWBoundaryChartArtin
open RationalPointsN25QuotientTwoWBoundaryXLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoWBoundaryYZLocal
open RationalPointsN25QuotientTwoWBoundaryZLocal

local notation "k₂" => ZMod 2

local instance : xPrime.IsMaximal := xPrime_isMaximal
local instance : xPrime.IsPrime := xPrime_isMaximal.isPrime
local instance xzLocalRingCommRing : CommRing XLocalRing :=
  OreLocalization.instCommRing
local instance : yzPrime.IsMaximal := yzPrime_isMaximal
local instance : yzPrime.IsPrime := yzPrime_isMaximal.isPrime
local instance yzZLocalRingCommRing : CommRing YZLocalRing :=
  OreLocalization.instCommRing
local instance : zPrime.IsMaximal := zPrime_isMaximal
local instance : zPrime.IsPrime := zPrime_isMaximal.isPrime
local instance zZLocalRingCommRing : CommRing ZLocalRing :=
  OreLocalization.instCommRing

private theorem xz_quadric_relation :
    xZ + xW + xY ^ 2 + xY * xZ + xZ * xW = 0 := by
  have h := chartQuotientPoint_quadric (0 : Fin 4)
  simpa [canonicalQuadric25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, xY, xZ, xW, chartMap_X_pivot] using h

private theorem xz_cubic_relation :
    xW + xY * xZ + xY * xW + xZ * xW + xY * xZ * xW +
      xZ ^ 2 * xW + xZ * xW ^ 2 = 0 := by
  have h := chartQuotientPoint_cubic (0 : Fin 4)
  simpa [canonicalCubic25CharTwo, chartQuotientPoint,
    mappedAmbientPoint, xY, xZ, xW, chartMap_X_pivot] using h

private def xzArtinCoordinates : Coordinates4 DoubleArtin :=
  ⟨1, doubleRoot, 0, 0⟩

private def xzArtinAffineEval :
    AffineChart (0 : Fin 4) →ₐ[k₂] DoubleArtin :=
  MvPolynomial.aeval
    (fun j => coordinates4ToFun xzArtinCoordinates j.1)

private theorem xzArtinAffineEval_comp_dehomogenize :
    xzArtinAffineEval.toRingHom.comp (ambientDehomogenize 0) =
      MvPolynomial.eval₂Hom (algebraMap k₂ DoubleArtin)
        (coordinates4ToFun xzArtinCoordinates) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [xzArtinAffineEval, ambientDehomogenize]
  · intro j
    fin_cases j <;>
      simp [xzArtinAffineEval, ambientDehomogenize,
        dehomogenizedVariable, xzArtinCoordinates, coordinates4ToFun]

private theorem mappedAmbientPoint_xzArtinEval :
    mappedAmbientPoint
        (MvPolynomial.eval₂Hom (algebraMap k₂ DoubleArtin)
          (coordinates4ToFun xzArtinCoordinates)) =
      xzArtinCoordinates := by
  simp [mappedAmbientPoint, xzArtinCoordinates, coordinates4ToFun]

private theorem xzArtinAffineEval_quadric :
    xzArtinAffineEval (chartAffineQuadric 0) = 0 := by
  change (xzArtinAffineEval.toRingHom.comp (ambientDehomogenize 0))
    canonicalQuadricPolynomial25Two = 0
  rw [xzArtinAffineEval_comp_dehomogenize, map_canonicalQuadric,
    mappedAmbientPoint_xzArtinEval]
  dsimp [canonicalQuadric25CharTwo, xzArtinCoordinates]
  simpa using doubleRoot_sq

private theorem xzArtinAffineEval_cubic :
    xzArtinAffineEval (chartAffineCubic 0) = 0 := by
  change (xzArtinAffineEval.toRingHom.comp (ambientDehomogenize 0))
    canonicalCubicPolynomial25Two = 0
  rw [xzArtinAffineEval_comp_dehomogenize, map_canonicalCubic,
    mappedAmbientPoint_xzArtinEval]
  simp [canonicalCubic25CharTwo, xzArtinCoordinates]

private theorem xzEquationIdeal_le_artinKer :
    chartAffineEquationIdeal 0 ≤
      RingHom.ker xzArtinAffineEval.toRingHom := by
  rw [chartAffineEquationIdeal, chartAffineRelation_range]
  refine Ideal.span_le.2 ?_
  intro p hp
  rcases hp with rfl | rfl
  · exact xzArtinAffineEval_quadric
  · exact xzArtinAffineEval_cubic

private noncomputable def xzChartToDouble :
    XChartRing →ₐ[k₂] DoubleArtin :=
  Ideal.Quotient.liftₐ (chartAffineEquationIdeal 0) xzArtinAffineEval
    (fun _ hp => RingHom.mem_ker.mp (xzEquationIdeal_le_artinKer hp))

@[simp]
private theorem xzChartToDouble_xY :
    xzChartToDouble xY = doubleRoot := by
  simp [xzChartToDouble, xY, chartMap, xzArtinAffineEval,
    ambientDehomogenize, dehomogenizedVariable, xzArtinCoordinates,
    coordinates4ToFun]

@[simp]
private theorem xzChartToDouble_xZ : xzChartToDouble xZ = 0 := by
  simp [xzChartToDouble, xZ, chartMap, xzArtinAffineEval,
    ambientDehomogenize, dehomogenizedVariable, xzArtinCoordinates,
    coordinates4ToFun]

@[simp]
private theorem xzChartToDouble_xW : xzChartToDouble xW = 0 := by
  simp [xzChartToDouble, xW, chartMap, xzArtinAffineEval,
    ambientDehomogenize, dehomogenizedVariable, xzArtinCoordinates,
    coordinates4ToFun]

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

private theorem otherCoordinate_zero_cases
    (j : OtherCoordinate (0 : Fin 4)) :
    j = ⟨1, by decide⟩ ∨ j = ⟨2, by decide⟩ ∨
      j = ⟨3, by decide⟩ := by
  rcases j with ⟨j, hj⟩
  fin_cases j
  · exact (hj rfl).elim
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Or.inl (Subtype.ext rfl))
  · exact Or.inr (Or.inr (Subtype.ext rfl))

private theorem doubleResidueAlg_comp_xzChartToDouble :
    doubleResidueAlg.comp xzChartToDouble = xChartEval := by
  apply Ideal.Quotient.algHom_ext
  ext j
  rcases otherCoordinate_zero_cases j with rfl | rfl | rfl
  · simp only [AlgHom.comp_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 0))
          (MvPolynomial.X (⟨1, by decide⟩ : OtherCoordinate 0)) = xY := by
      simp [xY, chartMap, ambientDehomogenize, dehomogenizedVariable]
    rw [hgen, xzChartToDouble_xY, xChartEval_xY,
      doubleResidueAlg_doubleRoot]
  · simp only [AlgHom.comp_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 0))
          (MvPolynomial.X (⟨2, by decide⟩ : OtherCoordinate 0)) = xZ := by
      simp [xZ, chartMap, ambientDehomogenize, dehomogenizedVariable]
    rw [hgen, xzChartToDouble_xZ, xChartEval_xZ, map_zero]
  · simp only [AlgHom.comp_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 0))
          (MvPolynomial.X (⟨3, by decide⟩ : OtherCoordinate 0)) = xW := by
      simp [xW, chartMap, ambientDehomogenize, dehomogenizedVariable]
    rw [hgen, xzChartToDouble_xW, xChartEval_xW, map_zero]

private theorem xzChartToDouble_isUnit_of_primeCompl
    (s : xPrime.primeCompl) :
    IsUnit (xzChartToDouble (s : XChartRing)) := by
  have hsnot : (s : XChartRing) ∉ xPrime :=
    Ideal.mem_primeCompl_iff.mp s.2
  have hres_ne : xChartEval (s : XChartRing) ≠ 0 := by
    intro hzero
    exact hsnot (RingHom.mem_ker.mpr hzero)
  let u : DoubleArtin :=
    algebraMap k₂ DoubleArtin (xChartEval (s : XChartRing))
  have hu : IsUnit u :=
    (isUnit_iff_ne_zero.mpr hres_ne).map
      (algebraMap k₂ DoubleArtin : k₂ →+* DoubleArtin)
  have hdiff : xzChartToDouble (s : XChartRing) - u ∈
      Ideal.span {doubleRoot} := by
    rw [← doubleResidue_ker, RingHom.mem_ker]
    change doubleResidueAlg (xzChartToDouble (s : XChartRing) - u) = 0
    rw [map_sub]
    have hcomp := DFunLike.congr_fun
      doubleResidueAlg_comp_xzChartToDouble (s : XChartRing)
    change doubleResidueAlg (xzChartToDouble (s : XChartRing)) =
      xChartEval (s : XChartRing) at hcomp
    rw [hcomp]
    change xChartEval (s : XChartRing) -
      doubleResidueAlg
        (algebraMap k₂ DoubleArtin (xChartEval (s : XChartRing))) = 0
    rw [doubleResidueAlg.commutes]
    exact sub_self _
  have hnil : IsNilpotent (xzChartToDouble (s : XChartRing) - u) :=
    doubleRootIdeal_isNilpotent hdiff
  have hunit : IsUnit (u + (xzChartToDouble (s : XChartRing) - u)) :=
    hnil.isUnit_add_left_of_commute hu
      (Commute.all (xzChartToDouble (s : XChartRing) - u) u)
  convert hunit using 1
  ring

private noncomputable def xLocalToDouble : XLocalRing →ₐ[k₂] DoubleArtin :=
  IsLocalization.liftAlgHom
    (A := k₂) (R := XChartRing) (S := XLocalRing)
    (P := DoubleArtin) (f := xzChartToDouble)
    xzChartToDouble_isUnit_of_primeCompl

/-- The germ of `Z/X` at `[1:0:0:0]`. -/
noncomputable def xZGerm : XLocalRing :=
  algebraMap XChartRing XLocalRing xZ

/-- The principal ideal generated by the germ of `Z/X`. -/
def xZGermIdeal : Ideal XLocalRing := Ideal.span {xZGerm}

private theorem xZGerm_mem_localToDouble_ker :
    xZGerm ∈ RingHom.ker xLocalToDouble.toRingHom := by
  rw [RingHom.mem_ker]
  simp [xZGerm, xLocalToDouble]

private theorem xZGermIdeal_le_localToDouble_ker :
    xZGermIdeal ≤ RingHom.ker xLocalToDouble.toRingHom := by
  rw [xZGermIdeal, Ideal.span_le]
  intro a ha
  simp only [Set.mem_singleton_iff] at ha
  subst a
  exact xZGerm_mem_localToDouble_ker

private noncomputable def xZLocalQuotToDouble :
    (XLocalRing ⧸ xZGermIdeal) →ₐ[k₂] DoubleArtin :=
  Ideal.Quotient.liftₐ xZGermIdeal xLocalToDouble
    (fun _ ha => RingHom.mem_ker.mp (xZGermIdeal_le_localToDouble_ker ha))

private noncomputable def xZLocalQuot :
    XLocalRing →ₐ[k₂] (XLocalRing ⧸ xZGermIdeal) :=
  Ideal.Quotient.mkₐ k₂ xZGermIdeal

private def qY : XLocalRing ⧸ xZGermIdeal :=
  Ideal.Quotient.mk xZGermIdeal
    (algebraMap XChartRing XLocalRing xY)

private def qZ : XLocalRing ⧸ xZGermIdeal :=
  Ideal.Quotient.mk xZGermIdeal
    (algebraMap XChartRing XLocalRing xZ)

private def qW : XLocalRing ⧸ xZGermIdeal :=
  Ideal.Quotient.mk xZGermIdeal
    (algebraMap XChartRing XLocalRing xW)

private theorem qZ_eq_zero : qZ = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton xZGerm)

private theorem q_quadric_relation : qW + qY ^ 2 = 0 := by
  have h := congrArg
    (fun a : XChartRing => xZLocalQuot
      (algebraMap XChartRing XLocalRing a)) xz_quadric_relation
  simp only [map_add, map_mul, map_pow, map_zero] at h
  change qZ + qW + qY ^ 2 + qY * qZ + qZ * qW = 0 at h
  rw [qZ_eq_zero] at h
  linear_combination h

private theorem q_cubic_relation : qW + qY * qW = 0 := by
  have h := congrArg
    (fun a : XChartRing => xZLocalQuot
      (algebraMap XChartRing XLocalRing a)) xz_cubic_relation
  simp only [map_add, map_mul, map_pow, map_zero] at h
  change qW + qY * qZ + qY * qW + qZ * qW + qY * qZ * qW +
    qZ ^ 2 * qW + qZ * qW ^ 2 = 0 at h
  rw [qZ_eq_zero] at h
  linear_combination h

private theorem xY_add_one_not_mem_xPrime : xY + 1 ∉ xPrime := by
  rw [xPrime, RingHom.mem_ker]
  simp

private theorem qY_add_one_isUnit : IsUnit (qY + 1) := by
  let s : xPrime.primeCompl :=
    ⟨xY + 1, xY_add_one_not_mem_xPrime⟩
  have hs : IsUnit (algebraMap XChartRing XLocalRing (xY + 1)) :=
    IsLocalization.map_units XLocalRing s
  have hmap := hs.map xZLocalQuot.toRingHom
  change IsUnit (xZLocalQuot
    (algebraMap XChartRing XLocalRing (xY + 1))) at hmap
  have heq : xZLocalQuot
      (algebraMap XChartRing XLocalRing (xY + 1)) = qY + 1 := by
    simp [xZLocalQuot, qY]
  rw [heq] at hmap
  exact hmap

private theorem qW_eq_zero : qW = 0 := by
  have hmul : qW * (qY + 1) = 0 := by
    linear_combination q_cubic_relation
  exact (IsUnit.mul_left_eq_zero qY_add_one_isUnit).1 hmul

private theorem qY_sq : qY ^ 2 = 0 := by
  linear_combination q_quadric_relation - qW_eq_zero

@[simp]
private theorem xZLocalQuotToDouble_qY :
    xZLocalQuotToDouble qY = doubleRoot := by
  change xLocalToDouble (algebraMap XChartRing XLocalRing xY) = doubleRoot
  rw [xLocalToDouble, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  exact xzChartToDouble_xY

@[simp]
private theorem xZLocalQuotToDouble_qZ :
    xZLocalQuotToDouble qZ = 0 := by
  change xLocalToDouble (algebraMap XChartRing XLocalRing xZ) = 0
  rw [xLocalToDouble, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  exact xzChartToDouble_xZ

@[simp]
private theorem xZLocalQuotToDouble_qW :
    xZLocalQuotToDouble qW = 0 := by
  change xLocalToDouble (algebraMap XChartRing XLocalRing xW) = 0
  rw [xLocalToDouble, IsLocalization.liftAlgHom_apply,
    IsLocalization.lift_eq]
  exact xzChartToDouble_xW

private noncomputable def doubleArtinToXZLocalQuot :
    DoubleArtin →ₐ[k₂] (XLocalRing ⧸ xZGermIdeal) :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : k₂[X]) ^ 2)
    (Algebra.ofId k₂ (XLocalRing ⧸ xZGermIdeal))
    qY (by simpa using qY_sq)

@[simp]
private theorem doubleArtinToXZLocalQuot_doubleRoot :
    doubleArtinToXZLocalQuot doubleRoot = qY := by
  rw [doubleArtinToXZLocalQuot, doubleRoot,
    AdjoinRoot.liftAlgHom_root]

private theorem xZLocalQuotToDouble_comp_doubleArtinToXZLocalQuot :
    xZLocalQuotToDouble.comp doubleArtinToXZLocalQuot =
      AlgHom.id k₂ DoubleArtin := by
  apply AdjoinRoot.algHom_ext
  change xZLocalQuotToDouble
    (doubleArtinToXZLocalQuot doubleRoot) = doubleRoot
  rw [doubleArtinToXZLocalQuot_doubleRoot,
    xZLocalQuotToDouble_qY]

private theorem doubleArtinToXZLocalQuot_comp_xZLocalQuotToDouble :
    doubleArtinToXZLocalQuot.comp xZLocalQuotToDouble =
      AlgHom.id k₂ (XLocalRing ⧸ xZGermIdeal) := by
  apply Ideal.Quotient.algHom_ext
  apply IsLocalization.algHom_ext (R := k₂) (A := XChartRing)
    (W := xPrime.primeCompl)
  apply Ideal.Quotient.algHom_ext
  ext j
  rcases otherCoordinate_zero_cases j with rfl | rfl | rfl
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ xZGermIdeal)
            ((Algebra.algHom k₂ XChartRing XLocalRing)
              ((Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 0))
                (MvPolynomial.X (⟨1, by decide⟩ : OtherCoordinate 0)))) = qY := by
      simp [qY, xY, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
      exact (IsScalarTower.algebraMap_apply XChartRing XLocalRing
        (XLocalRing ⧸ xZGermIdeal) _).symm
    rw [hgen, xZLocalQuotToDouble_qY,
      doubleArtinToXZLocalQuot_doubleRoot]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ xZGermIdeal)
            ((Algebra.algHom k₂ XChartRing XLocalRing)
              ((Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 0))
                (MvPolynomial.X (⟨2, by decide⟩ : OtherCoordinate 0)))) = qZ := by
      simp [qZ, xZ, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
      exact (IsScalarTower.algebraMap_apply XChartRing XLocalRing
        (XLocalRing ⧸ xZGermIdeal) _).symm
    rw [hgen, xZLocalQuotToDouble_qZ, map_zero, qZ_eq_zero]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply]
    have hgen :
        (Ideal.Quotient.mkₐ k₂ xZGermIdeal)
            ((Algebra.algHom k₂ XChartRing XLocalRing)
              ((Ideal.Quotient.mkₐ k₂ (chartAffineEquationIdeal 0))
                (MvPolynomial.X (⟨3, by decide⟩ : OtherCoordinate 0)))) = qW := by
      simp [qW, xW, chartMap, ambientDehomogenize,
        dehomogenizedVariable]
      exact (IsScalarTower.algebraMap_apply XChartRing XLocalRing
        (XLocalRing ⧸ xZGermIdeal) _).symm
    rw [hgen, xZLocalQuotToDouble_qW, map_zero, qW_eq_zero]

/-- The quotient by `Z/X` in the actual point local ring is
`F₂[t]/(t²)`. -/
noncomputable def xZLocalAlgEquivDoubleArtin :
    (XLocalRing ⧸ xZGermIdeal) ≃ₐ[k₂] DoubleArtin :=
  AlgEquiv.ofAlgHom xZLocalQuotToDouble
    doubleArtinToXZLocalQuot
    xZLocalQuotToDouble_comp_doubleArtinToXZLocalQuot
    doubleArtinToXZLocalQuot_comp_xZLocalQuotToDouble

/-- The quotient by `Z/X` has `F₂`-length two. -/
theorem xZLocal_f2_length :
    Module.length k₂ (XLocalRing ⧸ xZGermIdeal) = 2 := by
  rw [xZLocalAlgEquivDoubleArtin.toLinearEquiv.length_eq]
  letI : Module.Finite k₂ DoubleArtin :=
    (Polynomial.monic_X_pow 2).finite_adjoinRoot
  rw [Module.length_eq_finrank, doubleArtin_finrank]
  norm_num

private noncomputable def xPrimeQuotientAlgEquivF2 :
    (XChartRing ⧸ xPrime) ≃ₐ[k₂] k₂ := by
  change (XChartRing ⧸ RingHom.ker xChartEval.toRingHom) ≃ₐ[k₂] k₂
  exact Ideal.quotientKerAlgEquivOfSurjective xChartEval_surjective

private noncomputable def xPrimeLocalResidueAlgEquiv :
    (XChartRing ⧸ xPrime) ≃ₐ[k₂]
      IsLocalRing.ResidueField XLocalRing := by
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal xPrime XLocalRing
  exact
    { e with
      commutes' := by
        intro c
        change e (Ideal.Quotient.mk xPrime
          (algebraMap k₂ XChartRing c)) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal XLocalRing)
              (algebraMap k₂ XLocalRing c)
        rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
        rfl }

private noncomputable def xLocalResidueAlgEquivF2 :
    IsLocalRing.ResidueField XLocalRing ≃ₐ[k₂] k₂ :=
  xPrimeLocalResidueAlgEquiv.symm.trans xPrimeQuotientAlgEquivF2

private theorem xLocalResidue_algebraMap_surjective :
    Function.Surjective
      (algebraMap k₂ (IsLocalRing.ResidueField XLocalRing)) := by
  intro y
  refine ⟨xLocalResidueAlgEquivF2 y, ?_⟩
  apply xLocalResidueAlgEquivF2.injective
  simp

private theorem xResidueExtension_algebraMap_surjective :
    Function.Surjective
      (algebraMap (IsLocalRing.ResidueField k₂)
        (IsLocalRing.ResidueField XLocalRing)) := by
  intro y
  obtain ⟨c, rfl⟩ := xLocalResidue_algebraMap_surjective y
  refine ⟨algebraMap k₂ (IsLocalRing.ResidueField k₂) c, ?_⟩
  exact IsScalarTower.algebraMap_apply k₂
    (IsLocalRing.ResidueField k₂)
    (IsLocalRing.ResidueField XLocalRing) c

private theorem xResidueExtension_length_one :
    Module.length (IsLocalRing.ResidueField k₂)
      (IsLocalRing.ResidueField XLocalRing) = 1 := by
  let e : IsLocalRing.ResidueField k₂ ≃ₐ[IsLocalRing.ResidueField k₂]
      IsLocalRing.ResidueField XLocalRing :=
    AlgEquiv.ofBijective (Algebra.ofId _ _)
      ⟨RingHom.injective _, xResidueExtension_algebraMap_surjective⟩
  exact e.toLinearEquiv.length_eq.symm.trans (Module.length_eq_one _ _)

/-- The quotient by `Z/X` has local-ring length two. -/
theorem xZLocal_local_length :
    Module.length XLocalRing (XLocalRing ⧸ xZGermIdeal) = 2 := by
  have h := IsLocalRing.length_restrictScalars
    k₂ XLocalRing (XLocalRing ⧸ xZGermIdeal)
  rw [xResidueExtension_length_one, mul_one] at h
  exact h.symm.trans xZLocal_f2_length

/-- The order of `Z/X` at `[1:0:0:0]` is two. -/
theorem xZGerm_ord_eq_two : Ring.ord XLocalRing xZGerm = 2 := by
  unfold Ring.ord
  change Module.length XLocalRing (XLocalRing ⧸ xZGermIdeal) = 2
  exact xZLocal_local_length

/-! ## The numerator `Z` at the other two boundary points -/

/-- The germ of `Z/Y` at `[0:1:1:0]`. -/
noncomputable def yzZGerm : YZLocalRing :=
  algebraMap YChartRing YZLocalRing yZ

private theorem yZ_not_mem_yzPrime : yZ ∉ yzPrime := by
  rw [yzPrime, RingHom.mem_ker]
  simp

theorem yzZGerm_isUnit : IsUnit yzZGerm := by
  let s : yzPrime.primeCompl := ⟨yZ, yZ_not_mem_yzPrime⟩
  exact IsLocalization.map_units YZLocalRing s

/-- Since `Z/Y` is a unit at `[0:1:1:0]`, it has order zero. -/
theorem yzZGerm_ord_eq_zero : Ring.ord YZLocalRing yzZGerm = 0 :=
  Ring.ord_of_isUnit yzZGerm_isUnit

/-- On the `Z` chart the numerator `Z/Z` is one, hence has order zero. -/
theorem zUnitGerm_ord_eq_zero : Ring.ord ZLocalRing (1 : ZLocalRing) = 0 :=
  Ring.ord_one ZLocalRing

/-! ## Pole multiplicities of the affine projection `Z/W` -/

/-- At X, `W/X` vanishes one order more than `Z/X`. -/
theorem xWGerm_ord_eq_xZGerm_ord_add_one :
    Ring.ord XLocalRing xWGerm = Ring.ord XLocalRing xZGerm + 1 := by
  rw [xWGerm_ord_eq_three, xZGerm_ord_eq_two]
  norm_num

/-- At YZ, `W/Y` vanishes one order more than the unit `Z/Y`. -/
theorem yzWGerm_ord_eq_yzZGerm_ord_add_one :
    Ring.ord YZLocalRing yzWGerm = Ring.ord YZLocalRing yzZGerm + 1 := by
  rw [yzWGerm_ord_eq_one, yzZGerm_ord_eq_zero]
  norm_num

/-- At Z, `W/Z` has order two while `Z/Z` is a unit. -/
theorem zWGerm_ord_eq_zUnitGerm_ord_add_two :
    Ring.ord ZLocalRing zWGerm = Ring.ord ZLocalRing (1 : ZLocalRing) + 2 := by
  rw [zWGerm_ord_eq_two, zUnitGerm_ord_eq_zero]
  norm_num

/-- The pole multiplicity of the affine coordinate `Z/W` at each of the
three points over infinity. -/
def zProjectionPoleMultiplicity :
    RationalPointsN25QuotientTwoClosedPointPartition.FullBoundaryTag25Two → ℕ
  | .X => 1
  | .YZ => 1
  | .Z => 2

/-- The three pole multiplicities have total degree four, matching the
quartic projection to the `z`-line. -/
theorem zProjectionPoleMultiplicity_total :
    zProjectionPoleMultiplicity .X +
      zProjectionPoleMultiplicity .YZ +
      zProjectionPoleMultiplicity .Z = 4 := by
  rfl

end MazurProof.RationalPointsN25QuotientTwoZProjectionXLocal
