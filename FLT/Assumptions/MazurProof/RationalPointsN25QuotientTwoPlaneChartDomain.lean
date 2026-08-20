import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneChartBoundary
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.Regular
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Domain control for the N25 plane chart

This file proves the commutative-algebra input needed to show that the
projection denominator is a non-zero-divisor on the canonical `w = 1`
chart.  We first separate the affine variables as `F₂[z][x]`.  In that
presentation

* `D = (z + 1)x + z` is irreducible, so `F₂[z][x]/(D)` is a domain; and
* `N = x² + zx + z² + z` does not lie in `(D)`.

The second statement follows without division: if `D` divided the monic
quadratic `N`, then the leading coefficient `z + 1` of `D` would be a unit,
contrary to its positive degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoPlaneChartDomain

open Polynomial

/-- The prime field used throughout the quotient-two chart calculation. -/
abbrev PlaneField := ZMod 2

/-- The inner polynomial ring, whose variable is the affine coordinate `z`. -/
abbrev PlaneZRing := PlaneField[X]

/-- The iterated polynomial ring `F₂[z][x]`, with outer variable `x`. -/
abbrev PlaneXZRing := PlaneZRing[X]

/-- The inner polynomial variable representing `z`. -/
def planeZ : PlaneZRing := X

/-- The projection denominator, regarded as a polynomial in `x` over
`F₂[z]`. -/
def planeDenominator : PlaneXZRing :=
  C (planeZ + 1) * X + C planeZ

/-- The projection numerator, regarded as a monic quadratic in `x` over
`F₂[z]`. -/
def planeNumerator : PlaneXZRing :=
  X ^ 2 + C planeZ * X + C (planeZ ^ 2 + planeZ)

/-- The coefficient `z + 1` of `x` in the denominator is nonzero. -/
theorem planeZ_add_one_ne_zero : planeZ + 1 ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : PlaneZRing => p.coeff 1) h
  simp [planeZ, Polynomial.coeff_one] at hcoeff

/-- The two coefficients `z + 1` and `z` of the denominator are relatively
prime.  Their sum is one in characteristic two. -/
theorem planeZ_add_one_isRelPrime_planeZ :
    IsRelPrime (planeZ + 1) planeZ := by
  intro d hd1 hdz
  apply isUnit_of_dvd_one
  have hsum : d ∣ (planeZ + 1) + planeZ := dvd_add hd1 hdz
  have hone : (planeZ + 1) + planeZ = (1 : PlaneZRing) := by
    calc
      (planeZ + 1) + planeZ = planeZ + planeZ + 1 := by ac_rfl
      _ = 0 + 1 := by rw [CharTwo.add_self_eq_zero]
      _ = 1 := zero_add 1
  rwa [hone] at hsum

/-- The linear polynomial `(z + 1)x + z` is irreducible in `F₂[z][x]`. -/
theorem planeDenominator_irreducible : Irreducible planeDenominator := by
  exact irreducible_C_mul_X_add_C planeZ_add_one_ne_zero
    planeZ_add_one_isRelPrime_planeZ

/-- The denominator is prime in the iterated polynomial UFD. -/
theorem planeDenominator_prime : Prime planeDenominator := by
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
    planeDenominator_irreducible

/-- The principal denominator ideal is prime. -/
theorem planeDenominatorIdeal_isPrime :
    (Ideal.span ({planeDenominator} : Set PlaneXZRing)).IsPrime := by
  exact (Ideal.span_singleton_prime planeDenominator_prime.ne_zero).mpr
    planeDenominator_prime

/- Keep polynomial constructions over the quotient on the semiring
projection of its canonical commutative-ring structure. -/
local instance planeDenominatorQuotient_semiring :
    Semiring
      (PlaneXZRing ⧸ Ideal.span ({planeDenominator} : Set PlaneXZRing)) :=
  (Ideal.Quotient.commRing
    (Ideal.span ({planeDenominator} : Set PlaneXZRing))).toSemiring

/-- The denominator hypersurface in the `(x,z)`-plane is integral. -/
noncomputable instance planeDenominatorQuotient_isDomain :
    IsDomain (PlaneXZRing ⧸ Ideal.span ({planeDenominator} : Set PlaneXZRing)) :=
  (Ideal.Quotient.isDomain_iff_prime
    (Ideal.span ({planeDenominator} : Set PlaneXZRing))).mpr
      planeDenominatorIdeal_isPrime

/-- The numerator is monic as a polynomial in `x`. -/
theorem planeNumerator_monic : planeNumerator.Monic := by
  unfold planeNumerator
  monicity!

/-- The leading coefficient of the denominator is `z + 1`. -/
theorem planeDenominator_leadingCoeff :
    planeDenominator.leadingCoeff = planeZ + 1 := by
  exact leadingCoeff_linear planeZ_add_one_ne_zero

/-- The projection numerator does not vanish identically on the denominator
hypersurface. -/
theorem planeNumerator_not_mem_denominatorIdeal :
    planeNumerator ∉ Ideal.span ({planeDenominator} : Set PlaneXZRing) := by
  intro hmem
  have hdvd : planeDenominator ∣ planeNumerator :=
    Ideal.mem_span_singleton.mp hmem
  have hunit : IsUnit planeDenominator.leadingCoeff :=
    planeNumerator_monic.isUnit_leadingCoeff_of_dvd hdvd
  have hzunit : IsUnit (planeZ + 1) := by
    rwa [planeDenominator_leadingCoeff] at hunit
  exact (Polynomial.not_isUnit_X_add_C (1 : PlaneField)) (by
    simpa [planeZ] using hzunit)

/-- The image of the numerator is nonzero in the integral denominator
hypersurface. -/
theorem planeNumerator_quotient_ne_zero :
    Ideal.Quotient.mk (Ideal.span ({planeDenominator} : Set PlaneXZRing))
        planeNumerator ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact planeNumerator_not_mem_denominatorIdeal

/-! ## An elementary two-element regular-sequence swap -/

/-- If `D` is left-regular in a commutative ring and `c` is left-regular
modulo `(D)`, then `D` is left-regular modulo `(c)`.  This special
two-element swap needs no Noetherian, local, or Jacobson hypothesis. -/
theorem isLeftRegular_quotient_swap
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsLeftRegular D)
    (hc : IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by
  apply isLeftRegular_of_non_zero_divisor
  rintro ⟨f⟩ hf
  change Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D *
      Ideal.Quotient.mk (Ideal.span ({c} : Set B)) f = 0 at hf
  change Ideal.Quotient.mk (Ideal.span ({c} : Set B)) f = 0
  have hDf0 :
      Ideal.Quotient.mk (Ideal.span ({c} : Set B)) (D * f) = 0 := by
    simpa only [map_mul] using hf
  have hcf : c ∣ D * f :=
    (Ideal.Quotient.eq_zero_iff_dvd c (D * f)).mp hDf0
  obtain ⟨g, hg⟩ := hcf
  have hcg0 :
      Ideal.Quotient.mk (Ideal.span ({D} : Set B)) (c * g) = 0 := by
    rw [← hg]
    simp only [map_mul, Ideal.Quotient.mk_singleton_self, zero_mul]
  have hg0 :
      Ideal.Quotient.mk (Ideal.span ({D} : Set B)) g = 0 := by
    apply hc
    simpa only [map_mul, mul_zero] using hcg0
  have hDg : D ∣ g :=
    (Ideal.Quotient.eq_zero_iff_dvd D g).mp hg0
  obtain ⟨h, hgh⟩ := hDg
  apply (Ideal.Quotient.eq_zero_iff_dvd c f).mpr
  refine ⟨h, ?_⟩
  apply hD
  calc
    D * f = c * g := hg
    _ = c * (D * h) := by rw [hgh]
    _ = D * (c * h) := by ac_rfl

/-- In a commutative ring, regularity of `D` and of `c` modulo `(D)`
implies regularity of `D` modulo `(c)`. -/
theorem isRegular_quotient_swap
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsRegular D)
    (hc : IsRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by
  have hleft : IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) :=
    isLeftRegular_quotient_swap hD.left hc.left
  refine ⟨hleft, ?_⟩
  intro x y hxy
  apply hleft
  simpa [mul_comm] using hxy

/-! ## Scalar regularity in a monic root extension -/

/-- A nonzero scalar remains regular after adjoining a root of a monic
polynomial over a domain.  The monic root extension is free, hence flat,
over the base ring. -/
theorem isRegular_algebraMap_adjoinRoot_of_monic
    {A : Type*} [CommRing A] [NoZeroDivisors A]
    (p : A[X]) (hp : p.Monic) {a : A} (ha : a ≠ 0) :
    IsRegular (algebraMap A (AdjoinRoot p) a) := by
  letI : Module.Free A (AdjoinRoot p) := hp.free_adjoinRoot
  have hscalar : IsSMulRegular (AdjoinRoot p) a :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero' ha)
  have hleft : IsLeftRegular (algebraMap A (AdjoinRoot p) a) := by
    intro x y hxy
    apply hscalar
    simpa only [Algebra.smul_def] using hxy
  refine ⟨hleft, ?_⟩
  intro x y hxy
  apply hleft
  simpa only [mul_comm] using hxy

/-! ## The affine quadric as a monic root extension -/

/-- The canonical affine quadric, viewed as a monic polynomial in `y` over
`F₂[z][x]`. -/
def planeQuadricInY : PlaneXZRing[X] :=
  X ^ 2 + C (C planeZ) * X + C planeDenominator

/-- The affine quadric is monic in the separated `y` coordinate. -/
theorem planeQuadricInY_monic : planeQuadricInY.Monic := by
  unfold planeQuadricInY
  monicity!

/-- The quotient by the affine quadric in the polynomial-tower model. -/
abbrev PlaneQuadricRootRing := AdjoinRoot planeQuadricInY

/-- The projection denominator in the affine-quadric quotient. -/
def planeDenominatorClass : PlaneQuadricRootRing :=
  algebraMap PlaneXZRing PlaneQuadricRootRing planeDenominator

/-- The affine cubic, viewed as a polynomial in the separated coordinate
`y`. -/
def planeCubicInY : PlaneXZRing[X] :=
  C planeDenominator * X + C planeNumerator

/-- The class of the affine cubic modulo the affine quadric. -/
def planeCubicClass : PlaneQuadricRootRing :=
  AdjoinRoot.mk planeQuadricInY planeCubicInY

/-- The denominator stays regular after passage to the free monic quadratic
root extension. -/
theorem planeDenominatorClass_isRegular :
    IsRegular planeDenominatorClass := by
  exact isRegular_algebraMap_adjoinRoot_of_monic planeQuadricInY
    planeQuadricInY_monic planeDenominator_prime.ne_zero

/-- Mapping the principal denominator ideal into the quadric root extension
gives the principal ideal generated by the denominator class. -/
theorem map_planeDenominatorIdeal :
    Ideal.map (AdjoinRoot.of planeQuadricInY)
        (Ideal.span ({planeDenominator} : Set PlaneXZRing)) =
      Ideal.span ({planeDenominatorClass} : Set PlaneQuadricRootRing) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- The quadric after restricting its base coefficients to the integral
denominator hypersurface. -/
def planeBoundaryQuadric :
    (PlaneXZRing ⧸ Ideal.span ({planeDenominator} : Set PlaneXZRing))[X] :=
  planeQuadricInY.map
    (Ideal.Quotient.mk (Ideal.span ({planeDenominator} : Set PlaneXZRing)))

/-- Monicity survives restriction to the denominator hypersurface. -/
theorem planeBoundaryQuadric_monic : planeBoundaryQuadric.Monic := by
  exact planeQuadricInY_monic.map _

/-- The image of the numerator on the denominator hypersurface. -/
def planeBoundaryNumerator :
    PlaneXZRing ⧸ Ideal.span ({planeDenominator} : Set PlaneXZRing) :=
  Ideal.Quotient.mk (Ideal.span ({planeDenominator} : Set PlaneXZRing))
    planeNumerator

/-- The boundary numerator is a regular scalar on the restricted monic
quadratic root extension. -/
theorem planeBoundaryNumerator_isRegular :
    IsRegular
      (AdjoinRoot.of planeBoundaryQuadric planeBoundaryNumerator) := by
  exact isRegular_algebraMap_adjoinRoot_of_monic planeBoundaryQuadric
    planeBoundaryQuadric_monic planeNumerator_quotient_ne_zero

/-! ## Regularity of the cubic after imposing the denominator -/

/-- Ring equivalences preserve regular elements. -/
theorem isRegular_map_ringEquiv
    {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S)
    {r : R} (hr : IsRegular r) : IsRegular (e r) := by
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply hr.left
    have h := congrArg e.symm hxy
    simpa only [map_mul, e.symm_apply_apply] using h
  · intro x y hxy
    apply e.symm.injective
    apply hr.right
    have h := congrArg e.symm hxy
    simpa only [map_mul, e.symm_apply_apply] using h

/-- Quotienting the monic quadric root extension by the denominator agrees
with first quotienting the coefficient ring by the denominator and then
adjoining the specialized quadric root. -/
def planeDenominatorQuotientEquiv :
    PlaneQuadricRootRing ⧸
        Ideal.span ({planeDenominatorClass} : Set PlaneQuadricRootRing) ≃+*
      AdjoinRoot planeBoundaryQuadric :=
  (Ideal.quotEquivOfEq map_planeDenominatorIdeal.symm).trans
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
      (Ideal.span ({planeDenominator} : Set PlaneXZRing)) planeQuadricInY)

/-- Under coefficient base change to `D = 0`, the cubic `yD + N` becomes
the scalar `N`. -/
theorem planeDenominatorQuotientEquiv_cubic :
    planeDenominatorQuotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span ({planeDenominatorClass} : Set PlaneQuadricRootRing))
          planeCubicClass) =
      AdjoinRoot.of planeBoundaryQuadric planeBoundaryNumerator := by
  have hD :
      Ideal.Quotient.mk
        (Ideal.span ({planeDenominator} : Set PlaneXZRing))
        planeDenominator = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  rw [planeDenominatorQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  change
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
        (Ideal.span ({planeDenominator} : Set PlaneXZRing)) planeQuadricInY
        (Ideal.Quotient.mk
          ((Ideal.span ({planeDenominator} : Set PlaneXZRing)).map
            (AdjoinRoot.of planeQuadricInY))
          (AdjoinRoot.mk planeQuadricInY planeCubicInY)) = _
  rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]
  simp only [planeCubicInY, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, hD, Polynomial.C_0, zero_mul, zero_add,
    planeBoundaryNumerator, AdjoinRoot.of, RingHom.comp_apply]
  rfl

/-- The affine cubic is regular after quotienting the affine quadric root
extension by the projection denominator. -/
theorem planeCubicClass_mod_denominator_isRegular :
    IsRegular
      (Ideal.Quotient.mk
        (Ideal.span ({planeDenominatorClass} : Set PlaneQuadricRootRing))
        planeCubicClass) := by
  have hmapped :
      IsRegular
        (planeDenominatorQuotientEquiv
          (Ideal.Quotient.mk
            (Ideal.span ({planeDenominatorClass} : Set PlaneQuadricRootRing))
            planeCubicClass)) := by
    rw [planeDenominatorQuotientEquiv_cubic]
    exact planeBoundaryNumerator_isRegular
  have hback :=
    isRegular_map_ringEquiv planeDenominatorQuotientEquiv.symm hmapped
  simpa only [RingEquiv.symm_apply_apply] using hback

/-- The denominator is regular after quotienting the affine quadric root
extension by the cubic.  Equivalently, `(c) : D = (c)` in this tower
presentation. -/
theorem planeDenominator_mod_cubic_isRegular :
    IsRegular
      (Ideal.Quotient.mk
        (Ideal.span ({planeCubicClass} : Set PlaneQuadricRootRing))
        planeDenominatorClass) :=
  isRegular_quotient_swap planeDenominatorClass_isRegular
    planeCubicClass_mod_denominator_isRegular

/-! ## Comparison with the repository's affine-chart presentation -/

open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoPlaneChartBridge
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoPlaneChartLocalization
open RationalPointsN25QuotientTwoStructuralJacobian

/-- The `x` label among the three coordinates on the `w = 1` chart. -/
def planeAffineX : OtherCoordinate 3 := ⟨0, by decide⟩

/-- The `y` label among the three coordinates on the `w = 1` chart. -/
def planeAffineY : OtherCoordinate 3 := ⟨1, by decide⟩

/-- The `z` label among the three coordinates on the `w = 1` chart. -/
def planeAffineZ : OtherCoordinate 3 := ⟨2, by decide⟩

/-- Reindex the three affine chart variables as `x,z` coefficients together
with a distinguished outer `y` variable. -/
def planeAffineVariableEquiv : OtherCoordinate 3 ≃ Option (Fin 2) :=
  (finSuccAboveEquiv (3 : Fin 4)).symm.trans
    (finSuccEquiv' (1 : Fin 3))

@[simp]
theorem planeAffineVariableEquiv_x :
    planeAffineVariableEquiv planeAffineX = some 0 := by decide

@[simp]
theorem planeAffineVariableEquiv_y :
    planeAffineVariableEquiv planeAffineY = none := by decide

@[simp]
theorem planeAffineVariableEquiv_z :
    planeAffineVariableEquiv planeAffineZ = some 1 := by decide

/-- Identify the two-variable coefficient ring with the iterated polynomial
ring `F₂[z][x]`, placing `x` outside and `z` inside. -/
def planeXZBaseEquiv :
    MvPolynomial (Fin 2) PlaneField ≃ₐ[PlaneField] PlaneXZRing :=
  (MvPolynomial.finSuccEquiv PlaneField 1).trans
    (Polynomial.mapAlgEquiv
      (MvPolynomial.uniqueAlgEquiv PlaneField (Fin 1)))

@[simp]
theorem planeXZBaseEquiv_x :
    planeXZBaseEquiv (MvPolynomial.X (0 : Fin 2)) = X := by
  simp [planeXZBaseEquiv, MvPolynomial.finSuccEquiv_apply]

@[simp]
theorem planeXZBaseEquiv_z :
    planeXZBaseEquiv (MvPolynomial.X (1 : Fin 2)) = C planeZ := by
  simp [planeXZBaseEquiv, planeZ, MvPolynomial.finSuccEquiv_apply,
    show
      Fin.cases X (fun k : Fin 1 => C (MvPolynomial.X k)) (1 : Fin 2) =
        C (MvPolynomial.X (0 : Fin 1)) by rfl]

/-- Separate `y` from the ordinary affine chart and identify its coefficient
ring with `F₂[z][x]`. -/
def planeAffineTowerEquiv :
    AffineChart 3 ≃ₐ[PlaneField] PlaneXZRing[X] :=
  (MvPolynomial.renameEquiv PlaneField planeAffineVariableEquiv).trans
    ((MvPolynomial.optionEquivLeft PlaneField (Fin 2)).trans
      (Polynomial.mapAlgEquiv planeXZBaseEquiv))

@[simp]
theorem planeAffineTowerEquiv_x :
    planeAffineTowerEquiv (MvPolynomial.X planeAffineX) = C X := by
  simp [planeAffineTowerEquiv]

@[simp]
theorem planeAffineTowerEquiv_y :
    planeAffineTowerEquiv (MvPolynomial.X planeAffineY) = X := by
  simp [planeAffineTowerEquiv]

@[simp]
theorem planeAffineTowerEquiv_z :
    planeAffineTowerEquiv (MvPolynomial.X planeAffineZ) = C (C planeZ) := by
  simp [planeAffineTowerEquiv]

@[simp]
theorem planeAffineTowerEquiv_X_zero
    (h : (0 : Fin 4) ≠ (3 : Fin 4)) :
    planeAffineTowerEquiv
      (MvPolynomial.X (⟨0, h⟩ : OtherCoordinate 3)) = C X := by
  rw [show (⟨0, h⟩ : OtherCoordinate 3) = planeAffineX by rfl]
  exact planeAffineTowerEquiv_x

@[simp]
theorem planeAffineTowerEquiv_X_one
    (h : (1 : Fin 4) ≠ (3 : Fin 4)) :
    planeAffineTowerEquiv
      (MvPolynomial.X (⟨1, h⟩ : OtherCoordinate 3)) = X := by
  rw [show (⟨1, h⟩ : OtherCoordinate 3) = planeAffineY by rfl]
  exact planeAffineTowerEquiv_y

@[simp]
theorem planeAffineTowerEquiv_X_two
    (h : (2 : Fin 4) ≠ (3 : Fin 4)) :
    planeAffineTowerEquiv
      (MvPolynomial.X (⟨2, h⟩ : OtherCoordinate 3)) = C (C planeZ) := by
  rw [show (⟨2, h⟩ : OtherCoordinate 3) = planeAffineZ by rfl]
  exact planeAffineTowerEquiv_z

/-- The affine chart quadric becomes the monic quadratic in the separated
`y` coordinate. -/
theorem planeAffineTowerEquiv_quadric :
    planeAffineTowerEquiv (chartAffineQuadric 3) = planeQuadricInY := by
  simp [chartAffineQuadric, ambientDehomogenize, dehomogenizedVariable,
    canonicalQuadricPolynomial25Two, planeQuadricInY, planeDenominator,
    planeZ]
  ring

/-- The affine chart cubic becomes `D*y + N` in the separated polynomial
tower. -/
theorem planeAffineTowerEquiv_cubic :
    planeAffineTowerEquiv (chartAffineCubic 3) = planeCubicInY := by
  simp [chartAffineCubic, ambientDehomogenize, dehomogenizedVariable,
    canonicalCubicPolynomial25Two, planeCubicInY, planeDenominator,
    planeNumerator, planeZ]
  ring

/-- The principal quadric ideal in the separated polynomial tower. -/
def planeQuadricIdealY : Ideal PlaneXZRing[X] :=
  Ideal.span {planeQuadricInY}

/-- The principal cubic ideal in the separated polynomial tower. -/
def planeCubicIdealY : Ideal PlaneXZRing[X] :=
  Ideal.span {planeCubicInY}

/-- The two-equation ideal in the separated polynomial tower. -/
def planeQuadricCubicIdealY : Ideal PlaneXZRing[X] :=
  Ideal.span {planeQuadricInY, planeCubicInY}

/-- The two-equation ideal is the supremum of its principal equation
ideals. -/
theorem planeQuadricIdealY_sup_planeCubicIdealY :
    planeQuadricIdealY ⊔ planeCubicIdealY = planeQuadricCubicIdealY := by
  rw [planeQuadricIdealY, planeCubicIdealY, planeQuadricCubicIdealY,
    Ideal.span_insert]

/-- The affine tower equivalence carries the repository's chart equation
ideal to the displayed quadric-cubic ideal. -/
theorem planeAffineTowerEquiv_chartIdeal :
    planeQuadricCubicIdealY =
      Ideal.map planeAffineTowerEquiv.toRingHom
        (chartAffineEquationIdeal 3) := by
  rw [planeQuadricCubicIdealY, chartAffineEquationIdeal,
    chartAffineRelation_range, Ideal.map_span]
  congr 1
  ext p
  simp [planeAffineTowerEquiv_quadric, planeAffineTowerEquiv_cubic, eq_comm]

/-- The repository's ordinary `w = 1` chart quotient, transported to the
two-equation ideal in the separated polynomial tower. -/
def planeAffineChartQuotientEquiv :
    ChartQuotient 3 ≃+*
      PlaneXZRing[X] ⧸ planeQuadricCubicIdealY :=
  Ideal.quotientEquiv (chartAffineEquationIdeal 3)
    planeQuadricCubicIdealY planeAffineTowerEquiv.toRingEquiv
    planeAffineTowerEquiv_chartIdeal

/-- Mapping the principal cubic ideal through the quadric quotient gives
the principal ideal generated by the cubic class. -/
theorem map_planeCubicIdealY :
    Ideal.map (AdjoinRoot.mk planeQuadricInY) planeCubicIdealY =
      Ideal.span ({planeCubicClass} : Set PlaneQuadricRootRing) := by
  rw [planeCubicIdealY, Ideal.map_span, Set.image_singleton]
  rfl

/-- Successively quotienting by the quadric and cubic agrees with quotienting
the separated polynomial tower by both equations at once. -/
def planeTowerDoubleQuotientEquiv :
    PlaneQuadricRootRing ⧸
        Ideal.span ({planeCubicClass} : Set PlaneQuadricRootRing) ≃+*
      PlaneXZRing[X] ⧸ planeQuadricCubicIdealY :=
  (Ideal.quotEquivOfEq map_planeCubicIdealY.symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup planeQuadricIdealY planeCubicIdealY).trans
      (Ideal.quotEquivOfEq planeQuadricIdealY_sup_planeCubicIdealY))

/-- The canonical `w = 1` chart is the quotient of the monic quadric root
extension by the cubic class. -/
def canonicalWChartTowerEquiv :
    ChartQuotient 3 ≃+*
      PlaneQuadricRootRing ⧸
        Ideal.span ({planeCubicClass} : Set PlaneQuadricRootRing) :=
  planeAffineChartQuotientEquiv.trans planeTowerDoubleQuotientEquiv.symm

/-- The first quotient equivalence acts on representatives by applying the
affine polynomial-tower equivalence. -/
theorem planeAffineChartQuotientEquiv_mk (p : AffineChart 3) :
    planeAffineChartQuotientEquiv
        (Ideal.Quotient.mk (chartAffineEquationIdeal 3) p) =
      Ideal.Quotient.mk planeQuadricCubicIdealY
        (planeAffineTowerEquiv p) := by
  exact Ideal.quotientEquiv_mk (chartAffineEquationIdeal 3)
    planeQuadricCubicIdealY planeAffineTowerEquiv.toRingEquiv
    planeAffineTowerEquiv_chartIdeal p

/-- The successive-quotient equivalence sends a doubly reduced
representative to the same polynomial reduced by the pair ideal. -/
theorem planeTowerDoubleQuotientEquiv_mk (p : PlaneXZRing[X]) :
    planeTowerDoubleQuotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span ({planeCubicClass} : Set PlaneQuadricRootRing))
          (AdjoinRoot.mk planeQuadricInY p)) =
      Ideal.Quotient.mk planeQuadricCubicIdealY p := by
  rfl

/-- The final chart-to-tower equivalence has the expected action on every
affine polynomial representative. -/
theorem canonicalWChartTowerEquiv_mk (p : AffineChart 3) :
    canonicalWChartTowerEquiv
        (Ideal.Quotient.mk (chartAffineEquationIdeal 3) p) =
      Ideal.Quotient.mk
        (Ideal.span ({planeCubicClass} : Set PlaneQuadricRootRing))
        (AdjoinRoot.mk planeQuadricInY (planeAffineTowerEquiv p)) := by
  rw [canonicalWChartTowerEquiv, RingEquiv.trans_apply,
    planeAffineChartQuotientEquiv_mk]
  apply planeTowerDoubleQuotientEquiv.injective
  rw [RingEquiv.apply_symm_apply, planeTowerDoubleQuotientEquiv_mk]

/-- The universal canonical `x` coordinate is the quotient class of the
ordinary affine `x` variable. -/
theorem canonicalWChartX_eq_mk :
    canonicalWChartX =
      Ideal.Quotient.mk (chartAffineEquationIdeal 3)
        (MvPolynomial.X planeAffineX) := by
  simp [canonicalWChartX, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, planeAffineX]

/-- The universal canonical `z` coordinate is the quotient class of the
ordinary affine `z` variable. -/
theorem canonicalWChartZ_eq_mk :
    canonicalWChartZ =
      Ideal.Quotient.mk (chartAffineEquationIdeal 3)
        (MvPolynomial.X planeAffineZ) := by
  simp [canonicalWChartZ, canonicalWChartPoint, chartQuotientPoint,
    mappedAmbientPoint, chartMap, ambientDehomogenize,
    dehomogenizedVariable, planeAffineZ]

/-- The chart-to-tower equivalence identifies the intrinsic projection
denominator with the separated-tower denominator class. -/
theorem canonicalWChartTowerEquiv_denominator :
    canonicalWChartTowerEquiv canonicalWChartProjectionDenominator =
      Ideal.Quotient.mk
        (Ideal.span ({planeCubicClass} : Set PlaneQuadricRootRing))
        planeDenominatorClass := by
  rw [canonicalWChartProjectionDenominator, projectionDenominator,
    canonicalWChartX_eq_mk, canonicalWChartZ_eq_mk]
  change canonicalWChartTowerEquiv
      (Ideal.Quotient.mk (chartAffineEquationIdeal 3)
        (MvPolynomial.X planeAffineX * MvPolynomial.X planeAffineZ +
          MvPolynomial.X planeAffineX + MvPolynomial.X planeAffineZ)) = _
  rw [canonicalWChartTowerEquiv_mk]
  simp [planeDenominatorClass, planeDenominator]
  ring

/-- The projection denominator is a non-zero-divisor on the canonical
`w = 1` chart. -/
theorem canonicalWChartProjectionDenominator_isRegular :
    IsRegular canonicalWChartProjectionDenominator := by
  have hmapped :
      IsRegular
        (canonicalWChartTowerEquiv canonicalWChartProjectionDenominator) := by
    rw [canonicalWChartTowerEquiv_denominator]
    exact planeDenominator_mod_cubic_isRegular
  have hback :=
    isRegular_map_ringEquiv canonicalWChartTowerEquiv.symm hmapped
  simpa only [RingEquiv.symm_apply_apply] using hback

/-! ## Integrality of the canonical affine chart -/

/-- The plane sextic has degree four in its outer `x` variable. -/
theorem planeSexticPolynomial_natDegree_four :
    planeSexticPolynomial.natDegree = 4 := by
  unfold planeSexticPolynomial
  compute_degree!

/-- The projection denominator has degree one in `x`. -/
theorem planeDenominator_natDegree : planeDenominator.natDegree = 1 := by
  unfold planeDenominator
  exact natDegree_linear planeZ_add_one_ne_zero

/-- The quartic plane equation cannot divide the nonzero linear projection
denominator. -/
theorem planeSexticPolynomial_not_dvd_planeDenominator :
    ¬planeSexticPolynomial ∣ planeDenominator := by
  apply planeSexticPolynomial_monic.not_dvd_of_natDegree_lt
    planeDenominator_prime.ne_zero
  rw [planeDenominator_natDegree, planeSexticPolynomial_natDegree_four]
  norm_num

/-- The projection denominator in the integral plane coordinate ring is the
class of the same linear polynomial used in the tower calculation. -/
theorem planeProjectionDenominator_eq_mk :
    planeProjectionDenominator =
      AdjoinRoot.mk planeSexticPolynomial planeDenominator := by
  change
    AdjoinRoot.root planeSexticPolynomial *
          AdjoinRoot.of planeSexticPolynomial X +
        AdjoinRoot.root planeSexticPolynomial +
        AdjoinRoot.of planeSexticPolynomial X =
      AdjoinRoot.mk planeSexticPolynomial
        (C (X + 1) * X + C X)
  rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, map_add, map_one]
  ring

/-- The projection denominator is nonzero in the integral plane coordinate
ring. -/
theorem planeProjectionDenominator_ne_zero :
    planeProjectionDenominator ≠ 0 := by
  rw [planeProjectionDenominator_eq_mk, Ne,
    AdjoinRoot.mk_eq_zero]
  exact planeSexticPolynomial_not_dvd_planeDenominator

/-- Localizing the integral plane chart at its nonzero projection
denominator remains an integral domain. -/
noncomputable instance planeDOpen_isDomain : IsDomain PlaneDOpen :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      planeProjectionDenominator_ne_zero)

/-- The canonical principal open is integral because it is ring-equivalent
to the integral plane principal open. -/
noncomputable instance canonicalWChartDOpen_isDomain :
    IsDomain CanonicalWChartDOpen :=
  Function.Injective.isDomain
    planeDOpenEquivCanonicalWChartDOpen.symm.toRingHom
    planeDOpenEquivCanonicalWChartDOpen.symm.injective

/-- Regularity of the denominator makes the canonical localization map
injective. -/
theorem canonicalWChartToDOpen_injective :
    Function.Injective
      (algebraMap (ChartQuotient 3) CanonicalWChartDOpen) := by
  apply IsLocalization.injectiveₛ
    (M := Submonoid.powers canonicalWChartProjectionDenominator)
    CanonicalWChartDOpen
  rintro s ⟨n, rfl⟩
  exact canonicalWChartProjectionDenominator_isRegular.pow n

/-- The canonical `w = 1` chart is an integral domain.  It embeds into its
integral principal open because the localization denominator is regular. -/
noncomputable instance canonicalWChart_isDomain :
    IsDomain (ChartQuotient 3) :=
  Function.Injective.isDomain
    (algebraMap (ChartQuotient 3) CanonicalWChartDOpen)
    canonicalWChartToDOpen_injective

end MazurProof.RationalPointsN25QuotientTwoPlaneChartDomain
