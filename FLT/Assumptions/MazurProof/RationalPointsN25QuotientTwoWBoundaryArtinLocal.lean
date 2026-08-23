import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryClosedPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoHyperplaneArtinLocal

/-!
# Artin presentations of the canonical binary curve's `W = 0` boundary

The hyperplane `W = 0` meets the canonical curve at the three rational
points `[1:0:0:0]`, `[0:0:1:0]`, and `[0:1:1:0]`.  This file isolates the
three factors on affine principal opens and presents their equation quotients
as `F_2[t]/(t^3)`, `F_2[t]/(t^2)`, and `F_2`, respectively.

These are ground-field lengths of explicit principal-open equation quotients.
Their later interpretation as local intersection orders still requires the
local-ring comparison supplied by the projective divisor construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryArtinLocal

open Polynomial
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientTwoHyperplaneArtin
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open CurveZetaFrobeniusOrbitGrading

private def zmodLinearEquivOfRingEquiv
    {n : ℕ} {A B : Type*} [Ring A] [Ring B]
    [Module (ZMod n) A] [Module (ZMod n) B]
    (e : A ≃+* B) : A ≃ₗ[ZMod n] B :=
  { e.toAddEquiv with
    map_smul' := fun c x ↦ ZMod.map_smul e.toAddEquiv c x }

/-! ## The tripled point `[1:0:0:0]` -/

/-- On the `x = 1` chart with `W = 0`, the quadric is
`y^2 + z + y*z`. -/
theorem xBoundary_quadric
    {K : Type*} [CommRing K] [CharP K 2] (y z : K) :
    canonicalQuadric25Over (⟨1, y, z, 0⟩ : Coordinates4 K) =
      y ^ 2 + z + y * z := by
  dsimp [canonicalQuadric25Over]
  rw [CharTwo.neg_eq]
  ring

/-- On the same chart, the cubic is `y*z`. -/
theorem xBoundary_cubic
    {K : Type*} [CommRing K] (y z : K) :
    canonicalCubic25Over (⟨1, y, z, 0⟩ : Coordinates4 K) = y * z := by
  simp [canonicalCubic25Over]

/-- After inverting `1+y`, the two boundary equations have normal form
`(y^2+z+y*z,y^3)`. -/
theorem xBoundary_intersectionIdeal_eq_normalForm
    {R : Type*} [CommRing R] (y z : R) (hu : IsUnit (1 + y)) :
    Ideal.span {y ^ 2 + z + y * z, y * z} =
      Ideal.span {y ^ 2 + z + y * z, y ^ 3} := by
  let uInv : R := ↑hu.unit⁻¹
  have hInv : uInv * (1 + y) = 1 := hu.val_inv_mul
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    · exact Ideal.mem_span_pair.mpr ⟨uInv * y, -uInv, by
        calc
          (uInv * y) * (y ^ 2 + z + y * z) + (-uInv) * y ^ 3 =
              uInv * (y * z * (1 + y)) := by ring
          _ = (uInv * (1 + y)) * (y * z) := by ring
          _ = y * z := by rw [hInv, one_mul]⟩
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    · exact Ideal.mem_span_pair.mpr ⟨y, -(1 + y), by ring⟩

/-- The binary affine plane with variables `y,z`. -/
abbrev BoundaryAffinePlane := MvPolynomial (Fin 2) (ZMod 2)

noncomputable def xBoundaryQuadricPolynomial : BoundaryAffinePlane :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 +
    MvPolynomial.X 0 * MvPolynomial.X 1

noncomputable def xBoundaryCubicPolynomial : BoundaryAffinePlane :=
  MvPolynomial.X 0 * MvPolynomial.X 1

noncomputable def xBoundaryDenominator : BoundaryAffinePlane :=
  1 + MvPolynomial.X 0

def xBoundaryNormalIdeal : Ideal BoundaryAffinePlane :=
  Ideal.span {xBoundaryQuadricPolynomial, MvPolynomial.X 0 ^ 3}

/-- Evaluation at the length-three infinitesimal point `(y,z)=(t,t^2)`. -/
noncomputable def xBoundaryEvaluation :
    BoundaryAffinePlane →ₐ[ZMod 2] TripleArtin :=
  MvPolynomial.aeval ![tripleRoot, tripleRoot ^ 2]

@[simp]
theorem xBoundaryEvaluation_X_zero :
    xBoundaryEvaluation (MvPolynomial.X 0) = tripleRoot := by
  simp [xBoundaryEvaluation]

@[simp]
theorem xBoundaryEvaluation_X_one :
    xBoundaryEvaluation (MvPolynomial.X 1) = tripleRoot ^ 2 := by
  simp [xBoundaryEvaluation]

theorem xBoundaryEvaluation_quadric :
    xBoundaryEvaluation xBoundaryQuadricPolynomial = 0 := by
  simp only [xBoundaryQuadricPolynomial, map_add, map_mul, map_pow,
    xBoundaryEvaluation_X_zero, xBoundaryEvaluation_X_one]
  have htwo : (2 : TripleArtin) = 0 := CharP.cast_eq_zero TripleArtin 2
  linear_combination tripleRoot_cube + tripleRoot ^ 2 * htwo

theorem xBoundaryEvaluation_cubic :
    xBoundaryEvaluation xBoundaryCubicPolynomial = 0 := by
  simp only [xBoundaryCubicPolynomial, map_mul,
    xBoundaryEvaluation_X_zero, xBoundaryEvaluation_X_one]
  calc
    tripleRoot * tripleRoot ^ 2 = tripleRoot ^ 3 := by ring
    _ = 0 := tripleRoot_cube

theorem xBoundaryNormalIdeal_le_ker :
    xBoundaryNormalIdeal ≤ RingHom.ker xBoundaryEvaluation.toRingHom := by
  refine Ideal.span_le.2 ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact xBoundaryEvaluation_quadric
  · simpa using tripleRoot_cube

def xBoundaryQuotientToArtin :
    BoundaryAffinePlane ⧸ xBoundaryNormalIdeal →ₐ[ZMod 2] TripleArtin :=
  Ideal.Quotient.liftₐ xBoundaryNormalIdeal xBoundaryEvaluation
    (fun _ hp ↦ xBoundaryNormalIdeal_le_ker hp)

theorem xBoundaryQuotient_y_cube :
    (Ideal.Quotient.mkₐ (ZMod 2) xBoundaryNormalIdeal
      (MvPolynomial.X 0)) ^ 3 = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))))

def tripleArtinToXBoundaryQuotient :
    TripleArtin →ₐ[ZMod 2] BoundaryAffinePlane ⧸ xBoundaryNormalIdeal :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : (ZMod 2)[X]) ^ 3)
    (Algebra.ofId (ZMod 2) (BoundaryAffinePlane ⧸ xBoundaryNormalIdeal))
    (Ideal.Quotient.mkₐ (ZMod 2) xBoundaryNormalIdeal
      (MvPolynomial.X 0)) (by simpa using xBoundaryQuotient_y_cube)

theorem xBoundaryQuotientToArtin_comp_tripleArtinToQuotient :
    xBoundaryQuotientToArtin.comp tripleArtinToXBoundaryQuotient =
      AlgHom.id (ZMod 2) TripleArtin := by
  ext
  simp [xBoundaryQuotientToArtin, tripleArtinToXBoundaryQuotient, tripleRoot]

/-- The normal-form relation and `y^3=0` solve `z=y^2`. -/
theorem xBoundaryQuotient_z_eq_y_sq :
    Ideal.Quotient.mkₐ (ZMod 2) xBoundaryNormalIdeal (MvPolynomial.X 1) =
      Ideal.Quotient.mkₐ (ZMod 2) xBoundaryNormalIdeal
        (MvPolynomial.X 0 ^ 2) := by
  let Y : BoundaryAffinePlane ⧸ xBoundaryNormalIdeal :=
    Ideal.Quotient.mkₐ (ZMod 2) xBoundaryNormalIdeal (MvPolynomial.X 0)
  let Z : BoundaryAffinePlane ⧸ xBoundaryNormalIdeal :=
    Ideal.Quotient.mkₐ (ZMod 2) xBoundaryNormalIdeal (MvPolynomial.X 1)
  have hRelation : Y ^ 2 + Z + Y * Z = 0 := by
    change Ideal.Quotient.mkₐ (ZMod 2) xBoundaryNormalIdeal
      xBoundaryQuadricPolynomial = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert _ _))
  have hCube : Y ^ 3 = 0 := xBoundaryQuotient_y_cube
  have hProduct : (1 + Y) * (Z + Y ^ 2) = 0 := by
    calc
      (1 + Y) * (Z + Y ^ 2) =
          (Y ^ 2 + Z + Y * Z) + Y ^ 3 := by ring
      _ = 0 := by rw [hRelation, hCube, add_zero]
  have hUnit : IsUnit (1 + Y) :=
    (show IsNilpotent Y from ⟨3, hCube⟩).isUnit_one_add
  have hSum : Z + Y ^ 2 = 0 := hUnit.mul_right_eq_zero.mp hProduct
  have htwo : (2 : BoundaryAffinePlane ⧸ xBoundaryNormalIdeal) = 0 := by
    have htwoCoeff : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    change Ideal.Quotient.mk xBoundaryNormalIdeal
      (MvPolynomial.C (2 : ZMod 2)) = 0
    rw [htwoCoeff, map_zero]
    exact map_zero (Ideal.Quotient.mk xBoundaryNormalIdeal)
  have hSelf : Y ^ 2 + Y ^ 2 = 0 := by
    calc
      Y ^ 2 + Y ^ 2 = 2 * Y ^ 2 := by ring
      _ = 0 := by rw [htwo, zero_mul]
  change Z = Y ^ 2
  exact (eq_neg_of_add_eq_zero_left hSum).trans
    (neg_eq_iff_add_eq_zero.mpr hSelf)

theorem tripleArtinToXBoundaryQuotient_comp_xBoundaryQuotientToArtin :
    tripleArtinToXBoundaryQuotient.comp xBoundaryQuotientToArtin =
      AlgHom.id (ZMod 2) (BoundaryAffinePlane ⧸ xBoundaryNormalIdeal) := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i
  · simp [xBoundaryQuotientToArtin, tripleArtinToXBoundaryQuotient,
      tripleRoot]
  · simpa [xBoundaryQuotientToArtin, tripleArtinToXBoundaryQuotient,
      tripleRoot] using xBoundaryQuotient_z_eq_y_sq.symm

def xBoundaryNormalQuotientAlgEquiv :
    (BoundaryAffinePlane ⧸ xBoundaryNormalIdeal) ≃ₐ[ZMod 2] TripleArtin :=
  AlgEquiv.ofAlgHom xBoundaryQuotientToArtin
    tripleArtinToXBoundaryQuotient
    xBoundaryQuotientToArtin_comp_tripleArtinToQuotient
    tripleArtinToXBoundaryQuotient_comp_xBoundaryQuotientToArtin

theorem xBoundaryEvaluation_ker :
    RingHom.ker xBoundaryEvaluation.toRingHom = xBoundaryNormalIdeal := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply xBoundaryNormalQuotientAlgEquiv.injective
    change xBoundaryEvaluation p = 0
    exact hp
  · exact xBoundaryNormalIdeal_le_ker

theorem xBoundaryEvaluation_surjective :
    Function.Surjective xBoundaryEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨Polynomial.toMvPolynomial (R := ZMod 2) (0 : Fin 2) p, ?_⟩
  rw [xBoundaryEvaluation, MvPolynomial.aeval_toMvPolynomial]
  exact AdjoinRoot.aeval_eq p

theorem xBoundaryEvaluation_denominator_isUnit :
    IsUnit (xBoundaryEvaluation xBoundaryDenominator) := by
  simpa [xBoundaryDenominator] using isUnit_one_add_tripleRoot

noncomputable def xBoundaryLocalizedEvaluation :
    Localization.Away xBoundaryDenominator →+* TripleArtin :=
  Localization.awayLift xBoundaryEvaluation.toRingHom xBoundaryDenominator
    xBoundaryEvaluation_denominator_isUnit

theorem xBoundaryLocalized_chartIdeal_eq_normalIdeal :
    Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away xBoundaryDenominator))
        (Ideal.span {xBoundaryQuadricPolynomial,
          xBoundaryCubicPolynomial}) =
      Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away xBoundaryDenominator))
        xBoundaryNormalIdeal := by
  let f := algebraMap BoundaryAffinePlane
    (Localization.Away xBoundaryDenominator)
  simpa [xBoundaryQuadricPolynomial, xBoundaryCubicPolynomial,
    xBoundaryNormalIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton] using
    xBoundary_intersectionIdeal_eq_normalForm
      (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1))
      (by
        change IsUnit (1 + f (MvPolynomial.X 0))
        rw [← map_one f, ← map_add]
        exact IsLocalization.Away.algebraMap_isUnit xBoundaryDenominator)

theorem xBoundaryLocalizedEvaluation_ker_eq_chartIdeal :
    RingHom.ker xBoundaryLocalizedEvaluation =
      Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away xBoundaryDenominator))
        (Ideal.span {xBoundaryQuadricPolynomial,
          xBoundaryCubicPolynomial}) := by
  rw [xBoundaryLocalizedEvaluation,
    awayLift_ker, xBoundaryEvaluation_ker,
    xBoundaryLocalized_chartIdeal_eq_normalIdeal.symm]

theorem xBoundaryLocalizedEvaluation_surjective :
    Function.Surjective xBoundaryLocalizedEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := xBoundaryEvaluation_surjective x
  refine ⟨algebraMap BoundaryAffinePlane
    (Localization.Away xBoundaryDenominator) p, ?_⟩
  exact IsLocalization.Away.lift_eq xBoundaryDenominator
    xBoundaryEvaluation_denominator_isUnit p

noncomputable def xBoundaryLocalizedChartQuotientEquiv :
    (Localization.Away xBoundaryDenominator ⧸
      Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away xBoundaryDenominator))
        (Ideal.span {xBoundaryQuadricPolynomial,
          xBoundaryCubicPolynomial})) ≃+* TripleArtin :=
  (Ideal.quotEquivOfEq
      xBoundaryLocalizedEvaluation_ker_eq_chartIdeal.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      xBoundaryLocalizedEvaluation_surjective)

/-- The isolated factor at `[1:0:0:0]` has `F₂`-length three. -/
theorem xBoundaryLocalizedChartQuotient_f2_length :
    Module.length (ZMod 2)
      (Localization.Away xBoundaryDenominator ⧸
        Ideal.map
          (algebraMap BoundaryAffinePlane
            (Localization.Away xBoundaryDenominator))
          (Ideal.span {xBoundaryQuadricPolynomial,
            xBoundaryCubicPolynomial})) = 3 := by
  let e :
      (Localization.Away xBoundaryDenominator ⧸
        Ideal.map
          (algebraMap BoundaryAffinePlane
            (Localization.Away xBoundaryDenominator))
          (Ideal.span {xBoundaryQuadricPolynomial,
            xBoundaryCubicPolynomial})) ≃ₗ[ZMod 2] TripleArtin :=
    zmodLinearEquivOfRingEquiv xBoundaryLocalizedChartQuotientEquiv
  rw [e.length_eq]
  letI : Module.Finite (ZMod 2) TripleArtin :=
    (Polynomial.monic_X_pow 3).finite_adjoinRoot
  rw [Module.length_eq_finrank, tripleArtin_finrank]
  norm_num

/-! ## The doubled point `[0:0:1:0]` -/

/-- On the `z = 1` chart with `W = 0`, the equations are
`x+y^2+y` and `x*y`. -/
theorem zBoundary_quadric
    {K : Type*} [CommRing K] [CharP K 2] (x y : K) :
    canonicalQuadric25Over (⟨x, y, 1, 0⟩ : Coordinates4 K) =
      x + y ^ 2 + y := by
  dsimp [canonicalQuadric25Over]
  rw [CharTwo.neg_eq]
  ring

theorem zBoundary_cubic
    {K : Type*} [CommRing K] (x y : K) :
    canonicalCubic25Over (⟨x, y, 1, 0⟩ : Coordinates4 K) = x * y := by
  simp [canonicalCubic25Over]

/-- On `D(1+y)`, the equations at `(x,y)=(0,0)` have the normal form
`(x+y^2+y,y^2)`. -/
theorem zBoundary_intersectionIdeal_eq_normalForm
    {R : Type*} [CommRing R] (x y : R) (hu : IsUnit (1 + y)) :
    Ideal.span {x + y ^ 2 + y, x * y} =
      Ideal.span {x + y ^ 2 + y, y ^ 2} := by
  let uInv : R := ↑hu.unit⁻¹
  have hInv : uInv * (1 + y) = 1 := hu.val_inv_mul
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    · exact Ideal.mem_span_pair.mpr ⟨y, -(1 + y), by ring⟩
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1, 0, by ring⟩
    · exact Ideal.mem_span_pair.mpr ⟨uInv * y, -uInv, by
        calc
          (uInv * y) * (x + y ^ 2 + y) + (-uInv) * (x * y) =
              uInv * (y ^ 2 * (1 + y)) := by ring
          _ = (uInv * (1 + y)) * y ^ 2 := by ring
          _ = y ^ 2 := by rw [hInv, one_mul]⟩

noncomputable def zBoundaryQuadricPolynomial : BoundaryAffinePlane :=
  MvPolynomial.X 0 + MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1

noncomputable def zBoundaryCubicPolynomial : BoundaryAffinePlane :=
  MvPolynomial.X 0 * MvPolynomial.X 1

noncomputable def zBoundaryDenominator : BoundaryAffinePlane :=
  1 + MvPolynomial.X 1

def zBoundaryNormalIdeal : Ideal BoundaryAffinePlane :=
  Ideal.span {zBoundaryQuadricPolynomial, MvPolynomial.X 1 ^ 2}

/-- Evaluation at the length-two infinitesimal point `(x,y)=(t,t)`. -/
noncomputable def zBoundaryEvaluation :
    BoundaryAffinePlane →ₐ[ZMod 2] DoubleArtin :=
  MvPolynomial.aeval ![doubleRoot, doubleRoot]

@[simp]
theorem zBoundaryEvaluation_X_zero :
    zBoundaryEvaluation (MvPolynomial.X 0) = doubleRoot := by
  simp [zBoundaryEvaluation]

@[simp]
theorem zBoundaryEvaluation_X_one :
    zBoundaryEvaluation (MvPolynomial.X 1) = doubleRoot := by
  simp [zBoundaryEvaluation]

theorem zBoundaryEvaluation_quadric :
    zBoundaryEvaluation zBoundaryQuadricPolynomial = 0 := by
  simp only [zBoundaryQuadricPolynomial, map_add, map_pow,
    zBoundaryEvaluation_X_zero, zBoundaryEvaluation_X_one]
  have htwo : (2 : DoubleArtin) = 0 := CharP.cast_eq_zero DoubleArtin 2
  linear_combination doubleRoot_sq + doubleRoot * htwo

theorem zBoundaryEvaluation_cubic :
    zBoundaryEvaluation zBoundaryCubicPolynomial = 0 := by
  simp only [zBoundaryCubicPolynomial, map_mul,
    zBoundaryEvaluation_X_zero, zBoundaryEvaluation_X_one]
  calc
    doubleRoot * doubleRoot = doubleRoot ^ 2 := by ring
    _ = 0 := doubleRoot_sq

theorem zBoundaryNormalIdeal_le_ker :
    zBoundaryNormalIdeal ≤ RingHom.ker zBoundaryEvaluation.toRingHom := by
  refine Ideal.span_le.2 ?_
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact zBoundaryEvaluation_quadric
  · simpa using doubleRoot_sq

def zBoundaryQuotientToArtin :
    BoundaryAffinePlane ⧸ zBoundaryNormalIdeal →ₐ[ZMod 2] DoubleArtin :=
  Ideal.Quotient.liftₐ zBoundaryNormalIdeal zBoundaryEvaluation
    (fun _ hp ↦ zBoundaryNormalIdeal_le_ker hp)

theorem zBoundaryQuotient_y_sq :
    (Ideal.Quotient.mkₐ (ZMod 2) zBoundaryNormalIdeal
      (MvPolynomial.X 1)) ^ 2 = 0 := by
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))))

def doubleArtinToZBoundaryQuotient :
    DoubleArtin →ₐ[ZMod 2] BoundaryAffinePlane ⧸ zBoundaryNormalIdeal :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : (ZMod 2)[X]) ^ 2)
    (Algebra.ofId (ZMod 2) (BoundaryAffinePlane ⧸ zBoundaryNormalIdeal))
    (Ideal.Quotient.mkₐ (ZMod 2) zBoundaryNormalIdeal
      (MvPolynomial.X 1)) (by simpa using zBoundaryQuotient_y_sq)

theorem zBoundaryQuotientToArtin_comp_doubleArtinToQuotient :
    zBoundaryQuotientToArtin.comp doubleArtinToZBoundaryQuotient =
      AlgHom.id (ZMod 2) DoubleArtin := by
  ext
  simp [zBoundaryQuotientToArtin, doubleArtinToZBoundaryQuotient, doubleRoot]

/-- The normal-form relation and `y^2=0` solve `x=y`. -/
theorem zBoundaryQuotient_x_eq_y :
    Ideal.Quotient.mkₐ (ZMod 2) zBoundaryNormalIdeal (MvPolynomial.X 0) =
      Ideal.Quotient.mkₐ (ZMod 2) zBoundaryNormalIdeal
        (MvPolynomial.X 1) := by
  let X : BoundaryAffinePlane ⧸ zBoundaryNormalIdeal :=
    Ideal.Quotient.mkₐ (ZMod 2) zBoundaryNormalIdeal (MvPolynomial.X 0)
  let Y : BoundaryAffinePlane ⧸ zBoundaryNormalIdeal :=
    Ideal.Quotient.mkₐ (ZMod 2) zBoundaryNormalIdeal (MvPolynomial.X 1)
  have hRelation : X + Y ^ 2 + Y = 0 := by
    change Ideal.Quotient.mkₐ (ZMod 2) zBoundaryNormalIdeal
      zBoundaryQuadricPolynomial = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert _ _))
  have hSq : Y ^ 2 = 0 := zBoundaryQuotient_y_sq
  have hSum : X + Y = 0 := by simpa [hSq] using hRelation
  have htwo : (2 : BoundaryAffinePlane ⧸ zBoundaryNormalIdeal) = 0 := by
    have htwoCoeff : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    change Ideal.Quotient.mk zBoundaryNormalIdeal
      (MvPolynomial.C (2 : ZMod 2)) = 0
    rw [htwoCoeff, map_zero]
    exact map_zero (Ideal.Quotient.mk zBoundaryNormalIdeal)
  have hSelf : Y + Y = 0 := by
    calc
      Y + Y = 2 * Y := by ring
      _ = 0 := by rw [htwo, zero_mul]
  change X = Y
  exact (eq_neg_of_add_eq_zero_left hSum).trans
    (neg_eq_iff_add_eq_zero.mpr hSelf)

theorem doubleArtinToZBoundaryQuotient_comp_zBoundaryQuotientToArtin :
    doubleArtinToZBoundaryQuotient.comp zBoundaryQuotientToArtin =
      AlgHom.id (ZMod 2) (BoundaryAffinePlane ⧸ zBoundaryNormalIdeal) := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i
  · simpa [zBoundaryQuotientToArtin, doubleArtinToZBoundaryQuotient,
      doubleRoot] using zBoundaryQuotient_x_eq_y.symm
  · simp [zBoundaryQuotientToArtin, doubleArtinToZBoundaryQuotient,
      doubleRoot]

def zBoundaryNormalQuotientAlgEquiv :
    (BoundaryAffinePlane ⧸ zBoundaryNormalIdeal) ≃ₐ[ZMod 2] DoubleArtin :=
  AlgEquiv.ofAlgHom zBoundaryQuotientToArtin
    doubleArtinToZBoundaryQuotient
    zBoundaryQuotientToArtin_comp_doubleArtinToQuotient
    doubleArtinToZBoundaryQuotient_comp_zBoundaryQuotientToArtin

theorem zBoundaryEvaluation_ker :
    RingHom.ker zBoundaryEvaluation.toRingHom = zBoundaryNormalIdeal := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply zBoundaryNormalQuotientAlgEquiv.injective
    change zBoundaryEvaluation p = 0
    exact hp
  · exact zBoundaryNormalIdeal_le_ker

theorem zBoundaryEvaluation_surjective :
    Function.Surjective zBoundaryEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨Polynomial.toMvPolynomial (R := ZMod 2) (1 : Fin 2) p, ?_⟩
  rw [zBoundaryEvaluation, MvPolynomial.aeval_toMvPolynomial]
  exact AdjoinRoot.aeval_eq p

theorem zBoundaryEvaluation_denominator_isUnit :
    IsUnit (zBoundaryEvaluation zBoundaryDenominator) := by
  simpa [zBoundaryDenominator] using isUnit_one_add_doubleRoot

noncomputable def zBoundaryLocalizedEvaluation :
    Localization.Away zBoundaryDenominator →+* DoubleArtin :=
  Localization.awayLift zBoundaryEvaluation.toRingHom zBoundaryDenominator
    zBoundaryEvaluation_denominator_isUnit

theorem zBoundaryLocalized_chartIdeal_eq_normalIdeal :
    Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away zBoundaryDenominator))
        (Ideal.span {zBoundaryQuadricPolynomial,
          zBoundaryCubicPolynomial}) =
      Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away zBoundaryDenominator))
        zBoundaryNormalIdeal := by
  let f := algebraMap BoundaryAffinePlane
    (Localization.Away zBoundaryDenominator)
  simpa [zBoundaryQuadricPolynomial, zBoundaryCubicPolynomial,
    zBoundaryNormalIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton] using
    zBoundary_intersectionIdeal_eq_normalForm
      (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1))
      (by
        change IsUnit (1 + f (MvPolynomial.X 1))
        rw [← map_one f, ← map_add]
        exact IsLocalization.Away.algebraMap_isUnit zBoundaryDenominator)

theorem zBoundaryLocalizedEvaluation_ker_eq_chartIdeal :
    RingHom.ker zBoundaryLocalizedEvaluation =
      Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away zBoundaryDenominator))
        (Ideal.span {zBoundaryQuadricPolynomial,
          zBoundaryCubicPolynomial}) := by
  rw [zBoundaryLocalizedEvaluation,
    awayLift_ker, zBoundaryEvaluation_ker,
    zBoundaryLocalized_chartIdeal_eq_normalIdeal.symm]

theorem zBoundaryLocalizedEvaluation_surjective :
    Function.Surjective zBoundaryLocalizedEvaluation := by
  intro x
  obtain ⟨p, rfl⟩ := zBoundaryEvaluation_surjective x
  refine ⟨algebraMap BoundaryAffinePlane
    (Localization.Away zBoundaryDenominator) p, ?_⟩
  exact IsLocalization.Away.lift_eq zBoundaryDenominator
    zBoundaryEvaluation_denominator_isUnit p

noncomputable def zBoundaryLocalizedChartQuotientEquiv :
    (Localization.Away zBoundaryDenominator ⧸
      Ideal.map
        (algebraMap BoundaryAffinePlane
          (Localization.Away zBoundaryDenominator))
        (Ideal.span {zBoundaryQuadricPolynomial,
          zBoundaryCubicPolynomial})) ≃+* DoubleArtin :=
  (Ideal.quotEquivOfEq
      zBoundaryLocalizedEvaluation_ker_eq_chartIdeal.symm).trans
    (RingHom.quotientKerEquivOfSurjective
      zBoundaryLocalizedEvaluation_surjective)

/-- The isolated factor at `[0:0:1:0]` has `F₂`-length two. -/
theorem zBoundaryLocalizedChartQuotient_f2_length :
    Module.length (ZMod 2)
      (Localization.Away zBoundaryDenominator ⧸
        Ideal.map
          (algebraMap BoundaryAffinePlane
            (Localization.Away zBoundaryDenominator))
          (Ideal.span {zBoundaryQuadricPolynomial,
            zBoundaryCubicPolynomial})) = 2 := by
  let e :
      (Localization.Away zBoundaryDenominator ⧸
        Ideal.map
          (algebraMap BoundaryAffinePlane
            (Localization.Away zBoundaryDenominator))
          (Ideal.span {zBoundaryQuadricPolynomial,
            zBoundaryCubicPolynomial})) ≃ₗ[ZMod 2] DoubleArtin :=
    zmodLinearEquivOfRingEquiv zBoundaryLocalizedChartQuotientEquiv
  rw [e.length_eq]
  letI : Module.Finite (ZMod 2) DoubleArtin :=
    (Polynomial.monic_X_pow 2).finite_adjoinRoot
  rw [Module.length_eq_finrank, doubleArtin_finrank]
  norm_num

/-! ## The reduced point `[0:1:1:0]` -/

/-- In the `y = 1` chart, put `a=z+1` and `b=x`.  On `W = 0` the
equations become `a+b+a*b` and `b*(1+a)`. -/
theorem yzBoundary_quadric
    {K : Type*} [CommRing K] [CharP K 2] (a b : K) :
    canonicalQuadric25Over (⟨b, 1, 1 + a, 0⟩ : Coordinates4 K) =
      a + b + a * b := by
  dsimp [canonicalQuadric25Over]
  rw [CharTwo.neg_eq]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination htwo

theorem yzBoundary_cubic
    {K : Type*} [CommRing K] (a b : K) :
    canonicalCubic25Over (⟨b, 1, 1 + a, 0⟩ : Coordinates4 K) =
      b * (1 + a) := by
  simp [canonicalCubic25Over]

/-- The `y = 1` boundary equations cut out the reduced origin. -/
theorem yzBoundary_intersectionIdeal_eq_normalForm
    {R : Type*} [CommRing R] (a b : R) (htwo : (2 : R) = 0) :
    Ideal.span {a + b + a * b, b * (1 + a)} =
      Ideal.span {a, b} := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.mem_span_pair.mpr ⟨1 + b, 1, by ring⟩
    · exact Ideal.mem_span_pair.mpr ⟨b, 1, by ring⟩
  · refine Ideal.span_le.2 ?_
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with hr | hr
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨1, 1, by
        linear_combination (b + a * b) * htwo⟩
    · subst r
      exact Ideal.mem_span_pair.mpr ⟨-b, 1 - b, by
        linear_combination -(b ^ 2 + a * b ^ 2) * htwo⟩

noncomputable def yzBoundaryQuadricPolynomial : BoundaryAffinePlane :=
  MvPolynomial.X 0 + MvPolynomial.X 1 +
    MvPolynomial.X 0 * MvPolynomial.X 1

noncomputable def yzBoundaryCubicPolynomial : BoundaryAffinePlane :=
  MvPolynomial.X 1 * (1 + MvPolynomial.X 0)

def yzBoundaryChartIdeal : Ideal BoundaryAffinePlane :=
  Ideal.span {yzBoundaryQuadricPolynomial, yzBoundaryCubicPolynomial}

/-- The actual `y = 1` equations generate the maximal ideal of the
translated origin. -/
theorem yzBoundaryChartIdeal_eq_reducedNormalIdeal :
    yzBoundaryChartIdeal = zReducedNormalIdeal := by
  have htwo : (2 : BoundaryAffinePlane) = 0 := by
    have htwoCoeff : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
    change MvPolynomial.C (2 : ZMod 2) = 0
    rw [htwoCoeff, map_zero]
  simpa [yzBoundaryChartIdeal, yzBoundaryQuadricPolynomial,
    yzBoundaryCubicPolynomial, zReducedNormalIdeal] using
    yzBoundary_intersectionIdeal_eq_normalForm
      (MvPolynomial.X 0 : BoundaryAffinePlane)
      (MvPolynomial.X 1 : BoundaryAffinePlane) htwo

/-- Evaluation at the translated origin has exactly the `y = 1` boundary
equation ideal as kernel. -/
theorem yzBoundary_reducedEvaluation_ker :
    RingHom.ker zReducedEvaluation.toRingHom = yzBoundaryChartIdeal := by
  rw [zReducedEvaluation_ker, yzBoundaryChartIdeal_eq_reducedNormalIdeal]

noncomputable def yzBoundaryChartQuotientEquiv :
    (BoundaryAffinePlane ⧸ yzBoundaryChartIdeal) ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq yzBoundary_reducedEvaluation_ker.symm).trans
    (RingHom.quotientKerEquivOfSurjective zReducedEvaluation_surjective)

/-- The isolated factor at `[0:1:1:0]` is reduced and has `F₂`-length
one. -/
theorem yzBoundaryChartQuotient_f2_length :
    Module.length (ZMod 2)
      (BoundaryAffinePlane ⧸ yzBoundaryChartIdeal) = 1 := by
  let e :
      (BoundaryAffinePlane ⧸ yzBoundaryChartIdeal) ≃ₗ[ZMod 2] ZMod 2 :=
    zmodLinearEquivOfRingEquiv yzBoundaryChartQuotientEquiv
  rw [e.length_eq, Module.length_eq_one]

/-- The three isolated `W = 0` factors have total ground-field length six. -/
theorem wBoundary_total_f2_length :
    (3 : ℕ) + 2 + 1 = 6 := by norm_num

/-! ## Effective boundary cycle -/

/-- The explicit degree-six hyperplane cycle cut out by `W = 0` in the full
closed-point grading.  Its coefficients are the three Artin lengths above;
the atom degrees are all one. -/
noncomputable def wBoundaryHyperplaneDivisor :
    fullClosedPointGrading25Two.EffDiv :=
  Finsupp.single fullBoundaryAtomX 3 +
    Finsupp.single fullBoundaryAtomYZ 1 +
    Finsupp.single fullBoundaryAtomZ 2

/-- The `W = 0` boundary cycle has degree six. -/
theorem wBoundaryHyperplaneDivisor_degree :
    fullClosedPointGrading25Two.divDegree wBoundaryHyperplaneDivisor = 6 := by
  rw [wBoundaryHyperplaneDivisor,
    fullClosedPointGrading25Two.divDegree_add,
    fullClosedPointGrading25Two.divDegree_add]
  simp [fullClosedPointGrading25Two.divDegree_single]

/-- The explicit `W = 0` hyperplane cycle as an effective divisor of degree
six. -/
noncomputable def wBoundaryHyperplaneEffectiveDegreeSix :
    fullClosedPointGrading25Two.EffDivOfDegree 6 :=
  ⟨wBoundaryHyperplaneDivisor, wBoundaryHyperplaneDivisor_degree⟩

end MazurProof.RationalPointsN25QuotientTwoWBoundaryArtinLocal
