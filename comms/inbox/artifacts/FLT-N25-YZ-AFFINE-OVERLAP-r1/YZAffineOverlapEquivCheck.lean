import ZChartFractionEquivCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace MazurProof.RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
abbrev YChartRing := ChartQuotient (1 : Fin 4)

def yZ : YChartRing := chartMap 1 (MvPolynomial.X 2)


def yzW : YChartRing := chartMap 1 (MvPolynomial.X 3)

end MazurProof.RationalPointsN25QuotientTwoWBoundaryYZChartArtin

namespace MazurProof.N25F_YZOverlapMap
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
/-- The actual X/Y coordinate, exposed here because its original name is private. -/
def yX : YChartRing := chartMap 1 (MvPolynomial.X 0)
end MazurProof.N25F_YZOverlapMap

namespace MazurProof.N25F_YZAffineOverlapEquiv

open RationalPointsN25QuotientF2
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoStructuralJacobian
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWBoundaryZLocal
open RationalPointsN25QuotientTwoWBoundaryYZChartArtin
open N25F_ZChartWChartEquiv N25F_YZOverlapMap

/-- The actual Y-chart affine open on which Z/Y is invertible. -/
abbrev YZOpen := Localization.Away yZ

/-- The actual Z-chart affine open on which Y/Z is invertible. -/
abbrev ZYOpen := Localization.Away zY

private def affinePointEval {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A) : AffineChart pivot →ₐ[ZMod 2] A :=
  MvPolynomial.aeval (fun j => coordinates4ToFun P j.1)

private theorem affinePointEval_comp_dehomogenize
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A)
    (hp : coordinates4ToFun P pivot = 1) :
    (affinePointEval pivot P).toRingHom.comp (ambientDehomogenize pivot) =
      MvPolynomial.eval₂Hom (algebraMap (ZMod 2) A) (coordinates4ToFun P) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [affinePointEval, ambientDehomogenize]
  · intro j
    by_cases hj : j = pivot
    · subst j
      simp [affinePointEval, ambientDehomogenize, dehomogenizedVariable, hp]
    · simp [affinePointEval, ambientDehomogenize, dehomogenizedVariable, hj]

private theorem mappedAmbientPoint_eval
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (P : Coordinates4 A) :
    mappedAmbientPoint
        (MvPolynomial.eval₂Hom (algebraMap (ZMod 2) A) (coordinates4ToFun P)) =
      P := by
  cases P
  simp [mappedAmbientPoint, coordinates4ToFun]

private def chartPointEval {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A)
    (hp : coordinates4ToFun P pivot = 1)
    (hq : canonicalQuadric25CharTwo P = 0)
    (hc : canonicalCubic25CharTwo P = 0) : ChartQuotient pivot →ₐ[ZMod 2] A :=
  Ideal.Quotient.liftₐ (chartAffineEquationIdeal pivot) (affinePointEval pivot P)
    (by
      intro f hf
      have hker : chartAffineEquationIdeal pivot ≤
          RingHom.ker (affinePointEval pivot P).toRingHom := by
        rw [chartAffineEquationIdeal, chartAffineRelation_range]
        refine Ideal.span_le.2 ?_
        intro g hg
        rcases hg with rfl | rfl
        · change ((affinePointEval pivot P).toRingHom.comp
            (ambientDehomogenize pivot)) canonicalQuadricPolynomial25Two = 0
          rw [affinePointEval_comp_dehomogenize pivot P hp,
            map_canonicalQuadric, mappedAmbientPoint_eval]
          exact hq
        · change ((affinePointEval pivot P).toRingHom.comp
            (ambientDehomogenize pivot)) canonicalCubicPolynomial25Two = 0
          rw [affinePointEval_comp_dehomogenize pivot P hp,
            map_canonicalCubic, mappedAmbientPoint_eval]
          exact hc
      exact hker hf)

private theorem chartPointEval_chartMap_X
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (P : Coordinates4 A)
    (hp : coordinates4ToFun P pivot = 1)
    (hq : canonicalQuadric25CharTwo P = 0)
    (hc : canonicalCubic25CharTwo P = 0) (j : Fin 4) :
    chartPointEval pivot P hp hq hc (chartMap pivot (MvPolynomial.X j)) =
      coordinates4ToFun P j := by
  change ((affinePointEval pivot P).toRingHom.comp (ambientDehomogenize pivot))
    (MvPolynomial.X j) = _
  rw [affinePointEval_comp_dehomogenize pivot P hp]
  simp


private theorem yChartPoint_eq :
    chartQuotientPoint (1 : Fin 4) = (⟨yX, 1, yZ, yzW⟩ : Coordinates4 YChartRing) := by
  simp [chartQuotientPoint, mappedAmbientPoint, yX, yZ, yzW, chartMap_X_pivot]

private theorem zChartPoint_eq :
    chartQuotientPoint (2 : Fin 4) = (⟨zX, zY, 1, zW⟩ : Coordinates4 ZChartRing) := by
  simp [chartQuotientPoint, mappedAmbientPoint, zX, zY, zW, chartMap_X_pivot]

private def normalizedYPoint : Coordinates4 ZYOpen :=
  scaleCoordinates4 (IsLocalization.Away.invSelf zY : ZYOpen)
    (mapCoordinates4 (algebraMap ZChartRing ZYOpen) (chartQuotientPoint 2))

private def normalizedZPoint : Coordinates4 YZOpen :=
  scaleCoordinates4 (IsLocalization.Away.invSelf yZ : YZOpen)
    (mapCoordinates4 (algebraMap YChartRing YZOpen) (chartQuotientPoint 1))

private theorem normalizedYPoint_y : (normalizedYPoint).y = 1 := by
  rw [normalizedYPoint, zChartPoint_eq]
  change (IsLocalization.Away.invSelf zY : ZYOpen) *
    algebraMap ZChartRing ZYOpen zY = 1
  rw [mul_comm, IsLocalization.Away.mul_invSelf]

private theorem normalizedZPoint_z : (normalizedZPoint).z = 1 := by
  rw [normalizedZPoint, yChartPoint_eq]
  change (IsLocalization.Away.invSelf yZ : YZOpen) *
    algebraMap YChartRing YZOpen yZ = 1
  rw [mul_comm, IsLocalization.Away.mul_invSelf]

private theorem normalizedYPoint_quadric :
    canonicalQuadric25CharTwo normalizedYPoint = 0 := by
  rw [normalizedYPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem normalizedYPoint_cubic :
    canonicalCubic25CharTwo normalizedYPoint = 0 := by
  rw [normalizedYPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

private theorem normalizedZPoint_quadric :
    canonicalQuadric25CharTwo normalizedZPoint = 0 := by
  rw [normalizedZPoint, canonicalQuadric25CharTwo_scale,
    ← map_canonicalQuadric_coordinates, chartQuotientPoint_quadric, map_zero, mul_zero]

private theorem normalizedZPoint_cubic :
    canonicalCubic25CharTwo normalizedZPoint = 0 := by
  rw [normalizedZPoint, canonicalCubic25CharTwo_scale,
    ← map_canonicalCubic_coordinates, chartQuotientPoint_cubic, map_zero, mul_zero]

/-- Evaluate the actual Y chart on the Z-chart open, rescaling by (Y/Z)⁻¹. -/
def yChartToZYOpen : YChartRing →ₐ[ZMod 2] ZYOpen :=
  chartPointEval 1 normalizedYPoint
    (by simpa [coordinates4ToFun] using normalizedYPoint_y)
    normalizedYPoint_quadric normalizedYPoint_cubic

/-- Evaluate the actual Z chart on the Y-chart open, rescaling by (Z/Y)⁻¹. -/
def zChartToYZOpen : ZChartRing →ₐ[ZMod 2] YZOpen :=
  chartPointEval 2 normalizedZPoint
    (by simpa [coordinates4ToFun] using normalizedZPoint_z)
    normalizedZPoint_quadric normalizedZPoint_cubic

@[simp]
theorem yChartToZYOpen_yX :
    yChartToZYOpen yX = (IsLocalization.Away.invSelf zY : ZYOpen) *
      algebraMap ZChartRing ZYOpen zX := by
  rw [yChartToZYOpen, yX, chartPointEval_chartMap_X, normalizedYPoint, zChartPoint_eq]
  rfl

@[simp]
theorem yChartToZYOpen_yZ :
    yChartToZYOpen yZ = (IsLocalization.Away.invSelf zY : ZYOpen) := by
  rw [yChartToZYOpen, yZ, chartPointEval_chartMap_X, normalizedYPoint, zChartPoint_eq]
  change (IsLocalization.Away.invSelf zY : ZYOpen) *
    algebraMap ZChartRing ZYOpen 1 = _
  rw [map_one, mul_one]

@[simp]
theorem yChartToZYOpen_yzW :
    yChartToZYOpen yzW = (IsLocalization.Away.invSelf zY : ZYOpen) *
      algebraMap ZChartRing ZYOpen zW := by
  rw [yChartToZYOpen, yzW, chartPointEval_chartMap_X, normalizedYPoint, zChartPoint_eq]
  rfl

@[simp]
theorem zChartToYZOpen_zX :
    zChartToYZOpen zX = (IsLocalization.Away.invSelf yZ : YZOpen) *
      algebraMap YChartRing YZOpen yX := by
  rw [zChartToYZOpen, zX, chartPointEval_chartMap_X, normalizedZPoint, yChartPoint_eq]
  rfl

@[simp]
theorem zChartToYZOpen_zY :
    zChartToYZOpen zY = (IsLocalization.Away.invSelf yZ : YZOpen) := by
  rw [zChartToYZOpen, zY, chartPointEval_chartMap_X, normalizedZPoint, yChartPoint_eq]
  change (IsLocalization.Away.invSelf yZ : YZOpen) *
    algebraMap YChartRing YZOpen 1 = _
  rw [map_one, mul_one]

@[simp]
theorem zChartToYZOpen_zW :
    zChartToYZOpen zW = (IsLocalization.Away.invSelf yZ : YZOpen) *
      algebraMap YChartRing YZOpen yzW := by
  rw [zChartToYZOpen, zW, chartPointEval_chartMap_X, normalizedZPoint, yChartPoint_eq]
  rfl

private theorem yChartToZYOpen_powers_isUnit (s : Submonoid.powers yZ) :
    IsUnit (yChartToZYOpen (s : YChartRing)) := by
  obtain ⟨n, hn⟩ := s.2
  rw [← hn, map_pow, yChartToZYOpen_yZ]
  apply IsUnit.pow
  exact isUnit_iff_exists_inv.mpr ⟨algebraMap ZChartRing ZYOpen zY, by
    rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩

private theorem zChartToYZOpen_powers_isUnit (s : Submonoid.powers zY) :
    IsUnit (zChartToYZOpen (s : ZChartRing)) := by
  obtain ⟨n, hn⟩ := s.2
  rw [← hn, map_pow, zChartToYZOpen_zY]
  apply IsUnit.pow
  exact isUnit_iff_exists_inv.mpr ⟨algebraMap YChartRing YZOpen yZ, by
    rw [mul_comm, IsLocalization.Away.mul_invSelf]⟩

/-- Extend homogeneous Y-to-Z rescaling to the actual Y/Z affine overlap. -/
def yzOpenToZYOpen : YZOpen →ₐ[ZMod 2] ZYOpen :=
  IsLocalization.liftAlgHom
    (A := ZMod 2) (R := YChartRing) (S := YZOpen) (P := ZYOpen)
    (M := Submonoid.powers yZ) (f := yChartToZYOpen) yChartToZYOpen_powers_isUnit

/-- Extend homogeneous Z-to-Y rescaling to the actual Z/Y affine overlap. -/
def zyOpenToYZOpen : ZYOpen →ₐ[ZMod 2] YZOpen :=
  IsLocalization.liftAlgHom
    (A := ZMod 2) (R := ZChartRing) (S := ZYOpen) (P := YZOpen)
    (M := Submonoid.powers zY) (f := zChartToYZOpen) zChartToYZOpen_powers_isUnit

@[simp]
theorem yzOpenToZYOpen_algebraMap (a : YChartRing) :
    yzOpenToZYOpen (algebraMap YChartRing YZOpen a) = yChartToZYOpen a :=
  IsLocalization.lift_eq yChartToZYOpen_powers_isUnit a

@[simp]
theorem zyOpenToYZOpen_algebraMap (a : ZChartRing) :
    zyOpenToYZOpen (algebraMap ZChartRing ZYOpen a) = zChartToYZOpen a :=
  IsLocalization.lift_eq zChartToYZOpen_powers_isUnit a

/-- The inverse of Z/Y becomes the original coordinate Y/Z. -/
@[simp]
theorem yzOpenToZYOpen_invSelf :
    yzOpenToZYOpen (IsLocalization.Away.invSelf yZ : YZOpen) =
      algebraMap ZChartRing ZYOpen zY := by
  have h := congrArg yzOpenToZYOpen
    (IsLocalization.Away.mul_invSelf yZ (S := YZOpen))
  rw [map_mul, map_one, yzOpenToZYOpen_algebraMap, yChartToZYOpen_yZ] at h
  calc
    _ = 1 * yzOpenToZYOpen (IsLocalization.Away.invSelf yZ : YZOpen) := (one_mul _).symm
    _ = (algebraMap ZChartRing ZYOpen zY * IsLocalization.Away.invSelf zY) *
        yzOpenToZYOpen (IsLocalization.Away.invSelf yZ : YZOpen) := by
      rw [IsLocalization.Away.mul_invSelf]
    _ = _ := by rw [mul_assoc, h, mul_one]

/-- The inverse of Y/Z becomes the original coordinate Z/Y. -/
@[simp]
theorem zyOpenToYZOpen_invSelf :
    zyOpenToYZOpen (IsLocalization.Away.invSelf zY : ZYOpen) =
      algebraMap YChartRing YZOpen yZ := by
  have h := congrArg zyOpenToYZOpen
    (IsLocalization.Away.mul_invSelf zY (S := ZYOpen))
  rw [map_mul, map_one, zyOpenToYZOpen_algebraMap, zChartToYZOpen_zY] at h
  calc
    _ = 1 * zyOpenToYZOpen (IsLocalization.Away.invSelf zY : ZYOpen) := (one_mul _).symm
    _ = (algebraMap YChartRing YZOpen yZ * IsLocalization.Away.invSelf yZ) *
        zyOpenToYZOpen (IsLocalization.Away.invSelf zY : ZYOpen) := by
      rw [IsLocalization.Away.mul_invSelf]
    _ = _ := by rw [mul_assoc, h, mul_one]

private theorem chartAlgHom_ext {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (pivot : Fin 4) (f g : ChartQuotient pivot →ₐ[ZMod 2] A)
    (h : ∀ j : OtherCoordinate pivot,
      f (chartMap pivot (MvPolynomial.X j.1)) =
        g (chartMap pivot (MvPolynomial.X j.1))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  ext j
  simpa [chartMap, ambientDehomogenize, dehomogenizedVariable, j.2] using h j

private theorem zyOpenToYZOpen_comp_yzOpenToZYOpen :
    zyOpenToYZOpen.comp yzOpenToZYOpen = AlgHom.id (ZMod 2) YZOpen := by
  apply IsLocalization.algHom_ext (Submonoid.powers yZ)
  apply chartAlgHom_ext 1
  rintro ⟨j, hj⟩
  fin_cases j
  · change zyOpenToYZOpen (yzOpenToZYOpen (algebraMap YChartRing YZOpen yX)) =
      algebraMap YChartRing YZOpen yX
    simp only [yzOpenToZYOpen_algebraMap, yChartToZYOpen_yX, map_mul,
      zyOpenToYZOpen_invSelf, zyOpenToYZOpen_algebraMap, zChartToYZOpen_zX,
      ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  · exact (hj rfl).elim
  · change zyOpenToYZOpen (yzOpenToZYOpen (algebraMap YChartRing YZOpen yZ)) =
      algebraMap YChartRing YZOpen yZ
    rw [yzOpenToZYOpen_algebraMap, yChartToZYOpen_yZ, zyOpenToYZOpen_invSelf]
  · change zyOpenToYZOpen (yzOpenToZYOpen (algebraMap YChartRing YZOpen yzW)) =
      algebraMap YChartRing YZOpen yzW
    simp only [yzOpenToZYOpen_algebraMap, yChartToZYOpen_yzW, map_mul,
      zyOpenToYZOpen_invSelf, zyOpenToYZOpen_algebraMap, zChartToYZOpen_zW,
      ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]

private theorem yzOpenToZYOpen_comp_zyOpenToYZOpen :
    yzOpenToZYOpen.comp zyOpenToYZOpen = AlgHom.id (ZMod 2) ZYOpen := by
  apply IsLocalization.algHom_ext (Submonoid.powers zY)
  apply chartAlgHom_ext 2
  rintro ⟨j, hj⟩
  fin_cases j
  · change yzOpenToZYOpen (zyOpenToYZOpen (algebraMap ZChartRing ZYOpen zX)) =
      algebraMap ZChartRing ZYOpen zX
    simp only [zyOpenToYZOpen_algebraMap, zChartToYZOpen_zX, map_mul,
      yzOpenToZYOpen_invSelf, yzOpenToZYOpen_algebraMap, yChartToZYOpen_yX,
      ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]
  · change yzOpenToZYOpen (zyOpenToYZOpen (algebraMap ZChartRing ZYOpen zY)) =
      algebraMap ZChartRing ZYOpen zY
    rw [zyOpenToYZOpen_algebraMap, zChartToYZOpen_zY, yzOpenToZYOpen_invSelf]
  · exact (hj rfl).elim
  · change yzOpenToZYOpen (zyOpenToYZOpen (algebraMap ZChartRing ZYOpen zW)) =
      algebraMap ZChartRing ZYOpen zW
    simp only [zyOpenToYZOpen_algebraMap, zChartToYZOpen_zW, map_mul,
      yzOpenToZYOpen_invSelf, yzOpenToZYOpen_algebraMap, yChartToZYOpen_yzW,
      ← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]

/-- The coordinate-rigid equivalence between the two actual Y/Z affine opens. -/
def yzAffineOverlapEquiv : Localization.Away yZ ≃ₐ[ZMod 2] Localization.Away zY :=
  AlgEquiv.ofAlgHom yzOpenToZYOpen zyOpenToYZOpen
    yzOpenToZYOpen_comp_zyOpenToYZOpen zyOpenToYZOpen_comp_yzOpenToZYOpen

@[simp]
theorem yzAffineOverlapEquiv_algebraMap (a : YChartRing) :
    yzAffineOverlapEquiv (algebraMap YChartRing YZOpen a) = yChartToZYOpen a :=
  yzOpenToZYOpen_algebraMap a

@[simp]
theorem yzAffineOverlapEquiv_symm_algebraMap (a : ZChartRing) :
    yzAffineOverlapEquiv.symm (algebraMap ZChartRing ZYOpen a) = zChartToYZOpen a :=
  zyOpenToYZOpen_algebraMap a

@[simp]
theorem yzAffineOverlapEquiv_invSelf :
    yzAffineOverlapEquiv (IsLocalization.Away.invSelf yZ : YZOpen) =
      algebraMap ZChartRing ZYOpen zY :=
  yzOpenToZYOpen_invSelf

@[simp]
theorem yzAffineOverlapEquiv_symm_invSelf :
    yzAffineOverlapEquiv.symm (IsLocalization.Away.invSelf zY : ZYOpen) =
      algebraMap YChartRing YZOpen yZ :=
  zyOpenToYZOpen_invSelf

end MazurProof.N25F_YZAffineOverlapEquiv

#check @MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen
#check @MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen
#check @MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen_yX
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen_yX
#check @MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen_yZ
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen_yZ
#check @MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen_yzW
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yChartToZYOpen_yzW
#check @MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen_zX
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen_zX
#check @MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen_zY
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen_zY
#check @MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen_zW
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.zChartToYZOpen_zW
#check @MazurProof.N25F_YZAffineOverlapEquiv.yzOpenToZYOpen
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yzOpenToZYOpen
#check @MazurProof.N25F_YZAffineOverlapEquiv.zyOpenToYZOpen
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.zyOpenToYZOpen
#check @MazurProof.N25F_YZAffineOverlapEquiv.yzOpenToZYOpen_invSelf
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yzOpenToZYOpen_invSelf
#check @MazurProof.N25F_YZAffineOverlapEquiv.zyOpenToYZOpen_invSelf
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.zyOpenToYZOpen_invSelf
#check @MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv
#check @MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_algebraMap
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_algebraMap
#check @MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_symm_algebraMap
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_symm_algebraMap
#check @MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_invSelf
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_invSelf
#check @MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_symm_invSelf
#print axioms MazurProof.N25F_YZAffineOverlapEquiv.yzAffineOverlapEquiv_symm_invSelf
