import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSound
import FLT.Assumptions.MazurProof.N18PackageII
import FLT.Assumptions.MazurProof.N18RouteC_Reduction
import FLT.Assumptions.MazurProof.N18VpiWrapper

/-!
# Reduction of the N18 good model at `pi`

This file constructs the residue map and the pointwise reduction from the
`L`-points of the integral good model to its seven-point special fibre over
`ZMod 3`.  Additivity is proved in `N18GoodModelAssembly`.
-/

open scoped Classical NumberField WeierstrassCurve.Affine

namespace MazurProof.N18ReductionGood

open MazurProof.N18RouteC
open MazurProof.N18RouteC.FieldArithmetic
open MazurProof.N18RouteC.GoodModel
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18RouteC.LocalThreeSound

noncomputable section

set_option maxHeartbeats 0

abbrev OL := NumberField.RingOfIntegers L
abbrev LocalOL :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L p3
abbrev GoodPoint := WeierstrassCurve.Affine.Point E0Good
abbrev RedPoint := MazurProof.N18RouteC.Reduction.RedPoint

/-! ## The residue map on the local ring -/

/-- Reduction modulo `pi` on the global ring of integers.  In the integral
power basis `1, pi, pi^2`, this is the constant coordinate modulo `3`. -/
def reduceModPiOL : OL →+* ZMod 3 where
  toFun u := ((coordsOf u).c0 : ZMod 3)
  map_zero' := by simp [coordsOf_zero]
  map_one' := by simp [coordsOf_one, IntCoords.one]
  map_add' x y := by simp [coordsOf_add, IntCoords.add]
  map_mul' x y := by
    rw [coordsOf_mul]
    simp only [IntCoords.mul, prodC0]
    push_cast
    rw [show (3 : ZMod 3) = 0 by decide,
      show (9 : ZMod 3) = 0 by decide]
    ring

@[simp] theorem reduceModPiOL_pi : reduceModPiOL piInteger = 0 := by
  simp [reduceModPiOL, coordsOf_piInteger]

private theorem reduceModPiOL_isUnit_of_mem_primeCompl
    (s : p3.asIdeal.primeCompl) : IsUnit (reduceModPiOL s) := by
  apply isUnit_iff_ne_zero.mpr
  have hs := reduceOL_isUnit_of_not_mem s.prop
  rw [MazurProof.N18RouteC.LocalThree.isUnit5_iff] at hs
  simpa [reduceModPiOL, reduceOL, IntCoords.red, reduceInt,
    MazurProof.N18RouteC.LocalThree.red3] using hs

/-- Reduction modulo `pi`, extended from `OL` to its localization at `(pi)`. -/
def reduceModPi : LocalOL →+* ZMod 3 :=
  IsLocalization.lift reduceModPiOL_isUnit_of_mem_primeCompl

@[simp] theorem reduceModPi_algebraMap (u : OL) :
    reduceModPi (algebraMap OL LocalOL u) = reduceModPiOL u := by
  exact IsLocalization.lift_eq reduceModPiOL_isUnit_of_mem_primeCompl u

@[simp] theorem reduceModPi_aInteger :
    reduceModPi (algebraMap OL LocalOL aInteger) = 1 := by
  rw [reduceModPi_algebraMap]
  simp [reduceModPiOL, coordsOf_aInteger, aCoords]

private theorem maximalIdeal_eq_span_piLocal :
    IsLocalRing.maximalIdeal LocalOL =
      Ideal.span ({algebraMap OL LocalOL piInteger} : Set LocalOL) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p3.asIdeal LocalOL]
  change Ideal.map (algebraMap OL LocalOL) primeAboveThree = _
  rw [primeAboveThree_eq_span_pi, Ideal.map_span]
  rfl

theorem reduceModPi_eq_zero_iff_mem_maximal (u : LocalOL) :
    reduceModPi u = 0 ↔ u ∈ IsLocalRing.maximalIdeal LocalOL := by
  have hle : IsLocalRing.maximalIdeal LocalOL ≤ RingHom.ker reduceModPi := by
    rw [maximalIdeal_eq_span_piLocal, Ideal.span_le]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    simp [RingHom.mem_ker]
  have hker : RingHom.ker reduceModPi = IsLocalRing.maximalIdeal LocalOL := by
    symm
    exact (IsLocalRing.maximalIdeal.isMaximal LocalOL).eq_of_le hle (by
      intro htop
      have h1 : (1 : LocalOL) ∈ RingHom.ker reduceModPi := by rw [htop]; trivial
      simpa [RingHom.mem_ker] using h1)
  rw [← RingHom.mem_ker, hker]

private theorem mem_maximal_iff_v3_lt_one (u : LocalOL) :
    u ∈ IsLocalRing.maximalIdeal LocalOL ↔ v3 (u : L) < 1 := by
  change u ∈ IsLocalRing.maximalIdeal
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L p3) ↔ _
  rw [show IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L p3 =
      v3.valuationSubring from
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact Valuation.mem_maximalIdeal_iff

private theorem v3_le_one_of_ordPi_nonneg {x : L} (hx : 0 ≤ ordPi x) :
    v3 x ≤ 1 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hlog : WithZero.log (v3 x) ≤ 0 := by
      unfold ordPi at hx
      omega
    have h := (WithZero.log_le_iff_le_exp (v3_ne_zero hx0)).mp hlog
    simpa using h

/-- A field element of nonnegative `pi`-order, regarded as an element of the
localization of `OL` at `(pi)`. -/
def localOfNonneg (x : L) (hx : 0 ≤ ordPi x) : LocalOL :=
  ⟨x, by
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact v3_le_one_of_ordPi_nonneg hx⟩

@[simp] theorem localOfNonneg_coe (x : L) (hx : 0 ≤ ordPi x) :
    ((localOfNonneg x hx : LocalOL) : L) = x := rfl

private theorem good_coeff_orders :
    0 ≤ ordPi E0Good.a₁ ∧ 0 ≤ ordPi E0Good.a₂ ∧
    0 ≤ ordPi E0Good.a₃ ∧ 0 ≤ ordPi E0Good.a₄ ∧
    0 ≤ ordPi E0Good.a₆ := by
  have hmap := MazurProof.N18PackageII.E0GoodInt_map
  have h1 := congrArg (fun W : WeierstrassCurve L ↦ W.a₁) hmap
  have h2 := congrArg (fun W : WeierstrassCurve L ↦ W.a₂) hmap
  have h3 := congrArg (fun W : WeierstrassCurve L ↦ W.a₃) hmap
  have h4 := congrArg (fun W : WeierstrassCurve L ↦ W.a₄) hmap
  have h6 := congrArg (fun W : WeierstrassCurve L ↦ W.a₆) hmap
  simp only [WeierstrassCurve.map_a₁] at h1
  simp only [WeierstrassCurve.map_a₂] at h2
  simp only [WeierstrassCurve.map_a₃] at h3
  simp only [WeierstrassCurve.map_a₄] at h4
  simp only [WeierstrassCurve.map_a₆] at h6
  rw [← h1, ← h2, ← h3, ← h4, ← h6]
  exact ⟨GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _,
    GoodModel.zero_le_ordPi_ringOfIntegers _⟩

private theorem ordPi_mul_nonneg {u w : L}
    (hu : 0 ≤ ordPi u) (hw : 0 ≤ ordPi w) :
    0 ≤ ordPi (u * w) := by
  by_cases hu0 : u = 0
  · simp [hu0, ordPi_zero]
  by_cases hw0 : w = 0
  · simp [hw0, ordPi_zero]
  rw [ordPi_mul hu0 hw0]
  omega

private theorem ordPi_le_mul_right {u w : L}
    (hu : 0 ≤ ordPi u) (hw : ordPi w ≤ 0) :
    ordPi w ≤ ordPi (u * w) := by
  by_cases hu0 : u = 0
  · simp [hu0, ordPi_zero, hw]
  by_cases hw0 : w = 0
  · simp [hw0, ordPi_zero]
  rw [ordPi_mul hu0 hw0]
  omega

private theorem y_nonneg_of_x_nonneg {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) : 0 ≤ ordPi y := by
  by_cases hy0 : y = 0
  · simp [hy0, ordPi_zero]
  by_contra hy
  have hyneg : ordPi y < 0 := lt_of_not_ge hy
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have hx2 : 0 ≤ ordPi (x ^ 2) := by
    rw [pow_two]
    exact ordPi_mul_nonneg hx hx
  have hx3 : 0 ≤ ordPi (x ^ 3) := by
    rw [show x ^ 3 = x ^ 2 * x by ring]
    exact ordPi_mul_nonneg hx2 hx
  have hrhs : 0 ≤ ordPi
      (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    have h2 := ordPi_mul_nonneg ha2 hx2
    have h4 := ordPi_mul_nonneg ha4 hx
    exact le_ordPi_add
      (le_ordPi_add (le_ordPi_add hx3 h2 le_rfl) h4 le_rfl) ha6 le_rfl
  let tail := E0Good.a₁ * x * y + E0Good.a₃ * y
  have htail : ordPi y ≤ ordPi tail := by
    have hax : 0 ≤ ordPi (E0Good.a₁ * x) :=
      ordPi_mul_nonneg ha1 hx
    have h1 : ordPi y ≤ ordPi (E0Good.a₁ * x * y) :=
      ordPi_le_mul_right hax hyneg.le
    have h3 : ordPi y ≤ ordPi (E0Good.a₃ * y) :=
      ordPi_le_mul_right ha3 hyneg.le
    exact le_ordPi_add h1 h3 hyneg.le
  have hy2 : ordPi (y ^ 2) = 2 * ordPi y := by
    rw [pow_two, ordPi_mul hy0 hy0]
    ring
  have hlhs0 : y ^ 2 + tail ≠ 0 := by
    by_cases ht0 : tail = 0
    · simp [ht0, hy0]
    · intro hzero
      have heq := ordPi_add_eq_of_lt (pow_ne_zero 2 hy0) ht0 (by
        rw [hy2]
        omega)
      rw [hzero, ordPi_zero, hy2] at heq
      omega
  have hlhs : ordPi (y ^ 2 + tail) = 2 * ordPi y := by
    by_cases ht0 : tail = 0
    · simp [ht0, hy2]
    · rw [ordPi_add_eq_of_lt (pow_ne_zero 2 hy0) ht0 (by
          rw [hy2]
          omega), hy2]
  have hcurve := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  have hcurve' : y ^ 2 + tail =
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ := by
    simpa only [tail, add_assoc] using hcurve
  have hrhs0 :
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ ≠ 0 := by
    rwa [← hcurve']
  have hord := congrArg ordPi hcurve'
  rw [hlhs] at hord
  omega

/-! ## Compatibility of the integral and reduced equations -/

def E0GoodLocal : WeierstrassCurve LocalOL :=
  MazurProof.N18PackageII.E0GoodInt.map (algebraMap OL LocalOL)

theorem E0GoodLocal_map_L :
    E0GoodLocal.map (algebraMap LocalOL L) = E0Good := by
  rw [E0GoodLocal, ← WeierstrassCurve.map_map]
  simpa only [IsScalarTower.algebraMap_eq OL LocalOL L] using
    MazurProof.N18PackageII.E0GoodInt_map

theorem E0GoodLocal_reduce :
    E0GoodLocal.map reduceModPi = reducedGoodCurve := by
  ext <;>
    simp [E0GoodLocal, MazurProof.N18PackageII.E0GoodInt,
      reducedGoodCurve]

private theorem local_equation {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    WeierstrassCurve.Affine.Equation E0GoodLocal
      (localOfNonneg x hx) (localOfNonneg y hy) := by
  apply (E0GoodLocal.map_equation
    (algebraMap LocalOL L).injective _ _).mp
  simpa only [E0GoodLocal_map_L, localOfNonneg_coe] using h.1

private theorem reduced_equation {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    WeierstrassCurve.Affine.Equation reducedGoodCurve
      (reduceModPi (localOfNonneg x hx))
      (reduceModPi (localOfNonneg y hy)) := by
  rw [← E0GoodLocal_reduce]
  exact (local_equation h hx hy).map reduceModPi

def reduceIntegralPoint {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) : RedPoint :=
  let hy := y_nonneg_of_x_nonneg h hx
  WeierstrassCurve.Affine.Point.mk (reduced_equation h hx hy)

/-! ## Pointwise reduction -/

def reducePoint : GoodPoint → RedPoint
  | .zero => .zero
  | .some x y h =>
      if hx : ordPi x < 0 then .zero
      else reduceIntegralPoint h (le_of_not_gt hx)

@[simp] theorem reducePoint_zero : reducePoint (0 : GoodPoint) = 0 := rfl

@[simp] theorem reducePoint_some_of_neg {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : ordPi x < 0) :
    reducePoint (.some x y h) = 0 := by
  simp [reducePoint, hx]

@[simp] theorem reducePoint_some_of_nonneg {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) :
    reducePoint (.some x y h) = reduceIntegralPoint h hx := by
  simp [reducePoint, not_lt.mpr hx]

theorem reduceIntegralPoint_ne_zero {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) :
    reduceIntegralPoint h hx ≠ 0 := by
  simp [reduceIntegralPoint, WeierstrassCurve.Affine.Point.mk,
    WeierstrassCurve.Affine.Point.zero_def]

theorem reducePoint_eq_zero_iff (P : GoodPoint) :
    reducePoint P = 0 ↔
      P = 0 ∨
        match P with
        | .zero => False
        | .some x _ _ => ordPi x < 0 := by
  cases P with
  | zero => simp
  | some x y h =>
      by_cases hx : ordPi x < 0
      · simp [reducePoint, hx]
      · have hx' : 0 ≤ ordPi x := le_of_not_gt hx
        simp [reducePoint, hx, reduceIntegralPoint_ne_zero h hx']

end

end MazurProof.N18ReductionGood
