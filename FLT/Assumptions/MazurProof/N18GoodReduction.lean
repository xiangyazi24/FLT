import FLT.Assumptions.MazurProof.N18AddCongr
import FLT.Assumptions.MazurProof.N18PackageII
import FLT.Assumptions.MazurProof.N18GoodModelValCoords
import FLT.Assumptions.MazurProof.N18VpiWrapper
import FLT.Assumptions.MazurProof.N18RouteC_GoodModel
import FLT.Assumptions.MazurProof.N18RouteC_Reduction
import FLT.Assumptions.MazurProof.N18RouteC_ThreeAdic
import FLT.Assumptions.MazurProof.N18Block5Instantiation
import FLT.Assumptions.MazurProof.N18RouteC_Block7
import FLT.Assumptions.MazurProof.N18RouteC_LocalThreeSound
import FLT.Assumptions.MazurProof.N18RouteC_TorsionTable

/-!
# Reduction data for the N18 good model

This file starts from the concrete integral basis `1, pi, pi^2` for `OL`.
Modulo the prime `(pi)`, the residue of an algebraic integer is its constant
coefficient modulo `3`.
-/

open scoped Classical NumberField WeierstrassCurve.Affine

namespace MazurProof.N18GoodReduction

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.IsogenyPoints
open MazurProof.N18RouteC.ThreeAdic
open MazurProof.N18RouteC.FieldArithmetic
open MazurProof.N18Block5Instantiation.AddCongr

noncomputable section

abbrev GoodPoint := MazurProof.N18RouteC.GoodModel.E0GoodPoint
abbrev RedPoint := MazurProof.N18RouteC.Reduction.RedPoint

/-- The affine `x`-coordinate on the good equation, totalized by `0` at `O`. -/
def xCoordGood : GoodPoint → L
  | .zero => 0
  | .some x _ _ => x

/-- The near-origin locus on the good equation. -/
def InFormalKernel : GoodPoint → Prop :=
  fun P ↦ P = 0 ∨ ordPi (xCoordGood P) < 0

/-- Constant coefficient in the integral basis `1, pi, pi^2`. -/
def coeff0 (u : OL) : ℤ := integralPowerBasis.repr u (0 : Fin 3)

/-- `pi`-coefficient in the integral basis `1, pi, pi^2`. -/
def coeff1 (u : OL) : ℤ := integralPowerBasis.repr u (1 : Fin 3)

/-- `pi^2`-coefficient in the integral basis `1, pi, pi^2`. -/
def coeff2 (u : OL) : ℤ := integralPowerBasis.repr u (2 : Fin 3)

theorem coeffs_eq (u : OL) :
    u = algebraMap ℤ OL (coeff0 u) +
        algebraMap ℤ OL (coeff1 u) * piInteger +
          algebraMap ℤ OL (coeff2 u) * piInteger ^ 2 := by
  apply Subtype.ext
  have hsum := integralPowerBasis.sum_repr u
  rw [Fin.sum_univ_three] at hsum
  have hsumL := congrArg (fun v : OL ↦ (v : L)) hsum
  change (u : L) = (coeff0 u : L) + (coeff1 u : L) * pi +
    (coeff2 u : L) * pi ^ 2
  simpa [coeff0, coeff1, coeff2, Algebra.smul_def,
    integralPowerBasis_coe_L, basis_apply] using hsumL.symm

theorem coeffs_coe_eq (u : OL) :
    (u : L) = ofCoords (coeff0 u) (coeff1 u) (coeff2 u) := by
  have hsum := integralPowerBasis.sum_repr u
  rw [Fin.sum_univ_three] at hsum
  have hsumL := congrArg (fun v : OL ↦ (v : L)) hsum
  simpa [coeff0, coeff1, coeff2, ofCoords, Algebra.smul_def,
    integralPowerBasis_coe_L, basis_apply] using hsumL.symm

theorem basis_repr_coe_zero (u : OL) :
    basis.repr (u : L) (0 : Fin 3) = coeff0 u := by
  rw [coeffs_coe_eq u]
  exact basis_repr_ofCoords_zero (coeff0 u : ℚ) (coeff1 u : ℚ) (coeff2 u : ℚ)

@[simp] theorem coeff0_zero : coeff0 0 = 0 := by
  simp [coeff0]

@[simp] theorem coeff0_one : coeff0 1 = 1 := by
  apply Int.cast_injective (α := ℚ)
  rw [← basis_repr_coe_zero]
  simpa [ofCoords] using basis_repr_ofCoords_zero (1 : ℚ) 0 0

@[simp] theorem coeff0_intCast (n : ℤ) :
    coeff0 (algebraMap ℤ OL n) = n := by
  apply Int.cast_injective (α := ℚ)
  rw [← basis_repr_coe_zero]
  simpa [ofCoords] using basis_repr_ofCoords_zero (n : ℚ) 0 0

@[simp] theorem coeff0_add (x y : OL) :
    coeff0 (x + y) = coeff0 x + coeff0 y := by
  simp [coeff0]

@[simp] theorem coeff0_neg (x : OL) :
    coeff0 (-x) = -coeff0 x := by
  simp [coeff0]

@[simp] theorem coeff0_sub (x y : OL) :
    coeff0 (x - y) = coeff0 x - coeff0 y := by
  simp [sub_eq_add_neg]

/-- Algebraic integers reduce by taking the constant coefficient modulo `3`. -/
def residueOL (u : OL) : ZMod 3 :=
  coeff0 u

@[simp] theorem residueOL_zero : residueOL 0 = 0 := by
  simp [residueOL]

@[simp] theorem residueOL_one : residueOL 1 = 1 := by
  simp [residueOL]

@[simp] theorem residueOL_add (x y : OL) :
    residueOL (x + y) = residueOL x + residueOL y := by
  simp [residueOL]

@[simp] theorem residueOL_neg (x : OL) :
    residueOL (-x) = -residueOL x := by
  simp [residueOL]

@[simp] theorem residueOL_sub (x y : OL) :
    residueOL (x - y) = residueOL x - residueOL y := by
  simp [sub_eq_add_neg]

@[simp] theorem residueOL_intCast (n : ℤ) :
    residueOL (algebraMap ℤ OL n) = n := by
  change ((coeff0 (algebraMap ℤ OL n) : ℤ) : ZMod 3) = n
  rw [coeff0_intCast]

@[simp] theorem residueOL_natCast (n : ℕ) :
    residueOL (n : OL) = n := by
  simpa using residueOL_intCast (n : ℤ)

@[simp] theorem algebraMap_OL_L_intCast (n : ℤ) :
    algebraMap OL L (algebraMap ℤ OL n) = (n : L) :=
  map_intCast (algebraMap OL L) n

@[simp] theorem algebraMap_OL_L_natCast (n : ℕ) :
    algebraMap OL L (n : OL) = (n : L) :=
  map_natCast (algebraMap OL L) n

@[simp] theorem residueOL_two : residueOL (2 : OL) = (2 : ZMod 3) :=
  residueOL_natCast 2

@[simp] theorem residueOL_three : residueOL (3 : OL) = (3 : ZMod 3) :=
  residueOL_natCast 3

@[simp] theorem residueOL_four : residueOL (4 : OL) = (4 : ZMod 3) :=
  residueOL_natCast 4

@[simp] theorem residueOL_seven : residueOL (7 : OL) = (7 : ZMod 3) :=
  residueOL_natCast 7

@[simp] theorem algebraMap_OL_L_two :
    algebraMap OL L (2 : OL) = (2 : L) :=
  algebraMap_OL_L_natCast 2

@[simp] theorem algebraMap_OL_L_three :
    algebraMap OL L (3 : OL) = (3 : L) :=
  algebraMap_OL_L_natCast 3

@[simp] theorem algebraMap_OL_L_four :
    algebraMap OL L (4 : OL) = (4 : L) :=
  algebraMap_OL_L_natCast 4

@[simp] theorem algebraMap_OL_L_seven :
    algebraMap OL L (7 : OL) = (7 : L) :=
  algebraMap_OL_L_natCast 7

theorem mem_primeAboveThree_iff_dvd_coeff0 (u : OL) :
    u ∈ primeAboveThree ↔ (3 : ℤ) ∣ coeff0 u := by
  constructor
  · rw [primeAboveThree_eq_span_pi, Ideal.mem_span_singleton]
    rintro ⟨b, hb⟩
    have hbL := congrArg (fun z : OL ↦ (z : L)) hb
    have hbpi :
        ((piInteger * b : OL) : L) =
          ofCoords (3 * coeff2 b) (coeff0 b) (-3 * coeff2 b + coeff1 b) := by
      calc
        ((piInteger * b : OL) : L) = pi * (b : L) := rfl
        _ = pi * ofCoords (coeff0 b) (coeff1 b) (coeff2 b) := by
          rw [coeffs_coe_eq b]
        _ = ofCoords (3 * coeff2 b) (coeff0 b)
              (-3 * coeff2 b + coeff1 b) := by
          unfold ofCoords
          ring_nf
          rw [pi_cubed]
          simp only [map_add, map_neg, map_mul, map_ofNat]
          ring
    have h0 : (coeff0 u : ℚ) = (3 * coeff2 b : ℚ) := by
      calc
        (coeff0 u : ℚ) = basis.repr (u : L) (0 : Fin 3) := by
          exact (basis_repr_coe_zero u).symm
        _ = basis.repr
              (ofCoords (3 * coeff2 b) (coeff0 b)
                (-3 * coeff2 b + coeff1 b)) (0 : Fin 3) := by
          rw [hbL, hbpi]
        _ = (3 * coeff2 b : ℚ) := by
          exact basis_repr_ofCoords_zero (3 * coeff2 b : ℚ)
            (coeff0 b : ℚ) (-3 * coeff2 b + coeff1 b : ℚ)
    refine ⟨coeff2 b, ?_⟩
    exact_mod_cast h0
  · rintro ⟨q, hq⟩
    rw [primeAboveThree_eq_span_pi, coeffs_eq u]
    apply Ideal.add_mem
    · apply Ideal.add_mem
      · rw [show coeff0 u = 3 * q by simpa using hq, map_mul]
        exact Ideal.mul_mem_right _ (Ideal.span ({piInteger} : Set OL))
          three_mem_span_pi
      · exact (Ideal.span ({piInteger} : Set OL)).mul_mem_left _
          (Ideal.subset_span (Set.mem_singleton piInteger))
    · apply (Ideal.span ({piInteger} : Set OL)).mul_mem_left
      exact (Ideal.span ({piInteger} : Set OL)).pow_mem_of_mem
        (Ideal.subset_span (Set.mem_singleton piInteger)) 2 (by norm_num)

theorem sub_const_mem_primeAboveThree (u : OL) :
    u - algebraMap ℤ OL (coeff0 u) ∈ primeAboveThree := by
  rw [mem_primeAboveThree_iff_dvd_coeff0]
  refine ⟨0, ?_⟩
  rw [coeff0_sub, coeff0_intCast]
  ring

@[simp] theorem residueOL_mul (x y : OL) :
    residueOL (x * y) = residueOL x * residueOL y := by
  have hx := sub_const_mem_primeAboveThree x
  have hy := sub_const_mem_primeAboveThree y
  have hmem :
      x * y - algebraMap ℤ OL (coeff0 x * coeff0 y) ∈ primeAboveThree := by
    have hxmul :
        (x - algebraMap ℤ OL (coeff0 x)) * y ∈ primeAboveThree :=
      Ideal.mul_mem_right _ primeAboveThree hx
    have hymul :
        algebraMap ℤ OL (coeff0 x) *
            (y - algebraMap ℤ OL (coeff0 y)) ∈ primeAboveThree :=
      Ideal.mul_mem_left primeAboveThree _ hy
    convert Ideal.add_mem primeAboveThree hxmul hymul using 1
    simp [map_mul]
    ring
  have hdvd := (mem_primeAboveThree_iff_dvd_coeff0
    (x * y - algebraMap ℤ OL (coeff0 x * coeff0 y))).mp hmem
  change ((coeff0 (x * y) : ℤ) : ZMod 3) =
    ((coeff0 x : ℤ) : ZMod 3) * ((coeff0 y : ℤ) : ZMod 3)
  rw [← Int.cast_mul]
  symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub
    (coeff0 x * coeff0 y) (coeff0 (x * y)) 3).2
  have hdvd' :
      (3 : ℤ) ∣ coeff0 (x * y) -
        coeff0 (algebraMap ℤ OL (coeff0 x * coeff0 y)) := by
    simpa [coeff0_sub] using hdvd
  have hconst :
      coeff0 (algebraMap ℤ OL (coeff0 x * coeff0 y)) =
        coeff0 x * coeff0 y :=
    coeff0_intCast _
  rw [hconst] at hdvd'
  exact hdvd'

@[simp] theorem residueOL_pow (x : OL) (n : ℕ) :
    residueOL (x ^ n) = residueOL x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, residueOL_mul, ih, pow_succ]

/-- Ring-hom form of the residue map on algebraic integers. -/
def residueOLHom : OL →+* ZMod 3 where
  toFun := residueOL
  map_zero' := residueOL_zero
  map_one' := residueOL_one
  map_add' := residueOL_add
  map_mul' := residueOL_mul

@[simp] theorem residueOLHom_apply (u : OL) :
    residueOLHom u = residueOL u := rfl

theorem residueOL_piInteger : residueOL piInteger = 0 := by
  change ((coeff0 piInteger : ℤ) : ZMod 3) = 0
  have h0 : coeff0 piInteger = 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [← basis_repr_coe_zero]
    simpa [ofCoords] using basis_repr_ofCoords_zero (0 : ℚ) 1 0
  simp [h0]

theorem residueOL_aInteger : residueOL aInteger = 1 := by
  change ((coeff0 aInteger : ℤ) : ZMod 3) = 1
  have h0 : coeff0 aInteger = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [← basis_repr_coe_zero]
    change basis.repr (pi + 1) (0 : Fin 3) = (1 : ℚ)
    rw [show pi + 1 = ofCoords (1 : ℚ) 1 0 by
      simp [ofCoords, add_comm]]
    exact basis_repr_ofCoords_zero (1 : ℚ) 1 0
  simp [h0]

/-! ## The integral good model and its special fibre -/

/-- The good equation with coefficients in the ring of integers. -/
def E0GoodInt : WeierstrassCurve OL where
  a₁ := aInteger ^ 2 - 2
  a₂ := -aInteger ^ 2 + 2 * aInteger + 1
  a₃ := aInteger + 1
  a₄ := -aInteger ^ 2 + 1
  a₆ := 4 * aInteger ^ 2 - 7 * aInteger - 3

theorem E0GoodInt_map_L : E0GoodInt.map (algebraMap OL L) = E0Good := by
  ext <;> simp [E0GoodInt, E0Good, aInteger]

theorem E0GoodInt_map_residue :
    E0GoodInt.map residueOLHom = reducedGoodCurve := by
  ext <;>
    simp [E0GoodInt, reducedGoodCurve, residueOLHom_apply,
      residueOL_aInteger] <;> decide

theorem E0GoodInt_a₁_map :
    algebraMap OL L E0GoodInt.a₁ = E0Good.a₁ := by
  have h := congrArg (fun W : WeierstrassCurve L ↦ W.a₁) E0GoodInt_map_L
  simpa only [WeierstrassCurve.map_a₁] using h

theorem E0GoodInt_a₂_map :
    algebraMap OL L E0GoodInt.a₂ = E0Good.a₂ := by
  have h := congrArg (fun W : WeierstrassCurve L ↦ W.a₂) E0GoodInt_map_L
  simpa only [WeierstrassCurve.map_a₂] using h

theorem E0GoodInt_a₃_map :
    algebraMap OL L E0GoodInt.a₃ = E0Good.a₃ := by
  have h := congrArg (fun W : WeierstrassCurve L ↦ W.a₃) E0GoodInt_map_L
  simpa only [WeierstrassCurve.map_a₃] using h

theorem E0GoodInt_a₄_map :
    algebraMap OL L E0GoodInt.a₄ = E0Good.a₄ := by
  have h := congrArg (fun W : WeierstrassCurve L ↦ W.a₄) E0GoodInt_map_L
  simpa only [WeierstrassCurve.map_a₄] using h

theorem E0GoodInt_a₆_map :
    algebraMap OL L E0GoodInt.a₆ = E0Good.a₆ := by
  have h := congrArg (fun W : WeierstrassCurve L ↦ W.a₆) E0GoodInt_map_L
  simpa only [WeierstrassCurve.map_a₆] using h

theorem E0GoodInt_a₁_residue :
    residueOL E0GoodInt.a₁ = reducedGoodCurve.a₁ := by
  have h := congrArg (fun W : WeierstrassCurve (ZMod 3) ↦ W.a₁)
    E0GoodInt_map_residue
  simpa only [WeierstrassCurve.map_a₁, residueOLHom_apply] using h

theorem E0GoodInt_a₂_residue :
    residueOL E0GoodInt.a₂ = reducedGoodCurve.a₂ := by
  have h := congrArg (fun W : WeierstrassCurve (ZMod 3) ↦ W.a₂)
    E0GoodInt_map_residue
  simpa only [WeierstrassCurve.map_a₂, residueOLHom_apply] using h

theorem E0GoodInt_a₃_residue :
    residueOL E0GoodInt.a₃ = reducedGoodCurve.a₃ := by
  have h := congrArg (fun W : WeierstrassCurve (ZMod 3) ↦ W.a₃)
    E0GoodInt_map_residue
  simpa only [WeierstrassCurve.map_a₃, residueOLHom_apply] using h

theorem E0GoodInt_a₄_residue :
    residueOL E0GoodInt.a₄ = reducedGoodCurve.a₄ := by
  have h := congrArg (fun W : WeierstrassCurve (ZMod 3) ↦ W.a₄)
    E0GoodInt_map_residue
  simpa only [WeierstrassCurve.map_a₄, residueOLHom_apply] using h

theorem E0GoodInt_a₆_residue :
    residueOL E0GoodInt.a₆ = reducedGoodCurve.a₆ := by
  have h := congrArg (fun W : WeierstrassCurve (ZMod 3) ↦ W.a₆)
    E0GoodInt_map_residue
  simpa only [WeierstrassCurve.map_a₆, residueOLHom_apply] using h

theorem residueOL_den_ne_zero (d : p3.asIdeal.primeCompl) :
    residueOL d ≠ 0 := by
  intro hzero
  apply d.property
  change (d : OL) ∈ primeAboveThree
  rw [mem_primeAboveThree_iff_dvd_coeff0]
  change ((coeff0 (d : OL) : ℤ) : ZMod 3) = 0 at hzero
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff0 (d : OL)) 3).mp hzero

/-- `x` is integral at the prime above `3`. -/
def IntegralAtPi (x : L) : Prop :=
  p3.valuation L x ≤ 1

theorem v3_ne_zero {x : L} (hx : x ≠ 0) : v3 x ≠ 0 :=
  v3.ne_zero_iff.mpr hx

theorem ordPi_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordPi (x * y) = ordPi x + ordPi y := by
  unfold ordPi
  rw [map_mul, WithZero.log_mul (v3_ne_zero hx) (v3_ne_zero hy)]
  ring

theorem ordPi_div {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordPi (x / y) = ordPi x - ordPi y := by
  unfold ordPi
  rw [map_div₀, WithZero.log_div (v3_ne_zero hx) (v3_ne_zero hy)]
  ring

@[simp] theorem ordPi_neg (x : L) : ordPi (-x) = ordPi x := by
  unfold ordPi
  rw [Valuation.map_neg]

@[simp] theorem ordPi_zero : ordPi (0 : L) = 0 := by
  unfold ordPi
  rw [map_zero, WithZero.log_zero, neg_zero]

theorem ordPi_one : ordPi (1 : L) = 0 := by
  unfold ordPi
  rw [map_one, WithZero.log_one, neg_zero]

theorem ordPi_add_ge {x y : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (ordPi x) (ordPi y) ≤ ordPi (x + y) := by
  have hmax : v3 (x + y) ≤ max (v3 x) (v3 y) := v3.map_add x y
  have hlog : WithZero.log (v3 (x + y)) ≤
      max (WithZero.log (v3 x)) (WithZero.log (v3 y)) := by
    rcases le_total (v3 x) (v3 y) with hle | hle
    · have hle' : v3 (x + y) ≤ v3 y :=
        le_trans hmax (by rw [max_eq_right hle])
      exact le_trans
        ((WithZero.log_le_log (v3_ne_zero hxy) (v3_ne_zero hy)).mpr hle')
        (le_max_right _ _)
    · have hle' : v3 (x + y) ≤ v3 x :=
        le_trans hmax (by rw [max_eq_left hle])
      exact le_trans
        ((WithZero.log_le_log (v3_ne_zero hxy) (v3_ne_zero hx)).mpr hle')
        (le_max_left _ _)
  unfold ordPi
  omega

theorem le_ordPi_add {N : ℤ} {x y : L}
    (hx : N ≤ ordPi x) (hy : N ≤ ordPi y) (hN : N ≤ 0) :
    N ≤ ordPi (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, ordPi_zero]
    exact hN
  by_cases hx0 : x = 0
  · rw [hx0, zero_add]
    exact hy
  by_cases hy0 : y = 0
  · rw [hy0, add_zero]
    exact hx
  exact le_trans (le_min hx hy) (ordPi_add_ge hx0 hy0 hxy)

theorem ordPi_add_eq_of_lt {x y : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : ordPi x < ordPi y) :
    ordPi (x + y) = ordPi x := by
  have hsum : x + y ≠ 0 := by
    intro h
    have : y = -x := by linear_combination h
    rw [this, ordPi_neg] at hxy
    exact lt_irrefl _ hxy
  refine le_antisymm ?_ ?_
  · by_contra hlt
    push Not at hlt
    have h := ordPi_add_ge hsum (neg_ne_zero.mpr hy)
      (by rw [add_neg_cancel_right]; exact hx)
    rw [add_neg_cancel_right, ordPi_neg] at h
    exact absurd h (not_le.mpr (lt_min hlt hxy))
  · have h := ordPi_add_ge hx hy hsum
    rwa [min_eq_left hxy.le] at h

theorem nonneg_ordPi_add {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    0 ≤ ordPi (x + y) :=
  le_ordPi_add hx hy le_rfl

theorem nonneg_ordPi_mul {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    0 ≤ ordPi (x * y) := by
  by_cases hx0 : x = 0
  · simp [hx0, ordPi_zero]
  by_cases hy0 : y = 0
  · simp [hy0, ordPi_zero]
  rw [ordPi_mul hx0 hy0]
  omega

theorem nonneg_ordPi_pow {x : L}
    (hx : 0 ≤ ordPi x) (n : ℕ) : 0 ≤ ordPi (x ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, ordPi_one]
  | succ n ih =>
      rw [pow_succ]
      exact nonneg_ordPi_mul ih hx

theorem integralAtPi_iff_nonneg_ordPi (x : L) :
    IntegralAtPi x ↔ 0 ≤ ordPi x := by
  by_cases hx : x = 0
  · subst x
    simp [IntegralAtPi, ordPi_zero]
  constructor
  · intro h
    have hlog : WithZero.log (v3 x) ≤ 0 := by
      have h' := (WithZero.log_le_log (v3_ne_zero hx) one_ne_zero).mpr h
      rwa [WithZero.log_one] at h'
    unfold ordPi
    omega
  · intro h
    have hlog : WithZero.log (v3 x) ≤
        WithZero.log (1 : WithZero (Multiplicative ℤ)) := by
      rw [WithZero.log_one]
      unfold ordPi at h
      omega
    exact (WithZero.log_le_log (v3_ne_zero hx) one_ne_zero).mp hlog

theorem integralAtPi_of_nonneg_ordPi {x : L} (hx : 0 ≤ ordPi x) :
    IntegralAtPi x :=
  (integralAtPi_iff_nonneg_ordPi x).2 hx

theorem nonneg_ordPi_of_integralAtPi {x : L} (hx : IntegralAtPi x) :
    0 ≤ ordPi x :=
  (integralAtPi_iff_nonneg_ordPi x).1 hx

theorem integralAtPi_of_OL (u : OL) :
    IntegralAtPi (u : L) := by
  show p3.valuation L (algebraMap OL L u) ≤ 1
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := L) p3 u

theorem integralAtPi_E0Good_a₁ : IntegralAtPi E0Good.a₁ := by
  rw [← E0GoodInt_a₁_map]
  exact integralAtPi_of_OL E0GoodInt.a₁

theorem integralAtPi_E0Good_a₂ : IntegralAtPi E0Good.a₂ := by
  rw [← E0GoodInt_a₂_map]
  exact integralAtPi_of_OL E0GoodInt.a₂

theorem integralAtPi_E0Good_a₃ : IntegralAtPi E0Good.a₃ := by
  rw [← E0GoodInt_a₃_map]
  exact integralAtPi_of_OL E0GoodInt.a₃

theorem integralAtPi_E0Good_a₄ : IntegralAtPi E0Good.a₄ := by
  rw [← E0GoodInt_a₄_map]
  exact integralAtPi_of_OL E0GoodInt.a₄

theorem integralAtPi_E0Good_a₆ : IntegralAtPi E0Good.a₆ := by
  rw [← E0GoodInt_a₆_map]
  exact integralAtPi_of_OL E0GoodInt.a₆

theorem nonneg_ordPi_E0Good_a₁ : 0 ≤ ordPi E0Good.a₁ :=
  nonneg_ordPi_of_integralAtPi integralAtPi_E0Good_a₁

theorem nonneg_ordPi_E0Good_a₂ : 0 ≤ ordPi E0Good.a₂ :=
  nonneg_ordPi_of_integralAtPi integralAtPi_E0Good_a₂

theorem nonneg_ordPi_E0Good_a₃ : 0 ≤ ordPi E0Good.a₃ :=
  nonneg_ordPi_of_integralAtPi integralAtPi_E0Good_a₃

theorem nonneg_ordPi_E0Good_a₄ : 0 ≤ ordPi E0Good.a₄ :=
  nonneg_ordPi_of_integralAtPi integralAtPi_E0Good_a₄

theorem nonneg_ordPi_E0Good_a₆ : 0 ≤ ordPi E0Good.a₆ :=
  nonneg_ordPi_of_integralAtPi integralAtPi_E0Good_a₆

theorem y_integral_of_x_integral {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : IntegralAtPi x) : IntegralAtPi y := by
  apply integralAtPi_of_nonneg_ordPi
  by_contra hyNon
  have hyneg : ordPi y < 0 := by omega
  have hy0 : y ≠ 0 := by
    intro hzero
    rw [hzero, ordPi_zero] at hyneg
    omega
  have hxord : 0 ≤ ordPi x := nonneg_ordPi_of_integralAtPi hx
  let A : L := E0Good.a₁ * x + E0Good.a₃
  have hAnonneg : 0 ≤ ordPi A := by
    dsimp [A]
    exact nonneg_ordPi_add
      (nonneg_ordPi_mul nonneg_ordPi_E0Good_a₁ hxord)
      nonneg_ordPi_E0Good_a₃
  have hyAord : ordPi (y + A) = ordPi y := by
    by_cases hA0 : A = 0
    · simp [hA0]
    · exact ordPi_add_eq_of_lt hy0 hA0 (by omega)
  have hyA0 : y + A ≠ 0 := by
    intro hzero
    rw [hzero, ordPi_zero] at hyAord
    omega
  have hleftOrd :
      ordPi (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y) =
        2 * ordPi y := by
    rw [show y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y =
        y * (y + A) by dsimp [A]; ring]
    rw [ordPi_mul hy0 hyA0, hyAord]
    ring
  have hx3 : 0 ≤ ordPi (x ^ 3) := nonneg_ordPi_pow hxord 3
  have ha₂x2 : 0 ≤ ordPi (E0Good.a₂ * x ^ 2) :=
    nonneg_ordPi_mul nonneg_ordPi_E0Good_a₂
      (nonneg_ordPi_pow hxord 2)
  have ha₄x : 0 ≤ ordPi (E0Good.a₄ * x) :=
    nonneg_ordPi_mul nonneg_ordPi_E0Good_a₄ hxord
  have hrightOrd :
      0 ≤ ordPi (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    have h₁ : 0 ≤ ordPi (x ^ 3 + E0Good.a₂ * x ^ 2) :=
      nonneg_ordPi_add hx3 ha₂x2
    have h₂ : 0 ≤ ordPi (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x) := by
      simpa [add_assoc] using nonneg_ordPi_add h₁ ha₄x
    simpa [add_assoc] using nonneg_ordPi_add h₂ nonneg_ordPi_E0Good_a₆
  have hxy := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  have hord := congrArg ordPi hxy
  rw [hleftOrd] at hord
  have hnonneg : 0 ≤ 2 * ordPi y := by
    rw [hord]
    exact hrightOrd
  omega

/-- A field element reduces to `r` when, after multiplying by a denominator
outside `p3`, numerator and denominator have the expected algebraic-integer
residues. -/
def Reduces (x : L) (r : ZMod 3) : Prop :=
  ∃ n : OL, ∃ d : p3.asIdeal.primeCompl,
    x * algebraMap OL L d = algebraMap OL L n ∧
      r * residueOL d = residueOL n

theorem reduces_of_OL (u : OL) : Reduces (u : L) (residueOL u) := by
  refine ⟨u, 1, ?_, ?_⟩ <;> simp [residueOL_one]

theorem reduces_E0Good_a₁ :
    Reduces E0Good.a₁ reducedGoodCurve.a₁ := by
  simpa [E0GoodInt_a₁_map, E0GoodInt_a₁_residue]
    using reduces_of_OL E0GoodInt.a₁

theorem reduces_E0Good_a₂ :
    Reduces E0Good.a₂ reducedGoodCurve.a₂ := by
  simpa [E0GoodInt_a₂_map, E0GoodInt_a₂_residue]
    using reduces_of_OL E0GoodInt.a₂

theorem reduces_E0Good_a₃ :
    Reduces E0Good.a₃ reducedGoodCurve.a₃ := by
  simpa [E0GoodInt_a₃_map, E0GoodInt_a₃_residue]
    using reduces_of_OL E0GoodInt.a₃

theorem reduces_E0Good_a₄ :
    Reduces E0Good.a₄ reducedGoodCurve.a₄ := by
  simpa [E0GoodInt_a₄_map, E0GoodInt_a₄_residue]
    using reduces_of_OL E0GoodInt.a₄

theorem reduces_E0Good_a₆ :
    Reduces E0Good.a₆ reducedGoodCurve.a₆ := by
  simpa [E0GoodInt_a₆_map, E0GoodInt_a₆_residue]
    using reduces_of_OL E0GoodInt.a₆

theorem reduces_exists {x : L} (hx : IntegralAtPi x) :
    ∃ r : ZMod 3, Reduces x r := by
  obtain ⟨n, d, hnd⟩ := p3.exists_primeCompl_mul_eq_of_integer x hx
  refine ⟨residueOL n / residueOL d, n, d, hnd, ?_⟩
  exact div_mul_cancel₀ _ (residueOL_den_ne_zero d)

theorem reduces_unique {x : L} {r s : ZMod 3}
    (hr : Reduces x r) (hs : Reduces x s) : r = s := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  have hcrossL :
      algebraMap OL L (n * d') = algebraMap OL L (n' * d) := by
    simp only [map_mul]
    calc
      algebraMap OL L n * algebraMap OL L (d' : OL) =
          (x * algebraMap OL L (d : OL)) * algebraMap OL L (d' : OL) := by
            rw [hxd]
      _ = (x * algebraMap OL L (d' : OL)) * algebraMap OL L (d : OL) := by ring
      _ = algebraMap OL L n' * algebraMap OL L (d : OL) := by rw [hxd']
  have hcross : n * (d' : OL) = n' * (d : OL) :=
    (FaithfulSMul.algebraMap_injective OL L) hcrossL
  apply mul_right_cancel₀
    (mul_ne_zero (residueOL_den_ne_zero d) (residueOL_den_ne_zero d'))
  calc
    r * (residueOL d * residueOL d') =
        (r * residueOL d) * residueOL d' := by ring
    _ = residueOL n * residueOL d' := by rw [hrd]
    _ = residueOL (n * (d' : OL)) := by rw [residueOL_mul]
    _ = residueOL (n' * (d : OL)) := by rw [hcross]
    _ = residueOL n' * residueOL d := by rw [residueOL_mul]
    _ = (s * residueOL d') * residueOL d := by rw [hsd']
    _ = s * (residueOL d * residueOL d') := by ring

theorem reduces_existsUnique {x : L} (hx : IntegralAtPi x) :
    ∃! r : ZMod 3, Reduces x r := by
  obtain ⟨r, hr⟩ := reduces_exists hx
  exact ⟨r, hr, fun s hs ↦
    (reduces_unique (x := x) (r := r) (s := s) hr hs).symm⟩

/-- Residue of a field element integral at `pi`. -/
def reduce (x : L) (hx : IntegralAtPi x) : ZMod 3 :=
  Classical.choose (reduces_existsUnique hx)

theorem reduce_spec (x : L) (hx : IntegralAtPi x) :
    Reduces x (reduce x hx) :=
  (Classical.choose_spec (reduces_existsUnique hx)).1

theorem reduce_eq_of_reduces {x : L} (hx : IntegralAtPi x) {r : ZMod 3}
    (hr : Reduces x r) : reduce x hx = r :=
  reduces_unique (reduce_spec x hx) hr

theorem reduce_of_OL (u : OL) :
    reduce (u : L) (integralAtPi_of_OL u) = residueOL u :=
  reduce_eq_of_reduces (integralAtPi_of_OL u) (reduces_of_OL u)

theorem integralAtPi_zero : IntegralAtPi (0 : L) := by
  simp [IntegralAtPi]

theorem integralAtPi_one : IntegralAtPi (1 : L) := by
  simp [IntegralAtPi]

theorem IntegralAtPi.add {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x + y) := by
  exact (p3.valuation L).map_add x y |>.trans (max_le hx hy)

theorem IntegralAtPi.neg {x : L} (hx : IntegralAtPi x) :
    IntegralAtPi (-x) := by
  simpa [IntegralAtPi] using hx

theorem IntegralAtPi.sub {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem IntegralAtPi.mul {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x * y) := by
  unfold IntegralAtPi at hx hy ⊢
  rw [map_mul]
  exact (mul_le_mul' hx hy).trans_eq (mul_one 1)

theorem IntegralAtPi.pow {x : L} (hx : IntegralAtPi x) (n : ℕ) :
    IntegralAtPi (x ^ n) := by
  induction n with
  | zero => simpa using integralAtPi_one
  | succ n ih => simpa [pow_succ] using ih.mul hx

theorem reduces_zero : Reduces (0 : L) 0 := by
  refine ⟨0, 1, ?_, ?_⟩ <;> simp [residueOL_one]

theorem reduces_one : Reduces (1 : L) 1 := by
  refine ⟨1, 1, ?_, ?_⟩ <;> simp [residueOL_one]

theorem Reduces.add {x y : L} {r s : ZMod 3}
    (hr : Reduces x r) (hs : Reduces y s) : Reduces (x + y) (r + s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * (d' : OL) + n' * (d : OL), d * d', ?_, ?_⟩
  · simp only [map_add, map_mul, Submonoid.coe_mul]
    calc
      (x + y) * (algebraMap OL L d * algebraMap OL L d') =
          (x * algebraMap OL L d) * algebraMap OL L d' +
            (y * algebraMap OL L d') * algebraMap OL L d := by ring
      _ = algebraMap OL L n * algebraMap OL L d' +
            algebraMap OL L n' * algebraMap OL L d := by rw [hxd, hxd']
  · simp only [residueOL_add, residueOL_mul, Submonoid.coe_mul]
    calc
      (r + s) * (residueOL d * residueOL d') =
          (r * residueOL d) * residueOL d' +
            (s * residueOL d') * residueOL d := by ring
      _ = residueOL n * residueOL d' +
            residueOL n' * residueOL d := by rw [hrd, hsd']

theorem Reduces.neg {x : L} {r : ZMod 3} (hr : Reduces x r) :
    Reduces (-x) (-r) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  refine ⟨-n, d, ?_, ?_⟩
  · simp only [map_neg]
    linear_combination -1 * hxd
  · simp only [residueOL_neg]
    linear_combination -1 * hrd

theorem Reduces.mul {x y : L} {r s : ZMod 3}
    (hr : Reduces x r) (hs : Reduces y s) : Reduces (x * y) (r * s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * n', d * d', ?_, ?_⟩
  · simp only [map_mul, Submonoid.coe_mul]
    rw [← hxd, ← hxd']
    ring
  · simp only [residueOL_mul, Submonoid.coe_mul]
    rw [← hrd, ← hsd']
    ring

theorem Reduces.pow {x : L} {r : ZMod 3} (hr : Reduces x r) (n : ℕ) :
    Reduces (x ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using reduces_one
  | succ n ih => simpa [pow_succ] using ih.mul hr

@[simp] theorem reduce_zero : reduce 0 integralAtPi_zero = 0 :=
  reduce_eq_of_reduces integralAtPi_zero reduces_zero

@[simp] theorem reduce_one : reduce 1 integralAtPi_one = 1 :=
  reduce_eq_of_reduces integralAtPi_one reduces_one

theorem reduce_add {x y : L} (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reduce (x + y) (hx.add hy) = reduce x hx + reduce y hy :=
  reduce_eq_of_reduces (hx.add hy) ((reduce_spec x hx).add (reduce_spec y hy))

theorem reduce_neg {x : L} (hx : IntegralAtPi x) :
    reduce (-x) hx.neg = -reduce x hx :=
  reduce_eq_of_reduces hx.neg (reduce_spec x hx).neg

theorem reduce_sub {x y : L} (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reduce (x - y) (hx.sub hy) = reduce x hx - reduce y hy := by
  have hred : Reduces (x - y) (reduce x hx - reduce y hy) := by
    simpa [sub_eq_add_neg] using
      ((reduce_spec x hx).add (reduce_spec y hy).neg)
  exact reduce_eq_of_reduces (hx.sub hy) hred

theorem reduce_mul {x y : L} (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reduce (x * y) (hx.mul hy) = reduce x hx * reduce y hy :=
  reduce_eq_of_reduces (hx.mul hy) ((reduce_spec x hx).mul (reduce_spec y hy))

theorem reduce_pow {x : L} (hx : IntegralAtPi x) (n : ℕ) :
    reduce (x ^ n) (hx.pow n) = reduce x hx ^ n :=
  reduce_eq_of_reduces (hx.pow n) ((reduce_spec x hx).pow n)

theorem reduced_equation_of_integral {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y)
    (hxy : WeierstrassCurve.Affine.Equation E0Good x y) :
    WeierstrassCurve.Affine.Equation reducedGoodCurve
      (reduce x hx) (reduce y hy) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
  have hxred := reduce_spec x hx
  have hyred := reduce_spec y hy
  have hA₁xy :
      Reduces (E0Good.a₁ * x * y)
        (reducedGoodCurve.a₁ * reduce x hx * reduce y hy) := by
    simpa [mul_assoc] using
      ((reduces_E0Good_a₁.mul hxred).mul hyred)
  have hA₃y :
      Reduces (E0Good.a₃ * y)
        (reducedGoodCurve.a₃ * reduce y hy) := by
    simpa [mul_assoc] using
      (reduces_E0Good_a₃.mul hyred)
  have hleft :
      Reduces (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y)
        (reduce y hy ^ 2 +
          reducedGoodCurve.a₁ * reduce x hx * reduce y hy +
            reducedGoodCurve.a₃ * reduce y hy) := by
    simpa [add_assoc] using ((hyred.pow 2).add hA₁xy).add hA₃y
  have hA₂x₂ :
      Reduces (E0Good.a₂ * x ^ 2)
        (reducedGoodCurve.a₂ * reduce x hx ^ 2) := by
    simpa [mul_assoc] using
      (reduces_E0Good_a₂.mul (hxred.pow 2))
  have hA₄x :
      Reduces (E0Good.a₄ * x)
        (reducedGoodCurve.a₄ * reduce x hx) := by
    simpa [mul_assoc] using
      (reduces_E0Good_a₄.mul hxred)
  have hright :
      Reduces (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆)
        (reduce x hx ^ 3 +
          reducedGoodCurve.a₂ * reduce x hx ^ 2 +
            reducedGoodCurve.a₄ * reduce x hx +
              reducedGoodCurve.a₆) := by
    simpa [add_assoc] using
      ((((hxred.pow 3).add hA₂x₂).add hA₄x).add reduces_E0Good_a₆)
  have hright' :
      Reduces (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y)
        (reduce x hx ^ 3 +
          reducedGoodCurve.a₂ * reduce x hx ^ 2 +
            reducedGoodCurve.a₄ * reduce x hx +
              reducedGoodCurve.a₆) := by
    rw [hxy]
    exact hright
  have hred := reduces_unique hleft hright'
  simpa [add_assoc, mul_assoc] using hred

/-- Reduction of a finite point whose affine coordinates are integral at `pi`. -/
noncomputable def reduceIntegralPoint (x y : L)
    (hx : IntegralAtPi x) (hy : IntegralAtPi y)
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y) : RedPoint :=
  WeierstrassCurve.Affine.Point.mk
    (reduced_equation_of_integral hx hy h.1)

theorem reduceIntegralPoint_ne_zero (x y : L)
    (hx : IntegralAtPi x) (hy : IntegralAtPi y)
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y) :
    reduceIntegralPoint x y hx hy h ≠ 0 := by
  unfold reduceIntegralPoint
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The usual pointwise reduction map before proving additivity. -/
noncomputable def reductionMapToFun : GoodPoint → RedPoint
  | .zero => 0
  | .some x y h =>
      if hx : IntegralAtPi x then
        reduceIntegralPoint x y hx (y_integral_of_x_integral h hx) h
      else 0

@[simp] theorem reductionMapToFun_zero :
    reductionMapToFun (0 : GoodPoint) = 0 := rfl

theorem reductionMapToFun_eq_zero_iff (P : GoodPoint) :
    reductionMapToFun P = 0 ↔ InFormalKernel P := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        rfl
  | some x y h =>
      by_cases hx : IntegralAtPi x
      · have hxnonneg : 0 ≤ ordPi x := nonneg_ordPi_of_integralAtPi hx
        constructor
        · intro hzero
          simp [reductionMapToFun, hx] at hzero
          exact False.elim
            (reduceIntegralPoint_ne_zero x y hx
              (y_integral_of_x_integral h hx) h hzero)
        · intro hformal
          rcases hformal with hzero | hxneg
          · exact False.elim (WeierstrassCurve.Affine.Point.some_ne_zero h hzero)
          · exact False.elim ((not_lt_of_ge hxnonneg) hxneg)
      · have hxneg : ordPi x < 0 := by
          by_contra hnot
          have hxnonneg : 0 ≤ ordPi x := by omega
          exact hx (integralAtPi_of_nonneg_ordPi hxnonneg)
        constructor
        · intro _
          exact Or.inr hxneg
        · intro _
          simp [reductionMapToFun, hx]

end

/-! ## Existence proof exported for assembly wiring -/

set_option maxHeartbeats 0

namespace QuotientProof

@[simp] theorem zero_mem_formalKernel : InFormalKernel (0 : GoodPoint) :=
  Or.inl rfl

/-- Negation preserves the affine `x`-coordinate. -/
theorem xCoordGood_neg (P : GoodPoint) : xCoordGood (-P) = xCoordGood P := by
  cases P with
  | zero => rfl
  | some x y h => rfl

private theorem two_nsmul_eq_two_mul (a : WithTop ℤ) : 2 • a = 2 * a := by
  cases a with
  | top => simp [two_nsmul]
  | coe m =>
      rw [two_nsmul, ← WithTop.coe_add,
        show (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) by norm_cast,
        ← WithTop.coe_mul]
      congr
      ring

private theorem nsmul_zero_good (n : ℕ) : n • (0 : GoodPoint) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [succ_nsmul, ih]; rfl

/-- A finite good-model point with negative `x`-order cannot have `y = 0`.
This is the monic-cubic Newton-polygon lemma used immediately before
`GoodModel.val_coords`; it has no group-law or descent content. -/
theorem yCoordGood_ne_zero_of_ordPi_x_neg {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular
      MazurProof.N18RouteC.E0Good x y)
    (hx : ordPi x < 0) : y ≠ 0 := by
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, ordPi_zero] at hx
    omega
  intro hy
  subst y
  have heq := (WeierstrassCurve.Affine.equation_iff x 0).mp h.1
  have ha₂map :
      algebraMap MazurProof.N18PackageII.OL L
          MazurProof.N18PackageII.E0GoodInt.a₂ = E0Good.a₂ := by
    have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₂)
      MazurProof.N18PackageII.E0GoodInt_map
    simpa only [WeierstrassCurve.map_a₂] using hm
  have ha₄map :
      algebraMap MazurProof.N18PackageII.OL L
          MazurProof.N18PackageII.E0GoodInt.a₄ = E0Good.a₄ := by
    have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₄)
      MazurProof.N18PackageII.E0GoodInt_map
    simpa only [WeierstrassCurve.map_a₄] using hm
  have ha₆map :
      algebraMap MazurProof.N18PackageII.OL L
          MazurProof.N18PackageII.E0GoodInt.a₆ = E0Good.a₆ := by
    have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₆)
      MazurProof.N18PackageII.E0GoodInt_map
    simpa only [WeierstrassCurve.map_a₆] using hm
  have ha₂ : 0 ≤ ordPi E0Good.a₂ := by
    rw [← ha₂map]
    exact MazurProof.N18RouteC.GoodModel.zero_le_ordPi_ringOfIntegers _
  have ha₄ : 0 ≤ ordPi E0Good.a₄ := by
    rw [← ha₄map]
    exact MazurProof.N18RouteC.GoodModel.zero_le_ordPi_ringOfIntegers _
  have ha₆ : 0 ≤ ordPi E0Good.a₆ := by
    rw [← ha₆map]
    exact MazurProof.N18RouteC.GoodModel.zero_le_ordPi_ringOfIntegers _
  have hx2 : ordPi (x ^ 2) = 2 * ordPi x := by
    rw [show x ^ 2 = x * x by ring, ordPi_mul hx0 hx0]
    ring
  have hx3 : ordPi (x ^ 3) = 3 * ordPi x := by
    rw [show x ^ 3 = x * x * x by ring,
      ordPi_mul (mul_ne_zero hx0 hx0) hx0, ordPi_mul hx0 hx0]
    ring
  have ha₂x :
      2 * ordPi x ≤ ordPi (E0Good.a₂ * x ^ 2) := by
    by_cases hzero : E0Good.a₂ = 0
    · rw [hzero, zero_mul, ordPi_zero]
      omega
    · rw [ordPi_mul hzero (pow_ne_zero 2 hx0), hx2]
      omega
  have ha₄x :
      2 * ordPi x ≤ ordPi (E0Good.a₄ * x) := by
    by_cases hzero : E0Good.a₄ = 0
    · rw [hzero, zero_mul, ordPi_zero]
      omega
    · rw [ordPi_mul hzero hx0]
      omega
  have htail :
      2 * ordPi x ≤
        ordPi (E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    apply le_ordPi_add
    · exact le_ordPi_add ha₂x ha₄x (by omega)
    · omega
    · omega
  have hcurve :
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆ = 0 := by
    norm_num at heq
    exact heq.symm
  have hfactor :
      x ^ 3 = -(E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    linear_combination hcurve
  have hord := congrArg ordPi hfactor
  rw [hx3, ordPi_neg] at hord
  omega

/-- The forward coordinate-valuation bridge on the good model. -/
theorem vpi_pos_bridge_good (P : GoodPoint)
    (hx : ordPi (xCoordGood P) < 0) :
    0 < vpiGood (MazurProof.N18PackageII.zParamGood P) := by
  cases P with
  | zero =>
      simp [xCoordGood, ordPi_zero] at hx
  | some x y h =>
      simp only [xCoordGood] at hx
      have hx0 : x ≠ 0 := by
        intro hzero
        rw [hzero, ordPi_zero] at hx
        omega
      have hy0 : y ≠ 0 := yCoordGood_ne_zero_of_ordPi_x_neg h hx
      have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
      have hcoords := MazurProof.N18RouteC.GoodModel.val_coords
        hx0 hy0 (by simpa using heq) hx
      have hz0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
      rw [MazurProof.N18PackageII.zParamGood_some,
        vpiGood_apply_of_ne hz0]
      exact_mod_cast (show 0 < ordPi (-x / y) by omega)

/-- Negation has the same formal-parameter order on the good chart.  It is the
valuation-level form of the formal inverse expansion `i(T) = -T + O(T²)`. -/
theorem vpi_zParamGood_neg (P : GoodPoint) :
    InFormalKernel P →
    vpiGood (MazurProof.N18PackageII.zParamGood (-P)) =
      vpiGood (MazurProof.N18PackageII.zParamGood P) := by
  intro hP
  rcases hP with hzero | hx
  · subst P
    simp
  · cases P with
    | zero =>
        simp [xCoordGood, ordPi_zero] at hx
    | some x y h =>
        simp only [xCoordGood] at hx
        have hx0 : x ≠ 0 := by
          intro hzero
          rw [hzero, ordPi_zero] at hx
          omega
        have hy0 : y ≠ 0 := yCoordGood_ne_zero_of_ordPi_x_neg h hx
        have hneg : WeierstrassCurve.Affine.Nonsingular E0Good x
            (WeierstrassCurve.Affine.negY E0Good x y) :=
          (WeierstrassCurve.Affine.nonsingular_neg x y).mpr h
        have hyneg0 : WeierstrassCurve.Affine.negY E0Good x y ≠ 0 :=
          yCoordGood_ne_zero_of_ordPi_x_neg hneg hx
        have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
        have heqneg := (WeierstrassCurve.Affine.equation_iff x
          (WeierstrassCurve.Affine.negY E0Good x y)).mp hneg.1
        have hcoords := MazurProof.N18RouteC.GoodModel.val_coords
          hx0 hy0 (by simpa using heq) hx
        have hcoordsNeg := MazurProof.N18RouteC.GoodModel.val_coords
          hx0 hyneg0 (by simpa using heqneg) hx
        have hz0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
        have hzneg0 :
            -x / WeierstrassCurve.Affine.negY E0Good x y ≠ 0 :=
          div_ne_zero (neg_ne_zero.mpr hx0) hyneg0
        rw [WeierstrassCurve.Affine.Point.neg_some,
          MazurProof.N18PackageII.zParamGood_some,
          MazurProof.N18PackageII.zParamGood_some,
          vpiGood_apply_of_ne hzneg0, vpiGood_apply_of_ne hz0]
        exact_mod_cast (show
          ordPi (-x / WeierstrassCurve.Affine.negY E0Good x y) =
            ordPi (-x / y) by omega)

/-! The following chart calculation is deliberately local to this file.  It
uses only integrality of the five coefficients of `E0Good`; in particular it
does not use the coefficient-specific identity from `N18AddCongrProof`. -/

private def OrdGoodG (N : ℤ) (x : L) : Prop := x = 0 ∨ N ≤ ordPi x

private theorem OrdGoodG.neg {N : ℤ} {x : L} (hx : OrdGoodG N x) :
    OrdGoodG N (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [ordPi_neg]

private theorem OrdGoodG.add {N : ℤ} {x y : L}
    (hx : OrdGoodG N x) (hy : OrdGoodG N y) : OrdGoodG N (x + y) := by
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  right
  rcases hx with hx | hx
  · subst x
    simpa using hy.resolve_left (by intro h; apply hxy; simp [h])
  rcases hy with hy | hy
  · subst y
    simpa using hx
  by_cases hx0 : x = 0
  · simp only [hx0, zero_add] at hxy ⊢
    exact hy
  by_cases hy0 : y = 0
  · simp only [hy0, add_zero] at hxy ⊢
    exact hx
  exact le_trans (le_min hx hy) (ordPi_add_ge hx0 hy0 hxy)

private theorem OrdGoodG.sub {N : ℤ} {x y : L}
    (hx : OrdGoodG N x) (hy : OrdGoodG N y) : OrdGoodG N (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

private theorem OrdGoodG.mul {M N : ℤ} {x y : L}
    (hx : OrdGoodG M x) (hy : OrdGoodG N y) : OrdGoodG (M + N) (x * y) := by
  rcases hx with rfl | hx
  · left; simp
  rcases hy with rfl | hy
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  by_cases hy0 : y = 0
  · left; simp [hy0]
  right
  rw [ordPi_mul hx0 hy0]
  omega

private theorem OrdGoodG.mono {M N : ℤ} {x : L}
    (hMN : M ≤ N) (hx : OrdGoodG N x) : OrdGoodG M x := by
  rcases hx with rfl | hx
  · left; rfl
  · right; omega

private theorem OrdGoodG.nat_mul (n : ℕ) {N : ℤ} {x : L}
    (hx : OrdGoodG N x) : OrdGoodG N ((n : L) * x) := by
  by_cases hn : (n : L) = 0
  · left; simp [hn]
  rcases hx with rfl | hx
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  right
  rw [ordPi_mul hn hx0]
  have hnval := zero_le_ordPi_intCast (n : ℤ)
  norm_num at hnval ⊢
  omega

private theorem OrdGoodG.div_unit {N : ℤ} {x y : L}
    (hx : OrdGoodG N x) (hy0 : y ≠ 0) (hyv : ordPi y = 0) :
    OrdGoodG N (x / y) := by
  rcases hx with rfl | hx
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  right
  rw [ordPi_div hx0 hy0, hyv]
  omega

private theorem OrdGoodG.unit_one_add {q : L} (hq : OrdGoodG 1 q) :
    1 + q ≠ 0 ∧ ordPi (1 + q) = 0 := by
  rcases hq with rfl | hq
  · simp [ordPi_one]
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hq
    omega
  constructor
  · intro h
    have : q = -1 := by linear_combination h
    rw [this, ordPi_neg, ordPi_one] at hq
    omega
  · simpa only [ordPi_one] using
      ordPi_add_eq_of_lt one_ne_zero hq0 (by rw [ordPi_one]; omega)

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

private theorem ordPi_mul_nonneg_good {u w : L}
    (hu : 0 ≤ ordPi u) (hw : 0 ≤ ordPi w) :
    0 ≤ ordPi (u * w) := by
  by_cases hu0 : u = 0
  · simp [hu0, ordPi_zero]
  by_cases hw0 : w = 0
  · simp [hw0, ordPi_zero]
  rw [ordPi_mul hu0 hw0]
  omega

private theorem ordPi_le_mul_right_good {u w : L}
    (hu : 0 ≤ ordPi u) (hw : ordPi w ≤ 0) :
    ordPi w ≤ ordPi (u * w) := by
  by_cases hu0 : u = 0
  · simp [hu0, ordPi_zero, hw]
  by_cases hw0 : w = 0
  · simp [hw0, ordPi_zero]
  rw [ordPi_mul hu0 hw0]
  omega

/-- Integrality of `x` forces integrality of `y` on the good equation. -/
private theorem y_nonneg_of_x_nonneg_good {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) : 0 ≤ ordPi y := by
  by_cases hy0 : y = 0
  · simp [hy0, ordPi_zero]
  by_contra hy
  have hyneg : ordPi y < 0 := lt_of_not_ge hy
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have hx2 : 0 ≤ ordPi (x ^ 2) := by
    rw [pow_two]
    exact ordPi_mul_nonneg_good hx hx
  have hx3 : 0 ≤ ordPi (x ^ 3) := by
    rw [show x ^ 3 = x ^ 2 * x by ring]
    exact ordPi_mul_nonneg_good hx2 hx
  have hrhs : 0 ≤ ordPi
      (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) := by
    have h2 := ordPi_mul_nonneg_good ha2 hx2
    have h4 := ordPi_mul_nonneg_good ha4 hx
    exact le_ordPi_add
      (le_ordPi_add (le_ordPi_add hx3 h2 le_rfl) h4 le_rfl) ha6 le_rfl
  let tail := E0Good.a₁ * x * y + E0Good.a₃ * y
  have htail : ordPi y ≤ ordPi tail := by
    have hax : 0 ≤ ordPi (E0Good.a₁ * x) :=
      ordPi_mul_nonneg_good ha1 hx
    have h1 : ordPi y ≤ ordPi (E0Good.a₁ * x * y) :=
      ordPi_le_mul_right_good hax hyneg.le
    have h3 : ordPi y ≤ ordPi (E0Good.a₃ * y) :=
      ordPi_le_mul_right_good ha3 hyneg.le
    exact le_ordPi_add h1 h3 hyneg.le
  have hy2 : ordPi (y ^ 2) = 2 * ordPi y := by
    rw [pow_two, ordPi_mul hy0 hy0]
    ring
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
    intro hz
    have hlhs0 : y ^ 2 + tail = 0 := hcurve'.trans hz
    have hord := congrArg ordPi hlhs0
    rw [hlhs, ordPi_zero] at hord
    omega
  have hord := congrArg ordPi hcurve'
  rw [hlhs] at hord
  omega

private theorem good_a1_unit : E0Good.a₁ ≠ 0 ∧ ordPi E0Good.a₁ = 0 := by
  let c : MazurProof.N18PackageII.OL :=
    FieldArithmetic.aInteger ^ 2 - FieldArithmetic.aInteger - 1
  have hc : 0 ≤ ordPi ((c : MazurProof.N18PackageII.OL) : L) :=
    GoodModel.zero_le_ordPi_ringOfIntegers c
  have hmul : E0Good.a₁ * (c : L) = 1 := by
    change E0Good.a₁ * (a ^ 2 - a - 1) = 1
    simp only [E0Good]
    ring_nf
    simp only [a_pow_four, a_cubic]
    ring
  have ha0 : E0Good.a₁ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact zero_ne_one hmul
  have hc0 : (c : L) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact zero_ne_one hmul
  refine ⟨ha0, ?_⟩
  have hv := congrArg ordPi hmul
  rw [ordPi_mul ha0 hc0, ordPi_one] at hv
  have ha := good_coeff_orders.1
  omega

private noncomputable def GGood (t w : L) : L :=
  w - E0Good.a₁ * t * w - E0Good.a₂ * t ^ 2 * w -
    E0Good.a₃ * w ^ 2 - E0Good.a₄ * t * w ^ 2 -
    E0Good.a₆ * w ^ 3 - t ^ 3

private noncomputable def AGood (m : L) : L :=
  1 + E0Good.a₂ * m + E0Good.a₄ * m ^ 2 + E0Good.a₆ * m ^ 3

private noncomputable def BGood (m b : L) : L :=
  E0Good.a₁ * m + E0Good.a₂ * b + E0Good.a₃ * m ^ 2 +
    2 * E0Good.a₄ * m * b + 3 * E0Good.a₆ * m ^ 2 * b

private noncomputable def CGood (m b : L) : L :=
  m - E0Good.a₁ * b - 2 * E0Good.a₃ * m * b -
    E0Good.a₄ * b ^ 2 - 3 * E0Good.a₆ * m * b ^ 2

private noncomputable def DGood (b : L) : L :=
  b - E0Good.a₃ * b ^ 2 - E0Good.a₆ * b ^ 3

private theorem GGood_line (t m b : L) :
    GGood t (m * t + b) =
      -AGood m * t ^ 3 - BGood m b * t ^ 2 +
        CGood m b * t + DGood b := by
  simp only [GGood, AGood, BGood, CGood, DGood]
  ring

private theorem chartGGood_eq_zero {x y : L} (hy0 : y ≠ 0)
    (heq : y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y =
      x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆) :
    GGood (-x / y) (-1 / y) = 0 := by
  simp only [GGood] at heq ⊢
  field_simp [hy0]
  linear_combination -heq

private theorem secant_vieta_good (m b t₁ t₂ : L)
    (h₁ : GGood t₁ (m * t₁ + b) = 0)
    (h₂ : GGood t₂ (m * t₂ + b) = 0)
    (ht : t₁ ≠ t₂) (hA : AGood m ≠ 0) :
    let u := -BGood m b / AGood m - t₁ - t₂
    AGood m * (t₁ + t₂ + u) + BGood m b = 0 ∧
    AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0 ∧
    AGood m * t₁ * t₂ * u = DGood b := by
  let u := -BGood m b / AGood m - t₁ - t₂
  have hp₁ := h₁
  have hp₂ := h₂
  rw [GGood_line] at hp₁ hp₂
  have hsum : AGood m * (t₁ + t₂ + u) + BGood m b = 0 := by
    dsimp [u]
    field_simp [hA]
    ring
  have hdiff :
      -AGood m * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
          BGood m b * (t₁ + t₂) + CGood m b = 0 := by
    have hmul : (t₁ - t₂) *
        (-AGood m * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) -
          BGood m b * (t₁ + t₂) + CGood m b) = 0 := by
      linear_combination hp₁ - hp₂
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ht)
  have hpair :
      AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0 := by
    linear_combination hdiff + (t₁ + t₂) * hsum
  have hprod : AGood m * t₁ * t₂ * u = DGood b := by
    linear_combination -hp₁ - t₁ ^ 2 * hsum + t₁ * hpair
  exact ⟨hsum, hpair, hprod⟩

private theorem vieta_x_sum_good (m b t₁ t₂ u : L)
    (hA : AGood m ≠ 0) (hb : b ≠ 0)
    (hsum : AGood m * (t₁ + t₂ + u) + BGood m b = 0)
    (hpair : AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0)
    (hprod : AGood m * t₁ * t₂ * u = DGood b) :
    let q := (m * t₁ + b) * (m * t₂ + b) * (m * u + b)
    q ≠ 0 ∧
    t₁ / (m * t₁ + b) + t₂ / (m * t₂ + b) + u / (m * u + b) =
      (m / b) ^ 2 + E0Good.a₁ * (m / b) - E0Good.a₂ := by
  let q := (m * t₁ + b) * (m * t₂ + b) * (m * u + b)
  let n := t₁ * (m * t₂ + b) * (m * u + b) +
    t₂ * (m * t₁ + b) * (m * u + b) +
    u * (m * t₁ + b) * (m * t₂ + b)
  have hcoeffQ :
      m ^ 3 * DGood b - m ^ 2 * b * CGood m b -
        m * b ^ 2 * BGood m b + b ^ 3 * AGood m - b ^ 3 = 0 := by
    simp only [AGood, BGood, CGood, DGood]
    ring
  have hprod0 : AGood m * t₁ * t₂ * u - DGood b = 0 :=
    sub_eq_zero.mpr hprod
  have hQ : AGood m * q = b ^ 3 := by
    dsimp [q]
    linear_combination m ^ 3 * hprod0 + m ^ 2 * b * hpair +
      m * b ^ 2 * hsum + hcoeffQ
  have hcoeffN :
      3 * m ^ 2 * DGood b - 2 * m * b * CGood m b -
        b ^ 2 * BGood m b -
        b * (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) = 0 := by
    simp only [BGood, CGood, DGood]
    ring
  have hN : AGood m * n =
      b * (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) := by
    dsimp [n]
    linear_combination 3 * m ^ 2 * hprod0 + 2 * m * b * hpair +
      b ^ 2 * hsum + hcoeffN
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ
    exact (pow_ne_zero 3 hb) hQ.symm
  have h₁0 : m * t₁ + b ≠ 0 := by
    intro h; apply hq0; simp [q, h]
  have h₂0 : m * t₂ + b ≠ 0 := by
    intro h; apply hq0; simp [q, h]
  have hu0 : m * u + b ≠ 0 := by
    intro h; apply hq0; simp [q, h]
  have h₁0' : t₁ * m + b ≠ 0 := by simpa only [mul_comm] using h₁0
  have h₂0' : t₂ * m + b ≠ 0 := by simpa only [mul_comm] using h₂0
  have hu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hu0
  have hcleared :
      b ^ 2 * n =
        (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) * q := by
    apply mul_left_cancel₀ hA
    linear_combination b ^ 2 * hN -
      (m ^ 2 + E0Good.a₁ * m * b - E0Good.a₂ * b ^ 2) * hQ
  refine ⟨hq0, ?_⟩
  have hleft :
      t₁ / (m * t₁ + b) + t₂ / (m * t₂ + b) + u / (m * u + b) = n / q := by
    field_simp [hq0, h₁0, h₂0, hu0, h₁0', h₂0', hu0']
    simp only [n, q]
    ring
  rw [hleft]
  field_simp [hq0, hb]
  linear_combination hcleared

private theorem add_congr_inverse_good {x y : L}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hxneg : ordPi x < 0) :
    let P : GoodPoint := .some x y hns
    let r := ordPi (-x / y)
    InFormalKernel (P + (-P)) ∧
      (MazurProof.N18PackageII.zParamGood (P + (-P)) -
          MazurProof.N18PackageII.zParamGood P -
          MazurProof.N18PackageII.zParamGood (-P) = 0 ∨
        2 * r ≤ ordPi
          (MazurProof.N18PackageII.zParamGood (P + (-P)) -
            MazurProof.N18PackageII.zParamGood P -
            MazurProof.N18PackageII.zParamGood (-P))) := by
  let P : GoodPoint := .some x y hns
  let r : ℤ := ordPi (-x / y)
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hns.1
  have hcoords := GoodModel.val_coords hx0 hy0 (by simpa using heq) hxneg
  have hxv : ordPi x = -2 * r := hcoords.1
  have hyv : ordPi y = -3 * r := hcoords.2
  have hr : 1 ≤ r := by omega
  have ha1 := good_a1_unit
  have ha3v := good_coeff_orders.2.2.1
  let s : L := E0Good.a₁ * x + E0Good.a₃
  have hax0 : E0Good.a₁ * x ≠ 0 := mul_ne_zero ha1.1 hx0
  have haxv : ordPi (E0Good.a₁ * x) = -2 * r := by
    rw [ordPi_mul ha1.1 hx0, ha1.2, hxv]
    omega
  have hs0 : s ≠ 0 := by
    intro hs
    have hneg : E0Good.a₃ = -(E0Good.a₁ * x) := by
      dsimp [s] at hs
      linear_combination hs
    have hv := congrArg ordPi hneg
    rw [ordPi_neg, haxv] at hv
    omega
  have hsv : ordPi s = -2 * r := by
    dsimp [s]
    by_cases ha30 : E0Good.a₃ = 0
    · rw [ha30, add_zero, haxv]
    · exact (ordPi_add_eq_of_lt hax0 ha30 (by rw [haxv]; omega)).trans haxv
  let d : L := y + s
  have hd0 : d ≠ 0 := by
    intro hd
    have hsEq : s = -y := by
      dsimp [d] at hd
      linear_combination hd
    have hv := congrArg ordPi hsEq
    rw [ordPi_neg, hsv, hyv] at hv
    omega
  have hdv : ordPi d = -3 * r := by
    dsimp [d]
    exact (ordPi_add_eq_of_lt hy0 hs0 (by rw [hyv, hsv]; omega)).trans hyv
  have hzneg : MazurProof.N18PackageII.zParamGood (-P) = x / d := by
    change -x / WeierstrassCurve.Affine.negY E0Good x y = x / d
    rw [show WeierstrassCurve.Affine.negY E0Good x y = -d by
      simp only [WeierstrassCurve.Affine.negY]
      dsimp [d, s]
      ring]
    field_simp [hd0]
  have herr :
      (0 : L) - (-x / y) - x / d = x * s / (y * d) := by
    calc
      (0 : L) - (-x / y) - x / d = x / y - x / d := by ring
      _ = (x * d - y * x) / (y * d) := div_sub_div x x hy0 hd0
      _ = x * s / (y * d) := by
        congr 1
        dsimp only [d]
        ring
  have herr0 : x * s / (y * d) ≠ 0 :=
    div_ne_zero (mul_ne_zero hx0 hs0) (mul_ne_zero hy0 hd0)
  have herrv : ordPi (x * s / (y * d)) = 2 * r := by
    rw [ordPi_div (mul_ne_zero hx0 hs0) (mul_ne_zero hy0 hd0),
      ordPi_mul hx0 hs0, ordPi_mul hy0 hd0, hxv, hsv, hyv, hdv]
    omega
  dsimp only
  refine ⟨Or.inl (add_neg_cancel P), ?_⟩
  right
  rw [show P + -P = 0 by exact add_neg_cancel P,
    MazurProof.N18PackageII.zParamGood_zero, hzneg]
  change 2 * ordPi (-x / y) ≤ ordPi ((0 : L) - (-x / y) - x / d)
  rw [herr, herrv]

private theorem line_valuation_good (r : ℤ) (t₁ t₂ m b : L)
    (hr : 1 ≤ r) (ht₁ : OrdGoodG r t₁) (ht₂ : OrdGoodG r t₂)
    (hm : OrdGoodG (2 * r) m) (hb : OrdGoodG (3 * r) b) :
    let u := -BGood m b / AGood m - t₁ - t₂
    let d := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
    let t₃ := -u / d
    (AGood m ≠ 0 ∧ ordPi (AGood m) = 0) ∧
    (d ≠ 0 ∧ ordPi d = 0) ∧ OrdGoodG r u ∧
    (t₃ - t₁ - t₂ = 0 ∨ 2 * r ≤ ordPi (t₃ - t₁ - t₂)) := by
  let u := -BGood m b / AGood m - t₁ - t₂
  let d := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
  let t₃ := -u / d
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have c1 : OrdGoodG 0 E0Good.a₁ := Or.inr ha1
  have c2 : OrdGoodG 0 E0Good.a₂ := Or.inr ha2
  have c3 : OrdGoodG 0 E0Good.a₃ := Or.inr ha3
  have c4 : OrdGoodG 0 E0Good.a₄ := Or.inr ha4
  have c6 : OrdGoodG 0 E0Good.a₆ := Or.inr ha6
  have hm1 : OrdGoodG 1 m := hm.mono (by omega)
  have hmSq1 : OrdGoodG 1 (m ^ 2) := by
    rw [pow_two]
    exact (hm1.mul hm1).mono (by omega)
  have hmCube1 : OrdGoodG 1 (m ^ 3) := by
    rw [show m ^ 3 = m ^ 2 * m by ring]
    exact (hmSq1.mul hm1).mono (by omega)
  let qA := E0Good.a₂ * m + E0Good.a₄ * m ^ 2 + E0Good.a₆ * m ^ 3
  have hqA : OrdGoodG 1 qA := by
    dsimp [qA]
    exact ((c2.mul hm1).mono (by omega) |>.add
      ((c4.mul hmSq1).mono (by omega))).add
      ((c6.mul hmCube1).mono (by omega))
  have hAeq : AGood m = 1 + qA := by simp only [AGood, qA]; ring
  have hAunit : AGood m ≠ 0 ∧ ordPi (AGood m) = 0 := by
    rw [hAeq]
    exact hqA.unit_one_add
  have hmSq : OrdGoodG (2 * r) (m ^ 2) := by
    rw [pow_two]
    exact (hm.mul hm).mono (by omega)
  have hb2 : OrdGoodG (2 * r) b := hb.mono (by omega)
  have hmb : OrdGoodG (2 * r) (m * b) := (hm.mul hb).mono (by omega)
  have hmSqb : OrdGoodG (2 * r) (m ^ 2 * b) :=
    (hmSq.mul hb).mono (by omega)
  have hB : OrdGoodG (2 * r) (BGood m b) := by
    simp only [BGood]
    have h1 : OrdGoodG (2 * r) (E0Good.a₁ * m) :=
      (c1.mul hm).mono (by omega)
    have h2 : OrdGoodG (2 * r) (E0Good.a₂ * b) :=
      (c2.mul hb2).mono (by omega)
    have h3 : OrdGoodG (2 * r) (E0Good.a₃ * m ^ 2) :=
      (c3.mul hmSq).mono (by omega)
    have h4base : OrdGoodG (2 * r) (E0Good.a₄ * (m * b)) := by
      simpa only [zero_add] using c4.mul hmb
    have h4 : OrdGoodG (2 * r) (2 * E0Good.a₄ * m * b) := by
      simpa only [Nat.cast_ofNat, mul_assoc] using h4base.nat_mul 2
    have h6base : OrdGoodG (2 * r) (E0Good.a₆ * (m ^ 2 * b)) := by
      simpa only [zero_add] using c6.mul hmSqb
    have h6 : OrdGoodG (2 * r) (3 * E0Good.a₆ * m ^ 2 * b) := by
      simpa only [Nat.cast_ofNat, mul_assoc] using h6base.nat_mul 3
    exact (((h1.add h2).add h3).add h4).add h6
  have hu : OrdGoodG r u := by
    dsimp [u]
    have hquot : OrdGoodG (2 * r) (-BGood m b / AGood m) :=
      hB.neg.div_unit hAunit.1 hAunit.2
    exact ((hquot.mono (by omega)).sub ht₁).sub ht₂
  have hsumA1 : OrdGoodG 0 (E0Good.a₁ + E0Good.a₃ * m) := by
    exact c1.add ((c3.mul hm).mono (by omega))
  have hk : OrdGoodG r
      ((E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b) := by
    exact (hsumA1.mul hu |>.mono (by omega)).add
      ((c3.mul hb).mono (by omega))
  have hqD : OrdGoodG 1
      (-((E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b)) :=
    hk.neg.mono (by omega)
  have hdEq : d = 1 +
      (-((E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b)) := by
    dsimp [d]
    ring
  have hdunit : d ≠ 0 ∧ ordPi d = 0 := by
    rw [hdEq]
    exact hqD.unit_one_add
  let k := (E0Good.a₁ + E0Good.a₃ * m) * u + E0Good.a₃ * b
  have hk' : OrdGoodG r k := by simpa only [k] using hk
  have hfirst : OrdGoodG (2 * r) (BGood m b / AGood m) :=
    hB.div_unit hAunit.1 hAunit.2
  have hsecond : OrdGoodG (2 * r) (u * k / d) :=
    (hu.mul hk' |>.mono (by omega)).div_unit hdunit.1 hdunit.2
  let err := t₃ - t₁ - t₂
  have herrEq : err = BGood m b / AGood m - u * k / d := by
    have huEq : t₁ + t₂ = -BGood m b / AGood m - u := by
      dsimp only [u]
      ring
    have hdEq' : d = 1 - k := by
      dsimp only [d, k]
      ring
    have hdk : 1 - k ≠ 0 := by
      rw [← hdEq']
      exact hdunit.1
    calc
      err = -u / d - (t₁ + t₂) := by dsimp only [err, t₃]; ring
      _ = -u / d - (-BGood m b / AGood m - u) := by rw [huEq]
      _ = BGood m b / AGood m - u * k / d := by
        rw [hdEq']
        field_simp [hAunit.1, hdk]
        ring
  have herrGood : OrdGoodG (2 * r) err := by
    rw [herrEq]
    exact hfirst.sub hsecond
  refine ⟨hAunit, hdunit, hu, ?_⟩
  exact herrGood

private theorem add_congr_distinct_good {x₁ y₁ x₂ y₂ : L}
    (hx₁0 : x₁ ≠ 0) (hy₁0 : y₁ ≠ 0)
    (hx₂0 : x₂ ≠ 0) (hy₂0 : y₂ ≠ 0)
    (hns₁ : WeierstrassCurve.Affine.Nonsingular E0Good x₁ y₁)
    (hns₂ : WeierstrassCurve.Affine.Nonsingular E0Good x₂ y₂)
    (hxne : x₁ ≠ x₂) (hx₁neg : ordPi x₁ < 0) (hx₂neg : ordPi x₂ < 0) :
    let P : GoodPoint := .some x₁ y₁ hns₁
    let Q : GoodPoint := .some x₂ y₂ hns₂
    let r := min (ordPi (-x₁ / y₁)) (ordPi (-x₂ / y₂))
    InFormalKernel (P + Q) ∧
      (MazurProof.N18PackageII.zParamGood (P + Q) -
          MazurProof.N18PackageII.zParamGood P -
          MazurProof.N18PackageII.zParamGood Q = 0 ∨
        2 * r ≤ ordPi
          (MazurProof.N18PackageII.zParamGood (P + Q) -
            MazurProof.N18PackageII.zParamGood P -
            MazurProof.N18PackageII.zParamGood Q)) := by
  let P : GoodPoint := .some x₁ y₁ hns₁
  let Q : GoodPoint := .some x₂ y₂ hns₂
  let t₁ : L := -x₁ / y₁
  let w₁ : L := -1 / y₁
  let t₂ : L := -x₂ / y₂
  let w₂ : L := -1 / y₂
  let r₁ : ℤ := ordPi t₁
  let r₂ : ℤ := ordPi t₂
  let r : ℤ := min r₁ r₂
  have heq₁ := (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp hns₁.1
  have heq₂ := (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp hns₂.1
  have hc₁ := GoodModel.val_coords hx₁0 hy₁0 (by simpa using heq₁) hx₁neg
  have hc₂ := GoodModel.val_coords hx₂0 hy₂0 (by simpa using heq₂) hx₂neg
  have hx₁v : ordPi x₁ = -2 * r₁ := hc₁.1
  have hy₁v : ordPi y₁ = -3 * r₁ := hc₁.2
  have hx₂v : ordPi x₂ = -2 * r₂ := hc₂.1
  have hy₂v : ordPi y₂ = -3 * r₂ := hc₂.2
  have hr₁ : 1 ≤ r₁ := by omega
  have hr₂ : 1 ≤ r₂ := by omega
  have hr : 1 ≤ r := by simp only [r, le_min_iff]; exact ⟨hr₁, hr₂⟩
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := min_le_right _ _
  have ht₁0 : t₁ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₁0) hy₁0
  have ht₂0 : t₂ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx₂0) hy₂0
  have hw₁0 : w₁ ≠ 0 := div_ne_zero (by norm_num) hy₁0
  have hw₂0 : w₂ ≠ 0 := div_ne_zero (by norm_num) hy₂0
  have hw₁v : ordPi w₁ = 3 * r₁ := by
    dsimp [w₁]
    rw [ordPi_div (by norm_num) hy₁0, ordPi_neg, ordPi_one, hy₁v]
    omega
  have hw₂v : ordPi w₂ = 3 * r₂ := by
    dsimp [w₂]
    rw [ordPi_div (by norm_num) hy₂0, ordPi_neg, ordPi_one, hy₂v]
    omega
  have ht₁r : OrdGoodG r t₁ := Or.inr hrr₁
  have ht₂r : OrdGoodG r t₂ := Or.inr hrr₂
  have hw₁r : OrdGoodG (3 * r) w₁ := Or.inr (by rw [hw₁v]; omega)
  have hw₂r : OrdGoodG (3 * r) w₂ := Or.inr (by rw [hw₂v]; omega)
  have hG₁ : GGood t₁ w₁ = 0 := chartGGood_eq_zero hy₁0 heq₁
  have hG₂ : GGood t₂ w₂ = 0 := chartGGood_eq_zero hy₂0 heq₂
  let SU : L := 1 - E0Good.a₁ * t₂ - E0Good.a₂ * t₂ ^ 2 -
    E0Good.a₃ * (w₁ + w₂) - E0Good.a₄ * t₂ * (w₁ + w₂) -
    E0Good.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
  let SN : L := E0Good.a₁ * w₁ + E0Good.a₂ * (t₁ + t₂) * w₁ +
    E0Good.a₄ * w₁ ^ 2 + (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)
  have hcross : (w₁ - w₂) * SU = (t₁ - t₂) * SN := by
    dsimp [SU, SN]
    simp only [GGood] at hG₁ hG₂
    linear_combination hG₁ - hG₂
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have c1 : OrdGoodG 0 E0Good.a₁ := Or.inr ha1
  have c2 : OrdGoodG 0 E0Good.a₂ := Or.inr ha2
  have c3 : OrdGoodG 0 E0Good.a₃ := Or.inr ha3
  have c4 : OrdGoodG 0 E0Good.a₄ := Or.inr ha4
  have c6 : OrdGoodG 0 E0Good.a₆ := Or.inr ha6
  have ht₂1 : OrdGoodG 1 t₂ := ht₂r.mono (by omega)
  have hw₁1 : OrdGoodG 1 w₁ := hw₁r.mono (by omega)
  have hw₂1 : OrdGoodG 1 w₂ := hw₂r.mono (by omega)
  have hwsum1 : OrdGoodG 1 (w₁ + w₂) := hw₁1.add hw₂1
  have ht₂sq1 : OrdGoodG 1 (t₂ ^ 2) := by
    rw [pow_two]
    exact (ht₂1.mul ht₂1).mono (by omega)
  have hww1 : OrdGoodG 1 (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2) := by
    have h11 : OrdGoodG 1 (w₁ ^ 2) := by
      rw [pow_two]; exact (hw₁1.mul hw₁1).mono (by omega)
    have h12 : OrdGoodG 1 (w₁ * w₂) := (hw₁1.mul hw₂1).mono (by omega)
    have h22 : OrdGoodG 1 (w₂ ^ 2) := by
      rw [pow_two]; exact (hw₂1.mul hw₂1).mono (by omega)
    exact (h11.add h12).add h22
  let qSU : L := -E0Good.a₁ * t₂ - E0Good.a₂ * t₂ ^ 2 -
    E0Good.a₃ * (w₁ + w₂) - E0Good.a₄ * t₂ * (w₁ + w₂) -
    E0Good.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)
  have hqSU : OrdGoodG 1 qSU := by
    dsimp [qSU]
    have h1 : OrdGoodG 1 (-E0Good.a₁ * t₂) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₁ * t₂)) from
          (by simpa only [zero_add] using c1.mul ht₂1 :
            OrdGoodG 1 (E0Good.a₁ * t₂)).neg)
    have h2 : OrdGoodG 1 (-E0Good.a₂ * t₂ ^ 2) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₂ * t₂ ^ 2)) from
          (by simpa only [zero_add] using c2.mul ht₂sq1 :
            OrdGoodG 1 (E0Good.a₂ * t₂ ^ 2)).neg)
    have h3 : OrdGoodG 1 (-E0Good.a₃ * (w₁ + w₂)) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₃ * (w₁ + w₂))) from
          (by simpa only [zero_add] using c3.mul hwsum1 :
            OrdGoodG 1 (E0Good.a₃ * (w₁ + w₂))).neg)
    have h4base : OrdGoodG (1 + 1) (E0Good.a₄ * (t₂ * (w₁ + w₂))) := by
      simpa only [zero_add] using c4.mul (ht₂1.mul hwsum1)
    have h4 : OrdGoodG 1 (-E0Good.a₄ * t₂ * (w₁ + w₂)) := by
      simpa only [neg_mul, mul_assoc] using (h4base.mono (by norm_num)).neg
    have h6 : OrdGoodG 1
        (-E0Good.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)) := by
      simpa only [neg_mul, zero_add] using (c6.mul hww1).neg
    simpa only [sub_eq_add_neg, neg_mul] using (((h1.add h2).add h3).add h4).add h6
  have hSUeq : SU = 1 + qSU := by simp only [SU, qSU]; ring
  have hSUunit : SU ≠ 0 ∧ ordPi SU = 0 := by
    rw [hSUeq]
    exact hqSU.unit_one_add
  have htne : t₁ ≠ t₂ := by
    intro ht
    have hwdiff : w₁ - w₂ = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hSUunit.1
      rw [hcross, ht, sub_self, zero_mul]
    have hw : w₁ = w₂ := sub_eq_zero.mp hwdiff
    apply hxne
    have hx₁tw : x₁ = t₁ / w₁ := by
      dsimp [t₁, w₁]; field_simp [hy₁0]
    have hx₂tw : x₂ = t₂ / w₂ := by
      dsimp [t₂, w₂]; field_simp [hy₂0]
    rw [hx₁tw, hx₂tw, ht, hw]
  let m : L := (w₁ - w₂) / (t₁ - t₂)
  let b : L := w₁ - m * t₁
  have hline₁ : w₁ = m * t₁ + b := by dsimp [b]; ring
  have hline₂ : w₂ = m * t₂ + b := by
    dsimp [m, b]
    field_simp [sub_ne_zero.mpr htne]
    ring
  have hmEq : SU * m = SN := by
    dsimp [m]
    field_simp [sub_ne_zero.mpr htne]
    linear_combination hcross
  have hsumr : OrdGoodG r (t₁ + t₂) := ht₁r.add ht₂r
  have hSN : OrdGoodG (2 * r) SN := by
    have h1 : OrdGoodG (2 * r) (E0Good.a₁ * w₁) :=
      (c1.mul hw₁r).mono (by omega)
    have h2 : OrdGoodG (2 * r) (E0Good.a₂ * (t₁ + t₂) * w₁) :=
      (c2.mul hsumr |>.mul hw₁r).mono (by omega)
    have h4 : OrdGoodG (2 * r) (E0Good.a₄ * w₁ ^ 2) := by
      rw [pow_two]
      exact (c4.mul (hw₁r.mul hw₁r)).mono (by omega)
    have htt : OrdGoodG (2 * r) (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) := by
      have h11 : OrdGoodG (2 * r) (t₁ ^ 2) := by
        rw [pow_two]; simpa only [two_mul] using ht₁r.mul ht₁r
      have h12 : OrdGoodG (2 * r) (t₁ * t₂) := by
        simpa only [two_mul] using ht₁r.mul ht₂r
      have h22 : OrdGoodG (2 * r) (t₂ ^ 2) := by
        rw [pow_two]; simpa only [two_mul] using ht₂r.mul ht₂r
      exact (h11.add h12).add h22
    dsimp [SN]
    exact ((h1.add h2).add h4).add htt
  have hmGood : OrdGoodG (2 * r) m := by
    rcases hSN with hSN | hSN
    · left
      apply (mul_eq_zero.mp ?_).resolve_left hSUunit.1
      rw [hmEq, hSN]
    · have hSN0 : SN ≠ 0 := by
        intro h; rw [h, ordPi_zero] at hSN; omega
      have hm0 : m ≠ 0 := by
        intro h; rw [h, mul_zero] at hmEq; exact hSN0 hmEq.symm
      right
      have hv := congrArg ordPi hmEq
      rw [ordPi_mul hSUunit.1 hm0, hSUunit.2] at hv
      omega
  have hbGood : OrdGoodG (3 * r) b := by
    have hmt : OrdGoodG (3 * r) (m * t₁) :=
      (hmGood.mul ht₁r).mono (by omega)
    dsimp [b]
    exact hw₁r.sub hmt
  have hb0 : b ≠ 0 := by
    intro hb
    have hm0 : m ≠ 0 := by
      intro hm0
      rw [hb, hm0, zero_mul, add_zero] at hline₁
      exact hw₁0 hline₁
    apply hxne
    have hx₁tw : x₁ = t₁ / w₁ := by
      dsimp [t₁, w₁]; field_simp [hy₁0]
    have hx₂tw : x₂ = t₂ / w₂ := by
      dsimp [t₂, w₂]; field_simp [hy₂0]
    rw [hx₁tw, hx₂tw, hline₁, hline₂, hb]
    field_simp [hm0, ht₁0, ht₂0]
    ring
  let u : L := -BGood m b / AGood m - t₁ - t₂
  let d : L := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
  let t₃ : L := -u / d
  have hval := line_valuation_good r t₁ t₂ m b hr ht₁r ht₂r hmGood hbGood
  change (AGood m ≠ 0 ∧ ordPi (AGood m) = 0) ∧
    (d ≠ 0 ∧ ordPi d = 0) ∧ OrdGoodG r u ∧
    (t₃ - t₁ - t₂ = 0 ∨ 2 * r ≤ ordPi (t₃ - t₁ - t₂)) at hval
  rcases hval with ⟨hAunit, hdunit, huGood, herr⟩
  have hlineG₁ : GGood t₁ (m * t₁ + b) = 0 := by
    rw [← hline₁]; exact hG₁
  have hlineG₂ : GGood t₂ (m * t₂ + b) = 0 := by
    rw [← hline₂]; exact hG₂
  have hvieta := secant_vieta_good m b t₁ t₂ hlineG₁ hlineG₂ htne hAunit.1
  change AGood m * (t₁ + t₂ + u) + BGood m b = 0 ∧
    AGood m * (t₁ * t₂ + (t₁ + t₂) * u) + CGood m b = 0 ∧
    AGood m * t₁ * t₂ * u = DGood b at hvieta
  rcases hvieta with ⟨hsum, hpair, hprod⟩
  have hxsumData := vieta_x_sum_good m b t₁ t₂ u hAunit.1 hb0 hsum hpair hprod
  dsimp only at hxsumData
  rcases hxsumData with ⟨hqprod, hxsum⟩
  have hmu0 : m * u + b ≠ 0 := by
    intro h; apply hqprod; simp [h]
  have hmt₁0 : m * t₁ + b ≠ 0 := by simpa only [← hline₁] using hw₁0
  have hmt₂0 : m * t₂ + b ≠ 0 := by simpa only [← hline₂] using hw₂0
  have hx₁chart : x₁ = t₁ / (m * t₁ + b) := by
    rw [← hline₁]; dsimp [t₁, w₁]; field_simp [hy₁0]
  have hx₂chart : x₂ = t₂ / (m * t₂ + b) := by
    rw [← hline₂]; dsimp [t₂, w₂]; field_simp [hy₂0]
  have hy₁chart : y₁ = -1 / (m * t₁ + b) := by
    rw [← hline₁]; dsimp [w₁]; field_simp [hy₁0]
  have hy₂chart : y₂ = -1 / (m * t₂ + b) := by
    rw [← hline₂]; dsimp [w₂]; field_simp [hy₂0]
  let ell := WeierstrassCurve.Affine.slope E0Good x₁ x₂ y₁ y₂
  have hell : ell = m / b := by
    dsimp only [ell]
    rw [WeierstrassCurve.Affine.slope_of_X_ne hxne]
    rw [hx₁chart, hx₂chart, hy₁chart, hy₂chart]
    have hxdiff :
        t₁ / (m * t₁ + b) - t₂ / (m * t₂ + b) ≠ 0 := by
      simpa only [← hx₁chart, ← hx₂chart] using sub_ne_zero.mpr hxne
    have hbdiff : -(b * t₂) + b * t₁ ≠ 0 := by
      rw [show -(b * t₂) + b * t₁ = b * (t₁ - t₂) by ring]
      exact mul_ne_zero hb0 (sub_ne_zero.mpr htne)
    field_simp [hmt₁0, hmt₂0, hxdiff, hb0, hbdiff]
    calc
      b * (-(m * t₂ + b) - -(m * t₁ + b)) /
          (t₁ * (m * t₂ + b) - (m * t₁ + b) * t₂) =
          m * (-(b * t₂) + b * t₁) / (-(b * t₂) + b * t₁) := by
            congr 1 <;> ring
      _ = m := by
        have htdiff : -t₂ + t₁ ≠ 0 := by
          simpa only [neg_add_eq_sub, sub_ne_zero] using htne
        field_simp [htdiff]
  let x₃ := WeierstrassCurve.Affine.addX E0Good x₁ x₂ ell
  have hx₃ : x₃ = u / (m * u + b) := by
    change ell ^ 2 + E0Good.a₁ * ell - E0Good.a₂ - x₁ - x₂ =
      u / (m * u + b)
    rw [hell, hx₁chart, hx₂chart, ← hxsum]
    abel
  let ybar := WeierstrassCurve.Affine.negAddY E0Good x₁ x₂ y₁ ell
  have hybar : ybar = -1 / (m * u + b) := by
    change ell * (x₃ - x₁) + y₁ = -1 / (m * u + b)
    rw [hx₃, hell, hx₁chart, hy₁chart]
    field_simp [hb0, hmt₁0, hmu0]
    ring
  let y₃ := WeierstrassCurve.Affine.addY E0Good x₁ x₂ y₁ ell
  have hy₃ : y₃ = d / (m * u + b) := by
    change WeierstrassCurve.Affine.negY E0Good x₃ ybar = d / (m * u + b)
    rw [hybar, hx₃]
    simp only [WeierstrassCurve.Affine.negY]
    dsimp [d]
    field_simp [hmu0]
    ring
  have hbridge : MazurProof.N18PackageII.zParamGood (P + Q) = t₃ := by
    dsimp [P, Q]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
    change -x₃ / y₃ = t₃
    rw [hx₃, hy₃]
    dsimp [t₃]
    have hmu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hmu0
    field_simp [hmu0, hmu0', hdunit.1]
  have hmuGood : OrdGoodG (3 * r) (m * u) :=
    (hmGood.mul huGood).mono (by omega)
  have hmubGood : OrdGoodG (3 * r) (m * u + b) :=
    hmuGood.add hbGood
  have hmubOrd : 3 * r ≤ ordPi (m * u + b) := by
    rcases hmubGood with hmubZero | hmubOrd
    · exact (hmu0 hmubZero).elim
    · exact hmubOrd
  have hns₃ : WeierstrassCurve.Affine.Nonsingular E0Good x₃ y₃ := by
    exact WeierstrassCurve.Affine.nonsingular_add hns₁ hns₂
      (fun hxy ↦ hxne hxy.1)
  have hy₃v : ordPi y₃ = -ordPi (m * u + b) := by
    rw [hy₃, ordPi_div hdunit.1 hmu0, hdunit.2]
    ring
  have hy₃neg : ordPi y₃ < 0 := by
    rw [hy₃v]
    omega
  have hx₃neg : ordPi x₃ < 0 := by
    by_contra hx₃
    have hy₃nonneg := y_nonneg_of_x_nonneg_good hns₃ (le_of_not_gt hx₃)
    omega
  have hformal : InFormalKernel (P + Q) := by
    dsimp only [P, Q]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
    exact Or.inr hx₃neg
  dsimp only
  refine ⟨hformal, ?_⟩
  rw [hbridge]
  exact herr

private theorem add_congr_tangent_good {x y : L}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hns : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hxneg : ordPi x < 0)
    (hyne : WeierstrassCurve.Affine.negY E0Good x y ≠ y) :
    let P : GoodPoint := .some x y hns
    let r := ordPi (-x / y)
    InFormalKernel (P + P) ∧
      (MazurProof.N18PackageII.zParamGood (P + P) -
          2 * MazurProof.N18PackageII.zParamGood P = 0 ∨
        2 * r ≤ ordPi
          (MazurProof.N18PackageII.zParamGood (P + P) -
            2 * MazurProof.N18PackageII.zParamGood P)) := by
  let P : GoodPoint := .some x y hns
  let t : L := -x / y
  let w : L := -1 / y
  let r : ℤ := ordPi t
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp hns.1
  have hc := GoodModel.val_coords hx0 hy0 (by simpa using heq) hxneg
  have hxv : ordPi x = -2 * r := hc.1
  have hyv : ordPi y = -3 * r := hc.2
  have hr : 1 ≤ r := by omega
  have ht0 : t ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy0
  have hw0 : w ≠ 0 := div_ne_zero (by norm_num) hy0
  have hwv : ordPi w = 3 * r := by
    dsimp [w]
    rw [ordPi_div (by norm_num) hy0, ordPi_neg, ordPi_one, hyv]
    omega
  have htGood : OrdGoodG r t := Or.inr (by rfl)
  have hwGood : OrdGoodG (3 * r) w := Or.inr (by rw [hwv])
  have hG : GGood t w = 0 := chartGGood_eq_zero hy0 heq
  rcases good_coeff_orders with ⟨ha1, ha2, ha3, ha4, ha6⟩
  have c1 : OrdGoodG 0 E0Good.a₁ := Or.inr ha1
  have c2 : OrdGoodG 0 E0Good.a₂ := Or.inr ha2
  have c3 : OrdGoodG 0 E0Good.a₃ := Or.inr ha3
  have c4 : OrdGoodG 0 E0Good.a₄ := Or.inr ha4
  have c6 : OrdGoodG 0 E0Good.a₆ := Or.inr ha6
  let TU : L := 1 - E0Good.a₁ * t - E0Good.a₂ * t ^ 2 -
    2 * E0Good.a₃ * w - 2 * E0Good.a₄ * t * w -
    3 * E0Good.a₆ * w ^ 2
  let TN : L := 3 * t ^ 2 + E0Good.a₁ * w +
    2 * E0Good.a₂ * t * w + E0Good.a₄ * w ^ 2
  have ht1 : OrdGoodG 1 t := htGood.mono (by omega)
  have hw1 : OrdGoodG 1 w := hwGood.mono (by omega)
  have htSq1 : OrdGoodG 1 (t ^ 2) := by
    rw [pow_two]; exact (ht1.mul ht1).mono (by omega)
  have hwSq1 : OrdGoodG 1 (w ^ 2) := by
    rw [pow_two]; exact (hw1.mul hw1).mono (by omega)
  let qTU : L := -E0Good.a₁ * t - E0Good.a₂ * t ^ 2 -
    2 * E0Good.a₃ * w - 2 * E0Good.a₄ * t * w -
    3 * E0Good.a₆ * w ^ 2
  have hqTU : OrdGoodG 1 qTU := by
    dsimp [qTU]
    have h1 : OrdGoodG 1 (-E0Good.a₁ * t) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₁ * t)) from
          (by simpa only [zero_add] using c1.mul ht1 :
            OrdGoodG 1 (E0Good.a₁ * t)).neg)
    have h2 : OrdGoodG 1 (-E0Good.a₂ * t ^ 2) := by
      simpa only [neg_mul] using
        (show OrdGoodG 1 (-(E0Good.a₂ * t ^ 2)) from
          (by simpa only [zero_add] using c2.mul htSq1 :
            OrdGoodG 1 (E0Good.a₂ * t ^ 2)).neg)
    have h3base : OrdGoodG 1 (E0Good.a₃ * w) := by
      simpa only [zero_add] using c3.mul hw1
    have h3 : OrdGoodG 1 (-2 * E0Good.a₃ * w) := by
      simpa only [Nat.cast_ofNat, neg_mul, mul_assoc] using
        (h3base.nat_mul 2).neg
    have h4base : OrdGoodG (1 + 1) (E0Good.a₄ * (t * w)) := by
      simpa only [zero_add] using c4.mul (ht1.mul hw1)
    have h4 : OrdGoodG 1 (-2 * E0Good.a₄ * t * w) := by
      simpa only [Nat.cast_ofNat, neg_mul, mul_assoc] using
        ((h4base.mono (by norm_num)).nat_mul 2).neg
    have h6base : OrdGoodG 1 (E0Good.a₆ * w ^ 2) := by
      simpa only [zero_add] using c6.mul hwSq1
    have h6 : OrdGoodG 1 (-3 * E0Good.a₆ * w ^ 2) := by
      simpa only [Nat.cast_ofNat, neg_mul, mul_assoc] using
        (h6base.nat_mul 3).neg
    simpa only [sub_eq_add_neg, neg_mul] using (((h1.add h2).add h3).add h4).add h6
  have hTUeq : TU = 1 + qTU := by simp only [TU, qTU]; ring
  have hTUunit : TU ≠ 0 ∧ ordPi TU = 0 := by
    rw [hTUeq]
    exact hqTU.unit_one_add
  have htSq : OrdGoodG (2 * r) (t ^ 2) := by
    rw [pow_two]; simpa only [two_mul] using htGood.mul htGood
  have hw2 : OrdGoodG (2 * r) w := hwGood.mono (by omega)
  have hTN : OrdGoodG (2 * r) TN := by
    have h0 := htSq.nat_mul 3
    have h1 : OrdGoodG (2 * r) (E0Good.a₁ * w) :=
      (c1.mul hw2).mono (by omega)
    have h2base : OrdGoodG (2 * r) (E0Good.a₂ * (t * w)) :=
      (c2.mul (htGood.mul hwGood)).mono (by omega)
    have h2 : OrdGoodG (2 * r) (2 * E0Good.a₂ * t * w) := by
      simpa only [Nat.cast_ofNat, mul_assoc] using h2base.nat_mul 2
    have h4 : OrdGoodG (2 * r) (E0Good.a₄ * w ^ 2) := by
      rw [pow_two]
      exact (c4.mul (hwGood.mul hwGood)).mono (by omega)
    dsimp [TN]
    exact ((h0.add h1).add h2).add h4
  let m : L := TN / TU
  have hmGood : OrdGoodG (2 * r) m :=
    hTN.div_unit hTUunit.1 hTUunit.2
  have hTUm : TU * m = TN := by
    dsimp [m]
    field_simp [hTUunit.1]
  let b : L := w - m * t
  have hline : w = m * t + b := by dsimp [b]; ring
  have hbGood : OrdGoodG (3 * r) b := by
    have hmt : OrdGoodG (3 * r) (m * t) :=
      (hmGood.mul htGood).mono (by omega)
    dsimp [b]
    exact hwGood.sub hmt
  let et : L := E0Good.a₁ * t + E0Good.a₃ * w - 2
  have hbIdentity : TU * b = w * et := by
    have hTUm' := hTUm
    dsimp [TU, TN] at hTUm'
    dsimp [b, et]
    simp only [GGood] at hG
    linear_combination 3 * hG - t * hTUm'
  have htwo : ordPi (2 : L) = 0 := by
    have hn1 : ordPi (-1 : L) = 0 := by rw [ordPi_neg, ordPi_one]
    calc
      ordPi (2 : L) = ordPi ((-1 : L) + 3) := by norm_num
      _ = ordPi (-1 : L) :=
        ordPi_add_eq_of_lt (by norm_num) (by norm_num)
          (by rw [hn1, ordPi_three]; omega)
      _ = 0 := hn1
  let qet : L := -(E0Good.a₁ * t + E0Good.a₃ * w) / 2
  have hqet : OrdGoodG 1 qet := by
    dsimp [qet]
    exact ((c1.mul ht1).mono (by omega) |>.add
      ((c3.mul hw1).mono (by omega))).neg.div_unit (by norm_num) htwo
  have hqetUnit : 1 + qet ≠ 0 ∧ ordPi (1 + qet) = 0 :=
    hqet.unit_one_add
  have hetEq : et = -2 * (1 + qet) := by
    dsimp [et, qet]
    field_simp
    ring
  have hetUnit : et ≠ 0 ∧ ordPi et = 0 := by
    constructor
    · rw [hetEq]
      exact mul_ne_zero (by norm_num) hqetUnit.1
    · rw [hetEq, ordPi_mul (by norm_num) hqetUnit.1,
        ordPi_neg, htwo, hqetUnit.2]
      omega
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, mul_zero] at hbIdentity
    exact (mul_ne_zero hw0 hetUnit.1) hbIdentity.symm
  let u : L := -BGood m b / AGood m - t - t
  let d : L := 1 - (E0Good.a₁ + E0Good.a₃ * m) * u - E0Good.a₃ * b
  let t₃ : L := -u / d
  have hval := line_valuation_good r t t m b hr htGood htGood hmGood hbGood
  change (AGood m ≠ 0 ∧ ordPi (AGood m) = 0) ∧
    (d ≠ 0 ∧ ordPi d = 0) ∧ OrdGoodG r u ∧
    (t₃ - t - t = 0 ∨ 2 * r ≤ ordPi (t₃ - t - t)) at hval
  rcases hval with ⟨hAunit, hdunit, huGood, herr⟩
  have hlineG : GGood t (m * t + b) = 0 := by rw [← hline]; exact hG
  have htangent :
      -3 * AGood m * t ^ 2 - 2 * BGood m b * t + CGood m b = 0 := by
    have hTUm' := hTUm
    dsimp [TU, TN] at hTUm'
    simp only [AGood, BGood, CGood]
    dsimp [b]
    linear_combination hTUm'
  have hsum : AGood m * (t + t + u) + BGood m b = 0 := by
    dsimp [u]
    field_simp [hAunit.1]
    ring
  have hpair :
      AGood m * (t * t + (t + t) * u) + CGood m b = 0 := by
    linear_combination htangent + 2 * t * hsum
  have hp := hlineG
  rw [GGood_line] at hp
  have hprod : AGood m * t * t * u = DGood b := by
    linear_combination -hp - t ^ 2 * hsum + t * hpair
  have hxsumData := vieta_x_sum_good m b t t u hAunit.1 hb0 hsum hpair hprod
  dsimp only at hxsumData
  rcases hxsumData with ⟨hqprod, hxsum⟩
  have hmu0 : m * u + b ≠ 0 := by
    intro h; apply hqprod; simp [h]
  have hmt0 : m * t + b ≠ 0 := by simpa only [← hline] using hw0
  have hxchart0 : x = t / w := by
    dsimp [t, w]; field_simp [hy0]
  have hychart0 : y = -1 / w := by
    dsimp [w]; field_simp [hy0]
  have hxchart : x = t / (m * t + b) := by rw [← hline]; exact hxchart0
  have hychart : y = -1 / (m * t + b) := by rw [← hline]; exact hychart0
  let ell := WeierstrassCurve.Affine.slope E0Good x x y y
  have hyne' : y ≠ WeierstrassCurve.Affine.negY E0Good x y := Ne.symm hyne
  have hellFormula : ell = TN / (w * et) := by
    dsimp only [ell]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne']
    rw [hxchart0, hychart0]
    simp only [WeierstrassCurve.Affine.negY]
    dsimp [TN, et]
    field_simp [hw0, hetUnit.1]
    ring
  have hell : ell = m / b := by
    rw [hellFormula]
    apply (div_eq_div_iff (mul_ne_zero hw0 hetUnit.1) hb0).2
    linear_combination -b * hTUm + m * hbIdentity
  let x₃ := WeierstrassCurve.Affine.addX E0Good x x ell
  have hx₃ : x₃ = u / (m * u + b) := by
    change ell ^ 2 + E0Good.a₁ * ell - E0Good.a₂ - x - x =
      u / (m * u + b)
    rw [hell, hxchart, ← hxsum]
    abel
  let ybar := WeierstrassCurve.Affine.negAddY E0Good x x y ell
  have hybar : ybar = -1 / (m * u + b) := by
    change ell * (x₃ - x) + y = -1 / (m * u + b)
    rw [hx₃, hell, hxchart, hychart]
    field_simp [hb0, hmt0, hmu0]
    ring
  let y₃ := WeierstrassCurve.Affine.addY E0Good x x y ell
  have hy₃ : y₃ = d / (m * u + b) := by
    change WeierstrassCurve.Affine.negY E0Good x₃ ybar = d / (m * u + b)
    rw [hybar, hx₃]
    simp only [WeierstrassCurve.Affine.negY]
    dsimp [d]
    field_simp [hmu0]
    ring
  have hbridge : MazurProof.N18PackageII.zParamGood (P + P) = t₃ := by
    dsimp [P]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne']
    change -x₃ / y₃ = t₃
    rw [hx₃, hy₃]
    dsimp [t₃]
    have hmu0' : u * m + b ≠ 0 := by simpa only [mul_comm] using hmu0
    field_simp [hmu0, hmu0', hdunit.1]
  have hmuGood : OrdGoodG (3 * r) (m * u) :=
    (hmGood.mul huGood).mono (by omega)
  have hmubGood : OrdGoodG (3 * r) (m * u + b) :=
    hmuGood.add hbGood
  have hmubOrd : 3 * r ≤ ordPi (m * u + b) := by
    rcases hmubGood with hmubZero | hmubOrd
    · exact (hmu0 hmubZero).elim
    · exact hmubOrd
  have hns₃ : WeierstrassCurve.Affine.Nonsingular E0Good x₃ y₃ := by
    exact WeierstrassCurve.Affine.nonsingular_add hns hns
      (fun hxy ↦ hyne' hxy.2)
  have hy₃v : ordPi y₃ = -ordPi (m * u + b) := by
    rw [hy₃, ordPi_div hdunit.1 hmu0, hdunit.2]
    ring
  have hy₃neg : ordPi y₃ < 0 := by
    rw [hy₃v]
    omega
  have hx₃neg : ordPi x₃ < 0 := by
    by_contra hx₃
    have hy₃nonneg := y_nonneg_of_x_nonneg_good hns₃ (le_of_not_gt hx₃)
    omega
  have hformal : InFormalKernel (P + P) := by
    dsimp only [P]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne']
    exact Or.inr hx₃neg
  dsimp only
  refine ⟨hformal, ?_⟩
  rw [hbridge]
  change t₃ - 2 * t = 0 ∨ 2 * r ≤ ordPi (t₃ - 2 * t)
  rw [show t₃ - 2 * t = t₃ - t - t by ring]
  exact herr

/-- Package I on the good model, in the weak form used by the induction.
The intended proof expands the integral chart law and applies the
ultrametric inequality term by term; every error monomial has total order at
least twice the smaller input order. -/
theorem add_congr_good_weak (P Q : GoodPoint)
    (hP : InFormalKernel P) (hQ : InFormalKernel Q) :
    2 * min
        (vpiGood (MazurProof.N18PackageII.zParamGood P))
        (vpiGood (MazurProof.N18PackageII.zParamGood Q)) ≤
      vpiGood
        (MazurProof.N18PackageII.zParamGood (P + Q) -
          MazurProof.N18PackageII.zParamGood P -
          MazurProof.N18PackageII.zParamGood Q) := by
  rcases hP with hP0 | hPx
  · subst P
    have herr : MazurProof.N18PackageII.zParamGood ((0 : GoodPoint) + Q) -
        MazurProof.N18PackageII.zParamGood 0 -
        MazurProof.N18PackageII.zParamGood Q = 0 := by
      rw [zero_add Q, MazurProof.N18PackageII.zParamGood_zero]
      ring
    rw [herr, vpiGood_zero]
    exact le_top
  rcases hQ with hQ0 | hQx
  · subst Q
    have herr : MazurProof.N18PackageII.zParamGood (P + (0 : GoodPoint)) -
        MazurProof.N18PackageII.zParamGood P -
        MazurProof.N18PackageII.zParamGood 0 = 0 := by
      rw [add_zero P, MazurProof.N18PackageII.zParamGood_zero]
      ring
    rw [herr, vpiGood_zero]
    exact le_top
  rcases P with _ | ⟨x₁, y₁, hns₁⟩
  · simp [xCoordGood, ordPi_zero] at hPx
  rcases Q with _ | ⟨x₂, y₂, hns₂⟩
  · simp [xCoordGood, ordPi_zero] at hQx
  simp only [xCoordGood] at hPx hQx
  have hx₁0 : x₁ ≠ 0 := by
    intro h; rw [h, ordPi_zero] at hPx; omega
  have hx₂0 : x₂ ≠ 0 := by
    intro h; rw [h, ordPi_zero] at hQx; omega
  have hy₁0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₁ hPx
  have hy₂0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₂ hQx
  let P₁ : GoodPoint := .some x₁ y₁ hns₁
  let Q₂ : GoodPoint := .some x₂ y₂ hns₂
  have hzP : MazurProof.N18PackageII.zParamGood P₁ ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hx₁0) hy₁0
  have hzQ : MazurProof.N18PackageII.zParamGood Q₂ ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hx₂0) hy₂0
  have hzPpos : 1 ≤ ordPi (MazurProof.N18PackageII.zParamGood P₁) := by
    have hc := GoodModel.val_coords hx₁0 hy₁0
      (by simpa using (WeierstrassCurve.Affine.equation_iff x₁ y₁).mp hns₁.1) hPx
    dsimp [P₁, MazurProof.N18PackageII.zParamGood]
    omega
  have hzQpos : 1 ≤ ordPi (MazurProof.N18PackageII.zParamGood Q₂) := by
    have hc := GoodModel.val_coords hx₂0 hy₂0
      (by simpa using (WeierstrassCurve.Affine.equation_iff x₂ y₂).mp hns₂.1) hQx
    dsimp [Q₂, MazurProof.N18PackageII.zParamGood]
    omega
  change 2 * min
      (vpiGood (MazurProof.N18PackageII.zParamGood P₁))
      (vpiGood (MazurProof.N18PackageII.zParamGood Q₂)) ≤
    vpiGood (MazurProof.N18PackageII.zParamGood (P₁ + Q₂) -
      MazurProof.N18PackageII.zParamGood P₁ -
      MazurProof.N18PackageII.zParamGood Q₂)
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = WeierstrassCurve.Affine.negY E0Good x₁ y₂
    · have hy₂ : y₂ = WeierstrassCurve.Affine.negY E0Good x₁ y₁ := by
        rw [hy, WeierstrassCurve.Affine.negY_negY]
      have hQnegP : Q₂ = -P₁ := by
        subst y₂
        dsimp only [P₁, Q₂]
        rfl
      rw [hQnegP]
      have hb := (add_congr_inverse_good hx₁0 hy₁0 hns₁ hPx).2
      let err := MazurProof.N18PackageII.zParamGood (P₁ + -P₁) -
        MazurProof.N18PackageII.zParamGood P₁ -
        MazurProof.N18PackageII.zParamGood (-P₁)
      change err = 0 ∨
        2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) ≤ ordPi err at hb
      rcases hb with herr | herr
      · change 2 * min
            (vpiGood (MazurProof.N18PackageII.zParamGood P₁))
            (vpiGood (MazurProof.N18PackageII.zParamGood (-P₁))) ≤
          vpiGood err
        rw [herr, vpiGood_zero]
        exact le_top
      · have herr0 : err ≠ 0 := by
          intro h
          rw [h, ordPi_zero] at herr
          omega
        have hvneg := vpi_zParamGood_neg P₁ (Or.inr hPx)
        rw [hvneg, min_self, vpiGood_apply_of_ne hzP,
          vpiGood_apply_of_ne herr0]
        change ((2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) : ℤ) :
          WithTop ℤ) ≤ (ordPi err : WithTop ℤ)
        exact WithTop.coe_le_coe.mpr herr
    · have hyEq : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne hns₁.1 hns₂.1 rfl hy
      subst y₂
      cases Subsingleton.elim hns₂ hns₁
      have hQP : Q₂ = P₁ := rfl
      rw [hQP]
      have hb :=
        (add_congr_tangent_good hx₁0 hy₁0 hns₁ hPx (fun h => hy h.symm)).2
      let err := MazurProof.N18PackageII.zParamGood (P₁ + P₁) -
        2 * MazurProof.N18PackageII.zParamGood P₁
      change err = 0 ∨
        2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) ≤ ordPi err at hb
      rcases hb with herr | herr
      · have herrShape :
            MazurProof.N18PackageII.zParamGood (P₁ + P₁) -
                MazurProof.N18PackageII.zParamGood P₁ -
                MazurProof.N18PackageII.zParamGood P₁ = err := by
          dsimp [err]
          ring
        rw [herrShape, herr, vpiGood_zero]
        exact le_top
      · have herr0 : err ≠ 0 := by
          intro h; rw [h, ordPi_zero] at herr; omega
        rw [min_self, vpiGood_apply_of_ne hzP,
          show MazurProof.N18PackageII.zParamGood (P₁ + P₁) -
              MazurProof.N18PackageII.zParamGood P₁ -
              MazurProof.N18PackageII.zParamGood P₁ = err by
            dsimp [err]; ring,
          vpiGood_apply_of_ne herr0]
        change ((2 * ordPi (MazurProof.N18PackageII.zParamGood P₁) : ℤ) :
          WithTop ℤ) ≤ (ordPi err : WithTop ℤ)
        exact WithTop.coe_le_coe.mpr herr
  · have hb := (add_congr_distinct_good
      hx₁0 hy₁0 hx₂0 hy₂0 hns₁ hns₂ hx hPx hQx).2
    let err := MazurProof.N18PackageII.zParamGood (P₁ + Q₂) -
      MazurProof.N18PackageII.zParamGood P₁ -
      MazurProof.N18PackageII.zParamGood Q₂
    change err = 0 ∨
      2 * min (ordPi (MazurProof.N18PackageII.zParamGood P₁))
        (ordPi (MazurProof.N18PackageII.zParamGood Q₂)) ≤ ordPi err at hb
    rcases hb with herr | herr
    · change 2 * min
          (vpiGood (MazurProof.N18PackageII.zParamGood P₁))
          (vpiGood (MazurProof.N18PackageII.zParamGood Q₂)) ≤
        vpiGood err
      rw [herr, vpiGood_zero]
      exact le_top
    · have herr0 : err ≠ 0 := by
        intro h; rw [h, ordPi_zero] at herr; omega
      rw [vpiGood_apply_of_ne hzP, vpiGood_apply_of_ne hzQ,
        vpiGood_apply_of_ne herr0]
      change ((2 * min
          (ordPi (MazurProof.N18PackageII.zParamGood P₁))
          (ordPi (MazurProof.N18PackageII.zParamGood Q₂)) : ℤ) :
        WithTop ℤ) ≤ (ordPi err : WithTop ℤ)
      exact WithTop.coe_le_coe.mpr herr

/-- The near-origin locus is closed under addition. -/
theorem kernel_add_closed_good (P Q : GoodPoint)
    (hP : InFormalKernel P) (hQ : InFormalKernel Q) :
    InFormalKernel (P + Q) := by
  rcases hP with hP0 | hPx
  · subst P
    rw [zero_add Q]
    exact hQ
  rcases hQ with hQ0 | hQx
  · subst Q
    rw [add_zero P]
    exact Or.inr hPx
  rcases P with _ | ⟨x₁, y₁, hns₁⟩
  · simp [xCoordGood, ordPi_zero] at hPx
  rcases Q with _ | ⟨x₂, y₂, hns₂⟩
  · simp [xCoordGood, ordPi_zero] at hQx
  simp only [xCoordGood] at hPx hQx
  have hx₁0 : x₁ ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hPx
    omega
  have hx₂0 : x₂ ≠ 0 := by
    intro h
    rw [h, ordPi_zero] at hQx
    omega
  have hy₁0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₁ hPx
  have hy₂0 := yCoordGood_ne_zero_of_ordPi_x_neg hns₂ hQx
  let P₁ : GoodPoint := .some x₁ y₁ hns₁
  let Q₂ : GoodPoint := .some x₂ y₂ hns₂
  change InFormalKernel (P₁ + Q₂)
  by_cases hx : x₁ = x₂
  · subst x₂
    by_cases hy : y₁ = WeierstrassCurve.Affine.negY E0Good x₁ y₂
    · have hy₂ : y₂ = WeierstrassCurve.Affine.negY E0Good x₁ y₁ := by
        rw [hy, WeierstrassCurve.Affine.negY_negY]
      have hQnegP : Q₂ = -P₁ := by
        subst y₂
        rfl
      rw [hQnegP]
      exact (add_congr_inverse_good hx₁0 hy₁0 hns₁ hPx).1
    · have hyEq : y₁ = y₂ :=
        WeierstrassCurve.Affine.Y_eq_of_Y_ne hns₁.1 hns₂.1 rfl hy
      subst y₂
      cases Subsingleton.elim hns₂ hns₁
      have hQP : Q₂ = P₁ := rfl
      rw [hQP]
      exact (add_congr_tangent_good hx₁0 hy₁0 hns₁ hPx
        (fun h ↦ hy h.symm)).1
  · exact (add_congr_distinct_good
      hx₁0 hy₁0 hx₂0 hy₂0 hns₁ hns₂ hx hPx hQx).1

/-! ## Residue codes for the quotient by the formal kernel -/

abbrev GoodOL := NumberField.RingOfIntegers L

/-- Reduction modulo `pi` in the integral basis `1, pi, pi²`. -/
private noncomputable def reducePiOL : GoodOL →+* ZMod 3 where
  toFun u := ((MazurProof.N18RouteC.LocalThreeSound.coordsOf u).c0 : ZMod 3)
  map_zero' := by
    simp [MazurProof.N18RouteC.LocalThreeSound.coordsOf_zero]
  map_one' := by
    simp [MazurProof.N18RouteC.LocalThreeSound.coordsOf_one,
      MazurProof.N18RouteC.LocalThreeSound.IntCoords.one]
  map_add' x y := by
    simp [MazurProof.N18RouteC.LocalThreeSound.coordsOf_add,
      MazurProof.N18RouteC.LocalThreeSound.IntCoords.add]
  map_mul' x y := by
    rw [MazurProof.N18RouteC.LocalThreeSound.coordsOf_mul]
    simp only [MazurProof.N18RouteC.LocalThreeSound.IntCoords.mul,
      MazurProof.N18RouteC.LocalThreeSound.prodC0]
    push_cast
    rw [show (3 : ZMod 3) = 0 by decide,
      show (9 : ZMod 3) = 0 by decide]
    ring

@[simp] private theorem reducePiOL_piInteger :
    reducePiOL FieldArithmetic.piInteger = 0 := by
  simp [reducePiOL, MazurProof.N18RouteC.LocalThreeSound.coordsOf_piInteger]

@[simp] private theorem reducePiOL_aInteger :
    reducePiOL FieldArithmetic.aInteger = 1 := by
  simp [reducePiOL, MazurProof.N18RouteC.LocalThreeSound.coordsOf_aInteger,
    MazurProof.N18RouteC.LocalThreeSound.aCoords]

@[simp] private theorem reducePiOL_natCast (n : ℕ) :
    reducePiOL (n : GoodOL) = (n : ZMod 3) :=
  map_natCast reducePiOL n

@[simp] private theorem reducePiOL_two :
    reducePiOL (2 : GoodOL) = (2 : ZMod 3) := by
  exact map_ofNat reducePiOL 2

@[simp] private theorem reducePiOL_three :
    reducePiOL (3 : GoodOL) = (3 : ZMod 3) := by
  exact map_ofNat reducePiOL 3

@[simp] private theorem reducePiOL_four :
    reducePiOL (4 : GoodOL) = (4 : ZMod 3) := by
  exact map_ofNat reducePiOL 4

@[simp] private theorem reducePiOL_seven :
    reducePiOL (7 : GoodOL) = (7 : ZMod 3) := by
  exact map_ofNat reducePiOL 7

private theorem reducePiOL_den_ne_zero (d : p3.asIdeal.primeCompl) :
    reducePiOL d ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  have hd := MazurProof.N18RouteC.LocalThreeSound.reduceOL_isUnit_of_not_mem d.prop
  rw [MazurProof.N18RouteC.LocalThree.isUnit5_iff] at hd
  exact isUnit_iff_ne_zero.mpr (by
    simpa [reducePiOL, MazurProof.N18RouteC.LocalThreeSound.reduceOL,
      MazurProof.N18RouteC.LocalThreeSound.IntCoords.red,
      MazurProof.N18RouteC.LocalThreeSound.reduceInt,
      MazurProof.N18RouteC.LocalThree.red3] using hd)

private def IntegralAtPi (x : L) : Prop := p3.valuation L x ≤ 1

private def ReducesPi (x : L) (r : ZMod 3) : Prop :=
  ∃ n : GoodOL, ∃ d : p3.asIdeal.primeCompl,
    x * algebraMap GoodOL L d = algebraMap GoodOL L n ∧
      r * reducePiOL d = reducePiOL n

private theorem reducesPi_exists {x : L} (hx : IntegralAtPi x) :
    ∃ r : ZMod 3, ReducesPi x r := by
  obtain ⟨n, d, hnd⟩ := p3.exists_primeCompl_mul_eq_of_integer x hx
  refine ⟨reducePiOL n / reducePiOL d, n, d, hnd, ?_⟩
  exact div_mul_cancel₀ _ (reducePiOL_den_ne_zero d)

private theorem reducesPi_unique {x : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi x s) : r = s := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  have hcrossL :
      algebraMap GoodOL L (n * d') = algebraMap GoodOL L (n' * d) := by
    simp only [map_mul]
    calc
      algebraMap GoodOL L n * algebraMap GoodOL L (d' : GoodOL) =
          (x * algebraMap GoodOL L (d : GoodOL)) *
            algebraMap GoodOL L (d' : GoodOL) := by rw [hxd]
      _ = (x * algebraMap GoodOL L (d' : GoodOL)) *
            algebraMap GoodOL L (d : GoodOL) := by ring
      _ = algebraMap GoodOL L n' * algebraMap GoodOL L (d : GoodOL) := by
        rw [hxd']
  have hcross : n * (d' : GoodOL) = n' * (d : GoodOL) :=
    (FaithfulSMul.algebraMap_injective GoodOL L) hcrossL
  apply mul_right_cancel₀
    (mul_ne_zero (reducePiOL_den_ne_zero d) (reducePiOL_den_ne_zero d'))
  calc
    r * (reducePiOL d * reducePiOL d') =
        (r * reducePiOL d) * reducePiOL d' := by ring
    _ = reducePiOL n * reducePiOL d' := by rw [hrd]
    _ = reducePiOL (n * (d' : GoodOL)) := by rw [map_mul]
    _ = reducePiOL (n' * (d : GoodOL)) := by rw [hcross]
    _ = reducePiOL n' * reducePiOL d := by rw [map_mul]
    _ = (s * reducePiOL d') * reducePiOL d := by rw [hsd']
    _ = s * (reducePiOL d * reducePiOL d') := by ring

private theorem integralAtPi_zero : IntegralAtPi (0 : L) := by
  simp [IntegralAtPi]

private theorem IntegralAtPi.add {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x + y) := by
  exact (p3.valuation L).map_add x y |>.trans (max_le hx hy)

private theorem IntegralAtPi.neg {x : L} (hx : IntegralAtPi x) :
    IntegralAtPi (-x) := by
  simpa [IntegralAtPi] using hx

private theorem IntegralAtPi.sub {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

private theorem IntegralAtPi.mul {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) : IntegralAtPi (x * y) := by
  unfold IntegralAtPi at hx hy ⊢
  rw [map_mul]
  exact (mul_le_mul' hx hy).trans_eq (mul_one 1)

private theorem IntegralAtPi.pow {x : L} (hx : IntegralAtPi x) (n : ℕ) :
    IntegralAtPi (x ^ n) := by
  induction n with
  | zero => simp [IntegralAtPi]
  | succ n ih => simpa [pow_succ] using ih.mul hx

private theorem ReducesPi.zero : ReducesPi (0 : L) 0 := by
  refine ⟨0, 1, ?_, ?_⟩
  · simp
  · rw [map_zero]
    simp

private theorem ReducesPi.add {x y : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi y s) :
    ReducesPi (x + y) (r + s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * (d' : GoodOL) + n' * (d : GoodOL), d * d', ?_, ?_⟩
  · simp only [map_add, map_mul, Submonoid.coe_mul]
    calc
      (x + y) * (algebraMap GoodOL L d * algebraMap GoodOL L d') =
          (x * algebraMap GoodOL L d) * algebraMap GoodOL L d' +
            (y * algebraMap GoodOL L d') * algebraMap GoodOL L d := by ring
      _ = algebraMap GoodOL L n * algebraMap GoodOL L d' +
            algebraMap GoodOL L n' * algebraMap GoodOL L d := by rw [hxd, hxd']
  · simp only [map_add, map_mul, Submonoid.coe_mul]
    calc
      (r + s) * (reducePiOL d * reducePiOL d') =
          (r * reducePiOL d) * reducePiOL d' +
            (s * reducePiOL d') * reducePiOL d := by ring
      _ = reducePiOL n * reducePiOL d' +
            reducePiOL n' * reducePiOL d := by rw [hrd, hsd']

private theorem ReducesPi.neg {x : L} {r : ZMod 3}
    (hr : ReducesPi x r) : ReducesPi (-x) (-r) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  refine ⟨-n, d, ?_, ?_⟩
  · simp only [map_neg]
    linear_combination -hxd
  · simp only [map_neg]
    linear_combination -hrd

private theorem ReducesPi.sub {x y : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi y s) :
    ReducesPi (x - y) (r - s) := by
  simpa [sub_eq_add_neg] using hr.add hs.neg

private theorem ReducesPi.mul {x y : L} {r s : ZMod 3}
    (hr : ReducesPi x r) (hs : ReducesPi y s) :
    ReducesPi (x * y) (r * s) := by
  obtain ⟨n, d, hxd, hrd⟩ := hr
  obtain ⟨n', d', hxd', hsd'⟩ := hs
  refine ⟨n * n', d * d', ?_, ?_⟩
  · simp only [map_mul, Submonoid.coe_mul]
    rw [← hxd, ← hxd']
    ring
  · simp only [map_mul, Submonoid.coe_mul]
    rw [← hrd, ← hsd']
    ring

private theorem ReducesPi.pow {x : L} {r : ZMod 3}
    (hr : ReducesPi x r) (n : ℕ) : ReducesPi (x ^ n) (r ^ n) := by
  induction n with
  | zero =>
      refine ⟨1, 1, ?_, ?_⟩ <;> simp [reducePiOL]
  | succ n ih => simpa [pow_succ] using ih.mul hr

private theorem reducesPi_existsUnique {x : L} (hx : IntegralAtPi x) :
    ∃! r : ZMod 3, ReducesPi x r := by
  obtain ⟨r, hr⟩ := reducesPi_exists hx
  exact ⟨r, hr, fun s hs ↦ (reducesPi_unique hr hs).symm⟩

private noncomputable def reducePi (x : L) (hx : IntegralAtPi x) : ZMod 3 :=
  Classical.choose (reducesPi_existsUnique hx)

private theorem reducePi_spec (x : L) (hx : IntegralAtPi x) :
    ReducesPi x (reducePi x hx) :=
  (Classical.choose_spec (reducesPi_existsUnique hx)).1

private theorem reducePi_eq_of_reduces {x : L} (hx : IntegralAtPi x)
    {r : ZMod 3} (hr : ReducesPi x r) : reducePi x hx = r :=
  reducesPi_unique (reducePi_spec x hx) hr

@[simp] private theorem reducePi_zero :
    reducePi 0 integralAtPi_zero = 0 :=
  reducePi_eq_of_reduces integralAtPi_zero ReducesPi.zero

private theorem reducePi_add {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reducePi (x + y) (hx.add hy) = reducePi x hx + reducePi y hy :=
  reducePi_eq_of_reduces (hx.add hy) ((reducePi_spec x hx).add (reducePi_spec y hy))

private theorem reducePi_neg {x : L} (hx : IntegralAtPi x) :
    reducePi (-x) hx.neg = -reducePi x hx :=
  reducePi_eq_of_reduces hx.neg (reducePi_spec x hx).neg

private theorem reducePi_sub {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reducePi (x - y) (hx.sub hy) = reducePi x hx - reducePi y hy :=
  reducePi_eq_of_reduces (hx.sub hy)
    ((reducePi_spec x hx).sub (reducePi_spec y hy))

private theorem reducePi_mul {x y : L}
    (hx : IntegralAtPi x) (hy : IntegralAtPi y) :
    reducePi (x * y) (hx.mul hy) = reducePi x hx * reducePi y hy :=
  reducePi_eq_of_reduces (hx.mul hy)
    ((reducePi_spec x hx).mul (reducePi_spec y hy))

private theorem reducePi_pow {x : L} (hx : IntegralAtPi x) (n : ℕ) :
    reducePi (x ^ n) (hx.pow n) = reducePi x hx ^ n :=
  reducePi_eq_of_reduces (hx.pow n) ((reducePi_spec x hx).pow n)

private theorem reducePi_of_integer (n : GoodOL) :
    reducePi (algebraMap GoodOL L n) (by
      simpa [IntegralAtPi] using p3.valuation_le_one (K := L) n) = reducePiOL n := by
  apply reducePi_eq_of_reduces
  refine ⟨n, 1, ?_, ?_⟩ <;> simp

private theorem valuation_eq_exp_neg_ordPi {x : L} (hx : x ≠ 0) :
    p3.valuation L x = WithZero.exp (-ordPi x) := by
  have hv : p3.valuation L x ≠ 0 :=
    (Valuation.ne_zero_iff (p3.valuation L)).2 hx
  calc
    p3.valuation L x = WithZero.exp (WithZero.log (p3.valuation L x)) :=
      (WithZero.exp_log hv).symm
    _ = WithZero.exp (-ordPi x) := by
      congr 1
      simp [ordPi, v3]

private theorem integralAtPi_of_ordPi_nonneg {x : L} (hx : x ≠ 0)
    (hord : 0 ≤ ordPi x) : IntegralAtPi x := by
  unfold IntegralAtPi
  rw [valuation_eq_exp_neg_ordPi hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

private theorem reducePi_eq_zero_of_ordPi_pos {x : L} (hx : x ≠ 0)
    (hord : 0 < ordPi x) :
    reducePi x (integralAtPi_of_ordPi_nonneg hx hord.le) = 0 := by
  let hxInt := integralAtPi_of_ordPi_nonneg hx hord.le
  obtain ⟨n, d, hxd, hred⟩ := reducePi_spec x hxInt
  have hdL : algebraMap GoodOL L (d : GoodOL) ≠ 0 :=
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective GoodOL L)).not.mpr
      (fun hd ↦ d.property (hd ▸ Submodule.zero_mem _))
  have hdord : ordPi (algebraMap GoodOL L (d : GoodOL)) = 0 := by
    have hv : p3.valuation L (algebraMap GoodOL L (d : GoodOL)) = 1 :=
      (p3.valuation_eq_one_iff_notMem (K := L)).2 d.property
    simp [ordPi, v3, hv]
  have hnL : algebraMap GoodOL L n ≠ 0 := by
    rw [← hxd]
    exact mul_ne_zero hx hdL
  have hnord : ordPi (algebraMap GoodOL L n) = ordPi x := by
    rw [← hxd, ordPi_mul hx hdL, hdord, add_zero]
  have hnmem : n ∈ p3.asIdeal := by
    by_contra hnmem
    have hv : p3.valuation L (algebraMap GoodOL L n) = 1 :=
      (p3.valuation_eq_one_iff_notMem (K := L)).2 hnmem
    have hz : ordPi (algebraMap GoodOL L n) = 0 := by
      simp [ordPi, v3, hv]
    rw [hnord] at hz
    omega
  have hnbar : reducePiOL n = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (by
      simpa [p3, primeAboveThree_eq_span_pi] using hnmem)
    rw [hc, map_mul, reducePiOL_piInteger, zero_mul]
  rw [hnbar] at hred
  exact (mul_eq_zero.mp hred).resolve_right (reducePiOL_den_ne_zero d)

private theorem reducePi_ne_zero_of_ordPi_eq_zero {x : L} (hx : x ≠ 0)
    (hord : ordPi x = 0) :
    reducePi x (integralAtPi_of_ordPi_nonneg hx hord.ge) ≠ 0 := by
  let hxInt := integralAtPi_of_ordPi_nonneg hx hord.ge
  have hvx : p3.valuation L x = 1 := by
    rw [valuation_eq_exp_neg_ordPi hx, hord]
    simp
  have hxInvInt : IntegralAtPi x⁻¹ := by
    unfold IntegralAtPi
    rw [map_inv₀, hvx, inv_one]
  let r := reducePi x hxInt
  let s := reducePi x⁻¹ hxInvInt
  have hrs : ReducesPi (1 : L) (r * s) := by
    obtain ⟨n, d, hxd, hrd⟩ := reducePi_spec x hxInt
    obtain ⟨n', d', hxd', hrd'⟩ := reducePi_spec x⁻¹ hxInvInt
    refine ⟨n * n', d * d', ?_, ?_⟩
    · simp only [map_mul, Submonoid.coe_mul]
      rw [← hxd, ← hxd']
      field_simp [hx]
    · simp only [map_mul, Submonoid.coe_mul]
      rw [← hrd, ← hrd']
      ring
  have hone : ReducesPi (1 : L) 1 := by
    refine ⟨1, 1, ?_, ?_⟩ <;> simp [reducePiOL]
  have hrsOne : r * s = 1 := reducesPi_unique hrs hone
  intro hr0
  change r = 0 at hr0
  rw [hr0, zero_mul] at hrsOne
  exact zero_ne_one hrsOne

private theorem integralAtPi_of_ordPi_nonneg_total {x : L}
    (hx : 0 ≤ ordPi x) : IntegralAtPi x := by
  by_cases hx0 : x = 0
  · subst x
    exact integralAtPi_zero
  · exact integralAtPi_of_ordPi_nonneg hx0 hx

private noncomputable def reduceNonneg (x : L) (hx : 0 ≤ ordPi x) : ZMod 3 :=
  reducePi x (integralAtPi_of_ordPi_nonneg_total hx)

private theorem reduceNonneg_sub {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y)
    (hxy : 0 ≤ ordPi (x - y)) :
    reduceNonneg (x - y) hxy = reduceNonneg x hx - reduceNonneg y hy := by
  unfold reduceNonneg
  simpa only using reducePi_sub
    (integralAtPi_of_ordPi_nonneg_total hx)
    (integralAtPi_of_ordPi_nonneg_total hy)

private theorem reduceNonneg_add {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y)
    (hxy : 0 ≤ ordPi (x + y)) :
    reduceNonneg (x + y) hxy = reduceNonneg x hx + reduceNonneg y hy := by
  unfold reduceNonneg
  simpa only using reducePi_add
    (integralAtPi_of_ordPi_nonneg_total hx)
    (integralAtPi_of_ordPi_nonneg_total hy)

private theorem reduceNonneg_neg {x : L}
    (hx : 0 ≤ ordPi x) (hnx : 0 ≤ ordPi (-x)) :
    reduceNonneg (-x) hnx = -reduceNonneg x hx := by
  unfold reduceNonneg
  simpa only using reducePi_neg (integralAtPi_of_ordPi_nonneg_total hx)

private theorem reduceNonneg_mul {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y)
    (hxy : 0 ≤ ordPi (x * y)) :
    reduceNonneg (x * y) hxy = reduceNonneg x hx * reduceNonneg y hy := by
  unfold reduceNonneg
  simpa only using reducePi_mul
    (integralAtPi_of_ordPi_nonneg_total hx)
    (integralAtPi_of_ordPi_nonneg_total hy)

private theorem reduceNonneg_pow {x : L}
    (hx : 0 ≤ ordPi x) (n : ℕ) (hxn : 0 ≤ ordPi (x ^ n)) :
    reduceNonneg (x ^ n) hxn = reduceNonneg x hx ^ n := by
  unfold reduceNonneg
  simpa only using reducePi_pow (integralAtPi_of_ordPi_nonneg_total hx) n

private theorem reduceNonneg_eq_zero_of_pos {x : L} (hx : x ≠ 0)
    (hord : 0 < ordPi x) :
    reduceNonneg x hord.le = 0 := by
  unfold reduceNonneg
  simpa only using reducePi_eq_zero_of_ordPi_pos hx hord

private theorem reduceNonneg_ne_zero_of_ord_eq_zero {x : L} (hx : x ≠ 0)
    (hord : ordPi x = 0) :
    reduceNonneg x hord.ge ≠ 0 := by
  unfold reduceNonneg
  simpa only using reducePi_ne_zero_of_ordPi_eq_zero hx hord

private theorem reduceNonneg_eq_of_eq {x y : L}
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) (hxy : x = y) :
    reduceNonneg x hx = reduceNonneg y hy := by
  subst y
  rfl

private theorem reduceNonneg_good_a₁ :
    reduceNonneg E0Good.a₁ good_coeff_orders.1 = 2 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₁)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₁] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₁
  calc
    reduceNonneg E0Good.a₁ good_coeff_orders.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₁) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₁ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 2 := by
      simp [MazurProof.N18PackageII.E0GoodInt]
      decide

private theorem reduceNonneg_good_a₂ :
    reduceNonneg E0Good.a₂ good_coeff_orders.2.1 = 2 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₂)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₂] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₂
  calc
    reduceNonneg E0Good.a₂ good_coeff_orders.2.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₂) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₂ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 2 := by norm_num [MazurProof.N18PackageII.E0GoodInt]

private theorem reduceNonneg_good_a₃ :
    reduceNonneg E0Good.a₃ good_coeff_orders.2.2.1 = 2 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₃)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₃] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₃
  calc
    reduceNonneg E0Good.a₃ good_coeff_orders.2.2.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₃) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₃ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 2 := by norm_num [MazurProof.N18PackageII.E0GoodInt]

private theorem reduceNonneg_good_a₄ :
    reduceNonneg E0Good.a₄ good_coeff_orders.2.2.2.1 = 0 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₄)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₄] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₄
  calc
    reduceNonneg E0Good.a₄ good_coeff_orders.2.2.2.1 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₄) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₄ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 0 := by
      simp [MazurProof.N18PackageII.E0GoodInt]

private theorem reduceNonneg_good_a₆ :
    reduceNonneg E0Good.a₆ good_coeff_orders.2.2.2.2 = 0 := by
  have hm := congrArg (fun W : WeierstrassCurve L ↦ W.a₆)
    MazurProof.N18PackageII.E0GoodInt_map
  simp only [WeierstrassCurve.map_a₆] at hm
  let hi := GoodModel.zero_le_ordPi_ringOfIntegers
    MazurProof.N18PackageII.E0GoodInt.a₆
  calc
    reduceNonneg E0Good.a₆ good_coeff_orders.2.2.2.2 =
        reduceNonneg (algebraMap GoodOL L MazurProof.N18PackageII.E0GoodInt.a₆) hi :=
      reduceNonneg_eq_of_eq _ _ hm.symm
    _ = reducePiOL MazurProof.N18PackageII.E0GoodInt.a₆ := by
      unfold reduceNonneg
      exact reducePi_of_integer _
    _ = 0 := by
      simp [MazurProof.N18PackageII.E0GoodInt]
      decide

private theorem reducesPi_nonneg {x : L} (hx : 0 ≤ ordPi x) :
    ReducesPi x (reduceNonneg x hx) := by
  unfold reduceNonneg
  exact reducePi_spec _ _

private theorem residue_equation_good {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    WeierstrassCurve.Affine.Equation reducedGoodCurve
      (reduceNonneg x hx) (reduceNonneg y hy) := by
  let rx := reduceNonneg x hx
  let ry := reduceNonneg y hy
  have hxRed : ReducesPi x rx := reducesPi_nonneg hx
  have hyRed : ReducesPi y ry := reducesPi_nonneg hy
  have ha₁Red : ReducesPi E0Good.a₁ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.1
    rwa [reduceNonneg_good_a₁] at hred
  have ha₂Red : ReducesPi E0Good.a₂ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.1
    rwa [reduceNonneg_good_a₂] at hred
  have ha₃Red : ReducesPi E0Good.a₃ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.1
    rwa [reduceNonneg_good_a₃] at hred
  have ha₄Red : ReducesPi E0Good.a₄ 0 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.2.1
    rwa [reduceNonneg_good_a₄] at hred
  have ha₆Red : ReducesPi E0Good.a₆ 0 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.2.2
    rwa [reduceNonneg_good_a₆] at hred
  have hlhs : ReducesPi
      (y ^ 2 + E0Good.a₁ * x * y + E0Good.a₃ * y)
      (ry ^ 2 + 2 * rx * ry + 2 * ry) := by
    exact ((hyRed.pow 2).add ((ha₁Red.mul hxRed).mul hyRed)).add
      (ha₃Red.mul hyRed)
  have hrhs : ReducesPi
      (x ^ 3 + E0Good.a₂ * x ^ 2 + E0Good.a₄ * x + E0Good.a₆)
      (rx ^ 3 + 2 * rx ^ 2 + 0 * rx + 0) := by
    exact ((hxRed.pow 3).add (ha₂Red.mul (hxRed.pow 2))).add
      (ha₄Red.mul hxRed) |>.add ha₆Red
  have heq := (WeierstrassCurve.Affine.equation_iff x y).mp h.1
  rw [heq] at hlhs
  have hred := reducesPi_unique hlhs hrhs
  simpa [rx, ry, reducedGoodCurve,
    WeierstrassCurve.Affine.equation_iff] using hred

private theorem redPoint_ne_neg_of_ne_zero
    (R : MazurProof.N18RouteC.Reduction.RedPoint) (hR : R ≠ 0) :
    R ≠ -R := by
  intro hself
  have htwo : (2 : ℕ) • R = 0 := by
    rw [two_nsmul]
    calc
      R + R = R + -R := congrArg (R + ·) hself
      _ = 0 := add_neg_cancel R
  have hordTwo : addOrderOf R ∣ 2 :=
    addOrderOf_dvd_of_nsmul_eq_zero htwo
  have hordSeven : addOrderOf R ∣ 7 :=
    addOrderOf_dvd_of_nsmul_eq_zero
      (MazurProof.N18RouteC.Reduction.seven_nsmul R)
  have hordOne : addOrderOf R = 1 := by
    apply Nat.dvd_one.mp
    simpa using Nat.dvd_gcd hordTwo hordSeven
  rw [AddMonoid.addOrderOf_eq_one_iff] at hordOne
  exact hR hordOne

private theorem reduced_pair_not_self_neg {x y : ZMod 3}
    (h : WeierstrassCurve.Affine.Equation reducedGoodCurve x y) :
    y ≠ WeierstrassCurve.Affine.negY reducedGoodCurve x y := by
  let R : MazurProof.N18RouteC.Reduction.RedPoint :=
    WeierstrassCurve.Affine.Point.mk h
  have hR0 : R ≠ 0 := by
    exact WeierstrassCurve.Affine.Point.some_ne_zero _
  have hRneg := redPoint_ne_neg_of_ne_zero R hR0
  intro hy
  apply hRneg
  change WeierstrassCurve.Affine.Point.some x y _ =
    WeierstrassCurve.Affine.Point.some x
      (WeierstrassCurve.Affine.negY reducedGoodCurve x y) _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, hy⟩

private theorem reduce_negY_good {x y : L}
    (h : WeierstrassCurve.Affine.Nonsingular E0Good x y)
    (hx : 0 ≤ ordPi x) (hy : 0 ≤ ordPi y) :
    ∃ hny : 0 ≤ ordPi (WeierstrassCurve.Affine.negY E0Good x y),
      reduceNonneg (WeierstrassCurve.Affine.negY E0Good x y) hny =
        WeierstrassCurve.Affine.negY reducedGoodCurve
          (reduceNonneg x hx) (reduceNonneg y hy) := by
  let ny := WeierstrassCurve.Affine.negY E0Good x y
  have hnonsing : WeierstrassCurve.Affine.Nonsingular E0Good x ny :=
    (WeierstrassCurve.Affine.nonsingular_neg x y).mpr h
  have hny : 0 ≤ ordPi ny := y_nonneg_of_x_nonneg_good hnonsing hx
  refine ⟨hny, ?_⟩
  have hxRed := reducesPi_nonneg hx
  have hyRed := reducesPi_nonneg hy
  have ha₁Red : ReducesPi E0Good.a₁ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.1
    rwa [reduceNonneg_good_a₁] at hred
  have ha₃Red : ReducesPi E0Good.a₃ 2 := by
    have hred := reducesPi_nonneg good_coeff_orders.2.2.1
    rwa [reduceNonneg_good_a₃] at hred
  have hformula : ReducesPi ny
      (-reduceNonneg y hy - 2 * reduceNonneg x hx - 2) := by
    simpa only [ny, WeierstrassCurve.Affine.negY] using
      (hyRed.neg.sub (ha₁Red.mul hxRed)).sub ha₃Red
  have hunique := reducesPi_unique (reducesPi_nonneg hny) hformula
  simpa only [ny, WeierstrassCurve.Affine.negY, reducedGoodCurve] using hunique

private noncomputable def residueCode :
    GoodPoint → Option (ZMod 3 × ZMod 3)
  | .zero => none
  | .some x y h =>
      if hx : ordPi x < 0 then none
      else
        let hx' := le_of_not_gt hx
        let hy' := y_nonneg_of_x_nonneg_good h hx'
        some (reduceNonneg x hx', reduceNonneg y hy')

private theorem formal_neg_good (P : GoodPoint)
    (hP : InFormalKernel P) : InFormalKernel (-P) := by
  rcases hP with rfl | hP
  · exact Or.inl rfl
  · exact Or.inr (by rwa [xCoordGood_neg])

private theorem residueCode_eq_none_iff (P : GoodPoint) :
    residueCode P = none ↔ InFormalKernel P := by
  cases P with
  | zero => exact iff_of_true rfl (Or.inl rfl)
  | some x y h =>
      simp [residueCode, InFormalKernel, xCoordGood]

private theorem formal_sub_of_residueCode_eq (P Q : GoodPoint)
    (hcode : residueCode P = residueCode Q) :
    InFormalKernel (P - Q) := by
  cases P with
  | zero =>
      have hQ : InFormalKernel Q := by
        apply (residueCode_eq_none_iff Q).mp
        simpa [residueCode] using hcode.symm
      rw [show WeierstrassCurve.Affine.Point.zero - Q = -Q by rfl]
      exact formal_neg_good Q hQ
  | some x₁ y₁ h₁ =>
      by_cases hx₁neg : ordPi x₁ < 0
      · have hP : InFormalKernel
            (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) := Or.inr hx₁neg
        have hQ : InFormalKernel Q := by
          apply (residueCode_eq_none_iff Q).mp
          rw [← hcode]
          simp [residueCode, hx₁neg]
        simpa only [sub_eq_add_neg] using
          kernel_add_closed_good _ _ hP (formal_neg_good Q hQ)
      · have hx₁ : 0 ≤ ordPi x₁ := le_of_not_gt hx₁neg
        have hy₁ : 0 ≤ ordPi y₁ := y_nonneg_of_x_nonneg_good h₁ hx₁
        cases Q with
        | zero =>
            have : False := by
              have hc : residueCode
                  (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) ≠ none := by
                simp [residueCode, hx₁neg]
              exact hc (by simpa [residueCode] using hcode)
            exact this.elim
        | some x₂ y₂ h₂ =>
            by_cases hx₂neg : ordPi x₂ < 0
            · have : False := by
                have hc : residueCode
                    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) ≠ none := by
                  simp [residueCode, hx₁neg]
                apply hc
                rw [hcode]
                simp [residueCode, hx₂neg]
              exact this.elim
            · have hx₂ : 0 ≤ ordPi x₂ := le_of_not_gt hx₂neg
              have hy₂ : 0 ≤ ordPi y₂ := y_nonneg_of_x_nonneg_good h₂ hx₂
              have hcode' :
                  some (reduceNonneg x₁ hx₁, reduceNonneg y₁ hy₁) =
                    some (reduceNonneg x₂ hx₂, reduceNonneg y₂ hy₂) := by
                simpa only [residueCode, dif_neg hx₁neg, dif_neg hx₂neg] using hcode
              have hpair := Option.some.inj hcode'
              have hxred : reduceNonneg x₁ hx₁ = reduceNonneg x₂ hx₂ :=
                congrArg Prod.fst hpair
              have hyred : reduceNonneg y₁ hy₁ = reduceNonneg y₂ hy₂ :=
                congrArg Prod.snd hpair
              by_cases hxEq : x₁ = x₂
              · by_cases hyEq : y₁ = y₂
                · subst x₂
                  subst y₂
                  cases Subsingleton.elim h₂ h₁
                  exact Or.inl (sub_self _)
                · have hyNeg : y₁ = WeierstrassCurve.Affine.negY E0Good x₂ y₂ :=
                    (WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hxEq).resolve_left hyEq
                  obtain ⟨hny₂, hnyred⟩ := reduce_negY_good h₂ hx₂ hy₂
                  have hredEq : reduceNonneg y₁ hy₁ =
                      WeierstrassCurve.Affine.negY reducedGoodCurve
                        (reduceNonneg x₁ hx₁) (reduceNonneg y₁ hy₁) := by
                    calc
                      reduceNonneg y₁ hy₁ = reduceNonneg
                          (WeierstrassCurve.Affine.negY E0Good x₂ y₂) hny₂ :=
                        reduceNonneg_eq_of_eq _ _ hyNeg
                      _ = WeierstrassCurve.Affine.negY reducedGoodCurve
                          (reduceNonneg x₂ hx₂) (reduceNonneg y₂ hy₂) := hnyred
                      _ = WeierstrassCurve.Affine.negY reducedGoodCurve
                          (reduceNonneg x₁ hx₁) (reduceNonneg y₁ hy₁) := by
                        rw [hxred, hyred]
                  exact (reduced_pair_not_self_neg
                    (residue_equation_good h₁ hx₁ hy₁) hredEq).elim
              · let ny₂ := WeierstrassCurve.Affine.negY E0Good x₂ y₂
                obtain ⟨hny₂, hnyred⟩ := reduce_negY_good h₂ hx₂ hy₂
                let num := y₁ - ny₂
                let den := x₁ - x₂
                have hden0 : den ≠ 0 := sub_ne_zero.mpr hxEq
                have hden : 0 ≤ ordPi den := by
                  dsimp only [den]
                  have hnx₂ : 0 ≤ ordPi (-x₂) := by rwa [ordPi_neg]
                  simpa only [sub_eq_add_neg] using le_ordPi_add hx₁ hnx₂ le_rfl
                have hdenRed : reduceNonneg den hden = 0 := by
                  rw [reduceNonneg_sub hx₁ hx₂ hden, hxred, sub_self]
                have hdenPos : 0 < ordPi den := by
                  by_contra hpos
                  have hzero : ordPi den = 0 := by omega
                  exact (reduceNonneg_ne_zero_of_ord_eq_zero hden0 hzero)
                    (by simpa only [hzero] using hdenRed)
                have hnum : 0 ≤ ordPi num := by
                  dsimp only [num]
                  have hnny₂ : 0 ≤ ordPi (-ny₂) := by rwa [ordPi_neg]
                  simpa only [sub_eq_add_neg] using le_ordPi_add hy₁ hnny₂ le_rfl
                have hnumRed : reduceNonneg num hnum =
                    reduceNonneg y₁ hy₁ -
                      WeierstrassCurve.Affine.negY reducedGoodCurve
                        (reduceNonneg x₂ hx₂) (reduceNonneg y₂ hy₂) := by
                  rw [reduceNonneg_sub hy₁ hny₂ hnum, hnyred]
                have hnumRed0 : reduceNonneg num hnum ≠ 0 := by
                  rw [hnumRed]
                  intro hz
                  have hself : reduceNonneg y₁ hy₁ =
                      WeierstrassCurve.Affine.negY reducedGoodCurve
                        (reduceNonneg x₁ hx₁) (reduceNonneg y₁ hy₁) := by
                    have := sub_eq_zero.mp hz
                    simpa only [hxred, hyred] using this
                  exact reduced_pair_not_self_neg
                    (residue_equation_good h₁ hx₁ hy₁) hself
                have hnum0 : num ≠ 0 := by
                  intro hz
                  have hzeroOrd : 0 ≤ ordPi (0 : L) := by simp [ordPi_zero]
                  have hredEq := reduceNonneg_eq_of_eq hnum hzeroOrd hz
                  apply hnumRed0
                  rw [hredEq]
                  unfold reduceNonneg
                  simpa only using reducePi_zero
                have hnumOrd : ordPi num = 0 := by
                  by_contra hne
                  have hpos : 0 < ordPi num := by omega
                  exact hnumRed0 (by
                    simpa only using reduceNonneg_eq_zero_of_pos hnum0 hpos)
                let ell := WeierstrassCurve.Affine.slope E0Good x₁ x₂ y₁ ny₂
                have hell : ell = num / den := by
                  dsimp only [ell, num, den]
                  rw [WeierstrassCurve.Affine.slope_of_X_ne hxEq]
                have hell0 : ell ≠ 0 := by
                  rw [hell]
                  exact div_ne_zero hnum0 hden0
                have hellOrd : ordPi ell = -ordPi den := by
                  rw [hell, ordPi_div hnum0 hden0, hnumOrd]
                  omega
                have hellNeg : ordPi ell < 0 := by rw [hellOrd]; omega
                let tail := E0Good.a₁ * ell - E0Good.a₂ - x₁ - x₂
                have htail : ordPi ell ≤ ordPi tail := by
                  have h1 : ordPi ell ≤ ordPi (E0Good.a₁ * ell) :=
                    ordPi_le_mul_right_good good_coeff_orders.1 hellNeg.le
                  have h2 : ordPi ell ≤ ordPi (-E0Good.a₂) := by
                    have ha₂ := good_coeff_orders.2.1
                    rw [ordPi_neg]
                    omega
                  have h3 : ordPi ell ≤ ordPi (-x₁) := by
                    rw [ordPi_neg]
                    omega
                  have h4 : ordPi ell ≤ ordPi (-x₂) := by
                    rw [ordPi_neg]
                    omega
                  dsimp only [tail]
                  simpa only [sub_eq_add_neg] using
                    le_ordPi_add (le_ordPi_add (le_ordPi_add h1 h2 hellNeg.le)
                      h3 hellNeg.le) h4 hellNeg.le
                let x₃ := WeierstrassCurve.Affine.addX E0Good x₁ x₂ ell
                have hx₃Eq : x₃ = ell ^ 2 + tail := by
                  simp only [x₃, tail, WeierstrassCurve.Affine.addX]
                  ring
                have hellSq0 : ell ^ 2 ≠ 0 := pow_ne_zero 2 hell0
                have hellSqOrd : ordPi (ell ^ 2) = 2 * ordPi ell := by
                  rw [pow_two, ordPi_mul hell0 hell0]
                  ring
                have hx₃Ord : ordPi x₃ = 2 * ordPi ell := by
                  rw [hx₃Eq]
                  by_cases ht0 : tail = 0
                  · simp [ht0, hellSqOrd]
                  · exact (ordPi_add_eq_of_lt hellSq0 ht0 (by
                      rw [hellSqOrd]
                      omega)).trans hellSqOrd
                have hx₃Neg : ordPi x₃ < 0 := by rw [hx₃Ord]; omega
                rw [sub_eq_add_neg,
                  WeierstrassCurve.Affine.Point.neg_some,
                  WeierstrassCurve.Affine.Point.add_of_X_ne hxEq]
                exact Or.inr hx₃Neg

private def goodKernelSubgroup : AddSubgroup GoodPoint where
  carrier := {P | InFormalKernel P}
  zero_mem' := zero_mem_formalKernel
  add_mem' := by
    intro P Q hP hQ
    exact kernel_add_closed_good P Q hP hQ
  neg_mem' := by
    intro P hP
    exact formal_neg_good P hP

private instance : goodKernelSubgroup.Normal where
  conj_mem := by
    intro P hP Q
    simpa [add_assoc, add_comm, add_left_comm] using hP

private abbrev GoodReductionQuotient :=
  GoodPoint ⧸ goodKernelSubgroup

private noncomputable def quotientResidueCode :
    GoodReductionQuotient → Option (ZMod 3 × ZMod 3) :=
  fun q ↦ residueCode (Quotient.out q)

private theorem quotientResidueCode_injective :
    Function.Injective quotientResidueCode := by
  intro q₁ q₂ hcode
  rw [← Quotient.out_eq' q₁, ← Quotient.out_eq' q₂]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change InFormalKernel (Quotient.out q₁ - Quotient.out q₂)
  exact formal_sub_of_residueCode_eq _ _ hcode

private noncomputable instance : Finite GoodReductionQuotient :=
  Finite.of_injective quotientResidueCode quotientResidueCode_injective

private theorem goodReductionQuotient_card_le_ten :
    Nat.card GoodReductionQuotient ≤ 10 := by
  calc
    Nat.card GoodReductionQuotient ≤
        Nat.card (Option (ZMod 3 × ZMod 3)) :=
      Nat.card_le_card_of_injective quotientResidueCode
        quotientResidueCode_injective
    _ = 10 := by
      rw [Nat.card_eq_fintype_card]
      decide

private theorem three_generator_good_xCoord :
    xCoordGood (MazurProof.N18RouteC.GoodModel.e0GoodEquiv
      ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21)) = 0 := by
  have hthree : (3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21 =
      MazurProof.N18RouteC.TorsionTable.torsionPoint (3 : Fin 21) := by
    simpa using MazurProof.N18RouteC.TorsionTable.nsmul_generator (3 : Fin 21)
  rw [hthree]
  change xCoordGood (MazurProof.N18RouteC.GoodModel.e0GoodEquiv
    (MazurProof.N18RouteC.TorsionTable.torsionAffine (2 : Fin 20))) = 0
  have h₀ : WeierstrassCurve.Affine.Nonsingular E0
      (MazurProof.N18RouteC.TorsionTable.torsionX (2 : Fin 20))
      (MazurProof.N18RouteC.TorsionTable.torsionY (2 : Fin 20)) := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    exact sub_eq_zero.mp
      (MazurProof.N18RouteC.TorsionTable.torsion_on_curve (2 : Fin 20))
  have hG : WeierstrassCurve.Affine.Nonsingular E0Good
      (MazurProof.N18RouteC.VariableChangePoints.variableChangePointX
        MazurProof.N18RouteC.GoodModel.toGoodChange
        (MazurProof.N18RouteC.TorsionTable.torsionX (2 : Fin 20)))
      (MazurProof.N18RouteC.VariableChangePoints.variableChangePointY
        MazurProof.N18RouteC.GoodModel.toGoodChange
        (MazurProof.N18RouteC.TorsionTable.torsionX (2 : Fin 20))
        (MazurProof.N18RouteC.TorsionTable.torsionY (2 : Fin 20))) := by
    apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    rw [← MazurProof.N18RouteC.GoodModel.toGoodChange_smul_E0]
    exact MazurProof.N18RouteC.VariableChangePoints.variableChangePoint_equation
      E0 MazurProof.N18RouteC.GoodModel.toGoodChange h₀.1
  unfold MazurProof.N18RouteC.TorsionTable.torsionAffine
  rw [MazurProof.N18RouteC.GoodModel.e0GoodEquiv_some (hG := hG)]
  simp [xCoordGood,
    MazurProof.N18RouteC.VariableChangePoints.variableChangePointX,
    MazurProof.N18RouteC.GoodModel.toGoodChange,
    MazurProof.N18RouteC.GoodModel.changeR,
    MazurProof.N18RouteC.TorsionTable.torsionX]
  ring

private theorem three_generator_good_not_formal :
    ¬ InFormalKernel (MazurProof.N18RouteC.GoodModel.e0GoodEquiv
      ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21)) := by
  intro hformal
  rcases hformal with hzero | hneg
  · have hold0 :
        ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21) ≠ 0 := by
      have hthree : (3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21 =
          MazurProof.N18RouteC.TorsionTable.torsionPoint (3 : Fin 21) := by
        simpa using MazurProof.N18RouteC.TorsionTable.nsmul_generator (3 : Fin 21)
      rw [hthree]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    apply hold0
    apply MazurProof.N18RouteC.GoodModel.e0GoodEquiv.injective
    simpa using hzero
  · rw [three_generator_good_xCoord, ordPi_zero] at hneg
    omega

private theorem seven_nsmul_three_generator_good :
    (7 : ℕ) • (MazurProof.N18RouteC.GoodModel.e0GoodEquiv
      ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21)) = 0 := by
  calc
    (7 : ℕ) • (MazurProof.N18RouteC.GoodModel.e0GoodEquiv
        ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21)) =
      MazurProof.N18RouteC.GoodModel.e0GoodEquiv
        ((7 : ℕ) • ((3 : ℕ) •
          MazurProof.N18RouteC.TorsionTable.generator21)) := by
            exact (map_nsmul MazurProof.N18RouteC.GoodModel.e0GoodEquiv 7
              ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21)).symm
    _ = MazurProof.N18RouteC.GoodModel.e0GoodEquiv
        ((21 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21) := by
          congr 1
          calc
            (7 : ℕ) • ((3 : ℕ) •
                MazurProof.N18RouteC.TorsionTable.generator21) =
              (3 * 7 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21 :=
                (mul_nsmul MazurProof.N18RouteC.TorsionTable.generator21 3 7).symm
            _ = (21 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21 := by
              norm_num
    _ = 0 := by
      rw [MazurProof.N18RouteC.TorsionTable.twenty_one_nsmul_generator,
        map_zero]

private noncomputable def quotientSevenPoint : GoodReductionQuotient :=
  QuotientAddGroup.mk' goodKernelSubgroup
    (MazurProof.N18RouteC.GoodModel.e0GoodEquiv
      ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21))

private theorem quotientSevenPoint_ne_zero : quotientSevenPoint ≠ 0 := by
  intro hzero
  apply three_generator_good_not_formal
  change MazurProof.N18RouteC.GoodModel.e0GoodEquiv
      ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21) ∈
    goodKernelSubgroup
  rw [← QuotientAddGroup.ker_mk' goodKernelSubgroup]
  exact hzero

private theorem seven_nsmul_quotientSevenPoint :
    (7 : ℕ) • quotientSevenPoint = 0 := by
  change (7 : ℕ) • QuotientAddGroup.mk' goodKernelSubgroup
      (MazurProof.N18RouteC.GoodModel.e0GoodEquiv
        ((3 : ℕ) • MazurProof.N18RouteC.TorsionTable.generator21)) = 0
  rw [← map_nsmul, seven_nsmul_three_generator_good, map_zero]

private theorem goodReductionQuotient_card :
    Nat.card GoodReductionQuotient = 7 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : addOrderOf quotientSevenPoint = 7 :=
    addOrderOf_eq_prime seven_nsmul_quotientSevenPoint
      quotientSevenPoint_ne_zero
  have hdvd : 7 ∣ Nat.card GoodReductionQuotient := by
    rw [← hord]
    exact addOrderOf_dvd_natCard quotientSevenPoint
  have hpos : 0 < Nat.card GoodReductionQuotient := Finite.card_pos
  have hle := goodReductionQuotient_card_le_ten
  omega

/-- The good-model reduction map, obtained by identifying the quotient by the
formal kernel with the seven-point special fiber. -/
theorem exists_good_reduction :
    ∃ red : GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint,
      ∀ P, P ∈ red.ker ↔ InFormalKernel P := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hredCard :
      Nat.card MazurProof.N18RouteC.Reduction.RedPoint = 7 := by
    rw [Nat.card_eq_fintype_card]
    exact MazurProof.N18RouteC.Reduction.redPoint_card
  let e : GoodReductionQuotient ≃+
      MazurProof.N18RouteC.Reduction.RedPoint :=
    addEquivOfPrimeCardEq goodReductionQuotient_card hredCard
  let red : GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint :=
    e.toAddMonoidHom.comp (QuotientAddGroup.mk' goodKernelSubgroup)
  refine ⟨red, ?_⟩
  intro P
  change e (QuotientAddGroup.mk' goodKernelSubgroup P) = 0 ↔
    InFormalKernel P
  constructor
  · intro hred
    have hquot : QuotientAddGroup.mk' goodKernelSubgroup P = 0 :=
      e.injective (hred.trans e.map_zero.symm)
    change P ∈ goodKernelSubgroup
    rw [← QuotientAddGroup.ker_mk' goodKernelSubgroup]
    exact hquot
  · intro hformal
    have hquot : QuotientAddGroup.mk' goodKernelSubgroup P = 0 := by
      change P ∈ (QuotientAddGroup.mk' goodKernelSubgroup).ker
      rw [QuotientAddGroup.ker_mk' goodKernelSubgroup]
      exact hformal
    rw [hquot, e.map_zero]

end QuotientProof

/-- Exported proof requested by `N18GoodModelAssembly`. -/
theorem exists_good_reduction_proof :
    ∃ red : GoodPoint →+ MazurProof.N18RouteC.Reduction.RedPoint,
      ∀ P : GoodPoint, P ∈ red.ker ↔ InFormalKernel P := by
  exact QuotientProof.exists_good_reduction

end MazurProof.N18GoodReduction
