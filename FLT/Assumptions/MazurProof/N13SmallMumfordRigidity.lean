import FLT.Assumptions.MazurProof.N13FactorRigidity
import FLT.Assumptions.MazurProof.SexticMumfordPrincipalScale
import FLT.Assumptions.MazurProof.N13MumfordRigidity
import FLT.Assumptions.MazurProof.SexticMumfordGroup

/-!
# Rigidity of point-sized Mumford representatives on `X₁(13)`

For representatives with `deg(u) + nInf ≤ 1`, a principal relation clears
to two affine factors whose product has degree at most two.  The two-infinity
norm argument forces both factors into the polynomial subring.  Ideal
contraction then identifies the monic `u`-polynomials, so the principal
function is constant and the balanced representatives agree.

This yields the Abel--Jacobi embedding of the curve directly, without a
global Mumford normal-form hypothesis and without coefficient enumeration.
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13SmallMumfordRigidity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

open SexticMumford

private theorem numerator_order
    (α : (N13Mumford.FunctionField K)ˣ)
    (u : K[X]) (z : N13Mumford.CoordinateRing K)
    (hu : u ≠ 0)
    (hz :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z =
        (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass (N13Mumford.model K) u)) :
    (N13Infinity.coordinateToLaurent K z).order =
      (N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K)).order -
        (u.natDegree : ℤ) := by
  have hα :
      N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K) ≠ 0 :=
    by simpa only [map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have huL : N13BranchNorm.evalPoly K u ≠ 0 :=
    N13BranchNorm.evalPoly_ne_zero K hu
  have hmapped := congrArg (N13Infinity.functionFieldToLaurent K) hz
  rw [map_mul, N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass] at hmapped
  change
    N13Infinity.coordinateToLaurent K z =
      N13Infinity.functionFieldToLaurent K
          (α : N13Mumford.FunctionField K) *
        N13BranchNorm.evalPoly K u at hmapped
  calc
    (N13Infinity.coordinateToLaurent K z).order =
        (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K) *
          N13BranchNorm.evalPoly K u).order := by rw [hmapped]
    _ =
        (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K)).order +
          (N13BranchNorm.evalPoly K u).order :=
      HahnSeries.order_mul hα huL
    _ = _ := by
      rw [N13BranchNorm.evalPoly_order K u hu]
      omega

private theorem inverse_order
    (α : (N13Mumford.FunctionField K)ˣ) :
    (N13Infinity.functionFieldToLaurent K
        (↑α⁻¹ : N13Mumford.FunctionField K)).order =
      -(N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order := by
  let a :=
    N13Infinity.functionFieldToLaurent K
      (α : N13Mumford.FunctionField K)
  let b :=
    N13Infinity.functionFieldToLaurent K
      (↑α⁻¹ : N13Mumford.FunctionField K)
  have ha : a ≠ 0 :=
    by simpa only [a, map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have hb : b ≠ 0 := by
    simpa only [b, map_zero] using
      (N13Infinity.functionFieldToLaurent_injective K).ne
        (Units.ne_zero α⁻¹)
  have hab : a * b = 1 := by
    simp [a, b]
  have hord := HahnSeries.order_mul ha hb
  rw [hab, HahnSeries.order_one] at hord
  change b.order = -a.order
  omega

private theorem orientation_order
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (α : (N13Mumford.FunctionField K)ˣ)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    (N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order =
      (D₂.nInf : ℤ) - D₁.nInf := by
  change
    Multiplicative.ofAdd
        (((D₁.nInf : ℤ) - 1) +
          (N13Infinity.functionFieldToLaurent K
            (α : N13Mumford.FunctionField K)).order) =
      Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) at hInf
  have h := Multiplicative.ofAdd.injective hInf
  omega

private theorem principal_is_constant_of_small
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (α : (N13Mumford.FunctionField K)ˣ)
    (hsmall₁ : D₁.u.natDegree + D₁.nInf ≤ 1)
    (hsmall₂ : D₂.u.natDegree + D₂.nInf ≤ 1)
    (hIdeal :
      mumfordIdealUnit (N13Mumford.model K) D₁.toSemi *
          toPrincipalIdeal (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) α =
        mumfordIdealUnit (N13Mumford.model K) D₂.toSemi)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    ∃ c : Kˣ, α = N13Infinity.functionConstUnit K c := by
  let M := N13Mumford.model K
  obtain ⟨z, w, hzmem, hwmem, hprod, hzeq, hweq⟩ :=
    exists_integral_factor_pair_of_principal_relation
      M D₁.toSemi D₂.toSemi α hIdeal
  change z ∈ mumfordIdeal M D₂.u D₂.v at hzmem
  change w ∈ mumfordIdeal M D₁.u D₁.v at hwmem
  change z * w = xClass M (D₁.u * D₂.u) at hprod
  change
    algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K) z =
      (α : N13Mumford.FunctionField K) *
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₁.u) at hzeq
  change
    algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K) w =
      (↑α⁻¹ : N13Mumford.FunctionField K) *
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₂.u) at hweq
  have hu₁ : D₁.u ≠ 0 := D₁.u_monic.ne_zero
  have hu₂ : D₂.u ≠ 0 := D₂.u_monic.ne_zero
  have hαorder := orientation_order K D₁ D₂ α hInf
  have hzorder := numerator_order K α D₁.u z hu₁ hzeq
  have hworder := numerator_order K α⁻¹ D₂.u w hu₂ hweq
  have hαinv := inverse_order K α
  have hzplus :
      (-1 : ℤ) ≤ (N13Infinity.coordinateToLaurent K z).order := by
    rw [hzorder, hαorder]
    omega
  have hwplus :
      (-1 : ℤ) ≤ (N13Infinity.coordinateToLaurent K w).order := by
    rw [hworder, hαinv, hαorder]
    omega
  have hP : D₁.u * D₂.u ≠ 0 := mul_ne_zero hu₁ hu₂
  have hPdeg : (D₁.u * D₂.u).natDegree ≤ 2 := by
    rw [Polynomial.natDegree_mul hu₁ hu₂]
    omega
  obtain ⟨hzY, hwY, -, -⟩ :=
    N13FactorRigidity.factor_pair_rigidity K z w
      (D₁.u * D₂.u) hP hPdeg hprod hzplus hwplus
  let pz := coeff0 M z
  let pw := coeff0 M w
  have hzpoly : z = xClass M pz := by
    have hzY' : coeffY M z = 0 := by simpa [M] using hzY
    rw [← recompose M z]
    rw [hzY']
    simp [pz]
  have hwpoly : w = xClass M pw := by
    have hwY' : coeffY M w = 0 := by simpa [M] using hwY
    rw [← recompose M w]
    rw [hwY']
    simp [pw]
  have hpoly : pz * pw = D₁.u * D₂.u := by
    apply xClass_injective M
    rw [xClass_mul, ← hzpoly, ← hwpoly, hprod]
  have hu₂pz : D₂.u ∣ pz := by
    have hm :
        pz ∈
          (mumfordIdeal M D₂.u D₂.v).comap (xClassHom M) := by
      change xClass M pz ∈ mumfordIdeal M D₂.u D₂.v
      rw [← hzpoly]
      exact hzmem
    have hbase :
        (mumfordIdeal M D₂.u D₂.v).comap (xClassHom M) =
          Ideal.span ({D₂.u} : Set K[X]) := by
      simpa only [toSemi_u, toSemi_v] using
        mumfordIdeal_comap_base M D₂.toSemi
    rw [hbase, Ideal.mem_span_singleton] at hm
    exact hm
  have hu₁pw : D₁.u ∣ pw := by
    have hm :
        pw ∈
          (mumfordIdeal M D₁.u D₁.v).comap (xClassHom M) := by
      change xClass M pw ∈ mumfordIdeal M D₁.u D₁.v
      rw [← hwpoly]
      exact hwmem
    have hbase :
        (mumfordIdeal M D₁.u D₁.v).comap (xClassHom M) =
          Ideal.span ({D₁.u} : Set K[X]) := by
      simpa only [toSemi_u, toSemi_v] using
        mumfordIdeal_comap_base M D₁.toSemi
    rw [hbase, Ideal.mem_span_singleton] at hm
    exact hm
  obtain ⟨c, hpc⟩ := hu₂pz
  obtain ⟨d, hpd⟩ := hu₁pw
  have hcd : c * d = 1 := by
    apply mul_left_cancel₀ hP
    calc
      (D₁.u * D₂.u) * (c * d) =
          (D₂.u * c) * (D₁.u * d) := by ring
      _ = pz * pw := by rw [← hpc, ← hpd]
      _ = D₁.u * D₂.u := hpoly
      _ = (D₁.u * D₂.u) * 1 := by rw [mul_one]
  have hcunit : IsUnit c :=
    isUnit_iff_exists_inv.mpr ⟨d, hcd⟩
  have hpzfield :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M pz) =
        (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) := by
    rw [← hzpoly]
    exact hzeq
  have hscale :
      (α : N13Mumford.FunctionField K) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) =
        algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₂.u) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M c) := by
    calc
      _ = algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M pz) :=
        hpzfield.symm
      _ = algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M (D₂.u * c)) := by
            rw [hpc]
      _ = _ := by rw [xClass_mul, map_mul]
  have hunitX : xClass M c * xClass M d = 1 := by
    rw [← xClass_mul, hcd, xClass_one]
  have huEq : D₁.u = D₂.u :=
    mumford_u_eq_of_principal_scale M D₁.toSemi D₂.toSemi α
      (xClass M c) (xClass M d) hIdeal hscale hunitX
  have hpc' : pz = D₁.u * c := by
    rw [huEq]
    exact hpc
  have huField :
      algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M D₁.u) ≠ 0 := by
    simpa using
      (IsFractionRing.injective
        (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)).ne
        (xClass_ne_zero M hu₁)
  have hαfield :
      (α : N13Mumford.FunctionField K) =
        algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) (xClass M c) := by
    apply mul_right_cancel₀ huField
    calc
      (α : N13Mumford.FunctionField K) *
            algebraMap (N13Mumford.CoordinateRing K)
              (N13Mumford.FunctionField K) (xClass M D₁.u) =
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M pz) :=
        hpzfield.symm
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass M (D₁.u * c)) := by rw [hpc']
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K)
            (xClass M D₁.u * xClass M c) := by rw [xClass_mul]
      _ = algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M c) *
          algebraMap (N13Mumford.CoordinateRing K)
            (N13Mumford.FunctionField K) (xClass M D₁.u) := by
              rw [map_mul]
              ring
  obtain ⟨r, hrunit, hCr⟩ := Polynomial.isUnit_iff.mp hcunit
  let cr : Kˣ := hrunit.unit
  refine ⟨cr, ?_⟩
  apply Units.ext
  change
    (α : N13Mumford.FunctionField K) =
      algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (cr : K))
  rw [hαfield, ← hCr]
  rfl

theorem eq_of_class_eq_of_small
    (D₁ D₂ : Mumford (N13Mumford.model K))
    (hsmall₁ : D₁.u.natDegree + D₁.nInf ≤ 1)
    (hsmall₂ : D₂.u.natDegree + D₂.nInf ≤ 1)
    (hclass :
      classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₁ =
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K) D₂) :
    D₁ = D₂ := by
  obtain ⟨α, hIdeal, hInf⟩ :=
    (classOf_eq_iff (N13Mumford.model K)
      (N13Infinity.positiveInfinityOrder K) D₁ D₂).mp hclass
  obtain ⟨c, hα⟩ :=
    principal_is_constant_of_small K D₁ D₂ α
      hsmall₁ hsmall₂ hIdeal hInf
  exact N13Mumford.principal_between_balanced_of_constant
    K c hα hIdeal hInf

theorem pointMumford_small
    (P : CurvePoint (N13Mumford.model K)) :
    (pointMumford (N13Mumford.model K) P).u.natDegree +
        (pointMumford (N13Mumford.model K) P).nInf ≤ 1 := by
  cases P with
  | infinityPlus =>
      simp [pointMumford, zero]
  | infinityMinus =>
      simp [pointMumford, infinityMinusMumford]
  | affine x y h =>
      simp [pointMumford, affinePointMumford]

theorem point_class_injective :
    Function.Injective
      (fun P : CurvePoint (N13Mumford.model K) =>
        classOf (N13Mumford.model K)
          (N13Infinity.positiveInfinityOrder K)
          (pointMumford (N13Mumford.model K) P)) := by
  intro P Q hPQ
  apply pointMumford_injective (N13Mumford.model K)
  exact eq_of_class_eq_of_small K _ _
    (pointMumford_small K P) (pointMumford_small K Q) hPQ

end

end MazurProof.N13SmallMumfordRigidity
