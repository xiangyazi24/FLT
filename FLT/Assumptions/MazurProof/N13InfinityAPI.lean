import FLT.Assumptions.MazurProof.N13Infinity

/-!
# Evaluation API for the positive infinity embedding of the N13 sextic
-/

open Polynomial
open scoped LaurentSeries nonZeroDivisors

namespace MazurProof.N13Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

@[simp] theorem functionFieldToLaurent_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurent K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurent K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurent_injective K) z

theorem coordinateToAlgebraic_xClass (p : K[X]) :
    coordinateToAlgebraic K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      AdjoinRoot.of (curvePolyRat K)
        (algebraMap K[X] (RatFunc K) p) := by
  simpa only [SexticMumford.xClass, SexticMumford.mk, Polynomial.map_C,
    AdjoinRoot.mk_C] using coordinateToAlgebraic_mk K (C p)

@[simp] theorem coordinateToLaurent_xClass (p : K[X]) :
    coordinateToLaurent K
      (SexticMumford.xClass (N13Mumford.model K) p) =
      p.eval₂ (algebraMap K (LaurentSeries K)) ((parameter K)⁻¹) := by
  change algebraicToLaurent K
      (coordinateToAlgebraic K
        (SexticMumford.xClass (N13Mumford.model K) p)) = _
  rw [coordinateToAlgebraic_xClass]
  unfold algebraicToLaurent
  rw [AdjoinRoot.lift_of (curvePolyRat_eval_ySeries K)]
  exact DFunLike.congr_fun (ratToLaurent_comp_algebraMap K) p

@[simp] theorem coordinateToLaurent_scalar (c : K) :
    coordinateToLaurent K (algebraMap K (N13Mumford.CoordinateRing K) c) =
      algebraMap K (LaurentSeries K) c := by
  change coordinateToLaurent K
    (SexticMumford.xClass (N13Mumford.model K) (C c)) = _
  rw [coordinateToLaurent_xClass]
  simp

def coordinateConstUnit (c : Kˣ) : (N13Mumford.CoordinateRing K)ˣ :=
  Units.map (algebraMap K (N13Mumford.CoordinateRing K)) c

def functionConstUnit (c : Kˣ) : (N13Mumford.FunctionField K)ˣ :=
  Units.map
    (algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K))
    (coordinateConstUnit K c)

@[simp] theorem functionFieldToLaurent_functionConstUnit (c : Kˣ) :
    functionFieldToLaurent K (functionConstUnit K c :
      N13Mumford.FunctionField K) =
      algebraMap K (LaurentSeries K) (c : K) := by
  change functionFieldToLaurent K
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (algebraMap K (N13Mumford.CoordinateRing K) (c : K))) = _
  rw [functionFieldToLaurent_algebraMap, coordinateToLaurent_scalar]

@[simp] theorem ordPlus_functionConstUnit (c : Kˣ) :
    (positiveInfinityOrder K).ordPlus (functionConstUnit K c) = 1 := by
  change Multiplicative.ofAdd
      ((functionFieldToLaurent K
        (functionConstUnit K c : N13Mumford.FunctionField K)).order) = 1
  rw [functionFieldToLaurent_functionConstUnit]
  simp [HahnSeries.algebraMap_apply', HahnSeries.order_single c.ne_zero]

@[simp] theorem principalIdeal_functionConstUnit (c : Kˣ) :
    toPrincipalIdeal (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K) (functionConstUnit K c) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton
      (N13Mumford.CoordinateRing K)⁰
      (algebraMap (N13Mumford.CoordinateRing K)
        (N13Mumford.FunctionField K)
        (coordinateConstUnit K c : N13Mumford.CoordinateRing K)) = 1
  rw [← FractionalIdeal.spanSingleton_one]
  apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
  refine ⟨(coordinateConstUnit K c)⁻¹, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, ← map_mul]
  change algebraMap (N13Mumford.CoordinateRing K)
      (N13Mumford.FunctionField K)
      (((coordinateConstUnit K c)⁻¹ :
          (N13Mumford.CoordinateRing K)ˣ) * coordinateConstUnit K c :
        (N13Mumford.CoordinateRing K)ˣ) = 1
  simp

end

end MazurProof.N13Infinity
