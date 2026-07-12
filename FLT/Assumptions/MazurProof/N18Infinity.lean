import FLT.Assumptions.MazurProof.N18Mumford
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# The positive infinity of the N18 genus-two curve

We construct the chosen branch at infinity inside `K((s))`.  With `x=s⁻¹`,
the equation becomes

`(s³ y)² = 1 + 4s + 10s² + 10s³ + 5s⁴ + 2s⁵ + s⁶`.

The square root with constant coefficient `+1` is obtained from the formal
binomial series.  The resulting embedding of the function field supplies the
integer orientation used in `N18Mumford`.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N18Infinity

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

/-! ## The formal positive square root -/

def reverseF : K⟦X⟧ :=
  1 + 4 * PowerSeries.X + 10 * PowerSeries.X ^ 2 +
    10 * PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 4 +
    2 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6

def reverseTail : K⟦X⟧ := reverseF K - 1

@[simp] theorem reverseTail_constantCoeff :
    PowerSeries.constantCoeff (reverseTail K) = 0 := by
  simp [reverseTail, reverseF]

theorem reverseTail_hasSubst : PowerSeries.HasSubst (reverseTail K) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (reverseTail_constantCoeff K)

def sqrtReverseF : K⟦X⟧ :=
  PowerSeries.substAlgHom (reverseTail_hasSubst K)
    (PowerSeries.binomialSeries K (1 / 2 : K))

theorem sqrtReverseF_sq : sqrtReverseF K ^ 2 = reverseF K := by
  let h := reverseTail_hasSubst K
  change (PowerSeries.substAlgHom h
      (PowerSeries.binomialSeries K (1 / 2 : K))) ^ 2 = reverseF K
  rw [pow_two, ← map_mul, ← PowerSeries.binomialSeries_add]
  have hhalf : (1 / 2 : K) + 1 / 2 = 1 := by norm_num
  rw [hhalf]
  have hone : PowerSeries.binomialSeries K (1 : K) =
      (1 + PowerSeries.X : K⟦X⟧) := by
    simpa using (PowerSeries.binomialSeries_nat (R := K) (A := K) 1)
  rw [hone]
  simp only [Nat.cast_one, pow_one, map_add, map_one,
    PowerSeries.substAlgHom_X]
  simp [h, reverseTail]

@[simp] theorem sqrtReverseF_constantCoeff :
    PowerSeries.constantCoeff (sqrtReverseF K) = 1 := by
  rw [sqrtReverseF]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  rw [PowerSeries.coe_substAlgHom (reverseTail_hasSubst K)]
  rw [PowerSeries.coeff_subst' (reverseTail_hasSubst K)]
  simp only [PowerSeries.binomialSeries_coeff]
  rw [finsum_eq_single _ 0]
  · simp
  · intro b hb
    simp [PowerSeries.coeff_zero_eq_constantCoeff,
      reverseTail_constantCoeff, hb]

/-! ## An algebraic model of the function field -/

def curvePolyRat : (RatFunc K)[X] :=
  (N18Mumford.curvePoly K).map
    (algebraMap K[X] (RatFunc K))

theorem curvePolyRat_monic : (curvePolyRat K).Monic := by
  exact (N18Mumford.curvePoly_monic K).map _

theorem curvePolyRat_irreducible : Irreducible (curvePolyRat K) := by
  rw [curvePolyRat]
  exact (N18Mumford.curvePoly_monic K).irreducible_iff_irreducible_map_fraction_map.mp
      (N18Mumford.curvePoly_irreducible K)

instance curvePolyRatIrreducibleFact :
    Fact (Irreducible (curvePolyRat K)) :=
  ⟨curvePolyRat_irreducible K⟩

abbrev AlgebraicFunctionField : Type u := AdjoinRoot (curvePolyRat K)

def coordinateToAlgebraic :
    N18Mumford.CoordinateRing K →+* AlgebraicFunctionField K :=
  AdjoinRoot.map (algebraMap K[X] (RatFunc K))
    (N18Mumford.curvePoly K) (curvePolyRat K) (by
      rw [curvePolyRat])

@[simp] theorem coordinateToAlgebraic_mk (g : K[X][X]) :
    coordinateToAlgebraic K (AdjoinRoot.mk (N18Mumford.curvePoly K) g) =
      AdjoinRoot.mk (curvePolyRat K)
        (g.map (algebraMap K[X] (RatFunc K))) := by
  simp only [coordinateToAlgebraic, AdjoinRoot.map, AdjoinRoot.lift_mk]
  rw [← Polynomial.eval₂_map]
  simpa only [← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def] using
    (AdjoinRoot.aeval_eq
      (f := curvePolyRat K)
      (p := g.map (algebraMap K[X] (RatFunc K))))

theorem coordinateToAlgebraic_injective :
    Function.Injective (coordinateToAlgebraic K) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    let r : K[X][X] := g %ₘ N18Mumford.curvePoly K
    have hrz : AdjoinRoot.mk (N18Mumford.curvePoly K) r =
        AdjoinRoot.mk (N18Mumford.curvePoly K) g := by
      simpa only [r, AdjoinRoot.modByMonicHom_mk] using
        (AdjoinRoot.mk_leftInverse (N18Mumford.curvePoly_monic K)
          (AdjoinRoot.mk (N18Mumford.curvePoly K) g))
    have hmap : AdjoinRoot.mk (curvePolyRat K)
        (r.map (algebraMap K[X] (RatFunc K))) = 0 := by
      rw [← coordinateToAlgebraic_mk, hrz, hz]
    have hrdeg : r.degree < (N18Mumford.curvePoly K).degree := by
      exact Polynomial.degree_modByMonic_lt g
        (N18Mumford.curvePoly_monic K)
    have hbase : Function.Injective
        (algebraMap K[X] (RatFunc K)) :=
      IsFractionRing.injective K[X] (RatFunc K)
    have hmapdeg :
        (r.map (algebraMap K[X] (RatFunc K))).degree <
          (curvePolyRat K).degree := by
      rw [curvePolyRat, Polynomial.degree_map_eq_of_injective hbase,
        Polynomial.degree_map_eq_of_injective hbase]
      exact hrdeg
    have hrmapzero : r.map (algebraMap K[X] (RatFunc K)) = 0 := by
      by_contra hr0
      exact (curvePolyRat_monic K).not_dvd_of_degree_lt hr0 hmapdeg
        (AdjoinRoot.mk_eq_zero.mp hmap)
    have hrzero : r = 0 :=
      (Polynomial.map_eq_zero_iff hbase).mp hrmapzero
    rw [← hrz, hrzero, map_zero]
    exact Submodule.zero_mem _
  · exact bot_le

/-! ## The branch `x = s⁻¹`, `s³y = +sqrt(reverseF)` -/

theorem ratXInv_transcendental :
    Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
  rw [Transcendental, ← IsAlgebraic.inv_iff]
  simpa [Transcendental] using (RatFunc.transcendental_X (K := K))

def invPolyAlgHom : K[X] →ₐ[K] RatFunc K :=
  Polynomial.aeval ((RatFunc.X : RatFunc K)⁻¹)

theorem invPolyAlgHom_injective :
    Function.Injective (invPolyAlgHom K) := by
  exact transcendental_iff_injective.mp (ratXInv_transcendental K)

def ratInvAlgHom : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (invPolyAlgHom K)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (invPolyAlgHom_injective K))

@[simp] theorem ratInvAlgHom_X :
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
      (RatFunc.X : RatFunc K)⁻¹ := by
  calc
    ratInvAlgHom K (RatFunc.X : RatFunc K) =
        ratInvAlgHom K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = invPolyAlgHom K Polynomial.X := by
      change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
          (algebraMap K[X] (RatFunc K) Polynomial.X) = _
      exact RatFunc.liftRingHom_algebraMap _ _ _
    _ = (RatFunc.X : RatFunc K)⁻¹ := by simp [invPolyAlgHom]

def standardRatToLaurent : RatFunc K →+* LaurentSeries K :=
  IsFractionRing.lift
    (g := algebraMap K[X] (LaurentSeries K))
    (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ)

@[simp] theorem standardRatToLaurent_X :
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
      HahnSeries.single 1 1 := by
  calc
    standardRatToLaurent K (RatFunc.X : RatFunc K) =
        standardRatToLaurent K
          (algebraMap K[X] (RatFunc K) Polynomial.X) := by
            rw [RatFunc.algebraMap_X]
    _ = algebraMap K[X] (LaurentSeries K) Polynomial.X := by
      exact IsFractionRing.lift_algebraMap
        (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) _
    _ = HahnSeries.single 1 1 := by simp

@[simp] theorem standardRatToLaurent_algebraMap (p : K[X]) :
    standardRatToLaurent K (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (LaurentSeries K) p := by
  exact IsFractionRing.lift_algebraMap
    (Polynomial.algebraMap_hahnSeries_injective (R := K) ℤ) p

@[simp] theorem ratInvAlgHom_algebraMap (p : K[X]) :
    ratInvAlgHom K (algebraMap K[X] (RatFunc K) p) =
      invPolyAlgHom K p := by
  change RatFunc.liftRingHom (invPolyAlgHom K).toRingHom _
      (algebraMap K[X] (RatFunc K) p) = _
  exact RatFunc.liftRingHom_algebraMap _ _ _

def ratToLaurent : RatFunc K →+* LaurentSeries K :=
  (standardRatToLaurent K).comp
    (ratInvAlgHom K).toRingHom

def parameter : LaurentSeries K := HahnSeries.single 1 1

@[simp] theorem parameter_ne_zero : parameter K ≠ 0 := by
  simp [parameter]

@[simp] theorem ratToLaurent_X :
    ratToLaurent K (RatFunc.X : RatFunc K) = (parameter K)⁻¹ := by
  simp [ratToLaurent, parameter]

@[simp] theorem ratToLaurent_C (a : K) :
    ratToLaurent K (RatFunc.C a) =
      algebraMap K (LaurentSeries K) a := by
  rw [← RatFunc.algebraMap_C]
  change standardRatToLaurent K
      (ratInvAlgHom K (algebraMap K[X] (RatFunc K) (C a))) = _
  rw [ratInvAlgHom_algebraMap]
  simp only [invPolyAlgHom, Polynomial.aeval_C]
  change standardRatToLaurent K (RatFunc.C a) = _
  rw [← RatFunc.algebraMap_C]
  rw [standardRatToLaurent_algebraMap]
  rw [Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C,
    HahnSeries.ofPowerSeries_C]
  rw [HahnSeries.algebraMap_apply' (Γ := ℤ)]
  simp [PowerSeries.algebraMap_apply]

theorem ratToLaurent_comp_algebraMap :
    (ratToLaurent K).comp (algebraMap K[X] (RatFunc K)) =
      Polynomial.eval₂RingHom (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

def wSeries : LaurentSeries K := (sqrtReverseF K : LaurentSeries K)

def ySeries : LaurentSeries K :=
  ((parameter K)⁻¹) ^ 3 * wSeries K

theorem reverseF_coe :
    ((reverseF K : K⟦X⟧) : LaurentSeries K) =
      1 + 4 * parameter K + 10 * parameter K ^ 2 +
        10 * parameter K ^ 3 + 5 * parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  simp [reverseF, parameter, PowerSeries.coe_add, PowerSeries.coe_mul,
    PowerSeries.coe_pow, PowerSeries.coe_X, map_ofNat]

theorem wSeries_sq :
    wSeries K ^ 2 =
      1 + 4 * parameter K + 10 * parameter K ^ 2 +
        10 * parameter K ^ 3 + 5 * parameter K ^ 4 +
        2 * parameter K ^ 5 + parameter K ^ 6 := by
  rw [wSeries, ← PowerSeries.coe_pow, sqrtReverseF_sq, reverseF_coe]

theorem ySeries_sq :
    ySeries K ^ 2 =
      (N18Mumford.f K).eval₂ (algebraMap K (LaurentSeries K))
        ((parameter K)⁻¹) := by
  rw [ySeries]
  simp only [N18Mumford.f, eval₂_add, eval₂_pow, eval₂_X,
    eval₂_mul, eval₂_ofNat, eval₂_one]
  field_simp [parameter_ne_zero K]
  rw [wSeries_sq]
  ring

theorem curvePolyRat_eval_ySeries :
    (curvePolyRat K).eval₂ (ratToLaurent K) (ySeries K) = 0 := by
  rw [curvePolyRat, Polynomial.eval₂_map,
    ratToLaurent_comp_algebraMap]
  simp only [N18Mumford.curvePoly, eval₂_sub, eval₂_pow,
    eval₂_X, eval₂_C]
  rw [ySeries_sq]
  exact sub_self _

def algebraicToLaurent :
    AlgebraicFunctionField K →+* LaurentSeries K :=
  AdjoinRoot.lift (ratToLaurent K) (ySeries K)
    (curvePolyRat_eval_ySeries K)

theorem algebraicToLaurent_injective :
    Function.Injective (algebraicToLaurent K) :=
  (algebraicToLaurent K).injective

def coordinateToLaurent :
    N18Mumford.CoordinateRing K →+* LaurentSeries K :=
  (algebraicToLaurent K).comp (coordinateToAlgebraic K)

theorem coordinateToLaurent_injective :
    Function.Injective (coordinateToLaurent K) :=
  (algebraicToLaurent_injective K).comp
    (coordinateToAlgebraic_injective K)

def functionFieldToLaurent :
    N18Mumford.FunctionField K →+* LaurentSeries K :=
  IsFractionRing.lift (coordinateToLaurent_injective K)

theorem functionFieldToLaurent_injective :
    Function.Injective (functionFieldToLaurent K) :=
  (functionFieldToLaurent K).injective

def laurentOrder : (LaurentSeries K)ˣ →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (z.1.order)
  map_one' := by
    change (1 : LaurentSeries K).order = 0
    simp
  map_mul' x y := by
    change ((x.1 * y.1 : LaurentSeries K).order) =
      x.1.order + y.1.order
    exact HahnSeries.order_mul x.ne_zero y.ne_zero

def infinityOrderHom :
    (N18Mumford.FunctionField K)ˣ →* Multiplicative ℤ :=
  (laurentOrder K).comp (Units.map (functionFieldToLaurent K))

def positiveInfinityOrder : N18Mumford.InfinityOrder K where
  ordPlus := infinityOrderHom K

end

end MazurProof.N18Infinity
