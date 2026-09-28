import FLT.Assumptions.MazurProof.N25F_ChartLocalOrder
import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# Order zero and local units on the characteristic-two N25 W-chart

The common function field `K = FractionRing W` is also a fraction field of
`ChartLocalRing25Two A`.  This file constructs the canonical comparison with
the quotient-model fraction field of the local ring and proves that the
already-defined integer local order of a function-field unit is zero exactly
when that function is represented by a unit of the local ring.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ChartLocalOrder

open scoped nonZeroDivisors

open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open N25F_NonBoundaryPrincipalDivisor

/-- The chart prime is prime, as it is already known to be maximal.  This
local instance is repeated here because the corresponding instance in the
construction module is private to that module. -/
private instance fullNonBoundaryPrimeIdeal_isPrime_forUnitCriterion
    (A : FullNonBoundaryAtom25Two) :
    (fullNonBoundaryPrimeIdeal A).IsPrime :=
  (fullNonBoundaryPrimeData A).isMaximal.isPrime

/-- The localization of the Dedekind W-chart at a nonzero prime is a DVR. -/
private noncomputable instance chartLocalRing25Two_isDiscreteValuationRing
    (A : FullNonBoundaryAtom25Two) :
    IsDiscreteValuationRing (ChartLocalRing25Two A) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    W (P := fullNonBoundaryPrimeIdeal A)
    (fullNonBoundaryPrimeData A).ne_bot (ChartLocalRing25Two A)

/-! ## The common field as the local ring's fraction field -/

/-- The pinned localization instances make the common function field `K`
a fraction field of every nonboundary chart local ring. -/
theorem chartLocalRing25Two_isFractionRing
    (A : FullNonBoundaryAtom25Two) :
    IsFractionRing (ChartLocalRing25Two A) K :=
  inferInstance

/-- Although `K` is not definitionally the quotient-model fraction ring of
the local ring, the two fraction fields are canonically equivalent. -/
noncomputable def chartFractionRingEquiv
    (A : FullNonBoundaryAtom25Two) :
    FractionRing (ChartLocalRing25Two A) ≃ₐ[ChartLocalRing25Two A] K := by
  letI : IsFractionRing (ChartLocalRing25Two A) K :=
    chartLocalRing25Two_isFractionRing A

  let eData :
      {e : FractionRing (ChartLocalRing25Two A) ≃+* K //
        ∀ x : ChartLocalRing25Two A,
          e (OreLocalization.numeratorRingHom x) =
            algebraMap (ChartLocalRing25Two A) K x} := by
    letI : Algebra (ChartLocalRing25Two A)
        (FractionRing (ChartLocalRing25Two A)) :=
      OreLocalization.instAlgebra
    letI :
        IsLocalization
          (nonZeroDivisors (ChartLocalRing25Two A))
          (FractionRing (ChartLocalRing25Two A)) :=
      Localization.isLocalization
    let e :=
      IsLocalization.algEquiv
        (nonZeroDivisors (ChartLocalRing25Two A))
        (FractionRing (ChartLocalRing25Two A))
        K
    refine ⟨e.toRingEquiv, ?_⟩
    intro x
    exact e.commutes x

  have hsource :
      (algebraMap (ChartLocalRing25Two A)
          (FractionRing (ChartLocalRing25Two A)) :
        ChartLocalRing25Two A →+*
          FractionRing (ChartLocalRing25Two A)) =
      (OreLocalization.numeratorRingHom :
        ChartLocalRing25Two A →+*
          FractionRing (ChartLocalRing25Two A)) := by
    apply IsLocalization.ringHom_ext
      (fullNonBoundaryPrimeIdeal A).primeCompl
    exact RingHom.ext fun x => by
      with_reducible_and_instances
        simp [RingHom.algebraMap_toAlgebra]

  exact AlgEquiv.ofRingEquiv (f := eData.1) fun x => by
    rw [hsource]
    exact eData.2 x

/-- The exact map from the chart local ring to the common function field. -/
noncomputable def fractionFieldMapForChart
    (A : FullNonBoundaryAtom25Two) :
    ChartLocalRing25Two A →+* K :=
  algebraMap (ChartLocalRing25Two A) K

@[simp]
theorem fractionFieldMapForChart_apply
    (A : FullNonBoundaryAtom25Two) (x : ChartLocalRing25Two A) :
    fractionFieldMapForChart A x =
      algebraMap (ChartLocalRing25Two A) K x :=
  rfl

/-- The explicitly constructed fraction-field equivalence carries the
canonical quotient-model inclusion to `fractionFieldMapForChart`. -/
@[simp]
theorem chartFractionRingEquiv_algebraMap
    (A : FullNonBoundaryAtom25Two) (x : ChartLocalRing25Two A) :
    chartFractionRingEquiv A
        (algebraMap (ChartLocalRing25Two A)
          (FractionRing (ChartLocalRing25Two A)) x) =
      fractionFieldMapForChart A x := by
  simpa [fractionFieldMapForChart] using
    (chartFractionRingEquiv A).commutes x

/-- The local-ring fraction-field map is compatible with the original
W-chart inclusion into `K`. -/
@[simp]
theorem fractionFieldMapForChart_algebraMap
    (A : FullNonBoundaryAtom25Two) (a : W) :
    fractionFieldMapForChart A
        (algebraMap W (ChartLocalRing25Two A) a) =
      algebraMap W K a := by
  simpa [fractionFieldMapForChart] using
    (IsScalarTower.algebraMap_apply
      W (ChartLocalRing25Two A) K a).symm

/-! ## Comparing `localElementOrder` with `Ring.ordFrac` -/

/-- On a nonzero W-chart element, the fraction-field order attached to the
chart DVR is the exponential of the existing integer local element order. -/
theorem chartOrdFrac_algebraMap_eq_exp_localElementOrder
    (A : FullNonBoundaryAtom25Two) {a : W} (ha : a ≠ 0) :
    Ring.ordFrac (ChartLocalRing25Two A) (algebraMap W K a) =
      WithZero.exp (localElementOrder A a) := by
  have haLocal :
      algebraMap W (ChartLocalRing25Two A) a ≠ 0 :=
    (map_ne_zero_iff
      (algebraMap W (ChartLocalRing25Two A))
      (IsLocalization.injective (ChartLocalRing25Two A)
        (fullNonBoundaryPrimeIdeal A).primeCompl_le_nonZeroDivisors)).2 ha
  have hfinite :
      Ring.ord (ChartLocalRing25Two A)
          (algebraMap W (ChartLocalRing25Two A) a) ≠ ⊤ :=
    Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero haLocal)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfinite
  calc
    Ring.ordFrac (ChartLocalRing25Two A) (algebraMap W K a) =
        Ring.ordFrac (ChartLocalRing25Two A)
          (algebraMap (ChartLocalRing25Two A) K
            (algebraMap W (ChartLocalRing25Two A) a)) := by
      exact congrArg (Ring.ordFrac (ChartLocalRing25Two A))
        (IsScalarTower.algebraMap_apply
          W (ChartLocalRing25Two A) K a)
    _ = Ring.ordMonoidWithZeroHom (ChartLocalRing25Two A)
          (algebraMap W (ChartLocalRing25Two A) a) := by
      exact Ring.ordFrac_eq_ord (ChartLocalRing25Two A) haLocal
    _ = WithZero.exp (m : ℤ) := by
      simpa only [WithZero.exp_eq_coe_ofAdd] using
        (Ring.ordMonoidWithZeroHom_eq_coe
          (R := ChartLocalRing25Two A)
          (mem_nonZeroDivisors_of_ne_zero haLocal) hm.symm)
    _ = WithZero.exp (localElementOrder A a) := by
      have horder : localElementOrder A a = (m : ℤ) := by
        unfold localElementOrder
        rw [← hm]
        simp
      rw [horder]

/-- For an arbitrary nonzero rational function, the DVR fraction-field order
is exactly the exponential of the existing signed integer local order. -/
theorem chartOrdFrac_eq_exp_localFractionOrder
    (A : FullNonBoundaryAtom25Two) (f : Additive Kˣ) :
    Ring.ordFrac (ChartLocalRing25Two A) (f.toMul : K) =
      WithZero.exp (localFractionOrder A f) := by
  obtain ⟨n, d, hrep⟩ :=
    IsLocalization.exists_mk'_eq W⁰ (f.toMul : K)
  have hn : n ≠ 0 :=
    IsLocalization.ne_zero_of_mk'_ne_zero
      (S := K) (y := d) (by
        rw [hrep]
        exact Units.ne_zero _)
  have hd : (d : W) ≠ 0 :=
    nonZeroDivisors.ne_zero d.property
  calc
    Ring.ordFrac (ChartLocalRing25Two A) (f.toMul : K) =
        Ring.ordFrac (ChartLocalRing25Two A)
          (IsLocalization.mk' K n d) := by
      exact congrArg (Ring.ordFrac (ChartLocalRing25Two A)) hrep.symm
    _ = Ring.ordFrac (ChartLocalRing25Two A)
          (algebraMap W K n / algebraMap W K (d : W)) := by
      rw [IsFractionRing.mk'_eq_div]
    _ = Ring.ordFrac (ChartLocalRing25Two A) (algebraMap W K n) /
          Ring.ordFrac (ChartLocalRing25Two A)
            (algebraMap W K (d : W)) := by
      rw [map_div₀]
    _ = WithZero.exp (localElementOrder A n) /
          WithZero.exp (localElementOrder A (d : W)) := by
      rw [chartOrdFrac_algebraMap_eq_exp_localElementOrder A hn,
        chartOrdFrac_algebraMap_eq_exp_localElementOrder A hd]
    _ = WithZero.exp
          (localElementOrder A n - localElementOrder A (d : W)) := by
      rw [div_eq_mul_inv, ← WithZero.exp_neg,
        ← WithZero.exp_add, sub_eq_add_neg]
    _ = WithZero.exp (localFractionOrder A f) := by
      rw [localFractionOrder_eq_sub_of_rep A f hn d hrep]

/-- Integer local order zero is the multiplicative-kernel condition for the
DVR order on the common function field. -/
@[simp]
theorem localFractionOrder_eq_zero_iff_chartOrdFrac_eq_one
    (A : FullNonBoundaryAtom25Two) (f : Additive Kˣ) :
    localFractionOrder A f = 0 ↔
      Ring.ordFrac (ChartLocalRing25Two A) (f.toMul : K) = 1 := by
  simpa only [chartOrdFrac_eq_exp_localFractionOrder,
    WithZero.exp_eq_one]

/-- The order-zero condition is membership in the image of the local-ring
unit submonoid.  This is the exact pinned Mathlib DVR-kernel theorem. -/
theorem localFractionOrder_eq_zero_iff_mem_chartUnitMap
    (A : FullNonBoundaryAtom25Two) (f : Additive Kˣ) :
    localFractionOrder A f = 0 ↔
      (f.toMul : K) ∈
        (IsUnit.submonoid (ChartLocalRing25Two A)).map
          (algebraMap (ChartLocalRing25Two A) K) := by
  calc
    localFractionOrder A f = 0 ↔
        Ring.ordFrac (ChartLocalRing25Two A) (f.toMul : K) = 1 :=
      localFractionOrder_eq_zero_iff_chartOrdFrac_eq_one A f
    _ ↔ (f.toMul : K) ∈
        MonoidHom.mker (Ring.ordFrac (ChartLocalRing25Two A)) :=
      (MonoidHom.mem_mker
        (f := Ring.ordFrac (ChartLocalRing25Two A))
        (x := (f.toMul : K))).symm
    _ ↔ (f.toMul : K) ∈
        (IsUnit.submonoid (ChartLocalRing25Two A)).map
          (algebraMap (ChartLocalRing25Two A) K) := by
      rw [Ring.mker_ordFrac_eq_isUnitSubmonoid]

/-- Membership in the image of the local unit submonoid is the same as an
explicit unit witness for `fractionFieldMapForChart`. -/
theorem mem_chartUnitMap_iff_exists_unit
    (A : FullNonBoundaryAtom25Two) (x : K) :
    x ∈ (IsUnit.submonoid (ChartLocalRing25Two A)).map
        (algebraMap (ChartLocalRing25Two A) K) ↔
      ∃ u : (ChartLocalRing25Two A)ˣ,
        fractionFieldMapForChart A
          (u : ChartLocalRing25Two A) = x := by
  constructor
  · intro hx
    rcases Submonoid.mem_map.mp hx with ⟨y, hy, hxy⟩
    change IsUnit y at hy
    refine ⟨hy.unit, ?_⟩
    calc
      fractionFieldMapForChart A
          (hy.unit : ChartLocalRing25Two A) =
          algebraMap (ChartLocalRing25Two A) K
            (hy.unit : ChartLocalRing25Two A) :=
        fractionFieldMapForChart_apply A _
      _ = algebraMap (ChartLocalRing25Two A) K y := by
        rw [IsUnit.unit_spec hy]
      _ = x := hxy
  · rintro ⟨u, hu⟩
    apply Submonoid.mem_map.mpr
    refine ⟨(u : ChartLocalRing25Two A), u.isUnit, ?_⟩
    simpa [fractionFieldMapForChart] using hu

/-- A function-field unit has local order zero exactly when it is represented
by a unit of the chart local ring. -/
theorem localFractionOrder_eq_zero_iff_exists_chartUnit
    (A : FullNonBoundaryAtom25Two) (f : Additive Kˣ) :
    localFractionOrder A f = 0 ↔
      ∃ u : (ChartLocalRing25Two A)ˣ,
        fractionFieldMapForChart A
          (u : ChartLocalRing25Two A) = (f.toMul : K) := by
  calc
    localFractionOrder A f = 0 ↔
        (f.toMul : K) ∈
          (IsUnit.submonoid (ChartLocalRing25Two A)).map
            (algebraMap (ChartLocalRing25Two A) K) :=
      localFractionOrder_eq_zero_iff_mem_chartUnitMap A f
    _ ↔ ∃ u : (ChartLocalRing25Two A)ˣ,
        fractionFieldMapForChart A
          (u : ChartLocalRing25Two A) = (f.toMul : K) :=
      mem_chartUnitMap_iff_exists_unit A (f.toMul : K)

end MazurProof.N25F_ChartLocalOrder
