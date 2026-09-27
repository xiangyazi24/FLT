import FLT.Assumptions.MazurProof.N25F_NonBoundaryPrincipalDivisor
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.Tactic


set_option autoImplicit false
set_option relaxedAutoImplicit false


noncomputable section


namespace MazurProof.N25F_ChartLocalOrder


open scoped nonZeroDivisors


open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_NonBoundaryPrincipalDivisor


abbrev W := N25F_NonBoundaryPrincipalDivisor.W
abbrev K := FractionRing W

/- `Localization.AtPrime P` itself requires `[P.IsPrime]` while its
type is elaborated, so install the primality already carried by the
nonboundary prime data before defining the local-ring abbreviation. -/
private instance fullNonBoundaryPrimeIdeal_isPrime
    (A : FullNonBoundaryAtom25Two) :
    (fullNonBoundaryPrimeIdeal A).IsPrime :=
  (fullNonBoundaryPrimeData A).isMaximal.isPrime


/-- The local ring of the fixed `W)-chart at a nonboundary full closed
point. -/
abbrev ChartLocalRing25Two (A : FullNonBoundaryAtom25Two) :=
  Localization.AtPrime (fullNonBoundaryPrimeIdeal A)


/-- A nonzero chart element remains nonzero in its local ring. -/
private theorem algebraMap_chartLocalRing_ne_zero
    (A : FullNonBoundaryAtom25Two) {a : W} (ha : a ≠ 0) :
    algebraMap W (ChartLocalRing25Two A) a ≠ 0 := by
  letI : (fullNonBoundaryPrimeIdeal A).IsPrime :=
    (fullNonBoundaryPrimeData A).isMaximal.isPrime
  exact
    (map_ne_zero_iff
      (algebraMap W (ChartLocalRing25Two A))
      (IsLocalization.injective
        (ChartLocalRing25Two A)
        (fullNonBoundaryPrimeIdeal A).primeCompl_le_nonZeroDivisors)).mpr ha


/-- For a nonzero chart element, the local `Ring.ord` value is finite. -/
theorem chartLocalOrd_ne_top
    (A : FullNonBoundaryAtom25Two) {a : W} (ha : a ≠ 0) :
    Ring.ord (ChartLocalRing25Two A)
        (algebraMap W (ChartLocalRing25Two A) a) ≠ ⊤ := by
  letI : (fullNonBoundaryPrimeIdeal A).IsPrime :=
    (fullNonBoundaryPrimeData A).isMaximal.isPrime
  exact Ring.ord_ne_top
    (mem_nonZeroDivisors_of_ne_zero
      (algebraMap_chartLocalRing_ne_zero A ha))


/-- The nonnegative integer local order of a chart element.


The definition uses `Ring.ord : WithTop ℕ` and then `.toNat`.
All substantive uses below assume that the element is nonzero, so
`chartLocalOrd_ne_top` proves that no information is lost by `.toNat`. -/
noncomputable def localElementOrder
    (A : FullNonBoundaryAtom25Two) (a : W) : ℤ :=
  ((Ring.ord (ChartLocalRing25Two A)
      (algebraMap W (ChartLocalRing25Two A) a)).toNat : ℤ)


/-- Local element order is additive under multiplication of nonzero chart
elements. -/
theorem localElementOrder_mul
    (A : FullNonBoundaryAtom25Two)
    {a b : W} (ha : a ≠ 0) (hb : b ≠ 0) :
    localElementOrder A (a * b) =
      localElementOrder A a + localElementOrder A b := by
  letI : (fullNonBoundaryPrimeIdeal A).IsPrime :=
    (fullNonBoundaryPrimeData A).isMaximal.isPrime
  have hb' :
      algebraMap W (ChartLocalRing25Two A) b ∈
        nonZeroDivisors (ChartLocalRing25Two A) :=
    mem_nonZeroDivisors_of_ne_zero
      (algebraMap_chartLocalRing_ne_zero A hb)
  unfold localElementOrder
  rw [map_mul, Ring.ord_mul (ChartLocalRing25Two A) hb',
    ENat.toNat_add
      (chartLocalOrd_ne_top A ha)
      (chartLocalOrd_ne_top A hb)]
  norm_num


/-- The numerator-minus-denominator local order is independent of the
chosen fraction representation.


This is the representative-independence theorem requested in the question.
It uses only equality in the fraction ring, injectivity of the base map, and
multiplicativity of local `Ring.ord`; it does not use
`FractionalIdeal.count`. -/
theorem localElementOrder_sub_rep_independent
    (A : FullNonBoundaryAtom25Two)
    {n₁ n₂ : W}
    (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (d₁ d₂ : W⁰)
    (hrep :
      IsLocalization.mk' K n₁ d₁ =
        IsLocalization.mk' K n₂ d₂) :
    localElementOrder A n₁ - localElementOrder A (d₁ : W) =
      localElementOrder A n₂ - localElementOrder A (d₂ : W) := by
  have hd₁ : (d₁ : W) ≠ 0 :=
    nonZeroDivisors.ne_zero d₁.property
  have hd₂ : (d₂ : W) ≠ 0 :=
    nonZeroDivisors.ne_zero d₂.property
  have hcrossK :
      algebraMap W K (n₁ * (d₂ : W)) =
        algebraMap W K (n₂ * (d₁ : W)) :=
    (IsLocalization.mk'_eq_iff_eq').mp hrep
  have hcross :
      n₁ * (d₂ : W) = n₂ * (d₁ : W) :=
    (IsFractionRing.injective W K) hcrossK
  have hord := congrArg (localElementOrder A) hcross
  rw [localElementOrder_mul A hn₁ hd₂,
    localElementOrder_mul A hn₂ hd₁] at hord
  omega


/-! ## Global Dedekind multiplicity equals local Ring.ord -/


/-- The exponent of a nonzero principal ideal at the chosen global
height-one prime equals the local `Ring.ord` after localization.


This is the actual global/local algebra bridge.  Its proof goes through the
existing integer valuations, not through an assumed comparison theorem. -/
theorem globalFactorCount_eq_localElementOrder
    (A : FullNonBoundaryAtom25Two)
    {a : W} (ha : a ≠ 0) :
    ((Associates.mk
        (fullNonBoundaryAtomEquivHeightOne A).asIdeal).count
      (Associates.mk (Ideal.span {a} : Ideal W)).factors : ℤ) =
      localElementOrder A a := by
  classical


  let v : IsDedekindDomain.HeightOneSpectrum W :=
    fullNonBoundaryAtomEquivHeightOne A
  let P : Ideal W := fullNonBoundaryPrimeIdeal A


  have hP : P ≠ ⊥ := by
    dsimp [P]
    exact (fullNonBoundaryPrimeData A).ne_bot


  letI : P.IsPrime := by
    dsimp [P]
    exact (fullNonBoundaryPrimeData A).isMaximal.isPrime


  let O := Localization.AtPrime P


  letI : Module.IsTorsionFree W O :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (IsLocalization.injective O P.primeCompl_le_nonZeroDivisors)


  letI : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      W hP O


  let q : IsDedekindDomain.HeightOneSpectrum O :=
    IsDiscreteValuationRing.maximalIdeal O


  have hvP : v.asIdeal = P := by
    change
      (fullNonBoundaryAtomEquivHeightOne A).asIdeal =
        fullNonBoundaryPrimeIdeal A
    exact fullNonBoundaryAtomEquivHeightOne_asIdeal A


  letI : q.asIdeal.LiesOver v.asIdeal := by
    refine ⟨?_⟩
    change v.asIdeal =
      (IsLocalRing.maximalIdeal O).under W
    rw [Localization.AtPrime.under_maximalIdeal (I := P), hvP]


  /- Localization at the same height-one prime has ramification index one. -/
  have hram :
      v.asIdeal.ramificationIdx q.asIdeal = 1 := by
    rw [hvP]
    change
      P.ramificationIdx (IsLocalRing.maximalIdeal O) = 1
    rw [← Localization.AtPrime.map_eq_maximalIdeal (I := P)]
    apply Ideal.ramificationIdx_map_self_eq_one
    · rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
    · rw [Localization.AtPrime.map_eq_maximalIdeal]
      exact q.ne_bot


  let m : ℕ :=
    (Associates.mk v.asIdeal).count
      (Associates.mk (Ideal.span {a} : Ideal W)).factors


  /- The global Dedekind valuation of a is exp(-m). -/
  have hglobal :
      v.intValuation a = WithZero.exp (-(m : ℤ)) := by
    simpa [m] using v.intValuation_if_neg ha


  /- Transport that valuation to the local ring. -/
  have hlies :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_liesOver
      v q a
  rw [hram, pow_one] at hlies


  have hlocal :
      q.intValuation (algebraMap W O a) =
        WithZero.exp (-(m : ℤ)) :=
    hlies.symm.trans hglobal


  /- The valuation theorem is stated using the canonical DVR maximal
  ideal, while `hlocal` is spelled through the local alias `q`. -/
  have hlocal' :
      (IsDiscreteValuationRing.maximalIdeal O).intValuation
          (algebraMap W O a) =
        WithZero.exp (-(m : ℤ)) := by
    simpa only [q] using hlocal


  have hx : algebraMap W O a ≠ 0 := by
    exact
      (map_ne_zero_iff
        (algebraMap W O)
        (IsLocalization.injective O
          P.primeCompl_le_nonZeroDivisors)).mpr ha


  /- Ring.ord is the inverse of the local integer valuation. -/
  have hord :
      Ring.ordMonoidWithZeroHom O (algebraMap W O a) =
        WithZero.exp (m : ℤ) := by
    rw [Ring.ordMonoidWithZeroHom_eq_intValuation
      (mem_nonZeroDivisors_of_ne_zero hx), hlocal']
    simp


  /- Extract the finite natural value of Ring.ord. -/
  obtain ⟨n, hn⟩ :=
    ENat.ne_top_iff_exists.mp
      (Ring.ord_ne_top
        (mem_nonZeroDivisors_of_ne_zero hx))


  have hordn :=
    Ring.ordMonoidWithZeroHom_eq_coe
      (R := O)
      (mem_nonZeroDivisors_of_ne_zero hx)
      hn.symm


  have hnm : (n : ℤ) = (m : ℤ) := by
    apply WithZero.exp_injective
    calc
      WithZero.exp (n : ℤ) =
          Ring.ordMonoidWithZeroHom O
            (algebraMap W O a) := by
        simpa only [WithZero.exp_eq_coe_ofAdd] using hordn.symm
      _ = WithZero.exp (m : ℤ) := hord


  change (m : ℤ) = localElementOrder A a
  unfold localElementOrder
  change
    (m : ℤ) =
      ((Ring.ord O (algebraMap W O a)).toNat : ℤ)
  rw [← hn]
  simpa using hnm.symm


/-- For a nonzero regular chart element, the coefficient of its principal
fractional ideal is exactly the local `Ring.ord`. -/
theorem fractionalIdeal_count_spanSingleton_eq_localElementOrder
    (A : FullNonBoundaryAtom25Two)
    {a : W} (ha : a ≠ 0) :
    FractionalIdeal.count K
        (fullNonBoundaryAtomEquivHeightOne A)
        (FractionalIdeal.spanSingleton W⁰
          (algebraMap W K a)) =
      localElementOrder A a := by
  have hspan : (Ideal.span {a} : Ideal W) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  calc
    FractionalIdeal.count K
        (fullNonBoundaryAtomEquivHeightOne A)
        (FractionalIdeal.spanSingleton W⁰
          (algebraMap W K a)) =
      FractionalIdeal.count K
        (fullNonBoundaryAtomEquivHeightOne A)
        (↑(Ideal.span {a} : Ideal W) :
          FractionalIdeal W⁰ K) := by
        rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
      ((Associates.mk
          (fullNonBoundaryAtomEquivHeightOne A).asIdeal).count
        (Associates.mk (Ideal.span {a} : Ideal W)).factors : ℤ) := by
        exact
          FractionalIdeal.count_coe K
            (fullNonBoundaryAtomEquivHeightOne A) hspan
    _ = localElementOrder A a :=
      globalFactorCount_eq_localElementOrder A ha


/-! ## Arbitrary nonzero rational functions -/


/-- The global Dedekind coefficient of a represented nonzero fraction is
local numerator order minus local denominator order. -/
theorem fractionalIdeal_count_mk'_eq_localElementOrder_sub
    (A : FullNonBoundaryAtom25Two)
    {n : W} (hn : n ≠ 0) (d : W⁰) :
    FractionalIdeal.count K
        (fullNonBoundaryAtomEquivHeightOne A)
        (FractionalIdeal.spanSingleton W⁰
          (IsLocalization.mk' K n d)) =
      localElementOrder A n -
        localElementOrder A (d : W) := by
  classical


  have hd : (d : W) ≠ 0 :=
    nonZeroDivisors.ne_zero d.property


  have hdK : algebraMap W K (d : W) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _
      (IsFractionRing.injective W K) d.property


  have hI :
      FractionalIdeal.spanSingleton W⁰
          (IsLocalization.mk' K n d) ≠ 0 := by
    rw [FractionalIdeal.spanSingleton_ne_zero_iff,
      IsFractionRing.mk'_eq_div, ne_eq,
      div_eq_zero_iff, not_or]
    exact
      ⟨(map_ne_zero_iff
          (algebraMap W K)
          (IsFractionRing.injective W K)).mpr hn,
        hdK⟩


  have hrepI :
      FractionalIdeal.spanSingleton W⁰
          (IsLocalization.mk' K n d) =
        FractionalIdeal.spanSingleton W⁰
            ((algebraMap W K) (d : W))⁻¹ *
          (↑(Ideal.span {n} : Ideal W) :
            FractionalIdeal W⁰ K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]


  calc
    FractionalIdeal.count K
        (fullNonBoundaryAtomEquivHeightOne A)
        (FractionalIdeal.spanSingleton W⁰
          (IsLocalization.mk' K n d)) =
      ((Associates.mk
          (fullNonBoundaryAtomEquivHeightOne A).asIdeal).count
          (Associates.mk (Ideal.span {n} : Ideal W)).factors -
        (Associates.mk
          (fullNonBoundaryAtomEquivHeightOne A).asIdeal).count
          (Associates.mk
            (Ideal.span {(d : W)} : Ideal W)).factors : ℤ) :=
      FractionalIdeal.count_well_defined K
        (fullNonBoundaryAtomEquivHeightOne A) hI hrepI
    _ =
      localElementOrder A n -
        localElementOrder A (d : W) := by
      rw [globalFactorCount_eq_localElementOrder A hn,
        globalFactorCount_eq_localElementOrder A hd]


/-- The already-defined nonboundary principal-divisor coefficient equals
numerator local order minus denominator local order for every supplied
fraction representation. -/
theorem nonBoundaryPrincipalDivisor_apply_eq_localOrder_sub
    (A : FullNonBoundaryAtom25Two)
    (f : Additive Kˣ)
    {n : W} (hn : n ≠ 0) (d : W⁰)
    (hrep :
      IsLocalization.mk' K n d = (f.toMul : K)) :
    nonBoundaryPrincipalDivisor f A =
      localElementOrder A n -
        localElementOrder A (d : W) := by
  rw [nonBoundaryPrincipalDivisor_apply]
  change
    FractionalIdeal.count K
        (fullNonBoundaryAtomEquivHeightOne A)
        (FractionalIdeal.spanSingleton W⁰
          (f.toMul : K)) =
      localElementOrder A n -
        localElementOrder A (d : W)
  rw [← hrep]
  exact
    fractionalIdeal_count_mk'_eq_localElementOrder_sub
      A hn d


/-! ## A representation-independent local rational order -/


private noncomputable def chosenNumerator (x : K) : W :=
  Classical.choose (IsLocalization.exists_mk'_eq W⁰ x)


private noncomputable def chosenDenominator (x : K) : W⁰ :=
  Classical.choose
    (Classical.choose_spec
      (IsLocalization.exists_mk'_eq W⁰ x))


private theorem chosenRepresentation (x : K) :
    IsLocalization.mk' K
        (chosenNumerator x) (chosenDenominator x) = x :=
  Classical.choose_spec
    (Classical.choose_spec
      (IsLocalization.exists_mk'_eq W⁰ x))


private theorem chosenNumerator_ne_zero
    (f : Additive Kˣ) :
    chosenNumerator (f.toMul : K) ≠ 0 := by
  exact
    IsLocalization.ne_zero_of_mk'_ne_zero
      (S := K)
      (y := chosenDenominator (f.toMul : K))
      (by
        rw [chosenRepresentation]
        exact Units.ne_zero _)


/-- The integer local order of a nonzero rational function at a nonboundary
closed point, defined purely from local `Ring.ord` by one chosen
numerator/denominator representation.


The next theorem proves that the value is independent of that choice. -/
noncomputable def localFractionOrder
    (A : FullNonBoundaryAtom25Two)
    (f : Additive Kˣ) : ℤ :=
  localElementOrder A
      (chosenNumerator (f.toMul : K)) -
    localElementOrder A
      (chosenDenominator (f.toMul : K) : W)


/-- Every nonzero numerator/denominator representation computes the same
`localFractionOrder`.  This is the user-facing representative-independence
statement. -/
theorem localFractionOrder_eq_sub_of_rep
    (A : FullNonBoundaryAtom25Two)
    (f : Additive Kˣ)
    {n : W} (hn : n ≠ 0) (d : W⁰)
    (hrep :
      IsLocalization.mk' K n d = (f.toMul : K)) :
    localFractionOrder A f =
      localElementOrder A n -
        localElementOrder A (d : W) := by
  unfold localFractionOrder
  exact
    localElementOrder_sub_rep_independent
      A
      (chosenNumerator_ne_zero f) hn
      (chosenDenominator (f.toMul : K)) d
      ((chosenRepresentation (f.toMul : K)).trans hrep.symm)


/-- Main bridge: the affine Dedekind principal-divisor coefficient at every
nonboundary full closed point is exactly its representation-independent
integer local order. -/
theorem nonBoundaryPrincipalDivisor_apply_eq_localFractionOrder
    (A : FullNonBoundaryAtom25Two)
    (f : Additive Kˣ) :
    nonBoundaryPrincipalDivisor f A =
      localFractionOrder A f := by
  unfold localFractionOrder
  exact
    nonBoundaryPrincipalDivisor_apply_eq_localOrder_sub
      A f
      (chosenNumerator_ne_zero f)
      (chosenDenominator (f.toMul : K))
      (chosenRepresentation (f.toMul : K))


end MazurProof.N25F_ChartLocalOrder


namespace MazurProof.N25F_ChartLocalOrder

open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open N25F_NonBoundaryPrincipalDivisor

/-- A nonzero chart element has local order zero exactly when it avoids
the prime attached to the nonboundary atom. -/
theorem localElementOrder_eq_zero_iff_not_mem
    (A : FullNonBoundaryAtom25Two) {a : W} (ha : a ≠ 0) :
    localElementOrder A a = 0 ↔
      a ∉ fullNonBoundaryPrimeIdeal A := by
  letI : (fullNonBoundaryPrimeIdeal A).IsPrime :=
    (fullNonBoundaryPrimeData A).isMaximal.isPrime
  have hfinite := chartLocalOrd_ne_top A ha
  calc
    localElementOrder A a = 0 ↔
        Ring.ord (ChartLocalRing25Two A)
          (algebraMap W (ChartLocalRing25Two A) a) = 0 := by
      simp only [localElementOrder, Int.ofNat_eq_zero,
        ENat.toNat_eq_zero, hfinite, or_false]
    _ ↔ IsUnit (algebraMap W (ChartLocalRing25Two A) a) := by
      rw [Ring.ord, Module.length_eq_zero_iff,
        Submodule.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]
    _ ↔ algebraMap W (ChartLocalRing25Two A) a ∉
        IsLocalRing.maximalIdeal (ChartLocalRing25Two A) :=
      IsLocalRing.notMem_maximalIdeal.symm
    _ ↔ a ∉ fullNonBoundaryPrimeIdeal A :=
      not_congr
        (IsLocalization.AtPrime.to_map_mem_maximal_iff
          (ChartLocalRing25Two A) (fullNonBoundaryPrimeIdeal A) a)

/-- The representation-independent local order sends the additive identity
to zero. -/
@[simp]
theorem localFractionOrder_zero
    (A : FullNonBoundaryAtom25Two) :
    localFractionOrder A (0 : Additive Kˣ) = 0 := by
  calc
    localFractionOrder A (0 : Additive Kˣ) =
        nonBoundaryPrincipalDivisor (0 : Additive Kˣ) A :=
      (nonBoundaryPrincipalDivisor_apply_eq_localFractionOrder
        A (0 : Additive Kˣ)).symm
    _ = 0 := by simp

/-- Local order is additive on the function-field units, written as an
additive group. -/
@[simp]
theorem localFractionOrder_add
    (A : FullNonBoundaryAtom25Two)
    (f g : Additive Kˣ) :
    localFractionOrder A (f + g) =
      localFractionOrder A f + localFractionOrder A g := by
  calc
    localFractionOrder A (f + g) =
        nonBoundaryPrincipalDivisor (f + g) A :=
      (nonBoundaryPrincipalDivisor_apply_eq_localFractionOrder
        A (f + g)).symm
    _ = nonBoundaryPrincipalDivisor f A +
        nonBoundaryPrincipalDivisor g A := by simp
    _ = localFractionOrder A f + localFractionOrder A g := by
      rw [nonBoundaryPrincipalDivisor_apply_eq_localFractionOrder A f,
        nonBoundaryPrincipalDivisor_apply_eq_localFractionOrder A g]

/-- Local order at one nonboundary closed point as an additive homomorphism
on function-field units. -/
noncomputable def localFractionOrderHom
    (A : FullNonBoundaryAtom25Two) :
    Additive Kˣ →+ ℤ where
  toFun := localFractionOrder A
  map_zero' := localFractionOrder_zero A
  map_add' := localFractionOrder_add A

@[simp]
theorem localFractionOrderHom_apply
    (A : FullNonBoundaryAtom25Two)
    (f : Additive Kˣ) :
    localFractionOrderHom A f = localFractionOrder A f :=
  rfl

end MazurProof.N25F_ChartLocalOrder
