import FLT.Assumptions.MazurProof.N25F_ThreeWChartDRegular
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Prime ideals on the characteristic-three N25 denominator open

Prime ideals of the localization of the actual W-chart at D correspond,
by contraction and extension, to prime ideals of the actual W-chart
which do not contain D.

This is a correspondence of all prime ideals. It is not an identification
of every prime with a closed-point atom.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ThreeWOpenPrimeEquiv

open N25F_ThreeWChartDRegular

/-- The denominator localization of the existing characteristic-three
W-chart. This is only an abbreviation for the standard localization. -/
abbrev WChartDLocalizationThree :=
  Localization.Away wChartDenominatorThree

/-- Prime ideals of the actual W-chart lying in its denominator open. -/
abbrev WChartPrimeAvoidingDThree :=
  {p : Ideal WChartQuotientThree //
    p.IsPrime ∧ wChartDenominatorThree ∉ p}

/-- For a prime ideal, avoiding D is equivalent to avoiding every power
of D. The exponent-zero case is included in `mem_of_pow_mem`. -/
theorem wChartPrime_disjoint_powers_iff_three
    (p : Ideal WChartQuotientThree) (hp : p.IsPrime) :
    Disjoint
        (Submonoid.powers wChartDenominatorThree : Set WChartQuotientThree)
        (p : Set WChartQuotientThree) ↔
      wChartDenominatorThree ∉ p := by
  constructor
  · intro hdisj hD
    exact (Set.disjoint_left.mp hdisj)
      (Submonoid.mem_powers wChartDenominatorThree) hD
  · intro hD
    refine Set.disjoint_left.mpr ?_
    intro x hx hxp
    rcases hx with ⟨n, rfl⟩
    exact hD (hp.mem_of_pow_mem n hxp)

/-- Change only the description of the prime-ideal subtype; the
underlying ideal and its inclusion order are unchanged. -/
private def primeDisjointPowersOrderIsoThree :
    {p : Ideal WChartQuotientThree //
      p.IsPrime ∧
        Disjoint
          (Submonoid.powers wChartDenominatorThree : Set WChartQuotientThree)
          (p : Set WChartQuotientThree)} ≃o
      WChartPrimeAvoidingDThree where
  toFun p :=
    ⟨p.1, p.2.1,
      (wChartPrime_disjoint_powers_iff_three p.1 p.2.1).mp p.2.2⟩
  invFun p :=
    ⟨p.1, p.2.1,
      (wChartPrime_disjoint_powers_iff_three p.1 p.2.1).mpr p.2.2⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl
  map_rel_iff' := by
    intro p q
    rfl

/-- The correspondence for any explicitly specified localization model
of the actual W-chart at the powers of its actual denominator. -/
def wOpenPrimeOrderIsoThreeOfIsLocalization
    (T : Type*) [CommRing T] [Algebra WChartQuotientThree T]
    [IsLocalization (Submonoid.powers wChartDenominatorThree) T] :
    {P : Ideal T // P.IsPrime} ≃o WChartPrimeAvoidingDThree :=
  (IsLocalization.orderIsoOfPrime
      (Submonoid.powers wChartDenominatorThree) T).trans
    primeDisjointPowersOrderIsoThree

/-- Prime ideals in the D-localization correspond, preserving inclusion,
to prime ideals in the actual W-chart which do not contain D. -/
def wOpenPrimeOrderIsoThree :
    {P : Ideal WChartDLocalizationThree // P.IsPrime} ≃o
      WChartPrimeAvoidingDThree :=
  wOpenPrimeOrderIsoThreeOfIsLocalization WChartDLocalizationThree

/-- The requested equivalence, with both prime-ideal subtypes explicit. -/
def wOpenPrimeEquivThree :
    {P : Ideal (Localization.Away wChartDenominatorThree) // P.IsPrime} ≃
      {p : Ideal WChartQuotientThree //
        p.IsPrime ∧ wChartDenominatorThree ∉ p} :=
  wOpenPrimeOrderIsoThree.toEquiv

/-- The forward map is contraction along the canonical localization map. -/
@[simp]
theorem wOpenPrimeOrderIsoThree_apply_val
    (P : {P : Ideal WChartDLocalizationThree // P.IsPrime}) :
    (wOpenPrimeOrderIsoThree P).1 =
      P.1.comap
        (algebraMap WChartQuotientThree WChartDLocalizationThree) := by
  rfl

/-- The inverse map is extension along the same localization map. -/
@[simp]
theorem wOpenPrimeOrderIsoThree_symm_apply_val
    (p : WChartPrimeAvoidingDThree) :
    (wOpenPrimeOrderIsoThree.symm p).1 =
      p.1.map
        (algebraMap WChartQuotientThree WChartDLocalizationThree) := by
  rfl

/-- Extension after contraction is the identity for every ideal upstairs,
not only for prime ideals. -/
theorem map_comap_wChartDLocalizationThree
    (J : Ideal WChartDLocalizationThree) :
    (J.comap
        (algebraMap WChartQuotientThree WChartDLocalizationThree)).map
        (algebraMap WChartQuotientThree WChartDLocalizationThree) = J := by
  exact IsLocalization.map_under
    (Submonoid.powers wChartDenominatorThree)
    WChartDLocalizationThree J

/-- Contraction after extension recovers a prime which avoids D. -/
theorem comap_map_wChartPrimeAvoidingDThree
    (p : WChartPrimeAvoidingDThree) :
    (p.1.map
        (algebraMap WChartQuotientThree WChartDLocalizationThree)).comap
        (algebraMap WChartQuotientThree WChartDLocalizationThree) = p.1 := by
  exact IsLocalization.under_map_of_isPrime_disjoint
    (Submonoid.powers wChartDenominatorThree)
    WChartDLocalizationThree p.2.1
    ((wChartPrime_disjoint_powers_iff_three p.1 p.2.1).mpr p.2.2)

/-- An original chart element belongs to the extended prime exactly when
it belonged to the original prime. -/
theorem algebraMap_mem_map_wChartPrimeAvoidingDThree
    (p : WChartPrimeAvoidingDThree) (a : WChartQuotientThree) :
    algebraMap WChartQuotientThree WChartDLocalizationThree a ∈
        p.1.map
          (algebraMap WChartQuotientThree WChartDLocalizationThree) ↔
      a ∈ p.1 := by
  change a ∈
      (p.1.map
        (algebraMap WChartQuotientThree WChartDLocalizationThree)).comap
        (algebraMap WChartQuotientThree WChartDLocalizationThree) ↔
    a ∈ p.1
  rw [comap_map_wChartPrimeAvoidingDThree]

/-- For an evaluation homomorphism, the denominator-open condition is
exactly nonvanishing of the evaluated denominator. -/
theorem wChartDenominatorThree_notMem_ker_iff
    {F : Type*} [CommRing F] (ev : WChartQuotientThree →+* F) :
    wChartDenominatorThree ∉ RingHom.ker ev ↔
      ev wChartDenominatorThree ≠ 0 := by
  simp only [RingHom.mem_ker]

/-! ## Separate use of the established full-quotient regularity -/

/-- Regularity of D implies that all localization denominators are
non-zero-divisors in the full W-chart quotient. -/
theorem wChartDenominatorThree_powers_le_nonZeroDivisors :
    Submonoid.powers wChartDenominatorThree ≤
      nonZeroDivisors WChartQuotientThree := by
  rintro a ⟨n, rfl⟩
  exact pow_mem wChartDenominatorThree_mem_nonZeroDivisors n

/-- The canonical localization map is injective. This is the place where
Q8344's full-quotient regularity is used; the prime correspondence above
does not need that regularity result. -/
theorem wChartDLocalizationThree_algebraMap_injective :
    Function.Injective
      (algebraMap WChartQuotientThree WChartDLocalizationThree) := by
  exact IsLocalization.injective WChartDLocalizationThree
    wChartDenominatorThree_powers_le_nonZeroDivisors

end MazurProof.N25F_ThreeWOpenPrimeEquiv
