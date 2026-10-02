import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Zero
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.CurveZetaEffectiveDivisors
structure ClosedPointGrading where
  Closed : ℕ → Type*
  finite_closed : ∀ d, Finite (Closed d)
  empty_degree_zero : IsEmpty (Closed 0)

namespace ClosedPointGrading
variable (C : ClosedPointGrading)
abbrev Atom := Σ d : ℕ, C.Closed d

/-- The residue degree of a graded closed point. -/
def atomDegree (x : C.Atom) : ℕ := x.1

abbrev Divisor := C.Atom →₀ ℤ

/-- The integer degree of a signed divisor is the sum of each multiplicity
times the residue degree of its closed point. -/
def divisorDegree : C.Divisor →+ ℤ where
  toFun D := D.sum fun x m => m * (C.atomDegree x : ℤ)
  map_zero' := by simp
  map_add' D E := by
    classical
    exact Finsupp.sum_add_index' (by simp) (by
      intro x a b
      simp only [add_mul])

end ClosedPointGrading
end MazurProof.CurveZetaEffectiveDivisors

namespace MazurProof.N25F_RiemannRochSpace
open CurveZetaEffectiveDivisors
private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h


variable (C : ClosedPointGrading) {L : Type*} [Field L] [Algebra (ZMod 2) L]
variable (principal : Additive Lˣ →+ C.Divisor)
variable (hmin : ∀ f g h : Additive Lˣ,
  (h.toMul : L) = (f.toMul : L) + (g.toMul : L) → ∀ A,
    min (principal f A) (principal g A) ≤ principal h A)
variable (hzero : ∀ f : Additive Lˣ, C.divisorDegree (principal f) = 0)
/-- The actual F2-vector space of zero and rational functions whose poles
are bounded by D, using every full closed-point coefficient. -/
def fullRiemannRochSpace25Two (D : C.Divisor) : Submodule (ZMod 2) L where
  carrier := {f | f = 0 ∨ ∃ hf : f ≠ 0, ∀ A,
    0 ≤ D A + principal (Additive.ofMul (Units.mk0 f hf)) A}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    rcases hf with hf | ⟨hf0, hf⟩
    · subst f
      simpa only [zero_add] using hg
    rcases hg with hg | ⟨hg0, hg⟩
    · subst g
      simp only [add_zero]
      exact Or.inr ⟨hf0, hf⟩
    by_cases hs : f + g = 0
    · exact Or.inl hs
    refine Or.inr ⟨hs, ?_⟩
    intro A
    have hm := hmin
      (Additive.ofMul (Units.mk0 f hf0)) (Additive.ofMul (Units.mk0 g hg0))
      (Additive.ofMul (Units.mk0 (f + g) hs)) rfl A
    have hfa := hf A
    have hga := hg A
    have hl : -D A ≤ min
        (principal (Additive.ofMul (Units.mk0 f hf0)) A)
        (principal (Additive.ofMul (Units.mk0 g hg0)) A) :=
      le_min (by omega) (by omega)
    have hfinal := hl.trans hm
    omega
  smul_mem' := by
    intro a f hf
    rcases zmod_two_cases a with rfl | rfl
    · simp only [zero_smul]
      exact Or.inl rfl
    · simpa only [one_smul] using hf

@[simp]
theorem mem_fullRiemannRochSpace25Two (D : C.Divisor) (f : L) :
    f ∈ fullRiemannRochSpace25Two C principal hmin D ↔ f = 0 ∨ ∃ hf : f ≠ 0, ∀ A,
      0 ≤ D A + principal (Additive.ofMul (Units.mk0 f hf)) A := Iff.rfl

include hzero in
/-- A nonzero bounded-pole function forces the bounding divisor's degree
to be nonnegative, by the genuine projective product formula. -/
theorem degree_nonneg_of_nonzero_mem (D : C.Divisor) (f : L)
    (hf : f ∈ fullRiemannRochSpace25Two C principal hmin D) (hne : f ≠ 0) :
    0 ≤ C.divisorDegree D := by
  rcases hf with hf | ⟨hf0, hb⟩
  · exact (hne hf).elim
  have hp := hzero (Additive.ofMul (Units.mk0 f hf0))
  have hd : 0 ≤ C.divisorDegree
      (D + principal (Additive.ofMul (Units.mk0 f hf0))) := by
    change 0 ≤ (D + principal (Additive.ofMul (Units.mk0 f hf0))).sum
      (fun A m => m * (C.atomDegree A : ℤ))
    apply Finsupp.sum_nonneg'
    intro A
    exact mul_nonneg (by simpa only [Finsupp.add_apply] using hb A) (Nat.cast_nonneg _)
  rw [map_add, hp, add_zero] at hd
  exact hd

include hzero in
/-- The actual Riemann--Roch space of a negative-degree full divisor is zero. -/
theorem fullRiemannRochSpace25Two_eq_bot_of_degree_neg (D : C.Divisor)
    (hD : C.divisorDegree D < 0) :
    fullRiemannRochSpace25Two C principal hmin D = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hne
  have hp := degree_nonneg_of_nonzero_mem C principal hmin hzero D f hf hne
  exact (not_le.mpr hD) hp


end MazurProof.N25F_RiemannRochSpace
open scoped nonZeroDivisors

open IsDedekindDomain

noncomputable section

namespace MazurProof.CurveDedekindDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A Weil divisor on the spectrum of a Dedekind domain is a finite integer
combination of its height-one prime ideals. -/
abbrev Divisor := HeightOneSpectrum R →₀ ℤ

/-- The height-one valuation vector of a fractional ideal.  The finite support
is supplied by Dedekind factorization. -/
def fractionalIdealDivisor (I : FractionalIdeal R⁰ K) : Divisor (R := R) := by
  let support : Set (HeightOneSpectrum R) :=
    {v | FractionalIdeal.count K v I ≠ 0}
  have hsupport : support.Finite := by
    exact Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K) I)
  exact Finsupp.onFinset hsupport.toFinset
    (fun v ↦ FractionalIdeal.count K v I)
    (fun v hv ↦ hsupport.mem_toFinset.mpr hv)

@[simp]
theorem fractionalIdealDivisor_apply (I : FractionalIdeal R⁰ K)
    (v : HeightOneSpectrum R) :
    fractionalIdealDivisor I v = FractionalIdeal.count K v I := by
  rfl

/-- Multiplication of nonzero fractional ideals adds their valuation vectors. -/
theorem fractionalIdealDivisor_mul {I J : FractionalIdeal R⁰ K}
    (hI : I ≠ 0) (hJ : J ≠ 0) :
    fractionalIdealDivisor (I * J) =
      fractionalIdealDivisor I + fractionalIdealDivisor J := by
  ext v
  simp only [fractionalIdealDivisor_apply, Finsupp.add_apply]
  exact FractionalIdeal.count_mul K v hI hJ

/-- Nonzero fractional ideals are determined by their height-one valuation
vectors.  This is the uniqueness half of Dedekind factorization in divisor
form. -/
theorem fractionalIdealDivisor_injectiveOn_nonzero
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hdiv : fractionalIdealDivisor I = fractionalIdealDivisor J) : I = J := by
  calc
    I = ∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ FractionalIdeal.count K v I :=
      (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
    _ = ∏ᶠ v : HeightOneSpectrum R,
        (v.asIdeal : FractionalIdeal R⁰ K) ^ FractionalIdeal.count K v J := by
      apply finprod_congr
      intro v
      congr 1
      simpa only [fractionalIdealDivisor_apply] using DFunLike.congr_fun hdiv v
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ

/-- Principal fractional ideals define an additive homomorphism from nonzero
functions under multiplication to height-one divisors. -/
def principalDivisor : Additive Kˣ →+ Divisor (R := R) where
  toFun x := fractionalIdealDivisor
    (FractionalIdeal.spanSingleton R⁰ (x.toMul : K))
  map_zero' := by
    ext v
    change FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ (1 : K)) = 0
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]
  map_add' x y := by
    change fractionalIdealDivisor
      (FractionalIdeal.spanSingleton R⁰ ((x.toMul * y.toMul : Kˣ) : K)) = _
    rw [Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply fractionalIdealDivisor_mul
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.toMul.ne_zero
    · exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.toMul.ne_zero

/-- The subgroup generated by divisors of nonzero fraction-field elements. -/
def principalDivisors : AddSubgroup (Divisor (R := R)) :=
  (principalDivisor (R := R) (K := K)).range

end MazurProof.CurveDedekindDivisor
/-! Exact affine integrality and ideal membership from all genuine Dedekind orders. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped nonZeroDivisors
namespace MazurProof.N25F_DedekindOrderMembership
open CurveDedekindDivisor

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Nonnegative coefficients force a genuine fractional ideal to be integral. -/
theorem fractionalIdeal_le_one_of_count_nonneg (I : FractionalIdeal R⁰ K) (hI : I ≠ 0)
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K v I) :
    I ≤ 1 := by
  classical
  let d := fractionalIdealDivisor I
  let J : FractionalIdeal R⁰ K := d.prod fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m
  have hJ : J ≠ 0 := by
    apply Finsupp.prod_ne_zero_iff.mpr
    intro v hv
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have he : I = J := by
    apply fractionalIdealDivisor_injectiveOn_nonzero hI hJ
    ext v
    exact (FractionalIdeal.count_finsuppProd K v d).symm
  rw [he]
  change d.prod (fun v m => (v.asIdeal : FractionalIdeal R⁰ K) ^ m) ≤ 1
  rw [Finsupp.prod]
  apply Finset.prod_le_one'
  intro v hv
  have hd : 0 ≤ d v := hc v
  have hn : d v = ((d v).toNat : ℤ) := (Int.natCast_toNat_eq_self.mpr hd).symm
  rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

/-- The converse to order monotonicity, proved from actual fractional-ideal factorization. -/
theorem fractionalIdeal_le_of_count_le (I J : FractionalIdeal R⁰ K)
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) : I ≤ J := by
  have hprod : I * J⁻¹ ≤ 1 :=
    fractionalIdeal_le_one_of_count_nonneg _ (mul_ne_zero hI (inv_ne_zero hJ)) (by
      intro v
      rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
      exact sub_nonneg.mpr (hc v))
  have h := mul_le_mul_right' hprod J
  simpa only [mul_assoc, inv_mul_cancel₀ hJ, mul_one, one_mul] using h

/-- All nonnegative affine orders recover a unique real element of the original ring. -/
theorem existsUnique_algebraMap_eq_of_count_nonneg (f : K)
    (hc : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ f)) :
    ∃! a : R, algebraMap R K a = f := by
  have hex : ∃ a : R, algebraMap R K a = f := by
    by_cases hf : f = 0
    · exact ⟨0, by rw [map_zero, hf]⟩
    apply (FractionalIdeal.mem_one_iff R⁰).mp
    exact fractionalIdeal_le_one_of_count_nonneg _
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) hc
      (FractionalIdeal.mem_spanSingleton_self R⁰ f)
  obtain ⟨a, ha⟩ := hex
  exact ⟨a, ha, fun b hb => IsFractionRing.injective R K (hb.trans ha.symm)⟩

/-- Membership in a genuine nonzero fractional ideal is exactly the full set of order inequalities. -/
theorem mem_fractionalIdeal_iff_count_le (I : FractionalIdeal R⁰ K) (hI : I ≠ 0)
    (f : K) (hf : f ≠ 0) : f ∈ I ↔
      ∀ v : IsDedekindDomain.HeightOneSpectrum R,
        FractionalIdeal.count K v I ≤
          FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ f) := by
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  constructor
  · intro h v
    exact FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) h
  · exact fractionalIdeal_le_of_count_le _ I (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hf) hI

end MazurProof.N25F_DedekindOrderMembership


namespace MazurProof.N25F_WRegularSectionLift
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_DedekindOrderMembership
inductive Boundary | X | YZ | Z
variable (C : ClosedPointGrading)
def IsBoundary (boundaryAtom : Boundary → C.Atom) (a : C.Atom) : Prop := ∃ t, boundaryAtom t = a
abbrev NonBoundary (boundaryAtom : Boundary → C.Atom) := {a : C.Atom // ¬ IsBoundary C boundaryAtom a}
theorem boundary_isBoundary (b : Boundary → C.Atom) (t : Boundary) :
  IsBoundary C b (b t) := ⟨t, rfl⟩
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra (ZMod 2) S]
variable (principal : Additive ((FractionRing S)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing S)ˣ),
  (h.toMul : FractionRing S) = (f.toMul : FractionRing S) + (g.toMul : FractionRing S) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (boundaryAtom : Boundary → C.Atom)
variable (e : NonBoundary C boundaryAtom ≃ IsDedekindDomain.HeightOneSpectrum S)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (e a))
def basePoleDivisor : C.Divisor :=
  Finsupp.single (boundaryAtom .X) 1 + Finsupp.single (boundaryAtom .YZ) 1 +
    Finsupp.single (boundaryAtom .Z) 2
private theorem basePoleDivisor_nonBoundary (A : NonBoundary C boundaryAtom) :
    (basePoleDivisor C boundaryAtom) A.1 = 0 := by
  have hn (t : Boundary) : boundaryAtom t ≠ A.1 := by
    intro h
    exact A.2 (h ▸ boundary_isBoundary C boundaryAtom t)
  simp [basePoleDivisor, Ne.symm (hn .X), Ne.symm (hn .YZ), Ne.symm (hn .Z)]

include haff in
/-- Every genuine nH section has a unique actual S-chart representative. -/
theorem existsUnique_wChart_lift_of_mem_basePole_space (n : ℕ) (f : (FractionRing S))
    (hf : f ∈ fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) :
    ∃! a : S, algebraMap S (FractionRing S) a = f := by
  apply existsUnique_algebraMap_eq_of_count_nonneg
  intro v
  rcases hf with rfl | ⟨hf, hb⟩
  · simp only [FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero, le_refl]
  let A := e.symm v
  have h := hb A.1
  rw [Finsupp.smul_apply, smul_eq_mul, basePoleDivisor_nonBoundary C boundaryAtom A, mul_zero, zero_add,
    haff _ A] at h
  change 0 ≤ FractionalIdeal.count (FractionRing S) (e A)
    (FractionalIdeal.spanSingleton S⁰ f) at h
  simpa only [A, Equiv.apply_symm_apply] using h

/-- The uniquely recovered actual regular S-chart element. -/
def wRegularSectionLift25Two (n : ℕ)
    (f : fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) : S :=
  Classical.choose (existsUnique_wChart_lift_of_mem_basePole_space C S principal hmin boundaryAtom e haff n f.1 f.2)

@[simp]
theorem algebraMap_wRegularSectionLift25Two (n : ℕ)
    (f : fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) :
    algebraMap S (FractionRing S) (wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f) = (f : (FractionRing S)) :=
  (Classical.choose_spec (existsUnique_wChart_lift_of_mem_basePole_space C S principal hmin boundaryAtom e haff n f.1 f.2)).1

private theorem wRegularSectionLift_zero (n : ℕ) : wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n 0 = 0 := by
  apply IsFractionRing.injective S (FractionRing S)
  rw [algebraMap_wRegularSectionLift25Two C S principal hmin boundaryAtom e haff, map_zero]
  rfl

private theorem wRegularSectionLift_add (n : ℕ)
    (f g : fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) :
    wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n (f + g) = wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f + wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n g := by
  apply IsFractionRing.injective S (FractionRing S)
  simp only [map_add, algebraMap_wRegularSectionLift25Two C S principal hmin boundaryAtom e haff, Submodule.coe_add]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have hc : a.val = 0 ∨ a.val = 1 := by omega
  rcases hc with h | h
  · left
    apply ZMod.val_injective 2
    simpa using h
  · right
    apply ZMod.val_injective 2
    simpa only [ZMod.val_one_eq_one_mod] using h

/-- Recovery of the actual affine representative is F2-linear. -/
def wRegularSectionLiftLinearMap25Two (n : ℕ) :
    fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom)) →ₗ[ZMod 2] S where
  toFun := wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n
  map_add' := wRegularSectionLift_add C S principal hmin boundaryAtom e haff n
  map_smul' r f := by
    rcases zmod_two_cases r with rfl | rfl
    · simp only [zero_smul, wRegularSectionLift_zero C S principal hmin boundaryAtom e haff, map_zero]
    · simp only [map_one, one_smul]

theorem wRegularSectionLiftLinearMap25Two_injective (n : ℕ) :
    Function.Injective (wRegularSectionLiftLinearMap25Two C S principal hmin boundaryAtom e haff n) := by
  intro f g h
  apply Subtype.ext
  have he := congrArg (algebraMap S (FractionRing S)) h
  change algebraMap S (FractionRing S) (wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f) =
    algebraMap S (FractionRing S) (wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n g) at he
  simpa only [algebraMap_wRegularSectionLift25Two C S principal hmin boundaryAtom e haff] using he

end MazurProof.N25F_WRegularSectionLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace MazurProof.DedekindQuotientDegree

open UniqueFactorizationMonoid

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

/-- A nonzero ideal's quotient dimension is the sum of its factor multiplicities
weighted by the actual finite-field residue dimensions. -/
theorem finrank_quotient_eq_sum_factors (k : Type*) [Field k] [Finite k]
    [Algebra k S] (I : Ideal S) (hI : I ≠ ⊥) [Module.Finite k (S ⧸ I)] :
    Module.finrank k (S ⧸ I) =
      ∑ P ∈ (factors I).toFinset,
        (factors I).count P * Module.finrank k (S ⧸ P) := by
  classical
  haveI : Finite (S ⧸ I) := Module.finite_of_finite k
  apply Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card k)
  dsimp only
  rw [← Module.natCard_eq_pow_finrank]
  calc
    Nat.card (S ⧸ I) =
        Nat.card (∀ P : (factors I).toFinset,
          S ⧸ (P : Ideal S) ^ (factors I).count (P : Ideal S)) :=
      Nat.card_congr (IsDedekindDomain.quotientEquivPiFactors hI).toEquiv
    _ = ∏ P : (factors I).toFinset,
        Nat.card (S ⧸ (P : Ideal S) ^ (factors I).count (P : Ideal S)) := Nat.card_pi
    _ = ∏ P : (factors I).toFinset,
        Nat.card k ^ ((factors I).count (P : Ideal S) *
          Module.finrank k (S ⧸ (P : Ideal S))) := by
      apply Finset.prod_congr rfl
      intro P _
      have hmem : (P : Ideal S) ∈ factors I := Multiset.mem_toFinset.mp P.property
      have hprime : Prime (P : Ideal S) := prime_of_factor _ hmem
      haveI : (P : Ideal S).IsPrime := Ideal.isPrime_of_prime hprime
      have hle : I ≤ (P : Ideal S) := Ideal.dvd_iff_le.mp (dvd_of_mem_factors hmem)
      haveI : Finite (S ⧸ (P : Ideal S)) :=
        Finite.of_surjective (Ideal.Quotient.factor hle)
          (Ideal.Quotient.factor_surjective hle)
      calc
        Nat.card (S ⧸ (P : Ideal S) ^ (factors I).count (P : Ideal S)) =
            Nat.card (S ⧸ (P : Ideal S)) ^ (factors I).count (P : Ideal S) :=
          cardQuot_pow_of_prime hprime.ne_zero
        _ = Nat.card k ^ ((factors I).count (P : Ideal S) *
            Module.finrank k (S ⧸ (P : Ideal S))) := by
          rw [Module.natCard_eq_pow_finrank (K := k), ← pow_mul, Nat.mul_comm]
    _ = Nat.card k ^ (∑ P : (factors I).toFinset,
        (factors I).count (P : Ideal S) * Module.finrank k (S ⧸ (P : Ideal S))) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = Nat.card k ^ (∑ P ∈ (factors I).toFinset,
        (factors I).count P * Module.finrank k (S ⧸ P)) := by
      exact congrArg (fun n : ℕ => Nat.card k ^ n)
        ((factors I).toFinset.sum_coe_sort
          (fun P => (factors I).count P * Module.finrank k (S ⧸ P)))

/-- The normalized-factor version uses exactly the canonical multiplicities
appearing in Dedekind valuations. -/
theorem finrank_quotient_eq_sum_normalizedFactors (k : Type*) [Field k] [Finite k]
    [Algebra k S] (I : Ideal S) (hI : I ≠ ⊥) [Module.Finite k (S ⧸ I)] :
    Module.finrank k (S ⧸ I) =
      ∑ P ∈ (normalizedFactors I).toFinset,
        (normalizedFactors I).count P * Module.finrank k (S ⧸ P) := by
  simpa only [factors_eq_normalizedFactors] using finrank_quotient_eq_sum_factors k I hI

end MazurProof.DedekindQuotientDegree

namespace MazurProof.N25F_WAffineConditionCost
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace N25F_WRegularSectionLift N25F_DedekindOrderMembership
open scoped nonZeroDivisors BigOperators
variable (C : ClosedPointGrading)
variable (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra (ZMod 2) S]
  [Algebra.FiniteType (ZMod 2) S]
variable (principal : Additive ((FractionRing S)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing S)ˣ),
  (h.toMul : FractionRing S) = (f.toMul : FractionRing S) + (g.toMul : FractionRing S) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (boundaryAtom : Boundary → C.Atom)
variable (e : NonBoundary C boundaryAtom ≃ IsDedekindDomain.HeightOneSpectrum S)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (e a))
variable (hfinite : ∀ n : ℕ, Module.Finite (ZMod 2)
  (fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))))
/-- The real affine conditions map, using recovered S elements and the actual ideal quotient. -/
def wSectionIdealQuotient25Two (n : ℕ) (I : Ideal S) :
    fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom)) →ₗ[ZMod 2] S ⧸ I :=
  (Ideal.Quotient.mkₐ (ZMod 2) I).toLinearMap.comp (wRegularSectionLiftLinearMap25Two C S principal hmin boundaryAtom e haff n)

theorem wSectionIdealQuotient25Two_eq_zero_iff (n : ℕ) (I : Ideal S)
    (f : fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) :
    wSectionIdealQuotient25Two C S principal hmin boundaryAtom e haff n I f = 0 ↔ wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f ∈ I := by
  change Ideal.Quotient.mk I (wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The actual kernel imposes exactly all affine ideal-order inequalities, with zero handled honestly. -/
theorem wSectionIdealQuotient25Two_eq_zero_iff_orders (n : ℕ) (I : Ideal S) (hI : I ≠ ⊥)
    (f : fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) :
    wSectionIdealQuotient25Two C S principal hmin boundaryAtom e haff n I f = 0 ↔
      (f : (FractionRing S)) = 0 ∨ ∀ v : IsDedekindDomain.HeightOneSpectrum S,
        FractionalIdeal.count (FractionRing S) v (I : FractionalIdeal S⁰ (FractionRing S)) ≤
          FractionalIdeal.count (FractionRing S) v (FractionalIdeal.spanSingleton S⁰ (f : (FractionRing S))) := by
  rw [wSectionIdealQuotient25Two_eq_zero_iff C S principal hmin boundaryAtom e haff]
  have hmem : wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f ∈ I ↔ (f : (FractionRing S)) ∈ (I : FractionalIdeal S⁰ (FractionRing S)) := by
    constructor
    · intro h
      exact (FractionalIdeal.mem_coeIdeal S⁰).mpr
        ⟨wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f, h, algebraMap_wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f⟩
    · intro h
      obtain ⟨a, ha, he⟩ := (FractionalIdeal.mem_coeIdeal S⁰).mp h
      have hEq : a = wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f :=
        IsFractionRing.injective S (FractionRing S) (he.trans (algebraMap_wRegularSectionLift25Two C S principal hmin boundaryAtom e haff n f).symm)
      exact hEq ▸ ha
  rw [hmem]
  by_cases hf : (f : (FractionRing S)) = 0
  · simp [hf]
  rw [or_iff_right hf]
  exact mem_fractionalIdeal_iff_count_le _ (FractionalIdeal.coeIdeal_ne_zero.mpr hI) _ hf

private theorem wIdealQuotient_finite (I : Ideal S) (hI : I ≠ ⊥) :
    Module.Finite (ZMod 2) (S ⧸ I) := by
  apply (Module.finite_iff_krullDimLE_zero (ZMod 2) (S ⧸ I)).2
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  exact hP.1.1.isMaximal (ne_bot_of_le_ne_bot hI hP.1.2)

include hfinite in
/-- Imposing the actual affine ideal costs at most the dimension of its real quotient algebra. -/
theorem finrank_basePole_le_kernel_add_ideal_quotient (n : ℕ) (I : Ideal S) (hI : I ≠ ⊥) :
    Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (wSectionIdealQuotient25Two C S principal hmin boundaryAtom e haff n I)) +
        Module.finrank (ZMod 2) (S ⧸ I) := by
  letI := wIdealQuotient_finite S I hI
  letI := hfinite n
  have hdim := (wSectionIdealQuotient25Two C S principal hmin boundaryAtom e haff n I).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (wSectionIdealQuotient25Two C S principal hmin boundaryAtom e haff n I))
  omega

include hfinite in
/-- The affine condition cost is the full residue-degree-weighted prime multiplicity sum. -/
theorem finrank_basePole_le_kernel_add_weighted_affine_cost (n : ℕ) (I : Ideal S) (hI : I ≠ ⊥) :
    Module.finrank (ZMod 2)
        (fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • (basePoleDivisor C boundaryAtom))) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (wSectionIdealQuotient25Two C S principal hmin boundaryAtom e haff n I)) +
        ∑ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset,
          (UniqueFactorizationMonoid.normalizedFactors I).count P *
            Module.finrank (ZMod 2) (S ⧸ P) := by
  letI := wIdealQuotient_finite S I hI
  have h := finrank_basePole_le_kernel_add_ideal_quotient C S principal hmin boundaryAtom e haff hfinite n I hI
  rwa [DedekindQuotientDegree.finrank_quotient_eq_sum_normalizedFactors (ZMod 2) I hI] at h

#print axioms wSectionIdealQuotient25Two
#print axioms wSectionIdealQuotient25Two_eq_zero_iff
#print axioms wSectionIdealQuotient25Two_eq_zero_iff_orders
#print axioms finrank_basePole_le_kernel_add_ideal_quotient
#print axioms finrank_basePole_le_kernel_add_weighted_affine_cost
end MazurProof.N25F_WAffineConditionCost
