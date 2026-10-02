import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finsupp.Order
import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.FractionRing
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

/-!
# Divisors from Dedekind-domain factorization

For a Dedekind domain, every nonzero fractional ideal has a finite height-one
valuation vector.  This file packages that vector as a `Finsupp`, proves that
it determines the fractional ideal, and constructs the subgroup of principal
divisors from nonzero elements of the fraction field.

This is the affine algebra underlying the divisor-class input used by the
curve zeta argument.  Applying it to a projective curve still requires the
geometric comparison between its closed points and height-one local data,
including the points outside any chosen affine chart.
-/

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

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped nonZeroDivisors

namespace MazurProof.DedekindQuotientDegree

variable {S : Type*} [CommRing S] [IsDedekindDomain S]
variable (K : Type*) [Field K] [Algebra S K] [IsFractionRing S K]

/-- The fractional-ideal valuation of a nonzero regular function is exactly
its principal ideal's normalized-factor multiplicity. -/
theorem count_spanSingleton_eq_normalizedFactors
    (a : S) (ha : a ≠ 0) (v : IsDedekindDomain.HeightOneSpectrum S) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton S⁰ (algebraMap S K a)) =
      ((UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({a} : Set S))).count v.asIdeal : ℤ) := by
  have hI : Ideal.span ({a} : Set S) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr ha
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]

end MazurProof.DedekindQuotientDegree
open scoped nonZeroDivisors BigOperators

namespace MazurProof.CurveDedekindDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The existing principal-divisor coefficient of a nonzero regular function
is its actual principal ideal's normalized-factor multiplicity. -/
theorem principalDivisor_regular_apply (a : R) (ha : a ≠ 0)
    (f : Additive Kˣ) (hf : (f.toMul : K) = algebraMap R K a)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    principalDivisor f v =
      ((UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({a} : Set R))).count v.asIdeal : ℤ) := by
  change FractionalIdeal.count K v
    (FractionalIdeal.spanSingleton R⁰ (f.toMul : K)) = _
  rw [hf]
  exact MazurProof.DedekindQuotientDegree.count_spanSingleton_eq_normalizedFactors K a ha v

end MazurProof.CurveDedekindDivisor

namespace MazurProof.N25F_WBasisPoleSections
open CurveZetaEffectiveDivisors N25F_RiemannRochSpace
inductive Boundary | X | YZ | Z
variable (C : ClosedPointGrading)
def IsBoundary (boundaryAtom : Boundary → C.Atom) (a : C.Atom) : Prop :=
  ∃ t, boundaryAtom t = a
abbrev NonBoundary (boundaryAtom : Boundary → C.Atom) :=
  {a : C.Atom // ¬ IsBoundary C boundaryAtom a}
theorem isBoundary_iff (b : Boundary → C.Atom) (a : C.Atom) :
  IsBoundary C b a ↔ ∃ t, b t = a := Iff.rfl
theorem boundary_isBoundary (b : Boundary → C.Atom) (t : Boundary) :
  IsBoundary C b (b t) := ⟨t, rfl⟩
variable (A : Type*) [CommRing A] [IsDedekindDomain A]
  [Algebra (Polynomial (ZMod 2)) A] [Algebra (ZMod 2) (FractionRing A)]
variable (principal : Additive ((FractionRing A)ˣ) →+ C.Divisor)
variable (hmin : ∀ f g h : Additive ((FractionRing A)ˣ),
  (h.toMul : FractionRing A) = (f.toMul : FractionRing A) + (g.toMul : FractionRing A) → ∀ a,
    min (principal f a) (principal g a) ≤ principal h a)
variable (boundaryAtom : Boundary → C.Atom)
variable (hbinj : Function.Injective boundaryAtom)
variable (hdegree : ∀ t, C.atomDegree (boundaryAtom t) = 1)
variable (xOrder yzOrder zOrder : Additive ((FractionRing A)ˣ) →+ ℤ)
variable (hxcoeff : ∀ f, principal f (boundaryAtom .X) = xOrder f)
variable (hyzcoeff : ∀ f, principal f (boundaryAtom .YZ) = yzOrder f)
variable (hzcoeff : ∀ f, principal f (boundaryAtom .Z) = zOrder f)
variable (prime : NonBoundary C boundaryAtom → IsDedekindDomain.HeightOneSpectrum A)
variable (haff : ∀ f a, principal f a.1 = CurveDedekindDivisor.principalDivisor f (prime a))
variable (basis : Module.Basis (Fin 4) (Polynomial (ZMod 2)) A)
def basisFunction (i : Fin 4) : Additive ((FractionRing A)ˣ) :=
  Additive.ofMul (Units.mk0 (algebraMap A (FractionRing A) (basis i))
    ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr (basis.ne_zero i)))
variable (B : ℕ)
variable (hbounded : ∀ i, -(B : ℤ) ≤ xOrder (basisFunction A basis i) ∧
  -(B : ℤ) ≤ yzOrder (basisFunction A basis i) ∧
  -(2 * (B : ℤ)) ≤ zOrder (basisFunction A basis i))
/-- The actual pole-weight divisor of the established base coordinate Z/A. -/
def basePoleDivisor25Two : C.Divisor :=
  Finsupp.single (boundaryAtom .X) 1 +
    Finsupp.single (boundaryAtom .YZ) 1 +
      Finsupp.single (boundaryAtom .Z) 2

include hdegree in
theorem basePoleDivisor25Two_degree :
    C.divisorDegree (basePoleDivisor25Two C boundaryAtom) = 4 := by
  simp [basePoleDivisor25Two, ClosedPointGrading.divisorDegree, hdegree]

include hbinj in
private theorem basePoleDivisor_apply_boundary (t : Boundary) :
    basePoleDivisor25Two C boundaryAtom (boundaryAtom t) =
      match t with | .X => 1 | .YZ => 1 | .Z => 2 := by
  cases t <;> simp [basePoleDivisor25Two, hbinj.eq_iff]

private theorem basePoleDivisor_apply_nonBoundary (A : NonBoundary C boundaryAtom) :
    basePoleDivisor25Two C boundaryAtom A.1 = 0 := by
  have hn (t : Boundary) : boundaryAtom t ≠ A.1 := by
    intro h
    exact A.2 (h ▸ boundary_isBoundary C boundaryAtom t)
  simp [basePoleDivisor25Two, Ne.symm (hn .X), Ne.symm (hn .YZ), Ne.symm (hn .Z)]

include hbinj hxcoeff hyzcoeff hzcoeff haff in
/-- An actual regular A function satisfying the three boundary bounds belongs
to the genuine full section space; no affine positivity premise is assumed. -/
theorem regular_function_mem_basePole_space (n : ℕ) (a : A) (ha : a ≠ 0)
    (f : Additive ((FractionRing A)ˣ)) (hf : (f.toMul : (FractionRing A)) = algebraMap A (FractionRing A) a)
    (hx : -(n : ℤ) ≤ xOrder f)
    (hyz : -(n : ℤ) ≤ yzOrder f)
    (hz : -(2 * (n : ℤ)) ≤ zOrder f) :
    (f.toMul : (FractionRing A)) ∈ fullRiemannRochSpace25Two C principal hmin ((n : ℤ) • basePoleDivisor25Two C boundaryAtom) := by
  classical
  refine Or.inr ⟨f.toMul.ne_zero, ?_⟩
  have hunit : Additive.ofMul (Units.mk0 (f.toMul : (FractionRing A)) f.toMul.ne_zero) = f := by
    apply Additive.toMul.injective
    exact Units.ext rfl
  intro A
  rw [hunit, Finsupp.smul_apply, smul_eq_mul]
  by_cases hA : IsBoundary C boundaryAtom A
  · obtain ⟨t, rfl⟩ := (isBoundary_iff C boundaryAtom A).mp hA
    rw [basePoleDivisor_apply_boundary C boundaryAtom hbinj]
    cases t with
    | X => rw [hxcoeff]; simp only [mul_one]; omega
    | YZ => rw [hyzcoeff]; simp only [mul_one]; omega
    | Z =>
        rw [hzcoeff]
        change 0 ≤ (n : ℤ) * 2 + zOrder f
        omega
  · let B : NonBoundary C boundaryAtom := ⟨A, hA⟩
    have hb : basePoleDivisor25Two C boundaryAtom A = 0 := basePoleDivisor_apply_nonBoundary C boundaryAtom B
    rw [hb, mul_zero, zero_add]
    rw [haff f B,
      CurveDedekindDivisor.principalDivisor_regular_apply a ha f hf]
    exact Int.natCast_nonneg _

include hbinj hxcoeff hyzcoeff hzcoeff haff hbounded in
/-- Every element of the one fixed polynomial basis lies in L(B H), with
one constant B independent of every divisor class or representative. -/
theorem wPolynomialBasis_mem_uniform_section_space (i : Fin 4) :
    algebraMap A (FractionRing A) (basis i) ∈
      fullRiemannRochSpace25Two C principal hmin
        ((B : ℤ) • basePoleDivisor25Two C boundaryAtom) := by
  obtain ⟨hx, hyz, hz⟩ := hbounded i
  exact regular_function_mem_basePole_space C A principal hmin boundaryAtom hbinj xOrder yzOrder zOrder hxcoeff hyzcoeff hzcoeff prime haff B
    (basis i) (basis.ne_zero i)
    (basisFunction A basis i) rfl hx hyz hz

#print axioms basePoleDivisor25Two
#print axioms basePoleDivisor25Two_degree
#print axioms regular_function_mem_basePole_space
#print axioms wPolynomialBasis_mem_uniform_section_space
end MazurProof.N25F_WBasisPoleSections
