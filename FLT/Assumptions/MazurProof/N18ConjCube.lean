import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.GCD.Basic

/-!
# A UFD conjugate-product cube lemma

If `A * conj A` is a cube and conjugate prime factors are either associated
or separated in `A`, then `A` itself is a unit times a cube.
-/

set_option autoImplicit false

open UniqueFactorizationMonoid

namespace MazurProof.N18RouteC

/-- An element of a UFD whose normalized-prime multiplicities are all
divisible by three is a unit times a cube. -/
theorem unit_mul_cube_of_factorization_dvd
    {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] [DecidableEq R]
    {A : R} (hA : A ≠ 0)
    (hfac_dvd : ∀ p : R, 3 ∣ factorization A p) :
  ∃ eps : Rˣ, ∃ B : R, A = (eps : R) * B ^ 3 := by
  classical
  let fac : R →₀ ℕ := factorization A
  let rootFac : R →₀ ℕ :=
    Finsupp.mapRange (fun n : ℕ => n / 3) (by simp) fac
  have hthree_rootFac : (3 : ℕ) • rootFac = fac := by
    ext p
    simpa only [Finsupp.nsmul_apply, rootFac,
      Finsupp.mapRange_apply, Nat.nsmul_eq_mul, fac] using
      Nat.mul_div_cancel' (hfac_dvd p)
  let s : Multiset R := Finsupp.toMultiset rootFac
  have hroot_support : rootFac.support ⊆ fac.support := by
    dsimp [rootFac]
    exact Finsupp.support_mapRange
  have hsNF : ∀ p ∈ s, p ∈ normalizedFactors A := by
    intro p hp
    have hpRoot : p ∈ rootFac.support := by simpa [s] using hp
    have hpFac : p ∈ fac.support := hroot_support hpRoot
    simpa [fac] using hpFac
  have hsIrr : ∀ p ∈ s, Irreducible p := by
    intro p hp
    exact irreducible_of_normalized_factor p (hsNF p hp)
  have hsNorm : ∀ p ∈ s, normalize p = p := by
    intro p hp
    exact normalize_normalized_factor p (hsNF p hp)
  let B : R := s.prod
  have hB : B ≠ 0 := by
    dsimp [B]
    apply Multiset.prod_ne_zero
    intro hzero
    exact (hsIrr 0 hzero).ne_zero rfl
  have hnormB : normalizedFactors B = s := by
    calc
      normalizedFactors B = s.map normalize := by
        dsimp [B]
        exact normalizedFactors_prod_eq s hsIrr
      _ = s.map id := by
        apply Multiset.map_congr rfl
        intro p hp
        simpa using hsNorm p hp
      _ = s := by simp
  have hfacB : factorization B = rootFac := by
    change Multiset.toFinsupp (normalizedFactors B) = rootFac
    rw [hnormB]
    exact Finsupp.toMultiset_toFinsupp rootFac
  have hfacCube : factorization (B ^ 3) = factorization A := by
    calc
      factorization (B ^ 3) =
          (3 : ℕ) • factorization B := factorization_pow
      _ = (3 : ℕ) • rootFac := by rw [hfacB]
      _ = fac := hthree_rootFac
      _ = factorization A := rfl
  have hAssoc : Associated (B ^ 3) A :=
    associated_of_factorization_eq (B ^ 3) A
      (pow_ne_zero 3 hB) hA hfacCube
  rcases hAssoc with ⟨eps, heps⟩
  refine ⟨eps, B, ?_⟩
  calc
    A = B ^ 3 * (eps : R) := heps.symm
    _ = (eps : R) * B ^ 3 := mul_comm _ _

theorem unit_mul_cube_of_mul_conj_cube
    {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (conj : R ≃+* R) (hinv : Function.Involutive conj)
    {A M : R} (hA : A ≠ 0) (hEq : A * conj A = M ^ 3)
    (hsep : ∀ p : R, Irreducible p →
      (Associated p (conj p) ∨ ¬ (p ∣ A ∧ conj p ∣ A))) :
    ∃ eps : Rˣ, ∃ B : R, A = (eps : R) * B ^ 3 := by
  classical
  letI : NormalizationMonoid R :=
    UniqueFactorizationMonoid.normalizationMonoid

  have hconjA : conj A ≠ 0 := by
    intro h
    apply hA
    apply conj.injective
    simpa using h

  have hM : M ≠ 0 := by
    intro h
    have hz : A * conj A = 0 := by simpa [h] using hEq
    exact (mul_ne_zero hA hconjA) hz

  let fac : R →₀ ℕ := factorization A

  have hfac_dvd : ∀ p : R, 3 ∣ fac p := by
    intro p
    by_cases hp0 : fac p = 0
    · simp [hp0]

    have hpSupp : p ∈ fac.support := Finsupp.mem_support_iff.mpr hp0
    have hpNF : p ∈ normalizedFactors A := by simpa [fac] using hpSupp
    have hpPrime : Prime p := prime_of_normalized_factor p hpNF
    have hpIrr : Irreducible p := hpPrime.irreducible
    have hpNorm : normalize p = p := normalize_normalized_factor p hpNF
    have hpDivA : p ∣ A := dvd_of_mem_normalizedFactors hpNF

    have hfinProd : FiniteMultiplicity p (A * conj A) :=
      FiniteMultiplicity.of_prime_left hpPrime (mul_ne_zero hA hconjA)
    have hfinM : FiniteMultiplicity p M :=
      FiniteMultiplicity.of_prime_left hpPrime hM

    have hmul :
        multiplicity p A + multiplicity p (conj A) =
          3 * multiplicity p M := by
      calc
        multiplicity p A + multiplicity p (conj A) =
            multiplicity p (A * conj A) :=
          (multiplicity_mul hpPrime hfinProd).symm
        _ = multiplicity p (M ^ 3) := by rw [hEq]
        _ = 3 * multiplicity p M :=
          FiniteMultiplicity.multiplicity_pow hpPrime hfinM

    have hmap :
        multiplicity p (conj A) = multiplicity (conj p) A := by
      have h := multiplicity_map_eq conj (a := conj p) (b := A)
      simpa only [hinv p] using h

    have hfacEq : fac p = multiplicity p A := by
      change factorization A p = multiplicity p A
      rw [factorization_eq_count,
        multiplicity_eq_count_normalizedFactors hpIrr hA, hpNorm]

    rw [hfacEq]
    rcases hsep p hpIrr with hpSelf | hpSeparated
    · have hconjMult :
          multiplicity (conj p) A = multiplicity p A :=
        multiplicity_eq_of_associated_left hpSelf
      rw [hmap, hconjMult] at hmul
      have hthree_two : 3 ∣ 2 * multiplicity p A := by
        refine ⟨multiplicity p M, ?_⟩
        simpa [two_mul] using hmul
      exact (Nat.Coprime.dvd_mul_left
        (by decide : Nat.Coprime 3 2)).mp hthree_two
    · have hnotConj : ¬conj p ∣ A := by
        intro hpConj
        exact hpSeparated ⟨hpDivA, hpConj⟩
      have hzero : multiplicity (conj p) A = 0 :=
        multiplicity_eq_zero.mpr hnotConj
      rw [hmap, hzero, add_zero] at hmul
      exact ⟨multiplicity p M, hmul⟩

  let rootFac : R →₀ ℕ :=
    Finsupp.mapRange (fun n : ℕ => n / 3) (by simp) fac

  have hthree_rootFac : (3 : ℕ) • rootFac = fac := by
    ext p
    simpa only [Finsupp.nsmul_apply, rootFac,
      Finsupp.mapRange_apply, Nat.nsmul_eq_mul] using
      Nat.mul_div_cancel' (hfac_dvd p)

  let s : Multiset R := Finsupp.toMultiset rootFac

  have hroot_support : rootFac.support ⊆ fac.support := by
    dsimp [rootFac]
    exact Finsupp.support_mapRange

  have hsNF : ∀ p ∈ s, p ∈ normalizedFactors A := by
    intro p hp
    have hpRoot : p ∈ rootFac.support := by simpa [s] using hp
    have hpFac : p ∈ fac.support := hroot_support hpRoot
    simpa [fac] using hpFac

  have hsIrr : ∀ p ∈ s, Irreducible p := by
    intro p hp
    exact irreducible_of_normalized_factor p (hsNF p hp)

  have hsNorm : ∀ p ∈ s, normalize p = p := by
    intro p hp
    exact normalize_normalized_factor p (hsNF p hp)

  let B : R := s.prod

  have hB : B ≠ 0 := by
    dsimp [B]
    apply Multiset.prod_ne_zero
    intro hzero
    exact (hsIrr 0 hzero).ne_zero rfl

  have hnormB : normalizedFactors B = s := by
    calc
      normalizedFactors B = s.map normalize := by
        dsimp [B]
        exact normalizedFactors_prod_eq s hsIrr
      _ = s.map id := by
        apply Multiset.map_congr rfl
        intro p hp
        simpa using hsNorm p hp
      _ = s := by simp

  have hfacB : factorization B = rootFac := by
    change Multiset.toFinsupp (normalizedFactors B) = rootFac
    rw [hnormB]
    change Multiset.toFinsupp (Finsupp.toMultiset rootFac) = rootFac
    exact Finsupp.toMultiset_toFinsupp rootFac

  have hfacCube : factorization (B ^ 3) = factorization A := by
    calc
      factorization (B ^ 3) =
          (3 : ℕ) • factorization B := factorization_pow
      _ = (3 : ℕ) • rootFac := by rw [hfacB]
      _ = fac := hthree_rootFac
      _ = factorization A := rfl

  have hAssoc : Associated (B ^ 3) A :=
    associated_of_factorization_eq (B ^ 3) A
      (pow_ne_zero 3 hB) hA hfacCube

  rcases hAssoc with ⟨eps, heps⟩
  refine ⟨eps, B, ?_⟩
  calc
    A = B ^ 3 * (eps : R) := heps.symm
    _ = (eps : R) * B ^ 3 := mul_comm _ _

end MazurProof.N18RouteC
