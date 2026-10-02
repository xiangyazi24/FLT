import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Lean.Elab.Tactic.Omega

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityNormMultiplicity
open UniqueFactorizationMonoid

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S]

/-- A prime away from the chosen base prime contributes no factor there. -/
theorem count_relNorm_prime_zero_of_under_ne
    (Q : Ideal S) [Q.IsPrime] (hQ : Q ≠ ⊥) (p : Ideal R) (hunder : Q.under R ≠ p) :
    (normalizedFactors (Ideal.relNorm R Q)).count p = 0 := by
  classical
  obtain ⟨n, hn⟩ := Ideal.exists_relNorm_eq_pow_of_isPrime Q (Q.under R)
  have hp0 : Q.under R ≠ ⊥ := Ideal.under_ne_bot R hQ
  have hp : Prime (Q.under R) := Ideal.prime_of_isPrime hp0 inferInstance
  rw [hn, normalizedFactors_pow, normalizedFactors_irreducible hp.irreducible, normalize_eq]
  simp [Ne.symm hunder]

/-- Prime-wise norm coefficients extend to every nonzero ideal by actual
Dedekind factorization; the prime premise is discharged in the specialization. -/
theorem count_relNorm_sum_three_of_primes (p : Ideal R) (x y z : Ideal S)
    (hprime : ∀ Q : Ideal S, Prime Q →
      (normalizedFactors (Ideal.relNorm R Q)).count p =
        (normalizedFactors Q).count x + (normalizedFactors Q).count y +
          (normalizedFactors Q).count z)
    (I : Ideal S) (hI : I ≠ ⊥) :
    (normalizedFactors (Ideal.relNorm R I)).count p =
      (normalizedFactors I).count x + (normalizedFactors I).count y +
        (normalizedFactors I).count z := by
  classical
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h rfl).elim
  | h₂ I hu =>
      intro _
      simp [normalizedFactors_of_isUnit hu,
        normalizedFactors_of_isUnit (hu.map (Ideal.relNorm R))]
  | h₃ I Q hI hQ ih =>
      intro _
      have hNQ : Ideal.relNorm R Q ≠ 0 := Ideal.relNorm_eq_bot_iff.not.mpr hQ.ne_zero
      have hNI : Ideal.relNorm R I ≠ 0 := Ideal.relNorm_eq_bot_iff.not.mpr hI
      rw [map_mul, normalizedFactors_mul hNQ hNI, normalizedFactors_mul hQ.ne_zero hI]
      simp only [Multiset.count_add]
      rw [hprime Q hQ, ih hI]
      omega

#print axioms count_relNorm_prime_zero_of_under_ne
#print axioms count_relNorm_sum_three_of_primes
end MazurProof.N25F_InfinityNormMultiplicity
