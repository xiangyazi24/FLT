import FLT.Assumptions.MazurProof.N25F_InfinityPrimeNorms
import FLT.Assumptions.MazurProof.N25F_InfinityBoundaryAlgebras
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Lean.Elab.Tactic.Omega

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityNormMultiplicity
open UniqueFactorizationMonoid

section Generic
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

end Generic

open N25F_RationalBaseInversion N25F_InfinityNormalization
open N25F_InfinityBoundaryCenters N25F_InfinityPrimeContraction
open N25F_InfinityCenterDistinctness N25F_InfinityParameterOrders
open N25F_InfinityFiberComplete N25F_InfinityPrimeNorms N25F_InfinityBoundaryAlgebras
attribute [local instance] infinityPolynomialAlgebra
  xInfinityBaseAlgebra yzInfinityBaseAlgebra zInfinityBaseAlgebra
  xInfinityNormalizationAlgebra yzInfinityNormalizationAlgebra zInfinityNormalizationAlgebra

private theorem infinityBasePrime_ne_zero : infinityBasePrime ≠ 0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Polynomial.X_ne_zero (R := ZMod 2))

private theorem infinityBasePrime_prime : Prime infinityBasePrime :=
  Ideal.prime_of_isPrime infinityBasePrime_ne_zero inferInstance

/-- Every prime's norm coefficient at (T) is its indicator among the
three actual centers; the off-fiber case uses the complete classification. -/
theorem infinity_prime_norm_multiplicity (Q : Ideal InfinityNormalization) (hQ : Prime Q) :
    (normalizedFactors (Ideal.relNorm BasePolynomial Q)).count infinityBasePrime =
      (normalizedFactors Q).count xInfinityPrime + (normalizedFactors Q).count yzInfinityPrime +
        (normalizedFactors Q).count zInfinityPrime := by
  classical
  letI : Q.IsPrime := Ideal.isPrime_of_prime hQ
  have hNQ : normalizedFactors Q = {Q} := by
    rw [normalizedFactors_irreducible hQ.irreducible, normalize_eq]
  have hNp : normalizedFactors infinityBasePrime = {infinityBasePrime} := by
    rw [normalizedFactors_irreducible infinityBasePrime_prime.irreducible, normalize_eq]
  rw [hNQ]
  by_cases hx : Q = xInfinityPrime
  · subst Q
    rw [xInfinityPrime_relNorm, hNp]
    simp [Ne.symm xInfinityPrime_ne_yzInfinityPrime, Ne.symm xInfinityPrime_ne_zInfinityPrime]
  by_cases hy : Q = yzInfinityPrime
  · subst Q
    rw [yzInfinityPrime_relNorm, hNp]
    simp [xInfinityPrime_ne_yzInfinityPrime, Ne.symm yzInfinityPrime_ne_zInfinityPrime]
  by_cases hz : Q = zInfinityPrime
  · subst Q
    rw [zInfinityPrime_relNorm, hNp]
    simp [xInfinityPrime_ne_zInfinityPrime, yzInfinityPrime_ne_zInfinityPrime]
  have hunder : Q.under BasePolynomial ≠ infinityBasePrime := by
    intro h
    letI : Q.LiesOver infinityBasePrime := ⟨h.symm⟩
    rcases infinity_primesOver_complete Q with h | h | h
    · exact hx h
    · exact hy h
    · exact hz h
  rw [count_relNorm_prime_zero_of_under_ne Q hQ.ne_zero infinityBasePrime hunder]
  simp [Ne.symm hx, Ne.symm hy, Ne.symm hz]

/-- The coefficient of (T) in the relative norm of any nonzero actual
normalization ideal is the sum of its three genuine center multiplicities. -/
theorem infinity_relNorm_multiplicity (I : Ideal InfinityNormalization) (hI : I ≠ ⊥) :
    (normalizedFactors (Ideal.relNorm BasePolynomial I)).count infinityBasePrime =
      (normalizedFactors I).count xInfinityPrime + (normalizedFactors I).count yzInfinityPrime +
        (normalizedFactors I).count zInfinityPrime :=
  count_relNorm_sum_three_of_primes infinityBasePrime xInfinityPrime yzInfinityPrime zInfinityPrime
    infinity_prime_norm_multiplicity I hI

end MazurProof.N25F_InfinityNormMultiplicity
