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


variable (p : Ideal R) (x y z : Ideal S) (hp : Prime p)
variable (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
variable (hnx : Ideal.relNorm R x = p) (hny : Ideal.relNorm R y = p) (hnz : Ideal.relNorm R z = p)
variable (hcomplete : ∀ Q : Ideal S, Q.IsPrime → Q.LiesOver p → Q = x ∨ Q = y ∨ Q = z)
include hp hxy hxz hyz hnx hny hnz hcomplete in
/-- Every prime's norm coefficient at (T) is its indicator among the
three actual centers; the off-fiber case uses the complete classification. -/
theorem infinity_prime_norm_multiplicity (Q : Ideal S) (hQ : Prime Q) :
    (normalizedFactors (Ideal.relNorm R Q)).count p =
      (normalizedFactors Q).count x + (normalizedFactors Q).count y +
        (normalizedFactors Q).count z := by
  classical
  letI : Q.IsPrime := Ideal.isPrime_of_prime hQ
  have hNQ : normalizedFactors Q = {Q} := by
    rw [normalizedFactors_irreducible hQ.irreducible, normalize_eq]
  have hNp : normalizedFactors p = {p} := by
    rw [normalizedFactors_irreducible hp.irreducible, normalize_eq]
  rw [hNQ]
  by_cases hx : Q = x
  · subst Q
    rw [hnx, hNp]
    simp [Ne.symm hxy, Ne.symm hxz]
  by_cases hy : Q = y
  · subst Q
    rw [hny, hNp]
    simp [hxy, Ne.symm hyz]
  by_cases hz : Q = z
  · subst Q
    rw [hnz, hNp]
    simp [hxz, hyz]
  have hunder : Q.under R ≠ p := by
    intro h
    letI : Q.LiesOver p := ⟨h.symm⟩
    rcases hcomplete Q inferInstance inferInstance with h | h | h
    · exact hx h
    · exact hy h
    · exact hz h
  rw [count_relNorm_prime_zero_of_under_ne Q hQ.ne_zero p hunder]
  simp [Ne.symm hx, Ne.symm hy, Ne.symm hz]

include hp hxy hxz hyz hnx hny hnz hcomplete in
/-- The coefficient of (T) in the relative norm of any nonzero actual
normalization ideal is the sum of its three genuine center multiplicities. -/
theorem infinity_relNorm_multiplicity (I : Ideal S) (hI : I ≠ ⊥) :
    (normalizedFactors (Ideal.relNorm R I)).count p =
      (normalizedFactors I).count x + (normalizedFactors I).count y +
        (normalizedFactors I).count z :=
  count_relNorm_sum_three_of_primes p x y z
    (infinity_prime_norm_multiplicity p x y z hp hxy hxz hyz hnx hny hnz hcomplete) I hI

#print axioms count_relNorm_prime_zero_of_under_ne
#print axioms count_relNorm_sum_three_of_primes
#print axioms infinity_prime_norm_multiplicity
#print axioms infinity_relNorm_multiplicity
end MazurProof.N25F_InfinityNormMultiplicity
