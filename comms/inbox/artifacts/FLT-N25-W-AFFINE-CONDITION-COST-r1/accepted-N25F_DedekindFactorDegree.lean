import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.FieldTheory.Finiteness

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
