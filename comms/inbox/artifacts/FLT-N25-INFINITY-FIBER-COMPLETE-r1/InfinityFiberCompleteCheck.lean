import InfinityNormalizationCheck
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityFiberComplete

/-- Three distinct positive-weight points with weights 1,1,2 exhaust a
finite fiber whose total weight is four. -/
theorem exhaustive_of_weights {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : w a = 1) (hb : w b = 1) (hc : w c = 2)
    (hpos : ∀ i, 0 < w i) (hsum : ∑ i, w i = 4) :
    ∀ i, i = a ∨ i = b ∨ i = c := by
  classical
  intro i
  by_contra hi
  have hia : i ≠ a := fun h => hi (Or.inl h)
  have hib : i ≠ b := fun h => hi (Or.inr (Or.inl h))
  have hic : i ≠ c := fun h => hi (Or.inr (Or.inr h))
  have hle : ∑ x ∈ ({i, a, b, c} : Finset ι), w x ≤ ∑ x, w x :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    hia, hib, hic, hab, hac, hbc, or_self, not_false_eq_true,
    Finset.sum_singleton, ha, hb, hc] at hle
  have hp := hpos i
  rw [hsum] at hle
  omega


open N25F_RationalBaseInversion N25F_InfinityBaseMaps N25F_InfinityNormalization
local notation "CurveField" => FractionRing N25F_NonBoundaryPrincipalDivisor.W
variable [Module.IsTorsionFree BasePolynomial N25F_NonBoundaryPrincipalDivisor.W]
variable [IsDedekindDomain N25F_NonBoundaryPrincipalDivisor.W]
attribute [local instance] infinityPolynomialAlgebra

/-- The reciprocal base embeds into its actual normalization. -/
theorem infinityNormalization_algebraMap_injective :
    Function.Injective (algebraMap BasePolynomial InfinityNormalization) := by
  intro p q h
  apply infinityBaseToField_injective
  have hh := congrArg (fun a : InfinityNormalization => (a : CurveField)) h
  change infinityBaseToField p = infinityBaseToField q at hh
  exact hh

instance infinityNormalization_isTorsionFree : Module.IsTorsionFree BasePolynomial InfinityNormalization :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr infinityNormalization_algebraMap_injective

/-- The actual finite normalization is flat over the reciprocal polynomial base. -/
instance infinityNormalization_flat : Module.Flat BasePolynomial InfinityNormalization := inferInstance

variable [Module.Finite BasePolynomial InfinityNormalization]
variable (infinityBasePrime : Ideal BasePolynomial) [infinityBasePrime.IsPrime]
variable (hRank : Module.finrank BasePolynomial InfinityNormalization = 4)
include hRank in
/-- The entire infinity fiber has ramification-inertia weight four. -/
theorem infinityFiber_sum [Fintype (infinityBasePrime.primesOver InfinityNormalization)] :
    ∑ q : infinityBasePrime.primesOver InfinityNormalization,
      q.1.ramificationIdx' BasePolynomial * q.1.inertiaDeg' BasePolynomial = 4 := by
  rw [Ideal.sum_ramification_inertia_eq_finrank, hRank]

variable (xInfinityPrime yzInfinityPrime zInfinityPrime : Ideal InfinityNormalization)
variable [xInfinityPrime.IsPrime] [yzInfinityPrime.IsPrime] [zInfinityPrime.IsPrime]
variable [xInfinityPrime.LiesOver infinityBasePrime] [yzInfinityPrime.LiesOver infinityBasePrime]
variable [zInfinityPrime.LiesOver infinityBasePrime]
variable (xInfinityPrime_ne_yzInfinityPrime : xInfinityPrime ≠ yzInfinityPrime)
variable (xInfinityPrime_ne_zInfinityPrime : xInfinityPrime ≠ zInfinityPrime)
variable (yzInfinityPrime_ne_zInfinityPrime : yzInfinityPrime ≠ zInfinityPrime)
variable (xInfinityPrime_ramificationIdx_eq_one : xInfinityPrime.ramificationIdx' BasePolynomial = 1)
variable (yzInfinityPrime_ramificationIdx_eq_one : yzInfinityPrime.ramificationIdx' BasePolynomial = 1)
variable (zInfinityPrime_ramificationIdx_eq_two : zInfinityPrime.ramificationIdx' BasePolynomial = 2)
variable (xInfinityPrime_inertiaDeg_eq_one : xInfinityPrime.inertiaDeg' BasePolynomial = 1)
variable (yzInfinityPrime_inertiaDeg_eq_one : yzInfinityPrime.inertiaDeg' BasePolynomial = 1)
variable (zInfinityPrime_inertiaDeg_eq_one : zInfinityPrime.inertiaDeg' BasePolynomial = 1)
include hRank xInfinityPrime_ne_yzInfinityPrime xInfinityPrime_ne_zInfinityPrime
  yzInfinityPrime_ne_zInfinityPrime xInfinityPrime_ramificationIdx_eq_one
  yzInfinityPrime_ramificationIdx_eq_one zInfinityPrime_ramificationIdx_eq_two
  xInfinityPrime_inertiaDeg_eq_one yzInfinityPrime_inertiaDeg_eq_one zInfinityPrime_inertiaDeg_eq_one in
/-- The three actual center primes exhaust the entire fiber above (T). -/
theorem infinity_primesOver_complete (q : Ideal InfinityNormalization)
    [q.IsPrime] [q.LiesOver infinityBasePrime] :
    q = xInfinityPrime ∨ q = yzInfinityPrime ∨ q = zInfinityPrime := by
  classical
  letI : Fintype (infinityBasePrime.primesOver InfinityNormalization) :=
    (Algebra.QuasiFinite.finite_primesOver (S := InfinityNormalization) infinityBasePrime).fintype
  let w : infinityBasePrime.primesOver InfinityNormalization → ℕ := fun p =>
    p.1.ramificationIdx' BasePolynomial * p.1.inertiaDeg' BasePolynomial
  let a := Ideal.primesOver.mk infinityBasePrime xInfinityPrime
  let b := Ideal.primesOver.mk infinityBasePrime yzInfinityPrime
  let c := Ideal.primesOver.mk infinityBasePrime zInfinityPrime
  have hab : a ≠ b := fun h => xInfinityPrime_ne_yzInfinityPrime (congrArg Subtype.val h)
  have hac : a ≠ c := fun h => xInfinityPrime_ne_zInfinityPrime (congrArg Subtype.val h)
  have hbc : b ≠ c := fun h => yzInfinityPrime_ne_zInfinityPrime (congrArg Subtype.val h)
  have ha : w a = 1 := by
    change xInfinityPrime.ramificationIdx' BasePolynomial * xInfinityPrime.inertiaDeg' BasePolynomial = 1
    rw [xInfinityPrime_ramificationIdx_eq_one, xInfinityPrime_inertiaDeg_eq_one]
  have hb : w b = 1 := by
    change yzInfinityPrime.ramificationIdx' BasePolynomial * yzInfinityPrime.inertiaDeg' BasePolynomial = 1
    rw [yzInfinityPrime_ramificationIdx_eq_one, yzInfinityPrime_inertiaDeg_eq_one]
  have hc : w c = 2 := by
    change zInfinityPrime.ramificationIdx' BasePolynomial * zInfinityPrime.inertiaDeg' BasePolynomial = 2
    rw [zInfinityPrime_ramificationIdx_eq_two, zInfinityPrime_inertiaDeg_eq_one]
  have hp : ∀ p, 0 < w p := fun p => Nat.mul_pos
    (Ideal.ramificationIdx'_pos p.1 BasePolynomial) (Ideal.inertiaDeg'_pos p.1 BasePolynomial)
  have hs : ∑ p, w p = 4 := infinityFiber_sum infinityBasePrime hRank
  rcases exhaustive_of_weights w a b c hab hac hbc ha hb hc hp hs
    (Ideal.primesOver.mk infinityBasePrime q) with h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (congrArg Subtype.val h))

#print axioms infinityNormalization_algebraMap_injective
#print axioms infinityNormalization_isTorsionFree
#print axioms infinityNormalization_flat
#print axioms infinityFiber_sum
#print axioms infinity_primesOver_complete
end MazurProof.N25F_InfinityFiberComplete
