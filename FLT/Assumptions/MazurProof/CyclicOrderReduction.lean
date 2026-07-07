import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic-order reduction for the Mazur scaffold

This file separates the prime-order input from the composite-order residuals.
The theorem `exists_point_of_prime_order_of_dvd` is the elementary group-theory
step: from a finite point of order `n`, every prime divisor of `n` occurs as the
order of a rational point.

The current definition `HasRationalPointOfOrder E n` is just
`∃ P, addOrderOf P = n`.  Since `addOrderOf P = 0` denotes infinite additive
order, divisor-to-prime reduction is only true with the finite-order guard
`n ≠ 0`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

def allowedPrimeOrders : Finset ℕ :=
  ({2, 3, 5, 7} : Finset ℕ)

def allowedCyclicOrders : Finset ℕ :=
  ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ)

/--
Prime-order Mazur input: a rational point of prime order can only have order
`2`, `3`, `5`, or `7`.
-/
axiom mazur_prime_torsion_bound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : Nat.Prime p)
    (hord : HasRationalPointOfOrder E p) :
    p ∈ ({2, 3, 5, 7} : Finset ℕ)

/--
If `P` has finite additive order `n` and `p ∣ n`, then `(n / p) • P` has
additive order `p`.
-/
theorem exists_point_of_prime_order_of_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n p : ℕ}
    (hn : n ≠ 0) (hp : Nat.Prime p) (hpn : p ∣ n)
    (hord : HasRationalPointOfOrder E n) :
    HasRationalPointOfOrder E p := by
  rcases hord with ⟨P, hP⟩
  refine ⟨(n / p) • P, ?_⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hp_le_n : p ≤ n := Nat.le_of_dvd hnpos hpn
  have hdiv_ne : n / p ≠ 0 := (Nat.div_pos hp_le_n hp.pos).ne'
  rw [addOrderOf_nsmul' P hdiv_ne, hP]
  rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpn), Nat.div_div_self hpn hn]

private theorem prime_ge_eleven_of_not_mem_allowed {p : ℕ}
    (hp : Nat.Prime p) (hpnot : p ∉ allowedPrimeOrders) :
    11 ≤ p := by
  by_contra hlt_not
  have hp2 : 2 ≤ p := hp.two_le
  have hlt : p < 11 := by omega
  interval_cases p <;> contradiction

/--
The prime-only axiom excludes any finite order `n` with a prime divisor
`p ≥ 11`.
-/
theorem not_has_point_of_order_of_large_prime_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n p : ℕ}
    (hn : n ≠ 0) (hp : Nat.Prime p) (hpn : p ∣ n) (hpge : 11 ≤ p) :
    ¬ HasRationalPointOfOrder E n := by
  intro hord
  have hpord : HasRationalPointOfOrder E p :=
    exists_point_of_prime_order_of_dvd E hn hp hpn hord
  have hmem := mazur_prime_torsion_bound E hp hpord
  simp [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

/--
Residual finite cyclic orders that the prime-only axiom does not decide:
`n` is above the Mazur cyclic list, is not in that list, and all prime divisors
of `n` are among `2`, `3`, `5`, and `7`.

Examples include `14`, `15`, `16`, `18`, `20`, `21`, and higher composites.
Each such case requires an additional composite-order exclusion, not just the
prime-order axiom.
-/
def NeedsCompositeExclusion (n : ℕ) : Prop :=
  12 < n ∧
    n ∉ allowedCyclicOrders ∧
    ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ allowedPrimeOrders

theorem needs_composite_exclusion_of_small_prime_factors {n : ℕ}
    (hgt : 12 < n)
    (hnot : n ∉ allowedCyclicOrders)
    (hprime : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ allowedPrimeOrders) :
    NeedsCompositeExclusion n :=
  ⟨hgt, hnot, hprime⟩

/--
Future composite-order input needed after the prime-only reduction.

This is deliberately a parameter, not a new axiom in this file: downstream
files can instantiate it by proving the required composite exclusions.
-/
def FutureCompositeExclusions : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ},
    n ≠ 0 →
    NeedsCompositeExclusion n →
    ¬ HasRationalPointOfOrder E n

/--
Partial reconstruction of Mazur's cyclic order list from the prime-order axiom
plus future composite exclusions.  The `n ≠ 0` guard is the finite-order guard
required by the current `HasRationalPointOfOrder` definition.
-/
theorem mazur_cyclic_order_bound_from_prime_and_composite_exclusions
    (hcomp : FutureCompositeExclusions)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : n ≠ 0)
    (hord : HasRationalPointOfOrder E n) :
    n ∈ allowedCyclicOrders := by
  by_contra hnot
  by_cases hle : n ≤ 12
  · have hn11 : n = 11 := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [allowedCyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hnot
      omega
    subst hn11
    have hmem := mazur_prime_torsion_bound E (p := 11) (by norm_num) hord
    norm_num at hmem
  · have hgt : 12 < n := by omega
    have hprime :
        ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ allowedPrimeOrders := by
      intro p hp hpn
      by_cases hpallowed : p ∈ allowedPrimeOrders
      · exact hpallowed
      · have hpge : 11 ≤ p := prime_ge_eleven_of_not_mem_allowed hp hpallowed
        exact False.elim
          ((not_has_point_of_order_of_large_prime_dvd E hn hp hpn hpge) hord)
    have hgap : NeedsCompositeExclusion n :=
      needs_composite_exclusion_of_small_prime_factors hgt hnot hprime
    exact False.elim ((hcomp E (n := n) hn hgap) hord)

/-- Short alias for the finite-order partial reconstruction. -/
theorem mazur_cyclic_order_bound_from_prime
    (hcomp : FutureCompositeExclusions)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : n ≠ 0)
    (hord : HasRationalPointOfOrder E n) :
    n ∈ allowedCyclicOrders :=
  mazur_cyclic_order_bound_from_prime_and_composite_exclusions hcomp E hn hord

end MazurProof
