import Mathlib
import FLT.Assumptions.MazurProof.Axioms

/-! # Axiom 2: Two Invariant Factor Decomposition

Theorem: If a finite abelian group G has:
  - 2-rank ≤ 2 (no (ℤ/2)³ injection)
  - odd prime p-rank ≤ 1 for all p > 2 (no (ZMod p)² injection)

Then G ≅ ℤ/m × ℤ/n for some m | n.

This is a Mathlib-backed proof using AddCommGroup.equiv_directSum_zmod_of_finite
and Chinese Remainder Theorem.

Status (2026-06-26): Framework phase only. C1 in CHECKLIST.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Phase 1: Primary Decomposition + Exponent Bounds -/

-- The hypothesis "no (ZMod p)² injection" means the p-rank is ≤ 1 for odd p
-- and ≤ 2 for p=2. These translate to exponent bounds in the primary decomposition.

-- Helper: extract exponent of prime p in group G's primary decomposition
-- If G ≃+ ⊕ᵢ (ℤ/pᵢ^eᵢ), we need eₚ for a given prime p
def max_p_exponent (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) : ℕ := by
  -- Implementation: use Mathlib's primary decomposition extract
  -- For now: skeleton that returns the right value on the actual ⊕ structure
  have ⟨ι, decomp⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  -- The decomp is an equivalence to ⊕ᵢ (ℤ/nᵢ)
  -- We need to filter for powers of p and find max exponent
  sorry  -- ~50 LOC: filter decomp by prime p, extract and max exponents

-- The hypothesis h_no_odd (p, 2 < p) → ¬(ZMod p × ZMod p ↪ G) implies eₚ ≤ 1
lemma exponent_odd_prime_le_one
    (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) (hp : Nat.Prime p) (h2p : 2 < p)
    (h_no_odd : ∀ q : ℕ, Nat.Prime q → 2 < q →
      ¬ ∃ f : ZMod q × ZMod q →+ G, Function.Injective f) :
    max_p_exponent G p ≤ 1 := by
  by_contra h_contra
  push_neg at h_contra
  -- If eₚ ≥ 2, then (ZMod p)ᵉ contains (ZMod p)² as a direct summand
  have hp_in_decomp : ∃ f : ZMod p × ZMod p →+ G, Function.Injective f := by
    sorry  -- Extract from primary decomposition: e_p ≥ 2 → p² divides G
  exact h_no_odd p hp h2p hp_in_decomp

-- The hypothesis h_no_two → ¬((ℤ/2)³ ↪ G) implies e₂ ≤ 2
lemma exponent_two_le_two
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_no_two : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f) :
    max_p_exponent G 2 ≤ 2 := by
  by_contra h_contra
  push_neg at h_contra
  -- If e₂ ≥ 3, then (ℤ/2)³ divides G, contradicting h_no_two
  have h2_in_decomp : ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f := by
    sorry  -- Extract from primary decomposition: e_2 ≥ 3 → 2³ divides G
  exact h_no_two h2_in_decomp

-- Helper: Chinese Remainder Theorem assembly for two-factor form
-- Given finite list of prime powers pᵢ^eᵢ, group into m × n where m | n
lemma crt_two_factor_decomposition (primes : List ℕ) (exponents : ℕ → ℕ) :
    ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ m ∣ n ∧
      (∀ i, ZMod (primes.get i ^ exponents i) ≃+ ℤ/m × ℤ/n) := by
  sorry  -- CRT groups all odd-prime components into m, and 2^e₂ into n's second factor

-- The reduction step: separate G into (odd part) ⊕ (2-part)
lemma primary_to_binary
    (G : Type*) [AddCommGroup G] [Finite G]
    (e_odd : ∃ G_odd : Type*, AddCommGroup G_odd ∧ Finite G_odd)
    (e_two : ∃ G_two : Type*, AddCommGroup G_two ∧ Finite G_two) :
    ∃ (m n : ℕ), (G ≃+ G_odd × G_two) ∧ (0 < m ∧ 0 < n ∧ m ∣ n) := by
  sorry  -- Separates the ⊕ into binary form

theorem primary_decomposition_respects_rank_bounds
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_no_odd : ∀ p : ℕ, Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f)
    (h_no_two : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f) :
    ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ m ∣ n ∧ (G ≃+ ℤ/m × ℤ/n) := by
  -- Step 1: Primary decomposition via Mathlib
  obtain ⟨ι, e⟩ := AddCommGroup.equiv_directSum_zmod_of_finite G
  -- Step 2: Extract exponent bounds
  have e_odd_bound : ∀ p : ℕ, Nat.Prime p → 2 < p → max_p_exponent G p ≤ 1 :=
    fun p hp h2p => exponent_odd_prime_le_one G p hp h2p h_no_odd
  have e_two_bound : max_p_exponent G 2 ≤ 2 :=
    exponent_two_le_two G h_no_two
  -- Step 3: Separate odd and 2-part
  -- Step 4: Apply CRT to group into m × n
  -- Step 5: Combine via equivalence composition
  sorry  -- ~200 LOC: implement steps 3-5 with CRT machinery

/-! ## Phase 2: Package into TwoInvariantFactorData -/

-- Verify the packaged data satisfies invariants
def twoInvariantFactorData_of_equiv
    (G : Type*) [AddCommGroup G] [Finite G]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (e : G ≃+ ℤ/m × ℤ/n) :
    TwoInvariantFactorData G where
  m := m
  n := n
  m_pos := hm
  n_pos := hn
  m_divides_n := hmn
  equiv := e
  card_eq : by
    simp [Nat.card_equiv e, Nat.card_prod, ZMod.card]
    ring
  order_n : sorry  -- Verify order_n condition if needed for Mazur

theorem mk_two_invariant_factor_data
    (G : Type*) [AddCommGroup G] [Finite G]
    (e : G ≃+ ℤ/m × ℤ/n) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    TwoInvariantFactorData G :=
  twoInvariantFactorData_of_equiv G m n hm hn hmn e

/-! ## Phase 3: Final Assembly (Axiom 2 Discharge) -/

theorem finite_abelian_two_invariant_factors
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_no_odd : ∀ p : ℕ, Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f)
    (h_no_two : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f) :
    ∃ d : TwoInvariantFactorData G, True := by
  -- Apply Phase 1: primary decomposition with bounds
  obtain ⟨m, n, hm, hn, hmn, e⟩ := primary_decomposition_respects_rank_bounds G h_no_odd h_no_two
  -- Apply Phase 2: package into TwoInvariantFactorData
  let d := mk_two_invariant_factor_data G e hm hn hmn
  exact ⟨d, trivial⟩

end MazurProof
