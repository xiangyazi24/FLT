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

-- Key: from primary decomposition G ≃+ ⊕ᵢ (ℤ/pᵢ^eᵢ), extract injection ZMod p × ZMod p ↪ G
lemma injection_of_exponent_ge_two
    (G : Type*) [AddCommGroup G] [Finite G] (p : ℕ) (hp : Nat.Prime p) (e : ℕ) (he : e ≥ 2) :
    (let decomp := AddCommGroup.equiv_directSum_zmod_of_finite G
     -- If p^e appears in decomp, then ZMod p × ZMod p ↪ ZMod (p^e) ↪ G
     ∃ f : ZMod p × ZMod p →+ G, Function.Injective f) := by
  sorry  -- Use Mathlib's divisor lattice: p² | p^e (when e ≥ 2) → injection exists

-- Chinese Remainder Theorem assembly: group prime powers into two factors
lemma crt_two_factor_decomposition
    (odd_part : ℕ) (e_two : ℕ) (h_odd_pos : 0 < odd_part) (h_two_pos : 0 < e_two) :
    ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ m ∣ n ∧
      (ℤ/odd_part × ℤ/(2^e_two) ≃+ ℤ/m × ℤ/n) := by
  -- CRT: (ℤ/odd_part) × (ℤ/2^e_two) → (ℤ/m) × (ℤ/n) where m | n
  -- m = odd_part, n = lcm(odd_part, 2^e_two) = odd_part * 2^e_two (coprime)
  use odd_part, odd_part * 2^e_two
  refine ⟨h_odd_pos, Nat.mul_pos h_odd_pos h_two_pos, ?_, ?_⟩
  · exact dvd_mul_right odd_part (2^e_two)
  · sorry  -- CRT isomorphism: coprime factors combine directly

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

  -- Step 3: Extract odd_part and e_two from primary decomposition
  -- odd_part = ∏_{p odd prime, eₚ ≥ 1} p^eₚ (each eₚ ≤ 1 by h_no_odd)
  -- e_two = max_p_exponent G 2 (at most 2 by h_no_two)

  have all_odd_exp_le_one : ∀ p : ℕ, Nat.Prime p → 2 < p →
      max_p_exponent G p ≤ 1 :=
    fun p hp h2p => exponent_odd_prime_le_one G p hp h2p h_no_odd

  have two_exp_le_two : max_p_exponent G 2 ≤ 2 :=
    exponent_two_le_two G h_no_two

  let odd_part : ℕ := by
    sorry  -- ∏ p^eₚ over odd primes p where eₚ = max_p_exponent G p
            -- (eₚ ≤ 1 for all odd p by all_odd_exp_le_one)
  let e_two : ℕ := max_p_exponent G 2

  have odd_part_pos : 0 < odd_part := by
    sorry  -- Product of prime powers, so ≥ 1
  have e_two_pos : 0 < e_two := by
    sorry  -- G is finite → 2^e | order(G) for some e ≥ 1
            -- (and e ≤ 2 from two_exp_le_two)

  -- Step 5: Apply CRT to combine
  obtain ⟨m, n, hm, hn, hmn, crt_iso⟩ :=
    crt_two_factor_decomposition odd_part (2^e_two) odd_part_pos
      (Nat.pow_pos (by norm_num : 0 < 2) _)

  -- Step 6: Compose the three equivalences
  -- (1) Primary decomposition G ≃+ ⊕ᵢ(ℤ/pᵢ^eᵢ) from Mathlib
  -- (2) Grouping: rearrange ⊕ into (odd factors) × (2-part)
  -- (3) CRT: (ℤ/odd_part) × (ℤ/2^e_two) ≃+ ℤ/m × ℤ/n (coprime factors)

  have e2_iso : (∀ i : ℕ, (i.Prime ∧ i ≠ 2) → exponent_odd_prime_le_one G i _ _ h_no_odd ≤ 1) ∧
                (exponent_two_le_two G h_no_two ≤ 2) := by
    exact ⟨e_odd_bound, e_two_bound⟩

  -- The final composition (abstract, awaits Mathlib direct sum grouping)
  exact ⟨m, n, hm, hn, hmn, by
    sorry  -- G ≃+ ⊕ᵢ(...) ≃+ (ℤ/odd_part × ℤ/2^e_two) ≃+ ℤ/m × ℤ/n
            -- via three .trans (transitivity) steps
  ⟩

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
