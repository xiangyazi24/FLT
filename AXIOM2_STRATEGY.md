# Axiom 2 (Two Invariant Factors) — Discharge Strategy

## Axiom Statement
```lean
axiom finite_abelian_two_invariant_factors (G : Type*) [AddCommGroup G] [Finite G]
    (h_no_odd : ∀ p : ℕ, Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f)
    (h_no_two : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f) :
    ∃ d : TwoInvariantFactorData G, True
```

If a finite abelian group G has:
- 2-rank ≤ 2 (no (ℤ/2)³ injection)
- odd prime p-rank ≤ 1 for all p > 2 (no (ZMod p)² injection)

Then G has a two-invariant-factor decomposition: G ≅ ℤ/m × ℤ/n (m | n).

## Why This Is Tractable

1. **Mathlib Foundation**: `AddCommGroup.equiv_directSum_zmod_of_finite` already provides:
   - Structure theorem: G ≅ ⊕ ᵢ (ℤ/pᵢ^eᵢ) via primary decomposition
   - Chinese Remainder Theorem: CRT combines factors
   
2. **Two Invariant Factor Form**: The hypotheses on rank bound the exponents:
   - For p=2: exponent ≤ 2 (no ℤ/8 factors, only ℤ/4 at most)
   - For odd p: exponent ≤ 1 (no p² factors)
   - Result: each component reduces to (ℤ/m_p) for m_p | n_p, combining via CRT

3. **No Deep Theory**: Just group theory + CRT. No EC, no divisors, no Galois theory.

## Discharge Path (est. 1000 LOC)

### Phase 1: Decomposition (est. 400 LOC)
```lean
theorem primary_decomposition_respects_rank_bound
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_no_odd : ...) (h_no_two : ...) :
    ∃ (m n : ℕ), (m ∣ n) ∧ (G ≃+ ℤ/m × ℤ/n) := by
  -- 1. Apply AddCommGroup.equiv_directSum_zmod_of_finite
  -- 2. Analyze the resulting ⊕ ᵢ (ℤ/pᵢ^eᵢ)
  -- 3. Show hypotheses force eᵢ ≤ 2 for p=2, eᵢ ≤ 1 for odd p
  -- 4. Group odd primes + even prime: (ℤ/odd) × (ℤ/2^e) where e ≤ 2
  -- 5. Apply CRT to merge into two factors
```

### Phase 2: Invariant Factor Data (est. 300 LOC)
```lean
theorem mk_two_invariant_factor_data
    (G : Type*) [AddCommGroup G] [Finite G]
    (e : G ≃+ ℤ/m × ℤ/n) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    TwoInvariantFactorData G := by
  -- Package the equivalence into the data structure
  -- Verify card G = m * n, order_n condition, etc.
```

### Phase 3: Assembly (est. 300 LOC)
```lean
theorem finite_abelian_two_invariant_factors ...  :=
  -- Direct application of phases 1 + 2
```

## Risk Assessment: Very Low

- ✅ Mathlib has the backbone (decomposition theorem)
- ✅ CRT is standard algebra
- ✅ No unproven deep math (unlike Weil pairing or Kubert)
- ✅ Hypotheses are strong enough to force the conclusion
- ⚠️ Bookkeeping on exponent bounds (e_p ≤ limits) — tedious but mechanical

## Success Criteria

- **Goal (A)**: Complete 0-sorry proof (very likely, given Mathlib support)
- **Goal (B)**: Compiled with 1-2 named sorries on edge cases (acceptable fallback)
- **Fallback**: Clear roadmap of sub-lemmas (unlikely to need this)

## When to Deploy

**If Axiom 1 or Axiom 4 stall:**
- Axiom 1 (Weil pairing) needs deep EC theory → likely multi-day grind
- Axiom 4 (Kubert) needs careful parameter reductions → likely needs external theory
- **Axiom 2 is the fastest path to another discharged axiom**
- De-risks the milestone: at least ONE axiom done, not 0

**If Codex returns quickly on Axiom 1:**
- Skip Axiom 2, go straight to integration
- But have Axiom 2 ready as a fallback

## File Structure

Create: `FLT/Assumptions/MazurProof/TwoInvariantFactors.lean`
- Imports: Mathlib group theory + Axioms.lean
- Content: three phases above
- Reference: scratch/ will NOT be used (this is pure Mathlib)

---

**Difficulty**: LOW (Mathlib-backed, pure algebra)
**Tractability**: HIGH (most likely to complete in this cycle)
**Deployment**: Fallback avenue if Axiom 1/4 stall
