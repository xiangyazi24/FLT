import Mathlib

/-!
# Even factor multiplicities ⇒ square (element and principal-ideal level)

Reusable algebra for the descent lemmas (e.g. Billing–Mahler for `11a3`): if every
irreducible occurs to an even power in the unique factorization of `a ≠ 0`, then `a` is
associated to a square, and hence the principal ideal `span {a}` is a square ideal.

The element-level route (via `normalizedFactors`) is used rather than the ideal
`UniqueFactorizationMonoid` route, because the number rings we apply this to are PIDs.

Written by hand; the only genuinely combinatorial content is
`exists_multiset_half_of_count_even`.
-/

open UniqueFactorizationMonoid

namespace MazurProof.DedekindSquare

/-- A multiset in which every element occurs an even number of times is `t + t`
for some `t` (namely, take half of each multiplicity). -/
theorem exists_multiset_half_of_count_even {ι : Type*} [DecidableEq ι] :
    ∀ s : Multiset ι, (∀ a, Even (s.count a)) → ∃ t : Multiset ι, s = t + t := by
  intro s
  induction s using Multiset.strongInductionOn with
  | _ s ih =>
    intro h
    rcases s.empty_or_exists_mem with hs | ⟨a, ha⟩
    · exact ⟨0, by simp [hs]⟩
    · -- `a` occurs, and evenly, so at least twice; peel two copies via `erase`.
      have hpos : 0 < s.count a := Multiset.count_pos.mpr ha
      have hcount : 2 ≤ s.count a := by
        rcases h a with ⟨k, hk⟩; omega
      set s1 : Multiset ι := s.erase a with hs1
      have ha1 : a ∈ s1 := by
        rw [← Multiset.count_pos, hs1, Multiset.count_erase_self]; omega
      set s2 : Multiset ι := s1.erase a with hs2
      have hlt : s2 < s :=
        lt_of_le_of_lt (Multiset.erase_le a s1) (Multiset.erase_lt.mpr ha)
      have hchain : s = a ::ₘ a ::ₘ s2 := by
        rw [hs2, Multiset.cons_erase ha1, hs1, Multiset.cons_erase ha]
      have heven2 : ∀ b, Even (s2.count b) := by
        intro b
        by_cases hb : b = a
        · rw [hb]
          have hc : s2.count a = s.count a - 2 := by
            rw [hs2, hs1, Multiset.count_erase_self, Multiset.count_erase_self]; omega
          rw [hc]; rcases h a with ⟨k, hk⟩; exact ⟨k - 1, by omega⟩
        · have hc : s2.count b = s.count b := by
            rw [hs2, hs1, Multiset.count_erase_of_ne hb, Multiset.count_erase_of_ne hb]
          rw [hc]; exact h b
      obtain ⟨u, hu⟩ := ih s2 hlt heven2
      refine ⟨a ::ₘ u, ?_⟩
      rw [hchain, hu]
      -- a ::ₘ a ::ₘ (u + u) = (a ::ₘ u) + (a ::ₘ u)
      rw [Multiset.cons_add, Multiset.add_cons]

/-- If every irreducible occurs to an even power in `normalizedFactors a` (for `a ≠ 0`
in a UFM with normalization), then `a` is associated to a square. -/
theorem associated_sq_of_normalizedFactors_count_even
    {α : Type*} [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
    [NormalizationMonoid α] [DecidableEq α] {a : α} (ha : a ≠ 0)
    (h : ∀ p, Even ((normalizedFactors a).count p)) :
    ∃ b : α, Associated a (b ^ 2) := by
  obtain ⟨t, ht⟩ := exists_multiset_half_of_count_even (normalizedFactors a) h
  refine ⟨t.prod, ?_⟩
  have hassoc : Associated (normalizedFactors a).prod a := prod_normalizedFactors ha
  rw [ht, Multiset.prod_add] at hassoc
  have : Associated a (t.prod * t.prod) := hassoc.symm
  rwa [← pow_two] at this

/-- Principal-ideal corollary: even multiplicities make `span {a}` a square ideal. -/
theorem span_singleton_eq_sq_of_normalizedFactors_count_even
    {α : Type*} [CommRing α] [IsDomain α] [UniqueFactorizationMonoid α]
    [NormalizationMonoid α] [DecidableEq α] {a : α} (ha : a ≠ 0)
    (h : ∀ p, Even ((normalizedFactors a).count p)) :
    ∃ I : Ideal α, Ideal.span ({a} : Set α) = I ^ 2 := by
  obtain ⟨b, hb⟩ := associated_sq_of_normalizedFactors_count_even ha h
  refine ⟨Ideal.span ({b} : Set α), ?_⟩
  rw [Ideal.span_singleton_pow]
  exact (Ideal.span_singleton_eq_span_singleton.mpr hb)

end MazurProof.DedekindSquare
