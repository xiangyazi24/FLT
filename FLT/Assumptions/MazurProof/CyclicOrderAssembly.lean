import FLT.Assumptions.MazurProof.TorsionDefs
-- import FLT.Assumptions.MazurProof.CyclicOrderArithmetic  -- needs olean build

/-!
# Assembly: cyclic order bound from named sub-axioms

Proves `mazur_cyclic_order_bound_assembled` from 13 named sub-axioms.
Each sub-axiom will be replaced by a theorem as its CyclicExclusion file
is completed; `#print axioms` tracks exactly which remain.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Sub-axioms -/

axiom mazur_prime_torsion_bound_sub
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : Nat.Prime p)
    (hord : HasRationalPointOfOrder E p) :
    p ∈ ({2, 3, 5, 7} : Finset ℕ)

axiom no_order_11 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 11
axiom no_order_14 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 14
axiom no_order_15 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 15
axiom no_order_16 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 16
axiom no_order_18 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 18
axiom no_order_20 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 20
axiom no_order_21 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 21
axiom no_order_24 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 24
axiom no_order_25 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 25
axiom no_order_27 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 27
axiom no_order_35 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 35
axiom no_order_49 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 49

/-! ## Inline from CyclicOrderArithmetic (until olean is built) -/

private def minimalBadComposites' : Finset ℕ :=
  {14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49}

private def IsSmooth' (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ ({2, 3, 5, 7} : Finset ℕ)

private axiom exists_minimalBadComposite_dvd' {n : ℕ}
    (hn : 12 < n) (hsmooth : IsSmooth' n) :
    ∃ d ∈ minimalBadComposites', d ∣ n

private axiom hasRationalPointOfOrder_of_dvd'
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n d : ℕ}
    (hn : n ≠ 0) (hdn : d ∣ n)
    (hord : HasRationalPointOfOrder E n) :
    HasRationalPointOfOrder E d

/-! ## Composite dispatch -/

private theorem no_order_bad_composite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {d : ℕ}
    (hd : d ∈ minimalBadComposites')
    (hord : HasRationalPointOfOrder E d) : False := by
  simp [minimalBadComposites', Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact no_order_14 E hord
  · exact no_order_15 E hord
  · exact no_order_16 E hord
  · exact no_order_18 E hord
  · exact no_order_20 E hord
  · exact no_order_21 E hord
  · exact no_order_24 E hord
  · exact no_order_25 E hord
  · exact no_order_27 E hord
  · exact no_order_35 E hord
  · exact no_order_49 E hord

/-! ## Main assembly -/

theorem mazur_cyclic_order_bound_assembled
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 0 < n)
    (hord : HasRationalPointOfOrder E n) :
    n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ) := by
  by_contra hnot
  simp [Finset.mem_insert, Finset.mem_singleton] at hnot
  have hn_ne : n ≠ 0 := by omega
  -- n ∉ {1,...,10,12} and n > 0. So n = 11 or n ≥ 13.
  by_cases h11 : n = 11
  · exact no_order_11 E (h11 ▸ hord)
  · -- n ≥ 13 (since n ∉ {1,...,10,12} and n ≠ 11 and n > 0)
    have hn12 : 12 < n := by omega
    -- All prime factors of n are in {2,3,5,7}
    have hsmooth : IsSmooth' n := by
      intro p hp hpn
      have hpord := hasRationalPointOfOrder_of_dvd' E hn_ne hpn hord
      exact mazur_prime_torsion_bound_sub E hp hpord
    obtain ⟨d, hd_mem, hd_dvd⟩ := exists_minimalBadComposite_dvd' hn12 hsmooth
    have hd_ne : d ≠ 0 := by
      intro h; simp [h, minimalBadComposites'] at hd_mem
    have hd_ord := hasRationalPointOfOrder_of_dvd' E hn_ne hd_dvd hord
    exact no_order_bad_composite E hd_mem hd_ord

end MazurProof
