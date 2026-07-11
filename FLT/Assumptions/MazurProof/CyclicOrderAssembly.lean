import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.CyclicOrderArithmetic
import FLT.Assumptions.MazurProof.CyclicExclusion20
import FLT.Assumptions.MazurProof.CyclicExclusion25
import FLT.Assumptions.MazurProof.CyclicExclusion27

/-!
# Assembly: cyclic order bound from named sub-axioms

`mazur_cyclic_order_bound_assembled`: every rational point of an elliptic curve
over `ℚ` has order in `{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12}`.

## Arithmetic backbone (no longer axiomatic)

The composite-antichain lemma `exists_minimalBadComposite_dvd` and the
divisor-reduction lemma `hasRationalPointOfOrder_of_dvd` are real, `sorry`-free
and `axiom`-free theorems, imported from `CyclicOrderArithmetic`.  The earlier
private copies (`minimalBadComposites'`, `IsSmooth'`) and their two placeholder
`axiom`s have been removed and replaced by these theorems.

## Concrete exclusions

Endpoint wired to a real theorem:

* `20, 24` — `CyclicExclusion20.no_rational_point_of_order_20` and
  `CyclicExclusion20.no_rational_point_of_order_24`.  They share the correctly
  stated geometric seam `exists_rational_two_isogeny_quotient`, whose dual map
  composes with the quotient map as multiplication by `2`.
* `25` — `CyclicExclusion25.no_rational_point_of_order_25`; its geometric
  front end is now proved through the generic odd-order Tate bridge.  The sole
  remaining input is the explicit raw division system
  `no_raw_order25_tate_obstruction`.
* `27` — `CyclicExclusion27.no_rational_point_of_order_27`, via
  `X₀(27) ≅ {x³ + y³ = 1}` and Mathlib's `fermatLastTheoremThree`.  Its only
  remaining seam is the named geometric input `order27_to_fermat_cubic`, which
  `#print axioms mazur_cyclic_order_bound_assembled` reports explicitly — the
  wiring does not claim a closed proof of the order-`27` exclusion.

Endpoints kept as named sub-axioms, because no sound real theorem exists to
wire:

* `14, 15, 16, 18, 21` — the `CyclicExclusion` proofs still contain `sorry`.
* `35, 49` — their final arithmetic input is not yet formalized.

Together with the prime-order input `mazur_prime_torsion_bound_sub`, these are
exactly the named inputs reported by
`#print axioms mazur_cyclic_order_bound_assembled`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Prime-order input -/

axiom mazur_prime_torsion_bound_sub
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : Nat.Prime p)
    (hord : HasRationalPointOfOrder E p) :
    p ∈ ({2, 3, 5, 7} : Finset ℕ)

/-! ## Composite-order sub-axioms (no sound real theorem to wire yet) -/

axiom no_order_14 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 14
axiom no_order_15 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 15
axiom no_order_16 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 16
axiom no_order_18 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 18
axiom no_order_21 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 21
axiom no_order_35 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 35
axiom no_order_49 (E : WeierstrassCurve ℚ) [E.IsElliptic] : ¬ HasRationalPointOfOrder E 49

/-! ## Concrete exclusion wired to a real theorem -/

theorem no_order_20 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 20 :=
  no_rational_point_of_order_20 E

theorem no_order_24 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 24 :=
  no_rational_point_of_order_24 E

theorem no_order_25 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 25 :=
  CyclicExclusion25.no_rational_point_of_order_25 E

theorem no_order_27 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 27 :=
  CyclicExclusion27.no_rational_point_of_order_27 E

/-! ## Composite dispatch -/

private theorem no_order_bad_composite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {d : ℕ}
    (hd : d ∈ minimalBadComposites)
    (hord : HasRationalPointOfOrder E d) : False := by
  simp [minimalBadComposites, Finset.mem_insert, Finset.mem_singleton] at hd
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
  -- n ∉ {1,…,10,12} and n > 0. So n = 11 or n ≥ 13.
  by_cases h11 : n = 11
  · subst n
    have hprime := mazur_prime_torsion_bound_sub E (by norm_num : Nat.Prime 11) hord
    norm_num at hprime
  · -- n ≥ 13 (since n ∉ {1,…,10,12}, n ≠ 11, n > 0)
    have hn12 : 12 < n := by omega
    -- All prime factors of n are in {2,3,5,7}.
    have hsmooth : IsSmooth n := by
      intro p hp hpn
      have hpord := hasRationalPointOfOrder_of_dvd E hn_ne hpn hord
      exact mazur_prime_torsion_bound_sub E hp hpord
    obtain ⟨d, hd_mem, hd_dvd⟩ := exists_minimalBadComposite_dvd hn12 hsmooth
    have hd_ord := hasRationalPointOfOrder_of_dvd E hn_ne hd_dvd hord
    exact no_order_bad_composite E hd_mem hd_ord

end MazurProof
