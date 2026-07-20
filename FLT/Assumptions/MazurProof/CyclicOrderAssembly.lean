import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.CyclicOrderArithmetic
import FLT.Assumptions.MazurProof.CyclicExclusion14
import FLT.Assumptions.MazurProof.CyclicExclusion16
import FLT.Assumptions.MazurProof.CyclicExclusion20
import FLT.Assumptions.MazurProof.CyclicExclusion25
import FLT.Assumptions.MazurProof.CyclicExclusion27
import FLT.Assumptions.MazurProof.CyclicExclusion49
import FLT.Assumptions.MazurProof.CyclicExclusion35
import FLT.Assumptions.MazurProof.CyclicExclusion15
import FLT.Assumptions.MazurProof.CyclicExclusion21
import FLT.Assumptions.MazurProof.CyclicExclusion11
import FLT.Assumptions.MazurProof.CyclicExclusion18
import FLT.Assumptions.MazurProof.N18GoodModelAssembly
import FLT.Assumptions.MazurProof.PrimeExclusion17Bridge
import FLT.Assumptions.MazurProof.PrimeExclusion19Bridge

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

* `14` — `no_rational_point_of_order_14`, via the Tate/Kubert map to
  `X₁(14)` and the complete quartic descent in `scratch.ObstructionQ14`.
* `16` — `no_rational_point_of_order_16`, via the genuine Tate map to
  `X₁(16)` and the split genus-two factor descent in `RationalPointsX116`.
* `20, 24` — `CyclicExclusion20.no_rational_point_of_order_20` and
  `CyclicExclusion20.no_rational_point_of_order_24`.  They share the correctly
  stated geometric seam `exists_rational_two_isogeny_quotient`, whose dual map
  composes with the quotient map as multiplication by `2`.
* `25` — `CyclicExclusion25.no_rational_point_of_order_25`; its geometric
  front end is proved through the generic odd-order Tate bridge, and the
  order-25 division polynomial is factored as the proper order-five factor
  times an explicit primitive degree-40 polynomial.  The sole remaining input
  is `no_explicit_order25_obstruction`, the rational-point exclusion for that
  explicit affine model of `X₁(25)`.
* `49` — likewise reduced by the generic odd-order Tate bridge to
  `preΨ'₄₉(0)=0` with the proper factor `preΨ'₇(0)≠0`; its remaining input is
  `no_raw_order49_tate_obstruction`.
* `27` — `CyclicExclusion27.no_rational_point_of_order_27`, via simultaneous
  Tate normalization of `P` and `3P`, a special three-descent on the Kubert
  order-nine family, and the proved rational-point classification of the
  level-27 curve `y²+y=x³`.

All composite exclusions `14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49`
are wired to `sorry`-free theorems.  `15, 21, 35` are fully proved
(0 sorry, 0 axiom).  `18` is proved via
`N18GoodModelAssembly.no_five_descent_solution` composed with
`CyclicExclusion18.order18_to_five_descent` (both `sorry`-free).

Together with the prime-order input `mazur_prime_torsion_bound_sub`, these are
exactly the named inputs reported by
`#print axioms mazur_cyclic_order_bound_assembled`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Prime-order input — decomposed into three sub-pieces

The monolithic axiom `mazur_prime_torsion_bound_sub` is now a THEOREM
assembled from:
* `no_rational_point_of_order_11` — sorry-free (Billing–Mahler cubic descent)
* `no_order_13_prime` — sub-axiom (genus-2 Jacobian descent on X₁(13))
* `no_order_17_prime` — THEOREM via kernel polynomial bridge (PrimeExclusion17Bridge)
* `no_order_19_prime` — THEOREM via kernel polynomial bridge (PrimeExclusion19Bridge)
* `no_prime_order_ge_23` — sub-axiom (formal immersion on X₀(p), uniform tail)
-/

axiom no_order_13_prime
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 13

theorem no_order_17_prime
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 17 :=
  PrimeExclusion17Bridge.no_order_17_prime E

theorem no_order_19_prime
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 19 :=
  PrimeExclusion19Bridge.no_order_19_prime E

axiom no_prime_order_ge_23
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp23 : 23 ≤ p) :
    ¬ HasRationalPointOfOrder E p

theorem no_prime_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (hp : Nat.Prime p) (hp17 : 17 ≤ p) :
    ¬ HasRationalPointOfOrder E p := by
  by_cases hp23 : 23 ≤ p
  · exact no_prime_order_ge_23 E hp hp23
  · have hp22 : p ≤ 22 := by omega
    have : p = 17 ∨ p = 19 := by
      interval_cases p <;> first | left; rfl | right; rfl |
        (exfalso; revert hp; decide)
    rcases this with rfl | rfl
    · exact no_order_17_prime E
    · exact no_order_19_prime E

theorem mazur_prime_torsion_bound_sub
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} (hp : Nat.Prime p)
    (hord : HasRationalPointOfOrder E p) :
    p ∈ ({2, 3, 5, 7} : Finset ℕ) := by
  by_contra hnot
  by_cases hp17 : 17 ≤ p
  · exact no_prime_order_ge_17 E hp hp17 hord
  · have hp16 : p ≤ 16 := by omega
    interval_cases p <;> simp_all (config := { decide := true }) [Finset.mem_insert,
      Finset.mem_singleton] <;> first
      | exact no_rational_point_of_order_11 E hord
      | exact no_order_13_prime E hord

/-! ## Composite-order sub-axioms (no sound real theorem to wire yet) -/

theorem no_order_15 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 15 :=
  no_rational_point_of_order_15 E
theorem no_order_18 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 18 := by
  intro h18
  exact N18GoodModelAssembly.no_five_descent_solution
    (CyclicExclusion18.order18_to_five_descent E h18)
theorem no_order_21 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 21 :=
  CyclicExclusion21.no_rational_point_of_order_21 E

theorem no_order_35 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 35 :=
  no_rational_point_of_order_35 E

/-! ## Concrete exclusion wired to a real theorem -/

theorem no_order_14 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 14 :=
  no_rational_point_of_order_14 E

theorem no_order_16 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 16 :=
  no_rational_point_of_order_16 E

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

theorem no_order_49 (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 49 :=
  CyclicExclusion49.no_rational_point_of_order_49 E

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
    exact no_rational_point_of_order_11 E hord
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
