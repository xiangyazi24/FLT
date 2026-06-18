import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.NoncyclicN10
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.DescentBridgeN16
import FLT.Assumptions.MazurProof.GroupTheory
import FLT.Assumptions.MazurProof.TorsionFinite
import FLT.Assumptions.MazurProof.RootsOfUnity
import FLT.Assumptions.MazurProof.InvariantFactorLemmas

/-!
# Axioms for the Mazur torsion-bound proof scaffold

This file collects the hard mathematical inputs needed to prove the numerical
bound `|E(ℚ)_tors| ≤ 16`.  The axioms are grouped by expected discharge
priority.

## Changes from axiom to theorem

`rational_torsion_two_invariant_factors` was formerly an axiom. It is now
derived from:
- `mordell_weil_fg` (axiom in `TorsionFinite.lean`) via `rational_torsion_finite_alias`
- `weil_pairing_primitive_root` (axiom below) + `isPrimitiveRoot_rat_order_le_two`
  (proved in `RootsOfUnity.lean`) -- constrains odd primes to rank ≤ 1
- `no_triple_two_torsion` (axiom below) -- constrains 2-rank to ≤ 2
- `finite_abelian_two_invariant_factors` (pure group theory theorem below) --
  converts primary decomposition to invariant factor form

The net effect: the original *elliptic-curve-specific* axiom is eliminated.
`finite_abelian_two_invariant_factors` is now a theorem (with sorry) whose
statement is mathematically correct. The original axiom was false for groups
with 2-rank ≥ 3 (e.g. `(ℤ/2)³`), since its hypothesis only constrained
odd primes. A new axiom `no_triple_two_torsion` captures the 2-rank
constraint from `E[2] ≅ (ℤ/2)²`.
-/

open scoped WeierstrassCurve.Affine DirectSum

namespace MazurProof

/-- The torsion subgroup of `E(ℚ)`, as a set, matching `FLT/Assumptions/Mazur.lean`. -/
abbrev torsionSet (E : WeierstrassCurve ℚ) : Set (E⁄ℚ).Point :=
  AddCommGroup.torsion (E⁄ℚ).Point

/-- Placeholder for "all `m`-torsion points of `E` are rational". -/
def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

/-- Placeholder for "there is a rational point of exact order `n` on `E`". -/
def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

/--
Placeholder for the structure-theorem assertion
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`.
-/
def HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod n →+ (E⁄ℚ).Point, Function.Injective f

/-- Placeholder for `E(ℚ)_tors` containing a subgroup `ℤ/2ℤ × ℤ/nℤ`. -/
abbrev ContainsZ2xZn (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  HasTorsionStructure E 2 n

/--
Finite two-invariant-factor data for the rational torsion subgroup.

The `has_point_order_n` field records the evident element of order `n` in
`ℤ/mℤ × ℤ/nℤ`; it is kept as part of the axiom so the later arithmetic input
can be used without developing finite abelian group theory here.
-/
structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  has_structure : HasTorsionStructure E m n
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n

/-! ## Group B: Weil pairing (declared early so helpers can use it) -/

/--
Weil pairing consequence: if all `m`-torsion points are rational, then `ℚ`
contains a primitive `m`-th root of unity.
-/
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

/-! ## Pure group theory: invariant factor decomposition -/

/--
Bundled invariant-factor data for a finite abelian group.
Records the two factors `m | n` together with the structural injection,
an element of maximal order, and the cardinality identity.
-/
structure TwoInvariantFactorData (G : Type*) [AddCommGroup G] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  embed : ZMod m × ZMod n →+ G
  embed_inj : Function.Injective embed
  max_order_elt : G
  max_order_eq : addOrderOf max_order_elt = n
  card_eq : Nat.card G = m * n

/--
**Pure group theory theorem (with sorry).**
Any finite abelian group whose odd primes have rank at most 1 AND whose
2-rank is at most 2 has a two-invariant-factor decomposition.

The proof uses `AddCommGroup.equiv_directSum_zmod_of_finite` (Mathlib)
plus the Chinese Remainder Theorem to collect primary components into
invariant factors.

**Correctness note:** The original axiom only required `2 < p` in
`h_odd_rank`, which left the 2-rank unconstrained. This made the axiom
FALSE for groups like `(ℤ/2)³`. The corrected version adds `h_two_rank`
to constrain the 2-part, making the statement mathematically correct.

Proof sketch:
1. Primary decomposition: `G ≅ ⊕ᵢ ℤ/nᵢ` (Mathlib)
2. For odd `p ≥ 3`: `h_odd_rank` ⇒ at most one component divisible by `p`
   ⇒ odd part is cyclic `ℤ/N` (CRT, pairwise coprime)
3. For `p = 2`: `h_two_rank` ⇒ at most two 2-power components
4. Combine: `G ≅ ℤ/2^a × ℤ/2^b × ℤ/N ≅ ℤ/2^a × ℤ/(2^b · N)` (CRT)
5. Set `m = 2^a`, `n = 2^b · N`. Then `m ∣ n` and `|G| = m · n`.
-/
noncomputable def finite_abelian_two_invariant_factors
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_odd_rank : ∀ (p : ℕ), Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f)
    (h_two_rank : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+ G, Function.Injective f) :
    TwoInvariantFactorData G :=
  -- The proof uses Mathlib's primary decomposition
  -- `AddCommGroup.equiv_directSum_zmod_of_finite'` to get G ≅ ⊕ᵢ ℤ/nᵢ,
  -- then applies:
  -- - InvariantFactorLemmas.at_most_one_p_component (odd p-rank ≤ 1)
  -- - InvariantFactorLemmas.at_most_two_2_components (2-rank ≤ 2)
  -- to conclude at most 2 invariant factors, and combines via CRT.
  -- The remaining sorry is the combinatorial recombination step.
  sorry

/-! ## Weil pairing rank constraint -/

/--
The Weil pairing constraint: for any odd prime `p ≥ 3`,
`ZMod p × ZMod p` does not embed in `E(ℚ)_tors`.

Proof: if it did, composing with inclusion into `E(ℚ)` would give
`HasFullRationalTorsion E p`, and `weil_pairing_primitive_root` would produce
a primitive `p`-th root of unity in `ℚ`. But `isPrimitiveRoot_rat_order_le_two`
shows `p ≤ 2`, contradicting `2 < p`.
-/
theorem no_odd_prime_square_in_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : Nat.Prime p) (hp3 : 2 < p) :
    ¬ ∃ f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E⁄ℚ).Point),
        Function.Injective f := by
  intro ⟨f, hf⟩
  let incl : (AddCommGroup.torsion (E⁄ℚ).Point) →+ (E⁄ℚ).Point :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  have hfull : HasFullRationalTorsion E p :=
    ⟨incl.comp f, hincl.comp hf⟩
  rcases weil_pairing_primitive_root E hp.pos hfull with ⟨ζ, hζ⟩
  have hle : p ≤ 2 := isPrimitiveRoot_rat_order_le_two hζ
  omega

/-! ## 2-rank constraint on E(ℚ)_tors -/

/--
The 2-torsion of an elliptic curve `E` over `ℚ` has rank at most 2:
`(ℤ/2)³` does not inject into `E(ℚ)_tors`.

This follows from the fact that `E[2]` (the full 2-torsion over the algebraic
closure) is isomorphic to `(ℤ/2)²`, so any injection `(ℤ/2)³ → E(ℚ)_tors`
would factor through `E[2]` and violate the rank bound.
-/
axiom no_triple_two_torsion (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+
        (AddCommGroup.torsion (E⁄ℚ).Point), Function.Injective f

/-! ## Group A: torsion structure -- now derived, not an axiom -/

/--
The rational torsion subgroup has two invariant factors:
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`, and cardinality `m * n`.

Formerly an axiom. Now derived from:
- `rational_torsion_finite_alias` (torsion is finite)
- `weil_pairing_primitive_root` + `isPrimitiveRoot_rat_order_le_two` (odd
  primes have rank at most 1 in torsion)
- `no_triple_two_torsion` (2-rank at most 2, from `E[2] ≅ (ℤ/2)²`)
- `finite_abelian_two_invariant_factors` (pure group theory theorem)
-/
noncomputable def rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E :=
  have hfin : (torsionSet E).Finite := rational_torsion_finite_alias E
  haveI : Finite (AddCommGroup.torsion (E⁄ℚ).Point) := hfin.to_subtype
  have h_no_odd : ∀ (p : ℕ), Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ (AddCommGroup.torsion (E⁄ℚ).Point),
          Function.Injective f :=
    no_odd_prime_square_in_torsion E
  have h_no_two3 : ¬ ∃ f : ZMod 2 × ZMod 2 × ZMod 2 →+
      (AddCommGroup.torsion (E⁄ℚ).Point), Function.Injective f :=
    no_triple_two_torsion E
  let d := finite_abelian_two_invariant_factors
      (AddCommGroup.torsion (E⁄ℚ).Point) h_no_odd h_no_two3
  let incl : (AddCommGroup.torsion (E⁄ℚ).Point) →+ (E⁄ℚ).Point :=
    (AddCommGroup.torsion (E⁄ℚ).Point).subtype
  have hincl : Function.Injective incl := Subtype.val_injective
  { m := d.m
    n := d.n
    m_pos := d.m_pos
    n_pos := d.n_pos
    dvd_mn := d.dvd_mn
    has_structure := ⟨incl.comp d.embed, hincl.comp d.embed_inj⟩
    has_point_order_n := ⟨(d.max_order_elt : (E⁄ℚ).Point), by
      rw [← d.max_order_eq]
      exact AddSubgroup.addOrderOf_coe d.max_order_elt⟩
    card_eq := by rw [← d.card_eq]; rfl }

/--
If the first invariant factor of the rational torsion subgroup is `m`, then
the full `m`-torsion is rational.
-/
theorem first_invariant_factor_full_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n)
    (hstruct : HasTorsionStructure E m n) :
    HasFullRationalTorsion E m := by
  obtain ⟨embed, hembed⟩ := zmod_prod_contains_square m n hm hn hmn
  obtain ⟨f, hf⟩ := hstruct
  exact ⟨f.comp embed, hf.comp hembed⟩

/-! ## Group C: noncyclic exclusions -/

/-- No elliptic curve over `ℚ` has rational torsion containing `ℤ/2ℤ × ℤ/nℤ`
for `n ∈ {10, 12, 14, 16}`. -/
theorem no_Z2_cross_Z14
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ContainsZ2xZn E 14 :=
  no_Z2_cross_Z14_from_descent E

theorem no_Z2_cross_Z16
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ContainsZ2xZn E 16 :=
  no_Z2_cross_Z16_from_descent E

theorem no_Z2_cross_Zn_forbidden
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16) :
    ¬ ContainsZ2xZn E n := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact no_Z2_cross_Z10 E
  · exact no_Z2_cross_Z12 E
  · exact no_Z2_cross_Z14 E
  · exact no_Z2_cross_Z16 E

/-! ## Group D: cyclic order bound, the hard Mazur core -/

/-- No elliptic curve over `ℚ` has a rational point of order at least `17`. -/
axiom no_rational_point_of_order_ge_17
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 ≤ n) :
    ¬ HasRationalPointOfOrder E n

end MazurProof
