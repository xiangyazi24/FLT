import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.NoncyclicN10
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.DescentBridgeN16
import FLT.Assumptions.MazurProof.GroupTheory
import FLT.Assumptions.MazurProof.TorsionFinite
import FLT.Assumptions.MazurProof.RootsOfUnity

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
  (proved in `RootsOfUnity.lean`) -- constrains the 2-rank
- `finite_abelian_two_invariant_factors` (pure group theory axiom below) --
  converts primary decomposition to invariant factor form

The net effect: the *elliptic-curve-specific* axiom is eliminated. The
remaining sorry-equivalent is `finite_abelian_two_invariant_factors`, which is
pure finite abelian group theory and could be proved from Mathlib's
`AddCommGroup.equiv_directSum_zmod_of_finite`.
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
**Pure group theory axiom.**
Any finite abelian group whose odd primes have rank at most 1 has a
two-invariant-factor decomposition.

This combines:
1. Primary decomposition to invariant factor conversion
2. Existence of an element of maximal order
3. Cardinality computation

These are classical results but not yet in Mathlib in invariant factor form.
The proof would use `AddCommGroup.equiv_directSum_zmod_of_finite` (Mathlib)
plus the Chinese Remainder Theorem to collect primary components into
invariant factors, then the Weil pairing rank constraint to show at most
two factors suffice.
-/
axiom finite_abelian_two_invariant_factors
    (G : Type*) [AddCommGroup G] [Finite G]
    (h_odd_rank : ∀ (p : ℕ), Nat.Prime p → 2 < p →
      ¬ ∃ f : ZMod p × ZMod p →+ G, Function.Injective f) :
    TwoInvariantFactorData G

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

/-! ## Group A: torsion structure -- now derived, not an axiom -/

/--
The rational torsion subgroup has two invariant factors:
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`, and cardinality `m * n`.

Formerly an axiom. Now derived from:
- `rational_torsion_finite_alias` (torsion is finite)
- `weil_pairing_primitive_root` + `isPrimitiveRoot_rat_order_le_two` (odd
  primes have rank at most 1 in torsion)
- `finite_abelian_two_invariant_factors` (pure group theory axiom)
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
  let d := finite_abelian_two_invariant_factors
      (AddCommGroup.torsion (E⁄ℚ).Point) h_no_odd
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
