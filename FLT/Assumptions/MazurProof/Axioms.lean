import FLT.EllipticCurve.Torsion
import FLT.Assumptions.MazurProof.NoncyclicN10
import FLT.Assumptions.MazurProof.DescentBridgeN14
import FLT.Assumptions.MazurProof.DescentBridgeN16
import FLT.Assumptions.MazurProof.GroupTheory

/-!
# Axioms for the Mazur torsion-bound proof scaffold

This file collects the hard mathematical inputs needed to prove the numerical
bound `|E(ℚ)_tors| ≤ 16`.  The axioms are grouped by expected discharge
priority.
-/

open scoped WeierstrassCurve.Affine

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

/-! ## Group A: torsion structure, expected easiest to discharge -/


/--
The rational torsion subgroup has two invariant factors:
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`, and cardinality `m * n`.
-/
axiom rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E

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

/-! ## Group B: Weil pairing -/

/--
Weil pairing consequence: if all `m`-torsion points are rational, then `ℚ`
contains a primitive `m`-th root of unity.
-/
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

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
