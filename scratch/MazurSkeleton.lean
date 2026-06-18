import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.RootsOfUnityQ

/-!
# Skeleton for Mazur's torsion bound over `ℚ`

This file keeps the hard arithmetic inputs as axioms and checks that the
standard bookkeeping gives the bound `|E(ℚ)_tors| ≤ 16`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurSkeleton

/-- The torsion subgroup of `E(ℚ)`, as a set, matching `FLT/Assumptions/Mazur.lean`. -/
abbrev torsionSet (E : WeierstrassCurve ℚ) : Set (E⁄ℚ).Point :=
  AddCommGroup.torsion (E⁄ℚ).Point

/-- Placeholder for "all `m`-torsion points of `E` are rational". -/
axiom HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop

/-- Placeholder for "there is a rational point of exact order `n` on `E`". -/
axiom HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop

/--
Placeholder for the structure theorem assertion
`E(ℚ)_tors ≃ ℤ/mℤ × ℤ/nℤ`, with `m ∣ n`.
-/
axiom HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop

/--
Weil pairing consequence: if all `m`-torsion points are rational, then `ℚ`
contains a primitive `m`-th root of unity.
-/
axiom weil_pairing_primitive_root (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

/--
The finite abelian group structure of the rational torsion subgroup.

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
  full_m_torsion : HasFullRationalTorsion E m
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n

axiom torsion_structure (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E

/-- Mazur's hard input: no rational point of order at least `17`. -/
axiom no_rational_point_of_order_ge_17 (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : 17 ≤ n) : ¬ HasRationalPointOfOrder E n

/-- Mazur's hard input excluding the remaining full-2-torsion cases above size `16`. -/
axiom no_Z2_cross_Zn_forbidden (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
    (hn : n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16) :
    ¬ HasTorsionStructure E 2 n

/-- If `E` has full rational `m`-torsion, then `m ≤ 2`. -/
theorem full_rational_torsion_order_le_two (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) : m ≤ 2 := by
  rcases weil_pairing_primitive_root E hm hfull with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ

private theorem n_le_sixteen_of_structure (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (d : TorsionStructureData E) : d.n ≤ 16 := by
  by_contra h
  have hn : 17 ≤ d.n := by omega
  exact no_rational_point_of_order_ge_17 E hn d.has_point_order_n

private theorem even_forbidden_of_two_dvd {n : ℕ} (hdvd : 2 ∣ n) (hgt : 8 < n)
    (hle : n ≤ 16) : n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 16 := by
  rcases hdvd with ⟨k, rfl⟩
  have hk_low : 4 < k := by omega
  have hk_high : k ≤ 8 := by omega
  interval_cases k <;> omega

/-- Skeleton version of Mazur's bound. -/
theorem mazur_statement_skeleton (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (torsionSet E).ncard ≤ 16 := by
  let d := torsion_structure E
  have hm_le : d.m ≤ 2 :=
    full_rational_torsion_order_le_two E d.m_pos d.full_m_torsion
  have hn_le : d.n ≤ 16 := n_le_sixteen_of_structure E d
  have hm_ge_one : 1 ≤ d.m := d.m_pos
  have hm_cases : d.m = 1 ∨ d.m = 2 := by omega
  rw [d.card_eq]
  rcases hm_cases with hm | hm
  · rw [hm]
    omega
  · have hdvd2 : 2 ∣ d.n := by simpa [hm] using d.dvd_mn
    have hstruct2 : HasTorsionStructure E 2 d.n := by simpa [hm] using d.has_structure
    rw [hm]
    have hn_le_eight : d.n ≤ 8 := by
      by_contra hle8
      have hgt8 : 8 < d.n := by omega
      have hforbidden : d.n = 10 ∨ d.n = 12 ∨ d.n = 14 ∨ d.n = 16 :=
        even_forbidden_of_two_dvd hdvd2 hgt8 hn_le
      exact no_Z2_cross_Zn_forbidden E hforbidden hstruct2
    omega

end MazurSkeleton
