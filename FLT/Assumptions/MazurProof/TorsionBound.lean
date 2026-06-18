import FLT.Assumptions.MazurProof.RootsOfUnity
import FLT.Assumptions.MazurProof.Axioms

/-!
# Mazur torsion-bound proof scaffold

This file proves the numerical bound `|E(ℚ)_tors| ≤ 16` from the axioms in
`FLT.Assumptions.MazurProof.Axioms`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-- If `E` has full rational `m`-torsion, then `m ≤ 2`. -/
theorem full_rational_torsion_order_le_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) (hfull : HasFullRationalTorsion E m) : m ≤ 2 := by
  rcases weil_pairing_primitive_root E hm hfull with ⟨ζ, hζ⟩
  exact isPrimitiveRoot_rat_order_le_two hζ

private theorem n_le_sixteen_of_structure
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
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

/--
Mazur's bound for the size of the rational torsion subgroup, proved from the
axioms in this scaffold.
-/
theorem mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16 := by
  have _hfinite := rational_torsion_finite E
  let d := rational_torsion_two_invariant_factors E
  have hm_le : d.m ≤ 2 :=
    full_rational_torsion_order_le_two E d.m_pos
      (first_invariant_factor_full_torsion E d.has_structure)
  have hn_le : d.n ≤ 16 := n_le_sixteen_of_structure E d
  have hm_ge_one : 1 ≤ d.m := d.m_pos
  have hm_cases : d.m = 1 ∨ d.m = 2 := by omega
  change (torsionSet E).ncard ≤ 16
  rw [d.card_eq]
  rcases hm_cases with hm | hm
  · rw [hm]
    omega
  · have hdvd2 : 2 ∣ d.n := by simpa [hm] using d.dvd_mn
    have hcontains : ContainsZ2xZn E d.n := by
      simpa [ContainsZ2xZn, hm] using d.has_structure
    rw [hm]
    have hn_le_eight : d.n ≤ 8 := by
      by_contra hle8
      have hgt8 : 8 < d.n := by omega
      have hforbidden : d.n = 10 ∨ d.n = 12 ∨ d.n = 14 ∨ d.n = 16 :=
        even_forbidden_of_two_dvd hdvd2 hgt8 hn_le
      exact no_Z2_cross_Zn_forbidden E hforbidden hcontains
    omega

end MazurProof
