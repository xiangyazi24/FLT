import FLT.Assumptions.MazurProof.TorsionFiniteFromOrderBound

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
  exact fullRationalTorsion_order_le_two_route4B E hm hfull

private theorem n_in_mazur_list_of_structure
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (d : TorsionStructureData E) :
    d.n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ) :=
  mazur_cyclic_order_bound E d.n_pos d.has_point_order_n

private theorem even_forbidden_of_two_dvd {n : ℕ} (hdvd : 2 ∣ n) (hgt : 8 < n)
    (hmem : n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ)) :
    n = 10 ∨ n = 12 := by
  have hcases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
        n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem n_le_twelve_of_mazur_list {n : ℕ}
    (hmem : n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ)) :
    n ≤ 12 := by
  have hcases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
        n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

/--
Mazur's bound for the rational torsion subgroup, proved from the axioms in this
scaffold.  The first component records finiteness; the second is the numerical
bound.
-/
theorem mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (torsionSet E).Finite ∧ (torsionSet E).ncard ≤ 16 := by
  have hfin : (torsionSet E).Finite := rational_torsion_finite E
  refine ⟨hfin, ?_⟩
  let d := rational_torsion_two_invariant_factors E hfin
  have hm_le : d.m ≤ 2 :=
    full_rational_torsion_order_le_two E d.m_pos
      (first_invariant_factor_full_torsion E d.m_pos d.n_pos d.dvd_mn d.has_structure)
  have hn_mem := n_in_mazur_list_of_structure E d
  have hm_ge_one : 1 ≤ d.m := d.m_pos
  have hm_cases : d.m = 1 ∨ d.m = 2 := by omega
  rw [d.card_eq]
  rcases hm_cases with hm | hm
  · rw [hm]
    have hn_le : d.n ≤ 12 := n_le_twelve_of_mazur_list hn_mem
    omega
  · have hdvd2 : 2 ∣ d.n := by simpa [hm] using d.dvd_mn
    have hcontains : ContainsZ2xZn E d.n := by
      simpa [ContainsZ2xZn, hm] using d.has_structure
    rw [hm]
    have hn_le_eight : d.n ≤ 8 := by
      by_contra hle8
      have hgt8 : 8 < d.n := by omega
      have hforbidden : d.n = 10 ∨ d.n = 12 :=
        even_forbidden_of_two_dvd hdvd2 hgt8 hn_mem
      exact no_Z2_cross_Zn_forbidden E hforbidden hcontains
    omega

/-- The numerical component of `mazur_torsion_bound`. -/
theorem mazur_torsion_bound_ncard (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (torsionSet E).ncard ≤ 16 :=
  (mazur_torsion_bound E).2

end MazurProof
