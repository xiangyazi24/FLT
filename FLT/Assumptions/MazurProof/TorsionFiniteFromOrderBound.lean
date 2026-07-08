import FLT.Assumptions.MazurProof.Axioms
import FLT.Assumptions.MazurProof.RealTorsionBound

/-!
# Rational torsion finiteness from Mazur's cyclic order bound

This proves rational torsion finiteness without using Mordell-Weil finite
generation.  The input is the pointwise cyclic order bound, plus the already
proved real `n`-torsion bound.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

private theorem dvd_2520_of_mem_mazur_list {n : ℕ}
    (hmem : n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ)) :
    n ∣ 2520 := by
  have hcases :
      n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
        n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h
  all_goals rw [h]; norm_num

private theorem torsionSet_subset_2520_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    torsionSet E ⊆ {P : (E⁄ℚ).Point | (2520 : ℕ) • P = 0} := by
  intro P hP
  have hord_pos :
      0 < addOrderOf P ∧ HasRationalPointOfOrder E (addOrderOf P) :=
    ⟨((AddCommGroup.mem_torsion P).mp hP).addOrderOf_pos, ⟨P, rfl⟩⟩
  have hmem := mazur_cyclic_order_bound E hord_pos.2
  have hdvd : addOrderOf P ∣ 2520 := dvd_2520_of_mem_mazur_list hmem
  exact (addOrderOf_dvd_iff_nsmul_eq_zero (x := P)).mp hdvd

/--
The rational torsion subgroup is finite, using only Mazur's cyclic order bound
and the real `n`-torsion bound.
-/
theorem rational_torsion_finite (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (torsionSet E).Finite := by
  let bc : (E⁄ℚ).Point →+ (E⁄ℝ).Point :=
    WeierstrassCurve.Affine.Point.baseChange ℚ ℝ
  have hbc_inj : Function.Injective bc :=
    WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId ℚ ℝ)
  obtain ⟨hfinReal, hcardReal⟩ := card_E_R_torsion_le E 2520 (by norm_num)
  obtain ⟨hfinRat, _hcardRat⟩ :=
    nTorsionSet_ncard_le_of_injective_addMonoidHom bc hbc_inj 2520 (2 * 2520)
      hfinReal hcardReal
  exact hfinRat.subset (torsionSet_subset_2520_torsion E)

end MazurProof
