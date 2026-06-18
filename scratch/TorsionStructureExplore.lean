import Mathlib
import FLT.Assumptions.MazurProof.Axioms

/-!
# Exploration for `rational_torsion_two_invariant_factors`

This file records the Mathlib API relevant to replacing the current axiom

```
MazurProof.rational_torsion_two_invariant_factors
```

by a proof from finite abelian group structure plus elliptic-curve torsion
input.
-/

open scoped WeierstrassCurve.Affine DirectSum

namespace TorsionStructureExplore

open MazurProof

/-! ## Torsion subgroup API -/

#check AddCommGroup.torsion
#check AddCommGroup.mem_torsion
#check AddCommGroup.torsion_eq_top_iff
#check AddCommGroup.le_comap_torsion
#check Submodule.torsion
#check Submodule.torsion_isTorsion
#check Submodule.torsion_int
#check Submodule.torsionBy
#check Submodule.mem_torsionBy_iff

/-! ## Finite abelian group structure theorem API -/

#check AddCommGroup.equiv_free_prod_directSum_zmod
#check AddCommGroup.equiv_directSum_zmod_of_finite
#check AddCommGroup.equiv_directSum_zmod_of_finite'
#check CommGroup.equiv_prod_multiplicative_zmod_of_finite
#check Module.equiv_directSum_of_isTorsion
#check Module.equiv_free_prod_directSum
#check DirectSum.addEquivProd

/-! ## Cardinality API -/

#check Set.ncard
#check Set.ncard_eq_toFinset_card
#check Set.fintypeCard_eq_ncard
#check Set.ncard_congr'
#check Set.Finite.to_subtype
#check Fintype.card_congr
#check Nat.card_congr
#check Fintype.card_prod
#check Nat.card_prod
#check ZMod.card
#check Nat.card_zmod

/-! ## Target axiom and bundled data -/

#check MazurProof.torsionSet
#check MazurProof.TorsionStructureData
#check MazurProof.rational_torsion_finite
#check MazurProof.rational_torsion_two_invariant_factors
#check MazurProof.first_invariant_factor_full_torsion

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- The scaffold's `torsionSet` is definitionally the set underlying
`AddCommGroup.torsion`. -/
example :
    torsionSet E =
      ((AddCommGroup.torsion (E⁄ℚ).Point : AddSubgroup (E⁄ℚ).Point) : Set (E⁄ℚ).Point) :=
  rfl

/-- Finiteness of the torsion set gives finiteness of the subgroup subtype. -/
example (hfin : (torsionSet E).Finite) :
    Finite (AddCommGroup.torsion (E⁄ℚ).Point) := by
  exact hfin.to_subtype

/-- Once finite, `Set.ncard` is the same as `Fintype.card` of the set subtype. -/
example (hfin : (torsionSet E).Finite) :
    (torsionSet E).ncard = hfin.toFinset.card := by
  exact Set.ncard_eq_toFinset_card (torsionSet E) hfin

/-- The finite abelian group theorem applies to the torsion subgroup subtype
after proving finiteness. -/
example (hfin : (torsionSet E).Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (n : ι → ℕ),
      (∀ i, 1 < n i) ∧
        Nonempty (AddCommGroup.torsion (E⁄ℚ).Point ≃+ ⨁ i, ZMod (n i)) := by
  classical
  haveI : Finite (AddCommGroup.torsion (E⁄ℚ).Point) := hfin.to_subtype
  exact AddCommGroup.equiv_directSum_zmod_of_finite'
    (AddCommGroup.torsion (E⁄ℚ).Point)

/--
If a future proof supplies an additive equivalence
`E(ℚ)_tors ≃+ ZMod m × ZMod n`, the `card_eq` field follows from `Set.ncard`
and standard cardinality lemmas.
-/
example (_hfin : (torsionSet E).Finite) {m n : ℕ}
    (e : AddCommGroup.torsion (E⁄ℚ).Point ≃+ ZMod m × ZMod n) :
    (torsionSet E).ncard = m * n := by
  classical
  calc
    (torsionSet E).ncard = Nat.card (torsionSet E) := by
      rw [Nat.card_coe_set_eq]
    _ = Nat.card (ZMod m × ZMod n) := by
      exact Nat.card_congr e.toEquiv
    _ = m * n := by
      rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod]

end TorsionStructureExplore
