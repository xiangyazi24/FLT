# Q1194 (dm2): pure cardinality lemma for `ZMod m × ZMod m`

Lean uses additive scalar multiplication for an additive group:

```lean
{g : G | m • g = 0}
```

The finite hypothesis on this set is included explicitly because `Set.ncard_le_ncard` needs finiteness of the larger set.

## Mathlib-only code

```lean
import Mathlib

namespace FLT

/--
Core version: if every element of the domain is annihilated by `m`, then an
injective additive map from `ZMod m × ZMod m` lands injectively in the
`m`-torsion subset of `G`.  If that subset is finite and has `ncard ≤ 2*m`,
then `m ≤ 2`.
-/
theorem zmod_prod_injective_order_le_two_of_annihilated
    {G : Type*} [AddCommGroup G] {m : ℕ}
    (f : ZMod m × ZMod m →+ G)
    (hf : Function.Injective (f : ZMod m × ZMod m → G))
    (hann_dom : ∀ x : ZMod m × ZMod m, m • x = 0)
    (hfinite : ({g : G | m • g = 0} : Set G).Finite)
    (hncard : ({g : G | m • g = 0} : Set G).ncard ≤ 2 * m) :
    m ≤ 2 := by
  by_cases hm0 : m = 0
  · omega

  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  haveI : NeZero m := ⟨hm0⟩

  let T : Set G := {g : G | m • g = 0}

  have hRangeSubset : Set.range (f : ZMod m × ZMod m → G) ⊆ T := by
    intro g hg
    rcases hg with ⟨x, rfl⟩
    dsimp [T]
    calc
      m • f x = f (m • x) := (f.map_nsmul x m).symm
      _ = f 0 := by rw [hann_dom x]
      _ = 0 := f.map_zero

  have hfiniteT : T.Finite := by
    simpa [T] using hfinite

  have hRangeLeT :
      (Set.range (f : ZMod m × ZMod m → G)).ncard ≤ T.ncard := by
    exact Set.ncard_le_ncard hRangeSubset hfiniteT

  have hTncard : T.ncard ≤ 2 * m := by
    simpa [T] using hncard

  have hRangeCard :
      (Set.range (f : ZMod m × ZMod m → G)).ncard = m * m := by
    calc
      (Set.range (f : ZMod m × ZMod m → G)).ncard
          = Nat.card (ZMod m × ZMod m) := by
              exact Set.ncard_range_of_injective
                (f := (f : ZMod m × ZMod m → G)) hf
      _ = m * m := by
              simp [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]

  have hsq : m * m ≤ 2 * m := by
    calc
      m * m = (Set.range (f : ZMod m × ZMod m → G)).ncard := hRangeCard.symm
      _ ≤ T.ncard := hRangeLeT
      _ ≤ 2 * m := hTncard

  nlinarith [hmpos, hsq]

/--
Version stated with the additive-order hypothesis.  The conversion from
`addOrderOf x ∣ m` to `m • x = 0` uses
`addOrderOf_dvd_iff_nsmul_eq_zero`.
-/
theorem zmod_prod_injective_order_le_two
    {G : Type*} [AddCommGroup G] {m : ℕ}
    (f : ZMod m × ZMod m →+ G)
    (hf : Function.Injective (f : ZMod m × ZMod m → G))
    (horder_dom : ∀ x : ZMod m × ZMod m, addOrderOf x ∣ m)
    (hfinite : ({g : G | m • g = 0} : Set G).Finite)
    (hncard : ({g : G | m • g = 0} : Set G).ncard ≤ 2 * m) :
    m ≤ 2 := by
  exact zmod_prod_injective_order_le_two_of_annihilated
    f hf
    (fun x => (addOrderOf_dvd_iff_nsmul_eq_zero).mp (horder_dom x))
    hfinite hncard

end FLT
```

## Proof outline

The proof maps `Set.range f` into `{g : G | m • g = 0}`, applies `Set.ncard_le_ncard`, computes the range cardinality by `Set.ncard_range_of_injective`, evaluates the domain size with `ZMod.card` and `Fintype.card_prod`, and finishes from `m * m ≤ 2 * m` by `nlinarith`.
