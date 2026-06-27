# Q1307 (dm2): cardinal inequality into a subtype without an existing `Finite` codomain instance

## Main answer

You **cannot** get a `Finite` instance for the whole codomain from an injection

```lean
f : A → {x : B // P x}
```

and `[Finite A]` alone.  The direction is mathematically false: a finite type injects into an infinite type.  For example, `PUnit` injects into `{n : ℕ // True}`, but `{n : ℕ // True}` is infinite.

So the exact Lean answer is:

* `Finite.of_injective` pulls finiteness **backwards** along an injection:

  ```lean
  Finite.of_injective : [Finite β] → (f : α → β) → Function.Injective f → Finite α
  ```

* `Set.Finite.of_injOn` also pulls finiteness **backwards** from the target set to the source set:

  ```lean
  Set.Finite.of_injOn :
    Set.MapsTo f s t → Set.InjOn f s → t.Finite → s.Finite
  ```

* To push finiteness **forwards** from finite `A` to the subtype, you need **surjectivity** onto the subtype:

  ```lean
  Finite.of_surjective f hsurj
  ```

  or, for sets,

  ```lean
  Set.Finite.of_surjOn f hsurjOn hs
  ```

* If you only have an injection, what becomes finite is the **range/image**, not the whole codomain.

For `Nat.card`, the standard theorem really needs a finite codomain because `Nat.card` has junk value `0` on infinite types.  The theorem is:

```lean
Nat.card_le_card_of_injective {α β : Type*} [Finite β]
    (f : α → β) (hf : Function.Injective f) :
    Nat.card α ≤ Nat.card β
```

There is no unconditional `Nat.card` version for injections into possibly infinite types.  Use `ENat.card` if the codomain might be infinite.

## Exact incantations

```lean
import Mathlib

open Function

universe u v

section General

variable {A : Type u} {B : Type v} {P : B → Prop}
variable [Finite A]
variable (f : A → {x : B // P x})
variable (hf : Function.Injective f)

/-- If the subtype already has a `Finite` instance, just use the Nat-card theorem. -/
example [Finite {x : B // P x}] :
    Nat.card A ≤ Nat.card {x : B // P x} := by
  exact Nat.card_le_card_of_injective f hf

/-- If the ambient type `B` is finite, the subtype is finite automatically. -/
example [Finite B] :
    Nat.card A ≤ Nat.card {x : B // P x} := by
  haveI : Finite {x : B // P x} := inferInstance
  exact Nat.card_le_card_of_injective f hf

/-- If you have set-level finiteness of `{x | P x}`, turn it into subtype finiteness. -/
example (hPfin : Set.Finite ({x : B | P x} : Set B)) :
    Nat.card A ≤ Nat.card {x : B // P x} := by
  haveI : Finite {x : B // P x} := hPfin.to_subtype
  exact Nat.card_le_card_of_injective f hf

/-- If `f` is actually surjective onto the subtype, then the finite domain makes the subtype finite. -/
example (hsurj : Function.Surjective f) :
    Nat.card A ≤ Nat.card {x : B // P x} := by
  haveI : Finite {x : B // P x} := Finite.of_surjective f hsurj
  exact Nat.card_le_card_of_injective f hf

/-- With only injectivity, the range is finite, not the whole codomain. -/
example : Set.Finite (Set.range f) := by
  simpa [Set.image_univ] using
    (Set.finite_univ (α := A)).image f

/-- If the codomain may be infinite, use `ENat.card`: no finite codomain hypothesis. -/
example :
    (Nat.card A : ℕ∞) ≤ ENat.card {x : B // P x} := by
  simpa [ENat.card_eq_coe_natCard A] using
    (ENat.card_le_card_of_injective (f := f) hf)

/-- There is a `Nat.card` version without `[Finite β]`, but it needs the junk-zero side condition. -/
example (hzero : Nat.card {x : B // P x} = 0 → Nat.card A = 0) :
    Nat.card A ≤ Nat.card {x : B // P x} := by
  exact Finite.card_le_of_injective' (f := f) hf hzero

end General
```

## For `A = ZMod p × ZMod p`

If `p` is positive/prime and the subtype has a finite instance, this is the clean shape:

```lean
import Mathlib

open Function

example (p : ℕ) {B : Type*} {P : B → Prop}
    [Fact p.Prime]
    (f : ZMod p × ZMod p → {x : B // P x})
    (hf : Function.Injective f)
    [Finite {x : B // P x}] :
    p * p ≤ Nat.card {x : B // P x} := by
  have hcard :
      Nat.card (ZMod p × ZMod p) ≤ Nat.card {x : B // P x} := by
    exact Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod, Nat.card_zmod] using hcard
```

If Lean has trouble synthesizing finite instances for `ZMod p` from `[Fact p.Prime]`, add the local explicit instance:

```lean
  haveI : NeZero p := ⟨Fact.out.ne_zero⟩
```

before the `Nat.card_le_card_of_injective` line.

## If your map is into `B` instead of directly into the subtype

Suppose you have

```lean
g : A → B
hgP : ∀ a, P (g a)
hg_inj : Function.Injective g
```

then first package it into the subtype:

```lean
let f : A → {x : B // P x} := fun a => ⟨g a, hgP a⟩
have hf : Function.Injective f := by
  intro a a' h
  apply hg_inj
  exact congrArg Subtype.val h
```

Then use one of the cases above.

If you want to prove the subtype finite from the finite domain, you need surjectivity:

```lean
example {A : Type*} {B : Type*} {P : B → Prop} [Finite A]
    (g : A → B)
    (hgP : ∀ a, P (g a))
    (hsurj : ∀ y : B, P y → ∃ a : A, g a = y) :
    Finite {x : B // P x} := by
  let f : A → {x : B // P x} := fun a => ⟨g a, hgP a⟩
  have hf_surj : Function.Surjective f := by
    intro y
    rcases hsurj y.1 y.2 with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    ext
    exact ha
  exact Finite.of_surjective f hf_surj
```

## Bottom line

Use this when the subtype is known finite:

```lean
haveI : Finite {x : B // P x} := hPfin.to_subtype
exact Nat.card_le_card_of_injective f hf
```

Use this when the map is surjective onto the subtype:

```lean
haveI : Finite {x : B // P x} := Finite.of_surjective f hsurj
exact Nat.card_le_card_of_injective f hf
```

Use this when the codomain may be infinite:

```lean
have hENat : (Nat.card A : ℕ∞) ≤ ENat.card {x : B // P x} := by
  simpa [ENat.card_eq_coe_natCard A] using
    (ENat.card_le_card_of_injective (f := f) hf)
```

Do **not** try to prove `[Finite {x : B // P x}]` from injectivity of `A → {x : B // P x}` and `[Finite A]`; that implication is false.
