# Q1240 (dm1): Mathlib bridge from `Submodule.torsionBy` to `Set.ncard`

## Direct answers

I read `Mathlib/Algebra/Module/Torsion/Basic.lean`. The relevant definition is:

```lean
def Submodule.torsionBy (a : R) : Submodule R M :=
  (DistribSMul.toLinearMap R M a).ker
```

and the key membership theorem is:

```lean
@[simp]
theorem Submodule.mem_torsionBy_iff (x : M) :
    x ∈ Submodule.torsionBy R M a ↔ a • x = 0 :=
  Iff.rfl
```

So for an additive group `G`, the exact predicate of

```lean
Submodule.torsionBy ℤ G (m : ℤ)
```

is

```lean
(m : ℤ) • g = 0
```

not `m * g = 0`. For elliptic-curve points, use additive scalar notation:

```lean
(m : ℕ) • P = 0
```

The natural-scalar and integer-scalar sets are equal for natural `m`, because Mathlib has

```lean
Nat.cast_smul_eq_nsmul (R := ℤ) (M := G) m g :
  (m : ℤ) • g = (m : ℕ) • g
```

For `Set.ncard`, the important theorem is:

```lean
Nat.card_coe_set_eq (s : Set α) : Nat.card s = s.ncard
```

It is proved by `rfl`, so the bridge from `Set.ncard s` to `Nat.card s` is definitional.

For set-level finiteness from a finite subtype, use:

```lean
Set.toFinite s
```

after installing the finite subtype instance with `haveI`. The equivalence is also exposed as:

```lean
Set.finite_coe_iff : Finite s ↔ s.Finite
Set.Finite.to_subtype : s.Finite → Finite s
```

For the injection/cardinality step, use:

```lean
Nat.card_le_card_of_injective f hf
```

The codomain must be finite. For `Fin 2 × ZMod m`, use `hm : 0 < m` to get `NeZero m`, and then `simp [Nat.card_fin]` reduces

```lean
Nat.card (Fin 2 × ZMod m)
```

to `2 * m`, using the simp theorems `Nat.card_prod` and `Nat.card_zmod`.

## Copy-paste Lean bridge lemmas

```lean
import Mathlib

noncomputable section

/-- For an additive group, integer scalar multiplication by a natural integer is the same as
natural scalar multiplication. -/
lemma int_smul_nat_eq_nsmul
    {G : Type*} [AddCommGroup G] (m : ℕ) (g : G) :
    (m : ℤ) • g = (m : ℕ) • g := by
  simpa using (Nat.cast_smul_eq_nsmul (R := ℤ) (M := G) m g)

/-- Exact membership predicate for `Submodule.torsionBy ℤ G (m : ℤ)`. -/
lemma mem_torsionBy_int_iff
    {G : Type*} [AddCommGroup G] (m : ℕ) (g : G) :
    g ∈ Submodule.torsionBy ℤ G (m : ℤ) ↔ (m : ℤ) • g = 0 := by
  rw [Submodule.mem_torsionBy_iff]

/-- The carrier of `Submodule.torsionBy ℤ G (m : ℤ)` is the natural-`m` torsion set. -/
lemma torsionBy_int_carrier_eq_setOf_nsmul
    {G : Type*} [AddCommGroup G] (m : ℕ) :
    ((Submodule.torsionBy ℤ G (m : ℤ) : Submodule ℤ G) : Set G) =
      {g : G | (m : ℕ) • g = 0} := by
  ext g
  rw [Submodule.mem_torsionBy_iff, int_smul_nat_eq_nsmul]

/-- The two subtype presentations of a submodule's carrier are equivalent. -/
private def submoduleCarrierEquiv
    {G : Type*} [AddCommGroup G] (S : Submodule ℤ G) :
    ((S : Set G)) ≃ S where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by
    cases x
    rfl
  right_inv x := by
    cases x
    rfl

/-- If the submodule subtype is finite, then its carrier set is `Set.Finite`. -/
lemma setFinite_of_finite_submodule
    {G : Type*} [AddCommGroup G]
    (S : Submodule ℤ G) (hS : Finite S) :
    Set.Finite (S : Set G) := by
  haveI : Finite S := hS
  haveI : Finite ((S : Set G)) :=
    Finite.of_equiv S (submoduleCarrierEquiv S).symm
  exact Set.toFinite (S : Set G)

/-- From `Finite (Submodule.torsionBy ...)`, get finiteness of the natural-`m` torsion set. -/
lemma setFinite_setOf_nsmul_of_finite_torsionBy
    {G : Type*} [AddCommGroup G] (m : ℕ)
    (hfin : Finite (Submodule.torsionBy ℤ G (m : ℤ))) :
    Set.Finite {g : G | (m : ℕ) • g = 0} := by
  rw [← torsionBy_int_carrier_eq_setOf_nsmul (G := G) m]
  exact setFinite_of_finite_submodule
    (Submodule.torsionBy ℤ G (m : ℤ)) hfin

/-- `Set.ncard` of the natural-`m` torsion set is `Nat.card` of `Submodule.torsionBy`. -/
lemma ncard_setOf_nsmul_eq_nat_card_torsionBy
    {G : Type*} [AddCommGroup G] (m : ℕ) :
    Set.ncard {g : G | (m : ℕ) • g = 0} =
      Nat.card (Submodule.torsionBy ℤ G (m : ℤ)) := by
  rw [← torsionBy_int_carrier_eq_setOf_nsmul (G := G) m]
  calc
    Set.ncard (((Submodule.torsionBy ℤ G (m : ℤ) : Submodule ℤ G) : Set G))
        = Nat.card (((Submodule.torsionBy ℤ G (m : ℤ) : Submodule ℤ G) : Set G)) := by
          exact (Nat.card_coe_set_eq _).symm
    _ = Nat.card (Submodule.torsionBy ℤ G (m : ℤ)) := by
          exact Nat.card_congr
            (submoduleCarrierEquiv (Submodule.torsionBy ℤ G (m : ℤ)))

/-- Cardinal bound from an injection into `Fin 2 × ZMod m`. -/
lemma nat_card_le_two_mul_of_injective
    {S : Type*} (m : ℕ) (hm : 0 < m)
    (f : S → Fin 2 × ZMod m) (hf : Function.Injective f) :
    Nat.card S ≤ 2 * m := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  have hle : Nat.card S ≤ Nat.card (Fin 2 × ZMod m) :=
    Nat.card_le_card_of_injective f hf
  simpa [Nat.card_fin] using hle

/-- The final bridge in the form usually needed for elliptic-curve torsion. -/
lemma ncard_setOf_nsmul_le_two_mul_of_injective
    {G : Type*} [AddCommGroup G] (m : ℕ) (hm : 0 < m)
    (f : Submodule.torsionBy ℤ G (m : ℤ) → Fin 2 × ZMod m)
    (hf : Function.Injective f) :
    Set.ncard {g : G | (m : ℕ) • g = 0} ≤ 2 * m := by
  rw [ncard_setOf_nsmul_eq_nat_card_torsionBy (G := G) m]
  exact nat_card_le_two_mul_of_injective m hm f hf
```

## Instantiation for elliptic-curve real points

Use `(E⁄ℝ).Point`, not `(E/R).Point`, and use `•`, not `*`.

```lean
import Mathlib

noncomputable section

open WeierstrassCurve

example
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [DecidableEq ℝ]
    (m : ℕ) (hm : 0 < m)
    (f : Submodule.torsionBy ℤ (E⁄ℝ).Point (m : ℤ) → Fin 2 × ZMod m)
    (hf : Function.Injective f) :
    Set.ncard {P : (E⁄ℝ).Point | (m : ℕ) • P = 0} ≤ 2 * m := by
  exact ncard_setOf_nsmul_le_two_mul_of_injective
    (G := (E⁄ℝ).Point) m hm f hf
```

## Minimal answers to the four questions

1. Exact membership predicate:

```lean
g ∈ Submodule.torsionBy ℤ G (m : ℤ) ↔ (m : ℤ) • g = 0
```

Use:

```lean
rw [Submodule.mem_torsionBy_iff]
```

2. The two sets are equal:

```lean
((Submodule.torsionBy ℤ G (m : ℤ) : Submodule ℤ G) : Set G) =
  {g : G | (m : ℕ) • g = 0}
```

Use `torsionBy_int_carrier_eq_setOf_nsmul` above. The only coercion issue is resolved by:

```lean
Nat.cast_smul_eq_nsmul (R := ℤ) (M := G) m g
```

3. From finite subtype to `Set.Finite`, use:

```lean
haveI : Finite S := hS
exact Set.toFinite (S : Set G)
```

For a submodule where Lean needs help identifying the carrier subtype, use `setFinite_of_finite_submodule` above.

4. From an injective map to `Fin 2 × ZMod m`, use:

```lean
haveI : NeZero m := ⟨hm.ne'⟩
have hle : Nat.card S ≤ Nat.card (Fin 2 × ZMod m) :=
  Nat.card_le_card_of_injective f hf
simpa [Nat.card_fin] using hle
```

The `simpa` step uses `[simp]` theorems:

```lean
Nat.card_prod
Nat.card_zmod
```

and the explicit theorem:

```lean
Nat.card_fin
```
