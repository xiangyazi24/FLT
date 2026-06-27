# Q1074 (dm3): shortest Lean path for `HasFullRationalTorsion → IsPrimitiveRoot` over `ℚ`

## Bottom line

For the theorem

```lean
theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

the key point is correct: for `m ≥ 3`, the conclusion is impossible over `ℚ`, so the hypothesis `HasFullRationalTorsion E m` must be false.  But this observation is not itself a proof of falsity.  To use `False.elim`, Lean still needs a theorem of the form

```lean
¬ HasFullRationalTorsion E m
```

for `3 ≤ m`.

As of the FLT branch’s pinned Mathlib revision, the shortest practical proof path is therefore:

1. keep the existing `m = 1` and `m = 2` proofs;
2. for `m ≥ 3`, prove the theorem by contradiction from one bridge lemma:

   ```lean
   no_full_rational_torsion_of_three_le :
     ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ},
       3 ≤ m → ¬ HasFullRationalTorsion E m
   ```

3. decide later whether that bridge is justified by the Weil pairing, by determinant-of-Galois-representation, by Mazur, or by real Lie group classification.

If the goal is to minimize the new formalization burden **inside FLT**, the single bridge lemma above is the shortest interface.  If the goal is to keep the bridge mathematically close to the standard proof but avoid implementing a full pairing API, then the determinant route is the best interface:

```text
full rational m-torsion
  ⇒ mod-m Galois representation is trivial
  ⇒ det ρ_m is trivial
  ⇒ cyclotomic character mod m is trivial
  ⇒ μ_m ⊆ ℚ
  ⇒ rational primitive m-th root exists.
```

However, that is not currently just wiring together existing Mathlib declarations.  The missing hard theorem is essentially

```text
det ρ_m = χ_m.
```

Classically this theorem is usually proved using the Weil pairing.  So the determinant route avoids formalizing the *full user-facing Weil pairing API*, but it does not avoid the underlying theorem.

## Important warning about the “vacuous” argument

The lemma

```lean
isPrimitiveRoot_rat_order_le_two :
  IsPrimitiveRoot ζ m → m ≤ 2
```

or an equivalent theorem is useful only **after** one has produced a rational primitive root.  It gives

```text
(∃ ζ : ℚ, IsPrimitiveRoot ζ m) → m ≤ 2.
```

It does not by itself prove

```text
¬ HasFullRationalTorsion E m.
```

Thus this would be circular:

```lean
-- Bad / circular idea:
-- prove `¬ hfull` because otherwise the current theorem gives a primitive root,
-- then use `¬ hfull` to prove the current theorem by exfalso.
```

A non-circular proof needs an independent bridge from `hfull` to either:

```lean
False
```

or

```lean
∃ ζ : ℚ, IsPrimitiveRoot ζ m.
```

The determinant theorem is one such bridge; the Weil pairing theorem is another formulation of essentially the same bridge.

## Assessment of the proposed alternatives

### 1. Determinant of the mod-`m` Galois representation

Mathematically, yes.  This is the cleanest alternative interface:

```text
det ρ_m = ε_m,
```

where `ε_m` is the mod-`m` cyclotomic character.

If `E[m]` is rational, the Galois action on `E[m]` is trivial, so `ρ_m σ = 1` for every `σ`.  Hence `det ρ_m σ = 1`, so `ε_m σ = 1` for every `σ`.  That means all `m`-th roots of unity are Galois-fixed, hence defined over `ℚ`.

But in Lean this route still needs several nontrivial bridges.

First, your hypothesis is an injection

```lean
ZMod m × ZMod m →+ (E⁄ℚ).Point
```

not an explicit equality with the geometric `m`-torsion.  To conclude that the geometric Galois representation is trivial, one needs something like:

```lean
fullRationalTorsion_trivial_galoisRep :
  HasFullRationalTorsion E m →
  ∀ σ, WeierstrassCurve.galoisRep E m σ = 1
```

That lemma itself needs the statement that the geometric `m`-torsion has size at most, or exactly, `m^2`, plus the base-change/fixed-point comparison between rational points and geometric torsion.

Second, one needs the determinant theorem:

```lean
det_galoisRep_eq_modularCyclotomicCharacter :
  ∀ σ, det (WeierstrassCurve.galoisRep E m σ) = χ_m σ
```

This is the serious arithmetic input.  It is precisely the determinant form of the Weil-pairing theorem.

Third, one needs the descent step from trivial cyclotomic character to a rational primitive root.  Mathlib has substantial cyclotomic-character infrastructure, including `modularCyclotomicCharacter` and the comparison

```lean
IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
```

but this does not by itself manufacture a `ζ : ℚ`.  One still needs the Galois-fixed-implies-rational descent statement for a chosen primitive root in an algebraic closure, or an equivalent cyclotomic-field theorem.

So: determinant is the best **interface**, but not a zero-sorry route.

### 2. Structure of `E(ℚ)_tors`

Finiteness alone does not help.  From

```lean
ZMod m × ZMod m ↪ E(ℚ)
```

we get at least `m^2` rational torsion points.  For `m ≥ 3`, that is at least `9` points.  But finiteness of the torsion subgroup gives no contradiction; a finite group can have size `9`, `16`, `25`, and so on.

What would help is Mazur’s torsion theorem, or at least its corollary that `E(ℚ)_tors` never contains `ZMod m × ZMod m` for `m ≥ 3`.  That would immediately prove

```lean
no_full_rational_torsion_of_three_le
```

but Mathlib does not have Mazur’s theorem in a form that can be used here.  Formalizing Mazur is much larger than formalizing the determinant/Weil-pairing bridge.

There is also a real-analytic alternative:

```text
E(ℝ) ≃ S¹        or        E(ℝ) ≃ S¹ × Z/2Z.
```

Therefore `E(ℝ)` cannot contain `(Z/mZ)^2` for `m ≥ 3`.  Since `E(ℚ) ↪ E(ℝ)`, this would also prove `¬ HasFullRationalTorsion E m`.  Mathematically this avoids the Weil pairing, but in Lean it would require a formal classification of the real Lie group of a Weierstrass elliptic curve.  That is not presently the shortest route in Mathlib.

### 3. Purely number-theoretic route: Kronecker-Weber / NOS / class field theory

This is not shorter in Lean.

Kronecker-Weber describes abelian extensions of `ℚ`, but it does not by itself connect rational `m`-torsion on an elliptic curve to `ℚ(ζ_m)`.  That connection is again the determinant/cyclotomic-character theorem for the Galois action on `E[m]`, or an equivalent Weil-pairing statement.

Néron-Ogg-Shafarevich is also much heavier than needed.  It concerns ramification and good reduction.  To extract `ζ_m ∈ ℚ` from full rational `m`-torsion, one still needs the determinant/cyclotomic relation.

So these routes are mathematically valid context, but they are worse formalization targets than the determinant bridge.

### 4. Wiring `galoisRep`, `nTorsion`, and `IsPrimitiveRoot.autToPow`

The cyclotomic side is the part Mathlib is best prepared for.  The relevant shape is already present around:

```lean
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
```

with declarations such as:

```lean
modularCyclotomicCharacter
IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
```

But the elliptic-curve side is the blocker.  Even if your environment has declarations named

```lean
WeierstrassCurve.galoisRep
WeierstrassCurve.nTorsion
```

and even if `galoisRep` is currently defined using `sorry`, the following theorem is not automatic:

```lean
det (WeierstrassCurve.galoisRep E m σ) = modularCyclotomicCharacter ... σ
```

Nor is this automatic from an injection into rational points:

```lean
HasFullRationalTorsion E m → WeierstrassCurve.galoisRep E m σ = 1.
```

Those are the missing bridges.

My recommendation for FLT is therefore not to try to wire `galoisRep` directly unless you are willing to add the determinant theorem as a new trusted/sorried theorem.  With that theorem admitted, the remaining proof is short.  Without it, the determinant route expands into a formalization of essentially the same arithmetic content as the Weil pairing.

## The shortest Lean interface

The cleanest FLT-local interface is the contradiction lemma:

```lean
import Mathlib

noncomputable section

namespace FLT

/--
Project-local bridge theorem.

Mathematically this can be justified by any of the following:

* Weil pairing nondegeneracy plus Galois equivariance;
* determinant identity `det ρ_m = χ_m`;
* Mazur's torsion theorem;
* classification of the real Lie group `E(ℝ)`.

For the current FLT theorem, this is the smallest useful interface.
-/
axiom no_full_rational_torsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m

end FLT
```

Then the target theorem becomes only a case split.  The following code shows the intended shape.  Replace the namespace and the import with the actual FLT file containing `HasFullRationalTorsion` and the existing `m = 1`, `m = 2` lemmas if they already exist.

```lean
import Mathlib

noncomputable section

namespace FLT

/-- Existing project definition.  Do not redefine this if it already exists. -/
-- def HasFullRationalTorsion (E : WeierstrassCurve ℚ) (m : ℕ) : Prop :=
--   ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

axiom no_full_rational_torsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m

private theorem primitive_root_rat_one : IsPrimitiveRoot (1 : ℚ) 1 := by
  simpa using (IsPrimitiveRoot.one : IsPrimitiveRoot (1 : ℚ) 1)

private theorem primitive_root_rat_two : IsPrimitiveRoot (-1 : ℚ) 2 := by
  refine IsPrimitiveRoot.mk_of_lt (-1 : ℚ) (by norm_num) (by norm_num) ?_
  intro l hl hlt hpow
  interval_cases l
  norm_num at hpow

theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  have hm_cases : m = 1 ∨ m = 2 ∨ 3 ≤ m := by omega
  rcases hm_cases with rfl | rfl | hm3
  · exact ⟨1, primitive_root_rat_one⟩
  · exact ⟨-1, primitive_root_rat_two⟩
  · exact False.elim ((no_full_rational_torsion_of_three_le E hm3) hfull)

end FLT
```

This code intentionally keeps the hard arithmetic in one named bridge.  That makes the dependency explicit and prevents the current theorem from hiding a partial Weil-pairing formalization behind many small local `sorry`s.

## If you prefer the determinant-shaped bridge

If you want the bridge to be less “Mazur-like” and closer to the standard Weil-pairing proof, use this as the conceptual interface instead:

```lean
import Mathlib
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

noncomputable section

namespace FLT

/-
Schematic only: the exact type depends on the actual API of
`WeierstrassCurve.galoisRep` and `WeierstrassCurve.nTorsion` in the project.
-/

/-- Full rational `m`-torsion makes the geometric mod-`m` representation trivial. -/
axiom galoisRep_trivial_of_full_rational_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) :
    HasFullRationalTorsion E m →
    -- ∀ σ, WeierstrassCurve.galoisRep E m σ = 1
    True

/-- Determinant of the mod-`m` representation is the mod-`m` cyclotomic character. -/
axiom det_galoisRep_eq_modularCyclotomicCharacter
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) :
    -- ∀ σ, det (WeierstrassCurve.galoisRep E m σ) = χ_m σ
    True

/-- Trivial mod-`m` cyclotomic character gives a rational primitive `m`-th root. -/
axiom exists_rat_primitiveRoot_of_trivial_modularCyclotomicCharacter
    {m : ℕ} (hm : 0 < m) :
    -- CyclotomicCharacterIsTrivialOverRat m →
    True →
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

end FLT
```

The reason this is only schematic is that the exact determinant expression depends on how `nTorsion` is represented: as a finite additive group, a `ZMod m`-module with a transported basis, or a matrix representation.  For composite `m`, this is over the ring `ZMod m`, not over a field, so the determinant should be a determinant over `ZMod m` after choosing or transporting a rank-two basis.

The determinant route becomes genuinely short only after the following are available:

```lean
fullRationalTorsion_trivial_galoisRep
card_or_free_rank_two_nTorsion
baseChange_rational_points_fixed_by_Gal
det_galoisRep_eq_modularCyclotomicCharacter
fixed_primitiveRoot_descends_to_rat
```

Among these, `det_galoisRep_eq_modularCyclotomicCharacter` is the real arithmetic theorem.

## Recommended final strategy

For FLT, I would do this:

1. Add `no_full_rational_torsion_of_three_le` as the single explicit bridge lemma.
2. Close `weil_pairing_gives_primitive_root` by the three-way split `m = 1`, `m = 2`, `3 ≤ m`.
3. Put a comment on `no_full_rational_torsion_of_three_le` saying it is intended to be discharged later by the determinant identity `det ρ_m = χ_m`, equivalently by the Weil pairing.

This is the shortest robust path because it isolates the missing mathematics in one theorem whose statement is exactly what the FLT proof needs.  Trying to use `galoisRep` directly before the determinant theorem exists will likely create more small `sorry`s, not fewer.
