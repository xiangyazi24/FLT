# Q1221 (dm3): n-torsion finiteness search report

## Executive answer

For the FLT repo at branch `scratch`, Mathlib is pinned by `lake-manifest.json` to:

```text
leanprover-community/mathlib4 @ 96fd0fff3b8837985ae21dd02e712cb5df72ec05
```

At that pinned Mathlib revision, I do **not** find a Mathlib theorem saying the elliptic-curve `n`-torsion subgroup is finite. The closest exact theorem is in the FLT repo itself:

```lean
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) :
    Finite (E.nTorsion n) := sorry
```

This is in `FLT/EllipticCurve/Torsion.lean`, line 46. It is an FLT theorem stub using `sorry`, not an already-proved Mathlib theorem.

There is also an FLT `Module.Finite` instance for `E.nTorsion n` as a `ZMod n` module at line 72, again with `sorry`.

## Files actually read

I read these files through the GitHub connector:

```text
xiangyazi24/FLT:scratch/lake-manifest.json
xiangyazi24/FLT:scratch/FLT/EllipticCurve/Torsion.lean
leanprover-community/mathlib4:96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean
leanprover-community/mathlib4:96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
leanprover-community/mathlib4:96fd0fff3b8837985ae21dd02e712cb5df72ec05/Mathlib/Algebra/Module/Torsion/Basic.lean
```

I also checked whether this pinned Mathlib revision has `Mathlib/AlgebraicGeometry/EllipticCurve/Torsion.lean`; fetching that path returned 404, so there is no such Mathlib file at this revision.

## Import blocks

### `FLT/EllipticCurve/Torsion.lean`, lines 8-10

```lean
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Topology.Instances.ZMod
public import FLT.Deformations.RepresentationTheory.GaloisRep
```

### `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`, lines 8-9

```lean
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.EllipticDivisibilitySequence
```

### `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`, lines 8-9

```lean
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Tactic.ComputeDegree
```

### `Mathlib/Algebra/Module/Torsion/Basic.lean`, lines 8-17

```lean
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Coprime.Ideal
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
```

## What exists in `FLT/EllipticCurve/Torsion.lean`

The FLT file defines its own elliptic-curve `nTorsion`. This is not imported from Mathlib.

Exact declarations found:

| Line | Declaration | What it gives |
|---:|---|---|
| 33 | `abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n` | Defines elliptic-curve `n`-torsion as a `Submodule.torsionBy`. |
| 39 | `noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n)` | Gives the `ZMod n` module structure. |
| 46 | `theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry` | This is the direct finiteness theorem, but in FLT and currently `sorry`. |
| 50 | `theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) : Nat.card (E.nTorsion n) = n^2 := sorry` | Cardinality over separably closed fields, also `sorry`. |
| 53 | `theorem group_theory_lemma ... : Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := sorry` | Pure group-theory shape lemma for torsion by `n`, also `sorry`. |
| 60 | `theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) : Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by ...` | This is the closest found theorem to geometric rank two. It is not named `geomNTorsion_rank_two`. It depends on `n_torsion_card`, which is `sorry`. |
| 72 | `noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := sorry` | `Module.Finite`, not `Finite`/`Fintype` as a type. Also `sorry`. |

Relevant excerpt:

```lean
/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry

theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

-- follows easily from the above
noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := sorry
```

## Searches requested by name

### `Fintype (nTorsion E n)` or `Finite (nTorsion E n)`

I found no `Fintype` declaration for elliptic-curve `nTorsion` in `FLT/EllipticCurve/Torsion.lean`.

The file does have `Finite (E.nTorsion n)`, but the theorem name is:

```lean
WeierstrassCurve.n_torsion_finite
```

at line 46. Note the spelling: `n_torsion_finite`, not `nTorsion_finite`.

### `card_nTorsion_le` or `nTorsion_finite`

No exact declaration named `card_nTorsion_le` was found in the files read or by the connector code search.

No exact declaration named `nTorsion_finite` was found. The existing FLT declaration is `WeierstrassCurve.n_torsion_finite` at line 46.

### `torsionBy_finite` or `Submodule.torsionBy ... Finite`

In pinned Mathlib, `Mathlib/Algebra/Module/Torsion/Basic.lean` defines `Submodule.torsionBy`, but I found no theorem named `torsionBy_finite` and no theorem in that file asserting `Finite (Submodule.torsionBy ...)`.

The core definition is:

```lean
/-- The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that
  `a • x = 0`. -/
@[simps!]
def torsionBy (a : R) : Submodule R M :=
  (DistribSMul.toLinearMap R M a).ker
```

This is at `Mathlib/Algebra/Module/Torsion/Basic.lean`, lines 177-181.

The same file has additive notation for `A[n]`:

```lean
/-- The additive `n`-torsion subgroup for an integer `n`, denoted as `A[n]`. -/
@[reducible]
def torsionBy : AddSubgroup A :=
  (Submodule.torsionBy ℤ A n).toAddSubgroup
```

This is at lines 969-972. It also has:

```lean
/-- For a natural number `n`, the `n`-torsion subgroup of `A` is a `ZMod n` module. -/
@[implicit_reducible]
def torsionBy.zmodModule : Module (ZMod n) A[n] :=
  AddCommGroup.zmodModule torsionBy.nsmul
```

This is at lines 1007-1010.

Those are structural definitions/instances, not finiteness results.

### `geomNTorsion_rank_two`

No declaration named `geomNTorsion_rank_two` was found by connector code search.

The closest declaration found is the FLT theorem at line 60:

```lean
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
```

It is not in Mathlib and is not named `geomNTorsion_rank_two`.

## Division-polynomial files: what exists

### `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`

This file defines division-polynomial objects and congruence lemmas in the affine coordinate ring. It does **not** mention `nTorsion`, `Finite`, or `Fintype` for elliptic-curve torsion.

Important declarations found:

| Line | Declaration | Meaning |
|---:|---|---|
| 113 | `noncomputable def ψ₂ : R[X][Y]` | The `2`-division polynomial. |
| 117 | `noncomputable def Ψ₂Sq : R[X]` | Univariate polynomial congruent to `ψ₂²`. |
| 120 | `lemma C_Ψ₂Sq` | Relation between `Ψ₂Sq`, `ψ₂²`, and the affine Weierstrass polynomial. |
| 125 | `lemma ψ₂_sq` | Rewrites `ψ₂²`. |
| 128 | `lemma Affine.CoordinateRing.mk_ψ₂_sq` | Coordinate-ring congruence for `ψ₂²`. |
| 142 | `noncomputable def Ψ₃ : R[X]` | The `3`-division polynomial, univariate form. |
| 147 | `noncomputable def preΨ₄ : R[X]` | Auxiliary polynomial for `ψ₄`. |
| 153 | `noncomputable def preΨ' (n : ℕ) : R[X]` | Natural-indexed auxiliary univariate polynomials. |
| 194 | `noncomputable def preΨ (n : ℤ) : R[X]` | Integer-indexed auxiliary univariate polynomials. |
| 242 | `noncomputable def ΨSq (n : ℤ) : R[X]` | Univariate polynomial congruent to `ψₙ²`. |
| 290 | `protected noncomputable def Ψ (n : ℤ) : R[X][Y]` | Bivariate `Ψₙ`, congruent to `ψₙ`. |
| 338 | `lemma Affine.CoordinateRing.mk_Ψ_sq` | Coordinate-ring congruence `mk W (W.Ψ n)^2 = mk W (C <| W.ΨSq n)`. |
| 349 | `protected noncomputable def Φ (n : ℤ) : R[X]` | Univariate polynomial congruent to `φₙ`. |
| 401 | `protected noncomputable def ψ (n : ℤ) : R[X][Y]` | Bivariate `n`-division polynomial `ψₙ`. |
| 438 | `lemma Affine.CoordinateRing.mk_ψ` | Coordinate-ring congruence `mk W (W.ψ n) = mk W (W.Ψ n)`. |
| 448 | `protected noncomputable def φ (n : ℤ) : R[X][Y]` | Bivariate `φₙ`. |
| 482 | `lemma Affine.CoordinateRing.mk_φ` | Coordinate-ring congruence `mk W (W.φ n) = mk W (C <| W.Φ n)`. |
| 498-541 | `map_*` lemmas | Functoriality across ring homomorphisms. |
| 556-584 | `baseChange_*` lemmas | Base-change lemmas across algebra homomorphisms. |

Closest coordinate-ring lemmas:

```lean
lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) := by
  simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]

lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) := by
  simp_rw [φ, Φ, map_sub, map_mul, map_pow, mk_ψ, mk_Ψ_sq, Ψ, map_mul,
    mul_mul_mul_comm _ <| mk W <| ite .., Int.even_add_one, Int.even_sub_one, ite_not, ← sq,
    apply_ite C, apply_ite <| mk W, ite_pow, map_one, one_pow, mk_ψ₂_sq]
```

These are useful division-polynomial facts, but they are not the requested torsion-finiteness theorem and do not state a connection between `E.nTorsion n` and roots/zeros of `ψₙ`.

### `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean`

This file computes degrees and leading coefficients of division-polynomial-related objects. It does **not** mention `nTorsion`, `Finite`, or `Fintype` for elliptic-curve torsion.

Important declarations found:

| Line | Declaration | Meaning |
|---:|---|---|
| 65 | `lemma natDegree_Ψ₂Sq_le` | Degree bound for `Ψ₂Sq`. |
| 70 | `lemma coeff_Ψ₂Sq` | Top coefficient of `Ψ₂Sq`. |
| 78 | `lemma natDegree_Ψ₂Sq` | Exact degree of `Ψ₂Sq` under `(4 : R) ≠ 0`. |
| 85 | `lemma leadingCoeff_Ψ₂Sq` | Leading coefficient of `Ψ₂Sq`. |
| 95 | `lemma natDegree_Ψ₃_le` | Degree bound for `Ψ₃`. |
| 100 | `lemma coeff_Ψ₃` | Top coefficient of `Ψ₃`. |
| 108 | `lemma natDegree_Ψ₃` | Exact degree of `Ψ₃` under `(3 : R) ≠ 0`. |
| 115 | `lemma leadingCoeff_Ψ₃` | Leading coefficient of `Ψ₃`. |
| 125 | `lemma natDegree_preΨ₄_le` | Degree bound for `preΨ₄`. |
| 130 | `lemma coeff_preΨ₄` | Top coefficient of `preΨ₄`. |
| 138 | `lemma natDegree_preΨ₄` | Exact degree of `preΨ₄` under `(2 : R) ≠ 0`. |
| 145 | `lemma leadingCoeff_preΨ₄` | Leading coefficient of `preΨ₄`. |
| 233 | `lemma natDegree_preΨ'_le` | Degree bound for natural-indexed `preΨ'`. |
| 236 | `lemma coeff_preΨ'` | Expected coefficient for `preΨ'`. |
| 250 | `lemma natDegree_preΨ'` | Exact degree for `preΨ'` when `(n : R) ≠ 0`. |
| 261 | `lemma leadingCoeff_preΨ'` | Leading coefficient for `preΨ'`. |
| 272 | `lemma natDegree_preΨ_le` | Degree bound for integer-indexed `preΨ`. |
| 278 | `lemma coeff_preΨ` | Expected coefficient for `preΨ`. |
| 300 | `lemma natDegree_preΨ` | Exact degree for `preΨ` when `(n : R) ≠ 0`. |
| 311 | `lemma leadingCoeff_preΨ` | Leading coefficient for `preΨ`. |
| 345 | `lemma natDegree_ΨSq_le` | Degree bound for `ΨSq`. |
| 350 | `lemma coeff_ΨSq` | Top coefficient of `ΨSq`. |
| 360 | `lemma natDegree_ΨSq` | Exact degree for `ΨSq`. |
| 369 | `lemma leadingCoeff_ΨSq` | Leading coefficient of `ΨSq`. |
| 420 | `lemma natDegree_Φ_le` | Degree bound for `Φ`. |
| 425 | `lemma coeff_Φ` | Top coefficient of `Φ`. |
| 434 | `lemma natDegree_Φ` | Exact degree for `Φ`. |
| 441 | `lemma leadingCoeff_Φ` | Leading coefficient of `Φ`. |

Representative excerpt:

```lean
lemma natDegree_ΨSq_le (n : ℤ) : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := by
  induction n using Int.negInduction with
  | nat n => exact (W.natDegree_coeff_ΨSq_ofNat n).left
  | neg ih => simp_rw [ΨSq_neg, Int.natAbs_neg, ih]

@[simp]
lemma natDegree_ΨSq [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_ΨSq_le n) <| W.coeff_ΨSq_ne_zero h

@[simp]
lemma natDegree_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero (W.natDegree_Φ_le n) <| W.coeff_Φ_ne_zero n
```

Again, these are division-polynomial degree facts, not torsion-subgroup finiteness facts.

## Answer to the specific question

Does Mathlib already have a theorem that the `n`-torsion subgroup of an elliptic curve is finite?

**Not in the pinned Mathlib revision used by this FLT repo.** The relevant theorem exists only in `FLT/EllipticCurve/Torsion.lean`:

```lean
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry
```

That theorem is line 46 and is currently a `sorry`.

For geometric rank two, the closest existing declaration is:

```lean
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
```

This is line 60 of `FLT/EllipticCurve/Torsion.lean`. It is not named `geomNTorsion_rank_two` and depends on the `sorry` theorem `n_torsion_card`.

## Bottom line for wiring

If you need a declaration of type:

```lean
Finite (E.nTorsion n)
```

then the existing name to try is:

```lean
E.n_torsion_finite hn
```

where `hn : 0 < n`.

But this is an FLT-local theorem stub, not a proven Mathlib theorem. If the goal is to avoid new axioms/sorries, the current pinned Mathlib division-polynomial files do not yet provide the missing bridge from `E.nTorsion n` to division-polynomial zeros/degree/finiteness.
