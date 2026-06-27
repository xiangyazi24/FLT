# Q1136 (dm4): follow-up on `dm3`

## Interpretation

The prompt says only `dm3`, so I am treating the current `scratch/_CHATGPT_DROP_dm3.md` as the object of analysis.
That file is about the theorem

```lean
theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

and asks for the shortest Lean route from full rational torsion to a rational primitive root.

The main conclusion is unchanged, but there is an important connection with the newer `dm4` separability discussion:

```text
Global separability of [n] / preΨ' helps with the geometric size and reducedness of E[n],
but it does not replace the Weil-pairing/determinant/cyclotomic-character bridge.
```

So `dm4` can support one auxiliary missing lemma in `dm3`, namely the theorem that the geometric `m`-torsion has the expected size when `(m : K) ≠ 0`; it cannot by itself prove the existence of a rational primitive `m`-th root.

## Bottom line

For `dm3`, the shortest honest FLT-local interface is still one of these two bridge choices:

### Option A: contradiction bridge over `ℚ`

```lean
no_full_rational_torsion_of_three_le :
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ},
    3 ≤ m → ¬ HasFullRationalTorsion E m
```

Then `weil_pairing_gives_primitive_root` is just the split `m = 1`, `m = 2`, `3 ≤ m`.

### Option B: determinant / cyclotomic bridge

```text
full rational m-torsion
  ⇒ Galois action on E[m] is trivial
  ⇒ det ρ_m is trivial
  ⇒ χ_m is trivial
  ⇒ μ_m ⊆ ℚ
  ⇒ ∃ ζ : ℚ, IsPrimitiveRoot ζ m.
```

This is closer to the standard Weil-pairing proof.  But the real arithmetic theorem is still

```text
det ρ_m = χ_m,
```

which is essentially the determinant form of the Weil-pairing theorem.

## What the `dm4` global separability theorem can contribute

The global separability theorem from the `dm4` thread has the shape

```lean
preΨ'_rootwise_separable_of_natCast_ne_zero :
  (n : K) ≠ 0 →
  ∀ x : K,
    IsRoot (W.preΨ' n) x →
    ¬ IsRoot (derivative (W.preΨ' n)) x
```

or, more geometrically,

```text
(n : K) ≠ 0 ⇒ [n] : E → E is separable / étale.
```

This is relevant to `dm3` only through the geometric torsion-size bridge:

```text
[n] separable + degree([n]) = n²
  ⇒ E[n](Kbar) has n² reduced points.
```

That fact is useful because `HasFullRationalTorsion E m` is usually represented as an injection

```text
ZMod m × ZMod m ↪ E(ℚ).
```

To conclude that the mod-`m` Galois representation is trivial on all of `E[m]`, one must know that the geometric `m`-torsion has no more than `m²` points.  This is exactly where separability/cardinality can help.

But after this step, one still needs the determinant identity

```text
det ρ_m = χ_m.
```

Without that determinant/cyclotomic bridge, the statement “all `m`-torsion points are rational” does not produce a rational primitive `m`-th root.

## Why separability alone does not prove the primitive-root theorem

Separability tells us that the kernel of `[m]` is reduced when `(m : K) ≠ 0`.  Equivalently, it prevents infinitesimal torsion and multiple roots in the division-polynomial description.

It does **not** identify the determinant of the Galois action on `E[m]` with the cyclotomic character.  The existence of roots of unity is not encoded in `preΨ'` alone; it comes from the alternating Weil pairing

```text
e_m : E[m] × E[m] → μ_m
```

or equivalently from the determinant formula for the mod-`m` representation.

So this attempted shortcut is not valid:

```text
preΨ'_m separable
  ⇒ E[m] is reduced
  ⇒ full rational torsion forces μ_m ⊆ ℚ.
```

The missing implication is the last one.  It needs the pairing/determinant theorem.

## The role of `Φ_n`, `preΨ'`, and missing `Ω_n`

The `dm3` context also mentioned `preΨ'`, `Φ_n`, and missing `Ω_n`.

For a full projective formula for `[n]P`, one normally needs all coordinate pieces:

```text
x([n]P) = Φ_n(P) / Ψ_n(P)^2,
y([n]P) = Ω_n(P) / Ψ_n(P)^3.
```

The polynomial `preΨ' n` controls the `x`-coordinate zero locus of the division polynomial after eliminating or normalizing the `y`-factor.  It is enough for many root/separability statements about the `x`-projection, but it is not enough to build the full Galois representation on `E[n]`.

For the determinant route, the clean object is not just the roots of `preΨ' n`; it is the full finite group of geometric `n`-torsion points.  Thus one eventually needs either:

1. a genuine `E[n]` group-scheme / geometric torsion API, or
2. projective `[n]` formulas including the missing `Ω_n` piece, or
3. a trusted bridge theorem that packages this geometry.

This is why `dm4` separability is valuable but not decisive for `dm3`.

## Recommended Lean interface for `dm3`

The best immediate code interface is to keep the hard arithmetic in one named theorem and close the target by a simple case split.

Here is an abstract version that should compile independently of the exact FLT project names.  It isolates the case split from the arithmetic bridge.

```lean
import Mathlib

noncomputable section

/--
Abstract case split behind the FLT-local theorem.

`Full E m` stands for the project's `HasFullRationalTorsion E m`.
The theorem says that if the `m = 1` and `m = 2` cases are known and full
rational torsion is impossible for `m ≥ 3`, then full rational torsion implies
a rational primitive `m`-th root.
-/
theorem primitive_root_of_full_by_ge3_contradiction
    {Curve : Type*} (Full : Curve → ℕ → Prop)
    (h1 : ∀ E : Curve, Full E 1 → ∃ ζ : ℚ, IsPrimitiveRoot ζ 1)
    (h2 : ∀ E : Curve, Full E 2 → ∃ ζ : ℚ, IsPrimitiveRoot ζ 2)
    (hge3 : ∀ E : Curve, ∀ {m : ℕ}, 3 ≤ m → ¬ Full E m)
    (E : Curve) {m : ℕ} (hm : 0 < m) (hfull : Full E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  have hm_cases : m = 1 ∨ m = 2 ∨ 3 ≤ m := by
    omega
  rcases hm_cases with rfl | rfl | hm3
  · exact h1 E hfull
  · exact h2 E hfull
  · exact False.elim ((hge3 E hm3) hfull)
```

The FLT-local version should look like this, with the actual project import replacing `Mathlib` if there is a more specific file.

```lean
import Mathlib

noncomputable section

namespace FLT

/--
Project-local bridge theorem.

This is the shortest useful interface for the current target.  It can later be
proved from any of the following:

* Weil pairing nondegeneracy plus Galois equivariance;
* determinant identity `det ρ_m = χ_m`;
* Mazur's torsion theorem;
* classification of the real Lie group `E(ℝ)`.
-/
axiom no_full_rational_torsion_of_three_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm3 : 3 ≤ m) :
    ¬ HasFullRationalTorsion E m

/-- These should be replaced by the existing project lemmas for `m = 1`. -/
axiom primitive_root_from_full_torsion_one
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hfull : HasFullRationalTorsion E 1) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ 1

/-- These should be replaced by the existing project lemmas for `m = 2`. -/
axiom primitive_root_from_full_torsion_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hfull : HasFullRationalTorsion E 2) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ 2

theorem weil_pairing_gives_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := by
  have hm_cases : m = 1 ∨ m = 2 ∨ 3 ≤ m := by
    omega
  rcases hm_cases with rfl | rfl | hm3
  · exact primitive_root_from_full_torsion_one E hfull
  · exact primitive_root_from_full_torsion_two E hfull
  · exact False.elim ((no_full_rational_torsion_of_three_le E hm3) hfull)

end FLT
```

This is intentionally not pretending that the Weil pairing has been formalized.  It makes the missing theorem explicit and keeps the current target small.

## If you want to exploit `dm4` separability inside `dm3`

Then the right intermediate theorem is not directly `weil_pairing_gives_primitive_root`; it is a cardinality/free-rank theorem for geometric torsion.

The desired bridge has this conceptual shape:

```lean
import Mathlib

noncomputable section

namespace FLT

/--
Schematic interface only: exact types depend on the project's model of geometric
points and base change to an algebraic closure.

This is the place where the `dm4` global separability theorem for `[m]` is useful.
-/
axiom geometric_nTorsion_card_eq_sq_of_natCast_ne_zero
    {K : Type*} [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    {m : ℕ} (hm : (m : K) ≠ 0) :
    -- Fintype.card (E.nTorsionOverAlgClosure m) = m ^ 2
    True

/--
Full rational torsion plus the exact geometric cardinality makes the mod-`m`
Galois action trivial.  This is still only a bridge toward the determinant route.
-/
axiom galoisRep_trivial_of_full_rational_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    -- ∀ σ, WeierstrassCurve.galoisRep E m σ = 1
    True

end FLT
```

The first axiom is where the `dm4` separability work can eventually pay off.  The second still needs base-change/fixed-point bookkeeping.  And after both, the determinant/cyclotomic theorem is still required.

## If you prefer the determinant-shaped bridge

The determinant-shaped bridge is the best long-term replacement for the black-box contradiction lemma.

```lean
import Mathlib
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

noncomputable section

namespace FLT

/-- Full rational `m`-torsion makes the geometric mod-`m` representation trivial. -/
axiom fullRationalTorsion_trivial_galoisRep
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    -- ∀ σ, WeierstrassCurve.galoisRep E m σ = 1
    True

/-- The serious arithmetic input: determinant of the mod-`m` representation is cyclotomic. -/
axiom det_galoisRep_eq_modularCyclotomicCharacter
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m) :
    -- ∀ σ, det (WeierstrassCurve.galoisRep E m σ) = modularCyclotomicCharacter ... σ
    True

/-- Trivial mod-`m` cyclotomic character gives a rational primitive `m`-th root. -/
axiom exists_rat_primitiveRoot_of_trivial_modularCyclotomicCharacter
    {m : ℕ} (hm : 0 < m) :
    -- CyclotomicCharacterIsTrivialOverRat m →
    True →
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m

end FLT
```

Among these, `det_galoisRep_eq_modularCyclotomicCharacter` is the real theorem.  The `dm4` separability theorem can help justify that `E[m]` is the expected finite rank-two object, but it cannot prove the determinant identity.

## Final recommendation

For the current FLT proof, keep `dm3`'s recommendation:

1. Prove or temporarily admit one explicit bridge:

   ```lean
   no_full_rational_torsion_of_three_le
   ```

2. Close `weil_pairing_gives_primitive_root` by the elementary split `m = 1`, `m = 2`, `3 ≤ m`.

3. Add a comment that the bridge is intended to be discharged later by the determinant identity `det ρ_m = χ_m`, equivalently by the Weil pairing.

4. Treat the `dm4` global separability work as useful infrastructure for the geometric torsion cardinality theorem, not as a replacement for the arithmetic determinant theorem.

This keeps the proof dependency honest and prevents the project from hiding the Weil-pairing theorem behind division-polynomial separability lemmas.
