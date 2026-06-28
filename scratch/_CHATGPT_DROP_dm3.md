# Q2001 (dm3): Mathlib infrastructure for determinant / cyclotomic replacement of Weil pairing

Date: 2026-06-28.

## Executive answer

The closest existing Mathlib infrastructure is **not** elliptic-curve Galois representations.  It is the cyclotomic side:

* `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean` already defines a mod-`n` cyclotomic character
  ```lean
  modularCyclotomicCharacter {n : ℕ} [NeZero n]
      (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n) :
      (L ≃+* L) →* (ZMod n)ˣ
  ```
  together with `modularCyclotomicCharacter.spec`, `.unique`, and the `p`-adic
  ```lean
  cyclotomicCharacter (L) (p) : (L ≃+* L) →* ℤ_[p]ˣ
  ```
  plus the comparison
  ```lean
  IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
  ```
  for `Gal(L/R)`.

* `Mathlib/NumberTheory/Cyclotomic/Gal.lean` and
  `Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean` already identify cyclotomic Galois groups with `(ZMod n)ˣ`, for example
  ```lean
  IsCyclotomicExtension.autEquivPow
  IsCyclotomicExtension.Rat.galEquivZMod
  IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
  ```
  where `galEquivZMod` is the `ℚ(ζₙ)/ℚ` isomorphism sending `σ` to the exponent `a` with `σ ζ = ζ^a`.

By contrast, I did **not** find a Mathlib definition of the mod-`m` Galois representation attached to an elliptic curve, nor a theorem `det ρ_E,m = χ_m`.  So the proposed determinant argument is not currently a light-weight replacement for the Weil pairing; the missing determinant identity is essentially the same mathematical input that the Weil pairing normally supplies.

## Inventory by requested item

### (1) Galois representations attached to elliptic curves

Status: **absent / not close as a packaged object**.

Existing elliptic-curve infrastructure is substantial but lower-level:

* `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean` defines nonsingular projective points and gives
  ```lean
  WeierstrassCurve.Projective.Point
  instance : AddCommGroup W.Point
  ```
  along with base-change and map compatibility lemmas such as `map_neg`, `map_add`, `baseChange_neg`, and `baseChange_add`.

* `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` and `Degree.lean` contain division polynomial infrastructure.

What I did not find:

```lean
E[m]
rho_m
GaloisRepresentation
WeilPairing
Weil pairing on E[m]
det_rho_eq_cyclotomicCharacter
```

In particular, the following would all still need to be built or isolated as hypotheses:

1. a chosen algebraic closure `K = AlgebraicClosure ℚ` and the base-changed curve `E/K`;
2. the finite subgroup / `ZMod m`-module of `m`-torsion points;
3. the natural action of `Field.absoluteGaloisGroup ℚ` on that torsion module;
4. the statement that rationality of all `m`-torsion points makes this action trivial;
5. the determinant map out of this rank-two `ZMod m` module;
6. the determinant/cyclotomic identity.

The generic algebra for `GL` and determinants exists in Mathlib, but the bridge from elliptic-curve torsion to `GL₂(ZMod m)` does not appear to be packaged.

### (2) The cyclotomic character

Status: **best-existing piece**.

Relevant files/names:

```lean
Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean
  modularCyclotomicCharacter
  modularCyclotomicCharacter.spec
  modularCyclotomicCharacter.unique
  modularCyclotomicCharacter'
  cyclotomicCharacter
  cyclotomicCharacter.spec
  cyclotomicCharacter.toZModPow
  IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
```

This is the most directly reusable infrastructure for the `χ_m` side of the argument.  The mod-`m` character is phrased for automorphisms of a domain `L`, with a hypothesis that `L` contains exactly `m` roots of unity.  In an algebraically closed characteristic-zero field this hypothesis should be discharged via roots-of-unity / enough-roots-of-unity lemmas.

For cyclotomic fields over `ℚ`, there is even more specialized infrastructure:

```lean
Mathlib/NumberTheory/Cyclotomic/Gal.lean
  IsCyclotomicExtension.autEquivPow
  galCyclotomicEquivUnitsZMod
  galXPowEquivUnitsZMod

Mathlib/NumberTheory/NumberField/Cyclotomic/Galois.lean
  IsCyclotomicExtension.Rat.galEquivZMod
  IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
  IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply
```

This can often replace explicit references to complex conjugation when the only goal is to obtain the `-1` element of `(ZMod m)ˣ`: use the cyclotomic Galois equivalence and the unit `-1` in `(ZMod m)ˣ`.

### (3) Complex conjugation as an element of `Gal(ℚbar/ℚ)`

Status: **partly present, but not as the object needed here**.

Relevant existing pieces:

```lean
Mathlib/FieldTheory/Galois/Notation.lean
  Gal(L/K)  -- notation for `L ≃ₐ[K] L`

Mathlib/FieldTheory/AbsoluteGaloisGroup.lean
  Field.absoluteGaloisGroup K := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

Mathlib/LinearAlgebra/Complex/Module.lean
  Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ
  Complex.real_algHom_eq_id_or_conj
```

So Mathlib has complex conjugation as an `ℝ`-algebra automorphism of `ℂ`, and it has the absolute Galois group of a field.  What I did not find is a canonical declaration like

```lean
complexConjugation : Field.absoluteGaloisGroup ℚ
```

This absence is expected: `AlgebraicClosure ℚ` is an abstract chosen algebraic closure, not literally the algebraic numbers inside `ℂ`.  To get such an element one would need to choose/construct an embedding of `AlgebraicClosure ℚ` into `ℂ`, transport `Complex.conjAe`, and prove it fixes `ℚ`.  That is plausible but not currently a named off-the-shelf object.

If the goal is only the classical fact that rational roots of unity have order dividing `2`, the better Mathlib route may avoid complex conjugation entirely.  In `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` there is already:

```lean
IsPrimitiveRoot.dvd_of_isCyclotomicExtension
```

which says that if a primitive `l`-th root lies in an `n`-th cyclotomic extension of `ℚ`, then

```lean
l ∣ 2 * n
```

Specializing morally to the `n = 1` cyclotomic extension gives the expected `l ∣ 2` conclusion for roots of unity in `ℚ`.  This is probably a much cheaper endpoint than constructing an explicit complex-conjugation element in `Gal(ℚbar/ℚ)`.

### (4) The determinant equals cyclotomic character identity

Status: **not present**.

I did not find an existing theorem of the form

```lean
det (rho_m E σ) = modularCyclotomicCharacter ... σ
```

or any elliptic-curve-specific determinant/cyclotomic comparison.  Proving this identity usually uses the Weil pairing and its Galois equivariance:

```text
e_m(σP, σQ) = σ(e_m(P,Q)),
e_m(P,Q)^(det ρ_m σ) = σ(e_m(P,Q)).
```

Thus the proposed argument avoids using the full Weil pairing only if this determinant identity is taken as an imported theorem/axiom.  As a Mathlib development task, building `det ρ = χ` from scratch is not obviously smaller than building the Weil-pairing naturality needed for it.

## Fixed-field infrastructure

For the step "trivial cyclotomic character implies all `m`-th roots of unity are rational", Mathlib has useful infinite Galois theory:

```lean
Mathlib/FieldTheory/Galois/Infinite.lean
  InfiniteGalois.mem_range_algebraMap_iff_fixed
  InfiniteGalois.mem_bot_iff_fixed
  InfiniteGalois.fixedField_bot
```

So once the setup is phrased over a Galois extension `K/k`, an element fixed by every element of `Gal(K/k)` can be recognized as coming from the base field.  This is useful after the cyclotomic character is shown to be trivial, but it still does not supply the elliptic-curve determinant identity.

## Practical recommendation for dm3

If the near-term goal is to finish the number-theoretic obstruction, separate it into two layers.

### Layer A: elliptic-curve input, probably axiomatized or postponed

Use a local theorem/hypothesis with a name like

```lean
axiom full_rational_torsion_implies_trivial_cyclotomicCharacter
  (E : WeierstrassCurve ℚ) (m : ℕ) ... :
  -- every σ acts trivially on μ_m, equivalently χ_m σ = 1
```

or directly

```lean
axiom full_rational_torsion_implies_rootsOfUnity_rational
  ... :
  -- every m-th root of unity in AlgebraicClosure ℚ lies in the range of ℚ
```

This isolates the missing Weil-pairing/determinant theorem instead of hiding it inside an attempted proof.

### Layer B: cyclotomic/rational-root endpoint, using existing Mathlib

After Layer A gives `μ_m ⊂ ℚ`, use existing cyclotomic/root-of-unity infrastructure to derive `m ∣ 2`.  The names most likely to matter are:

```lean
IsPrimitiveRoot.dvd_of_isCyclotomicExtension
Polynomial.cyclotomic.irreducible_rat
IsCyclotomicExtension.Rat.galEquivZMod
InfiniteGalois.mem_range_algebraMap_iff_fixed
```

## Closest-to-existing ranking

1. **Cyclotomic character / cyclotomic Galois group**: very close; already in Mathlib.
2. **Absolute Galois group and fixed-field statements**: present and usable, though with abstract `AlgebraicClosure` choices.
3. **Complex conjugation**: exists as `Complex.conjAe` over `ℝ`; not packaged as an element of `Field.absoluteGaloisGroup ℚ`.
4. **Elliptic-curve Galois representation `ρ_m`**: not found as a packaged object.
5. **`det ρ_m = χ_m`**: not found; this is the major missing theorem and is morally the Weil-pairing input.

Bottom line: for a Mathlib proof today, the cyclotomic half is the promising existing infrastructure.  The elliptic-curve representation/determinant half remains the hard missing infrastructure, so this is not currently a clean way to avoid formalizing Weil-pairing-level input.
