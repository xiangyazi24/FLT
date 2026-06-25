# Q614 (dm1): group law on dual-number points of a Weierstrass curve

## Executive answer

At Mathlib rev `96fd0fff3b8837985ae21dd02e712cb5df72ec05`, the projective and affine nonsingular point types have the abelian group law **over fields**, but not over arbitrary commutative rings.  Since `TrivSqZeroExt K K` is not a field, Mathlib does **not** directly give an `AddCommGroup`/`nsmul` instance on dual-number points of `W`.  The raw projective formulas `Projective.addXYZ`, `Projective.add`, `Projective.neg`, and their map/base-change lemmas exist over commutative rings, but the packaged point-level group structure over `K[ε]` is missing.

Therefore the bridge

```text
[n] Pε = [n] ((-lift P) + Pε)
```

is a one-line group-theory proof **once** you have a dual-point `AddCommGroup` and a base-lift additive homomorphism, but Mathlib does not provide those objects for `TrivSqZeroExt K K` out of the box.

---

## What Mathlib has at the pinned rev

### 1. `nsmul` on projective/affine points

Yes, but only over fields.

In `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`, `WeierstrassCurve.Projective.Point.instAddCommGroup` gives

```lean
noncomputable instance : AddCommGroup W.Point
```

where the ambient variable is

```lean
{W : Projective F} [Field F]
```

So for a field `K`, a projective curve `W : WeierstrassCurve.Projective K`, and points

```lean
P Q : W.Point
```

Lean has:

```lean
P + Q
-P
n • P
```

and all generic additive-group lemmas such as:

```lean
nsmul_add      -- n • (P + Q) = n • P + n • Q
add_comm
add_assoc
zero_add
add_zero
neg_add_cancel
```

The affine file similarly has `WeierstrassCurve.Affine.Point.instAddCommGroup`, again over fields.

### 2. Compatibility with base change / maps

At the formula/representative level, yes.  Mathlib has, among others:

```lean
WeierstrassCurve.Projective.map_neg
WeierstrassCurve.Projective.map_add
WeierstrassCurve.Projective.baseChange_neg
WeierstrassCurve.Projective.baseChange_add
WeierstrassCurve.Projective.map_addXYZ
WeierstrassCurve.Projective.baseChange_addXYZ
```

The important distinction is:

* `map_addXYZ` / `baseChange_addXYZ` are raw formula naturality lemmas and work at the representative/formula level.
* `Projective.map_add` and `Projective.baseChange_add` in `Projective/Point.lean` are still in the field-point context when used to package the group law.
* There is no ready-made point-level additive homomorphism
  ```lean
  W.Point →+ (W.map f).Point
  ```
  that works with target `TrivSqZeroExt K K`, because the target point type is not equipped with the field-based group law.

For field extensions `f : F →+* K`, you can build such a map from the representative-level `map_add`; then `map_nsmul` gives nsmul compatibility automatically.  For dual numbers, the obstruction is the missing group law on the target.

### 3. Abelian group structure

Yes over fields, no over `K[ε]` by default.

For field points, the desired identity is pure additive-group theory:

```lean
example {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve.Projective K)
    (n : ℕ) (P δ : W.Point) (hP : n • P = 0) :
    n • (P + δ) = n • δ := by
  rw [nsmul_add, hP, zero_add]
```

This is exactly the algebra you want, but it is only directly available in `W.Point` when the coefficient ring is a field.

---

## The generic Lean lemma you want once dual points form an additive group

Suppose you introduce a type of dual-number points

```lean
DualPoint W
```

with an `AddCommGroup` instance, and a lift map

```lean
liftPointAddHom : W.Point →+ DualPoint W
```

that sends field points to their scalar/base-change lifts.  Then the translation bridge is completely generic:

```lean
theorem nsmul_eq_nsmul_translated
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (lift : G →+ H) (n : ℕ) (P : G) (Pε : H)
    (hPtor : n • P = 0) :
    n • Pε = n • (-lift P + Pε) := by
  let δ : H := -lift P + Pε
  have hdecomp : lift P + δ = Pε := by
    dsimp [δ]
    rw [← add_assoc, add_left_neg, zero_add]
  calc
    n • Pε = n • (lift P + δ) := by rw [hdecomp]
    _ = n • lift P + n • δ := by rw [nsmul_add]
    _ = lift (n • P) + n • δ := by
      have hmap : n • lift P = lift (n • P) := (map_nsmul lift P n).symm
      rw [hmap]
    _ = lift 0 + n • δ := by rw [hPtor]
    _ = n • δ := by simp
```

Instantiated with

```lean
G := W.Point
H := DualPoint W
δ := -liftPointAddHom P + Pε
```

this is exactly:

```lean
[n]Pε = [n]δ.
```

This is the proof you want to use after the missing dual-point infrastructure is available.

---

## Why Mathlib cannot prove this directly for `TrivSqZeroExt K K`

`TrivSqZeroExt K K` has nilpotents, so it is not a field.  The existing projective point group law in Mathlib is intentionally built for nonsingular projective points over a field.  In the source, the `Point` structure itself is defined over a general `CommRing`, but the operations

```lean
Point.neg
Point.add
AddCommGroup W.Point
```

are built in the field context.  So the following target is not available without adding infrastructure:

```lean
(W.map (algebraMap K (TrivSqZeroExt K K))).Point
```

as an additive group.

The raw formulas still exist:

```lean
W.neg      : (Fin 3 → R) → Fin 3 → R
W.add      : (Fin 3 → R) → (Fin 3 → R) → Fin 3 → R
W.addXYZ   : (Fin 3 → R) → (Fin 3 → R) → Fin 3 → R
```

for `R : Type*` with `[CommRing R]`, and their map lemmas are available.  What is missing is the theorem that these formulas induce an abelian group on the appropriate nonsingular projective `R`-points when `R = K[ε]`.

---

## Minimal infrastructure options

### Option A: build the full dual-point group

Define a dual-point type and prove it is an additive commutative group:

```lean
abbrev DualK (K : Type*) [CommRing K] := TrivSqZeroExt K K

structure DualPoint
    {K : Type*} [Field K]
    (W : WeierstrassCurve.Projective K) where
  point : (W.map (algebraMap K (DualK K))).Point
  -- optionally add a cached scalar part if convenient:
  -- fst_point : W.Point
  -- fst_eq : fstPoint point = fst_point
```

Then define:

```lean
noncomputable def liftPoint
    {K : Type*} [Field K]
    (W : WeierstrassCurve.Projective K) :
    W.Point → DualPoint W :=
  sorry

noncomputable def dualNeg : DualPoint W → DualPoint W :=
  sorry

noncomputable def dualAdd : DualPoint W → DualPoint W → DualPoint W :=
  sorry
```

using the raw projective formulas over `TrivSqZeroExt K K`.

The hard part is not writing the formulas; it is proving closure and the group laws:

```lean
instance : AddCommGroup (DualPoint W) := ...
```

This is essentially proving the functor-of-points group law for the elliptic curve over the nonreduced ring `K[ε]`.  It is mathematically standard but probably too large if your only immediate goal is the derivative/non-double-root lemma.

### Option B: build only the local theorem you need

This is the recommended route.

Do not try to instantiate all of `AddCommGroup` on all dual points.  Instead, define the few operations involved in the proof on normalized representatives and prove the single reduction lemma directly.

You need:

```lean
/-- Scalar/base lift of a field point to dual numbers. -/
def liftPointRep
    (P : Fin 3 → K) : Fin 3 → TrivSqZeroExt K K :=
  (algebraMap K (TrivSqZeroExt K K)) ∘ P

/-- Scalar part of a dual representative. -/
def fstRep
    (Pε : Fin 3 → TrivSqZeroExt K K) : Fin 3 → K :=
  TrivSqZeroExt.fst ∘ Pε
```

Then prove the representative-level map lemmas:

```lean
lemma fst_negRep
    (Pε : Fin 3 → TrivSqZeroExt K K) :
    fstRep ((W.map (algebraMap K (TrivSqZeroExt K K))).neg Pε)
      = W.neg (fstRep Pε) := by
  -- `Projective.map_neg` with `fst` as the ring hom, plus simp.
  sorry

lemma fst_addRep
    (Pε Qε : Fin 3 → TrivSqZeroExt K K)
    (hPε : (W.map (algebraMap K (TrivSqZeroExt K K))).Nonsingular Pε)
    (hQε : (W.map (algebraMap K (TrivSqZeroExt K K))).Nonsingular Qε) :
    fstRep ((W.map (algebraMap K (TrivSqZeroExt K K))).add Pε Qε)
      = W.add (fstRep Pε) (fstRep Qε) := by
  -- `Projective.map_add` wants field-to-field in Mathlib's point-law version,
  -- so for `fst : K[ε] → K` use formula-level `map_addXYZ`/`map_dblXYZ`
  -- and handle the `if P ≈ Q` branch, or avoid `Projective.add` and use
  -- the branch-specific formula you know applies.
  sorry
```

However, the `if P ≈ Q` branch in `Projective.add` is awkward over dual numbers.  If your points are in an affine chart and not in a doubling/vertical exceptional branch, use `addXYZ` or the affine formula branch directly.  If you are translating `Pε` by `-lift P`, the scalar part is the exceptional vertical line case, so you must be careful: this is precisely where raw formula branch management becomes annoying.

For that reason, the best local theorem is not “all dual points form a group”, but the exact identity required by your proof, stated abstractly and proved later by the specific formulas you already use for `[n]` and the formal group:

```lean
/-- The only dual-point group-law fact needed for the tangent bridge. -/
theorem nsmul_dual_eq_nsmul_delta
    {K : Type*} [Field K]
    (W : WeierstrassCurve.Projective K)
    (n : ℕ)
    (P : W.Point)
    (Pε : DualLiftAt W P)
    (hPtor : n • P = 0) :
    dualNsmul W n Pε =
      dualNsmulAtO W n (dualTranslateToOrigin W P Pε) := by
  -- Prove this either from a small local group-law infrastructure or from the
  -- raw projective formulas used to define `dualNsmul` and `dualTranslateToOrigin`.
  sorry
```

Once this lemma exists, your formal tangent bridge can use it without needing a global dual-point `AddCommGroup` instance.

---

## If you still want a point-level base-change map over fields

For field extensions only, the infrastructure is modest.  You can define a point map and package it as an additive homomorphism.

Sketch:

```lean
namespace WeierstrassCurve.Projective.Point

noncomputable def map
    {F K : Type*} [Field F] [Field K]
    {W : WeierstrassCurve.Projective F}
    (f : F →+* K) :
    W.Point → (W.map f).Point := by
  intro P
  refine ⟨?_⟩
  -- map the quotient point class by representatives `P ↦ f ∘ P`
  -- and use `Projective.map_nonsingular f.injective`.
  -- This is standard quotient-map code; `Projective.negMap` is a template.
  sorry

noncomputable def mapAddHom
    {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    {W : WeierstrassCurve.Projective F}
    (f : F →+* K) :
    W.Point →+ (W.map f).Point where
  toFun := map f
  map_zero' := by
    -- representatives `[0,1,0]` map to `[0,1,0]`
    sorry
  map_add' := by
    intro P Q
    -- use `Projective.map_add` on representatives, then quotient/ext
    sorry

@[simp] lemma mapAddHom_nsmul
    {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    {W : WeierstrassCurve.Projective F}
    (f : F →+* K) (n : ℕ) (P : W.Point) :
    mapAddHom (W := W) f (n • P) = n • mapAddHom (W := W) f P := by
  simpa using map_nsmul (mapAddHom (W := W) f) P n

end WeierstrassCurve.Projective.Point
```

This is useful for ordinary field extensions, but it does not solve `K[ε]` because `K[ε]` is not a field.

---

## Recommended plan for your current proof

For `preΨ'_deriv_ne_zero_at_nontorsion_root`, do not stop to build the full group of dual-number points unless you want a large reusable component.  Instead, add exactly one abstraction layer:

```lean
structure InfinitesimalAt
    {K : Type*} [Field K]
    (W : WeierstrassCurve.Projective K)
    (P : W.Point) where
  rep : Fin 3 → TrivSqZeroExt K K
  equation : (W.map (algebraMap K (TrivSqZeroExt K K))).Equation rep
  fst_eq : fstRep rep = chosenRepOf P      -- or quotient/class version
  tangent_ne_zero : Prop                  -- optional/cache if useful
```

Then define only:

```lean
liftAt        : (P : W.Point) → InfinitesimalAt W P
translateToO  : InfinitesimalAt W P → InfinitesimalAt W 0
nsmulDual     : (n : ℕ) → InfinitesimalAt W P → ...
```

and prove the one theorem:

```lean
theorem nsmul_lift_eq_nsmul_translateToO
    (hnP : n • P = 0) :
    nsmulDual n Pε = nsmulDualAtO n (translateToO Pε)
```

Mathematically this theorem is just `nsmul_add` plus `map_nsmul`; in Lean, because `K[ε]` lacks the packaged point group, this theorem is the minimal replacement for the missing group-scheme API.

---

## Bottom line

Answers to your three questions:

1. **`nsmul` on projective/affine points?** Yes over fields: `Projective.Point` and `Affine.Point` have `AddCommGroup` instances, hence `nsmul`. No packaged `nsmul` for dual-number points because `TrivSqZeroExt K K` is not a field.

2. **`nsmul` compatible with base change?** Formula-level map/base-change lemmas exist. Point-level additive base-change can be built for field extensions, then `map_nsmul` gives compatibility. For `K → K[ε]`, Mathlib does not provide the needed point-level additive hom because the target has no group instance.

3. **Abelian group structure?** Yes for field-valued nonsingular points. Not for `K[ε]`-valued points in the current Mathlib API.

So the translation bridge is straightforward **after** you provide either a custom dual-point `AddCommGroup` or, preferably, a single local lemma replacing that infrastructure:

```lean
[n]Pε = [n]((-lift P) + Pε)
```

under `n • P = 0`.
