# Q2013 (dm3): FLT Galois-representation infrastructure survey

Date: 2026-06-28.

Target searched: `ImperialCollegeLondon/FLT`, default branch `main`.

Search terms used included:

```text
GaloisRepresentation
GaloisRep
ModularForm
Tate module
TateModule
TateCurve
adic representation
l-adic representation
ell-adic representation
Weil pairing
WeilPairing
Pairing
nTorsion
```

## Executive answer

The FLT project **does** have useful Galois-representation infrastructure, and it is more relevant than vanilla Mathlib for dm3.  The key generic definition is:

```lean
def GaloisRep := Γ K →ₜ* Module.End A M
```

from

```text
FLT/Deformations/RepresentationTheory/GaloisRep.lean
```

where `Γ K` denotes `Field.absoluteGaloisGroup K`.  The file provides framing into `GL n A`, determinant, base change, local restriction, unramifiedness, Frobenius characteristic polynomials, flatness, and irreducibility wrappers.

For elliptic curves specifically, the relevant file is:

```text
FLT/EllipticCurve/Torsion.lean
```

It defines:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n

noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n)

def WeierstrassCurve.galoisRep ... (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
```

So the answer to “do they have mod-`m` Galois representations?” is: **yes, as a planned/stubbed definition for elliptic-curve `n`-torsion, with important supporting theorems still `sorry`.**

The answer to “do they define the Tate module `T_ℓ(E)`?” is: **no, I found no `TateModule` / `T_l` definition.**  There is a `FLT/TateCurve/TateCurve.lean` file, but it is only a planning comment/stub about Tate uniformization and `p`-torsion over `Qpbar`, not a Tate-module construction.

The answer to “do they have a pairing construction?” is: **no relevant implemented Weil pairing was found.**  Searches for `WeilPairing` returned no Lean definitions.  `HardlyRamified/Defs.lean` explicitly says that proving Frey-curve torsion is hardly ramified is standard but long and needs Tate-curve theory plus standard elliptic-curve facts “such as the Weil pairing.”  In the actual code, the theorem that the Frey curve torsion representation is hardly ramified is still a `sorry`.

Bottom line for dm3: FLT gives us a useful target shape and some scaffolding:

```lean
WeierstrassCurve.galoisRep ... : GaloisRep K (ZMod n) E[n]
GaloisRep.det
IsHardlyRamified.det = cyclotomicCharacter
```

but it does **not** give a completed Weil-pairing/determinant proof.  The determinant-cyclotomic statement is built into `IsHardlyRamified` as a field/assumption, and the Frey torsion theorem that would prove it for elliptic curves is currently `sorry`.

## Files under `FLT/GaloisRepresentation/`

The public imports in `FLT.lean` show the following Galois-representation files:

```text
FLT/GaloisRepresentation/Automorphic.lean
FLT/GaloisRepresentation/Cyclotomic.lean
FLT/GaloisRepresentation/HardlyRamified/Defs.lean
FLT/GaloisRepresentation/HardlyRamified/Family.lean
FLT/GaloisRepresentation/HardlyRamified/Frey.lean
FLT/GaloisRepresentation/HardlyRamified/Lift.lean
FLT/GaloisRepresentation/HardlyRamified/ModThree.lean
FLT/GaloisRepresentation/HardlyRamified/Threeadic.lean
```

### `FLT/GaloisRepresentation/Automorphic.lean`

Purpose: define automorphy of a 2-dimensional `p`-adic or mod-`p` Galois representation in the FLT-specific quaternionic setting.

Key declaration:

```lean
def GaloisRep.IsAutomorphicOfLevel ... (ρ : GaloisRep F A V)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop := ...
```

The definition asks for a totally definite quaternion algebra, a Hecke eigenform/eigencharacter, and good-prime compatibility:

```lean
ρ.IsUnramifiedAt v ∧
(ρ.toLocal v (Frob v)).det = v.1.absNorm ∧
LinearMap.trace A V (ρ.toLocal v (Frob v)) = π (HeckeAlgebra.T ...)
```

It imports `FLT.Deformations.RepresentationTheory.GaloisRep` and Mathlib cyclotomic characters.

Important for us: it uses the **determinant equals cyclotomic/norm** condition as part of automorphy compatibility, but it does not prove this from an elliptic-curve pairing.

### `FLT/GaloisRepresentation/Cyclotomic.lean`

Purpose: a `ZHat`-valued cyclotomic character wrapper using Mathlib’s modular cyclotomic character.

Key declarations:

```lean
lemma IsAlgClosed.card_rootsOfUnity (N : ℕ) [NeZero N] :
  Fintype.card (rootsOfUnity N L) = N

noncomputable def CyclotomicCharacterAux : (L ≃+* L) →* ZHat

noncomputable def CyclotomicCharacterZHat : (L ≃+* L) →* ZHatˣ
```

This is potentially useful for a full-adic/cyclotomic endpoint, but the hard elliptic determinant identity is elsewhere/not implemented.

### `FLT/GaloisRepresentation/HardlyRamified/Defs.lean`

Purpose: define the “hardly ramified” condition for 2-dimensional mod-`ℓ` or `ℓ`-adic representations of `Gal(ℚbar/ℚ)`.

Key declaration:

```lean
structure IsHardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    {R : Type u} ... {V : Type*} ... (hdim : Module.rank R V = 2)
    (ρ : GaloisRep ℚ R V) : Prop where
  det : ∀ g, ρ.det g =
    algebraMap ℤ_[ℓ] R (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ g.toRingEquiv)
  isUnramified : ...
  isFlat : ...
  isTameAtTwo : ...
```

The doc comment is crucial: it says the `p`-torsion of the Frey curve is hardly ramified, but that the full proof is long and needs the Tate curve plus standard elliptic curve facts such as the Weil pairing.

This is exactly the place where our desired determinant/cyclotomic theorem would enter.  FLT currently records it as part of a larger structure, not as an implemented theorem derived from Weil pairing.

### `FLT/GaloisRepresentation/HardlyRamified/Frey.lean`

Purpose: state that Frey-curve `ℓ`-torsion is hardly ramified and not irreducible.

Key declarations:

```lean
theorem FreyCurve.torsion_isHardlyRamified :
  IsHardlyRamified P.hp_odd sorry
    (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

theorem FreyCurve.torsion_not_isIrreducible :
  ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry
```

Important: this file imports both `FLT.FreyCurve.FreyPackage` and `FLT.EllipticCurve.Torsion`.  It is the explicit bridge from elliptic-curve torsion to the Galois-representation machine, but the bridge theorem is not proved.

### `FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`

Purpose: state a mod-3 classification theorem for hardly ramified representations.

Key declaration:

```lean
theorem mod_three ... {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  sorry
```

### `FLT/GaloisRepresentation/HardlyRamified/Threeadic.lean`

Purpose: state a 3-adic classification/trace theorem for hardly ramified representations.

Key declaration:

```lean
theorem three_adic ... {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ p (hp : Nat.Prime p) (hp5 : 5 ≤ p),
      letI v := hp.toHeightOneSpectrumRingOfIntegersRat
      (ρ.toLocal v (Frob v)).trace _ _ = 1 + p := sorry
```

### `FLT/GaloisRepresentation/HardlyRamified/Lift.lean`

Purpose: state a lifting theorem from irreducible hardly ramified mod-`p` representations to characteristic-zero `p`-adic representations.

Key declaration:

```lean
theorem lifts (ρ : GaloisRep ℚ k V) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ∃ R ... W ... (σ : GaloisRep ℚ R W) ...,
      IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := sorry
```

### `FLT/GaloisRepresentation/HardlyRamified/Family.lean`

Purpose: state that a hardly ramified representation lives in a compatible family.

Key declaration:

```lean
theorem mem_isCompatible (hρ : IsHardlyRamified hpodd hv ρ) :
  ∃ (E : Type v) (_ : Field E) (_ : NumberField E)
    (σ : GaloisRepFamily ℚ E 2),
    σ.isCompatible ∧ ... :=
  sorry
```

This imports `FLT.Deformations.RepresentationTheory.GaloisRepFamily`.

## Related non-`FLT/GaloisRepresentation` files

### `FLT/Deformations/RepresentationTheory/GaloisRep.lean`

This is the real core infrastructure file.

Key declarations:

```lean
def GaloisRep := Γ K →ₜ* Module.End A M

abbrev FramedGaloisRep := GaloisRep K A (n → A)

def GaloisRep.conj

def GaloisRep.frame

def FramedGaloisRep.GL : FramedGaloisRep K A n ≃ (Γ K →ₜ* GL n A)

def GaloisRep.det (ρ : GaloisRep K A M) : Γ K →ₜ* A

def GaloisRep.baseChange

abbrev GaloisRep.toLocal

class GaloisRep.IsUnramifiedAt

def GaloisRep.charFrob

class GaloisRep.IsFlatAt

def GaloisRep.IsIrreducible
```

For dm3, this is more useful than Mathlib’s current elliptic curve files because it already fixes a representation API with determinant and local/Frobenius structure.

### `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean`

Purpose: functoriality of absolute Galois groups.

Key declarations:

```lean
noncomputable def Field.absoluteGaloisGroup.mapAux (f : K →+* L) : Γ L →* Γ K

noncomputable def Field.absoluteGaloisGroup.map (f : K →+* L) : Γ L →ₜ* Γ K

lemma Field.absoluteGaloisGroup.lift_map ...
```

This underlies `GaloisRep.map` / restriction of representations along field extensions.

### `FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean`

Purpose: compatible families of Galois representations.

Key declarations:

```lean
def GaloisRepFamily (K : Type*) [Field K]
    (E : Type*) [Field E] [NumberField E] (d : ℕ) : Type _ :=
  ∀ {p : ℕ} (_ : Fact (p.Prime)) (φ : E →+* AlgebraicClosure ℚ_[p]),
    GaloisRep K (AlgebraicClosure ℚ_[p]) (Fin d → AlgebraicClosure ℚ_[p])

def GaloisRepFamily.isCompatible ... : Prop := ...
```

### `FLT/EllipticCurve/Torsion.lean`

Purpose: elliptic-curve torsion and its mod-`n` Galois representation.

Key declarations:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n

noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n)

theorem WeierstrassCurve.n_torsion_finite ... := sorry

theorem WeierstrassCurve.n_torsion_card ... := sorry

theorem WeierstrassCurve.n_torsion_dimension ... :
  Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := ...

def WeierstrassCurve.Points.map ...

instance WeierstrassCurve.galoisRepresentationSmul ... :
  SMul (K ≃ₐ[k] K) (E⁄K).Point

instance WeierstrassCurve.galoisRepresentation ... :
  DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point := ... sorry ...

def WeierstrassCurve.galoisRep ... :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
```

This is the closest thing in FLT to our desired `ρ_m : G_Q → GL₂(ZMod m)`.  However:

* it is a representation on the torsion module, not immediately framed as `GL₂(ZMod m)`;
* the rank/cardinality/finiteness API is partly `sorry`;
* the final continuous Galois representation is `sorry`;
* no determinant/cyclotomic theorem is proved here.

### `FLT/TateCurve/TateCurve.lean`

This file is not a Tate module implementation.  It is a planning stub/comment.  It says the desired Tate-uniformization input is a description of the Galois action on `Qpbar`-points of `p`-torsion of an elliptic curve over `Qp` as an explicit quotient of `Qpbar^* / q(E)^ℤ`.

## Answers to the four concrete questions

### (1) Do they define the Tate module `T_ℓ(E)`?

No.  I found no `TateModule` or `T_l(E)` definition.  There is `FLT/TateCurve/TateCurve.lean`, but it is a prose stub about Tate uniformization and `p`-torsion, not an inverse-limit Tate-module construction.

### (2) Do they have mod-`m` Galois representations?

Yes, in two senses.

First, generically:

```lean
GaloisRep K A M := Γ K →ₜ* Module.End A M
```

works for `A = ZMod m` and a finite `ZMod m` module `M`.

Second, elliptic-curve specifically:

```lean
WeierstrassCurve.galoisRep ... (n : ℕ) ... :
  GaloisRep K (ZMod n) E[n]
```

exists in `FLT/EllipticCurve/Torsion.lean`, but is currently `sorry`.  This is directly relevant to our desired `ρ_m`, though it is not yet a completed formal theorem.

### (3) Do they have any pairing construction?

No implemented Weil pairing was found.  The only relevant occurrence is a doc comment in `HardlyRamified/Defs.lean` saying that the proof that Frey-curve `p`-torsion is hardly ramified needs standard elliptic-curve facts such as the Weil pairing.  Searches for `WeilPairing` returned no code hits.

### (4) What files in `FLT/GaloisRepresentation/` exist?

The files imported by `FLT.lean` are:

```text
FLT/GaloisRepresentation/Automorphic.lean
FLT/GaloisRepresentation/Cyclotomic.lean
FLT/GaloisRepresentation/HardlyRamified/Defs.lean
FLT/GaloisRepresentation/HardlyRamified/Family.lean
FLT/GaloisRepresentation/HardlyRamified/Frey.lean
FLT/GaloisRepresentation/HardlyRamified/Lift.lean
FLT/GaloisRepresentation/HardlyRamified/ModThree.lean
FLT/GaloisRepresentation/HardlyRamified/Threeadic.lean
```

## Practical implications for dm3 Weil-pairing work

The FLT repo is useful because it already chose an API:

```lean
GaloisRep K A M
GaloisRep.det
GaloisRep.baseChange
GaloisRep.toLocal
FramedGaloisRep.GL
WeierstrassCurve.galoisRep
```

For our `E[m](ℚ) = (ZMod m)^2 ⇒ μ_m ⊂ ℚ` goal, the most relevant existing FLT pieces are:

```lean
WeierstrassCurve.nTorsion
WeierstrassCurve.galoisRep
GaloisRep.det
CyclotomicCharacterZHat / Mathlib cyclotomicCharacter
```

But the exact theorem we need is still absent:

```lean
-- not found
∀ σ, (E.galoisRep m).det σ = cyclotomicCharacter ... σ
```

FLT effectively treats this as part of the hard Frey-curve input: `IsHardlyRamified.det` includes determinant equals cyclotomic as a required field, and `FreyCurve.torsion_isHardlyRamified` is `sorry`.

So FLT gives us a good interface to build against, but not a completed workaround for the Weil pairing.  The likely best plan is to make our local statement compatible with `GaloisRep.det` and `WeierstrassCurve.galoisRep`, while isolating the missing determinant/cyclotomic theorem as the theorem that would ultimately be supplied by Weil-pairing formalization.
