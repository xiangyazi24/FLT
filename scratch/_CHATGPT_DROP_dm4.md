# Q441 / dm4 — Mathlib Projective.addXYZ over CommRing

## Question

For the `W.formalGroup` construction, we want to use the standard projective Silverman parameterization

```text
P(t) = [t : -1 : w(t)]
```

and then substitute two such points into the projective addition formula.  The API question is whether the FLT-pinned Mathlib has standard-projective formulas, in namespace `WeierstrassCurve.Projective`, over `CommRing`, not only field-level point/group-law statements.

## FLT Mathlib revision checked

`xiangyazi24/FLT` pins Mathlib at

```toml
rev = "96fd0fff3b8837985ae21dd02e712cb5df72ec05"
```

I checked the Mathlib files at that revision.

## Verdict

Yes.  Mathlib has **standard unweighted projective** formulas in

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Formula
```

with namespace

```lean
WeierstrassCurve.Projective
```

and the raw formula definitions are over `CommRing R`.

This is the representation needed by

```text
[t : -1 : w(t)]
```

namely the ordinary projective coordinates with weight `(1,1,1)`, not Jacobian weighted coordinates `(2,3,1)`.

## Evidence from `Projective.Basic`

The standard-projective file says explicitly that the projective point is an unweighted equivalence class:

```text
[x : y : z] ~ [u x : u y : u z]
```

for a unit `u`.  The homogeneous equation is

```text
Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³) = 0.
```

This is exactly the ordinary projective Weierstrass model used by `[t:-1:w(t)]`.

In Lean, the relevant type is only an abbreviation:

```lean
abbrev Projective : Type r := WeierstrassCurve R
abbrev toProjective (W : WeierstrassCurve R) : Projective R := W
```

and the scalar action is unweighted:

```lean
lemma smul_fin3 (P : Fin 3 → R) (u : R) :
  u • P = ![u * P x, u * P y, u * P z]
```

So this is not the Jacobian `(2,3,1)` coordinate model.

## Evidence from `Projective.Formula`

The file imports `Projective.Basic` and its module doc lists the projective formula API:

```lean
WeierstrassCurve.Projective.negY
WeierstrassCurve.Projective.dblZ
WeierstrassCurve.Projective.dblX
WeierstrassCurve.Projective.negDblY
WeierstrassCurve.Projective.dblY
WeierstrassCurve.Projective.addZ
WeierstrassCurve.Projective.addX
WeierstrassCurve.Projective.negAddY
WeierstrassCurve.Projective.addY
```

It also says the definitions of `dblXYZ` and `addXYZ` are homogeneous of degree `4`.

The variables at the top of `Projective.Formula` are:

```lean
variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Field F] [Field K] {W' : Projective R} {W : Projective F}
```

This is the important split:

* raw polynomial formula definitions and polynomial identities are generally over `CommRing R`;
* geometric/affine-normalization statements that divide or use `IsUnit` are over fields or require stronger hypotheses such as `[NoZeroDivisors R]`.

The raw addition formula is available over `CommRing R`:

```lean
variable (W') in
/-- The `X`-coordinate of a representative of `P + Q` ... -/
def addX (P Q : Fin 3 → R) : R := ...
```

and similarly for `addZ`, `negAddY`, `addY`.

The assembled coordinate vector is also over `CommRing R`:

```lean
variable (W') in
/-- The coordinates of a representative of `P + Q` ... -/
noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, W'.addZ P Q]
```

with component projection lemmas:

```lean
lemma addXYZ_X (P Q : Fin 3 → R) : W'.addXYZ P Q x = W'.addX P Q := rfl
lemma addXYZ_Y (P Q : Fin 3 → R) : W'.addXYZ P Q y = W'.addY P Q := rfl
lemma addXYZ_Z (P Q : Fin 3 → R) : W'.addXYZ P Q z = W'.addZ P Q := rfl
```

and a homogeneous scaling lemma over `CommRing R`:

```lean
lemma addXYZ_smul (P Q : Fin 3 → R) (u v : R) :
  W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q
```

It also has the degeneracy warning:

```lean
lemma addXYZ_self (P : Fin 3 → R) : W'.addXYZ P P = ![0, 0, 0]
```

So `addXYZ` is a raw homogeneous representative formula, not a globally nonzero point-valued morphism on representatives.

## Base-change API

The file has map/base-change lemmas for the projective formulas, e.g.

```lean
@[simp]
lemma map_addX : (W'.map f).addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q)

@[simp]
lemma map_addXYZ :
  (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q
```

and algebra base-change versions:

```lean
lemma baseChange_addX :
  (W'⁄B).addX (f ∘ P) (f ∘ Q) = f ((W'⁄A).addX P Q)

lemma baseChange_addXYZ :
  (W'⁄B).addXYZ (f ∘ P) (f ∘ Q) = f ∘ (W'⁄A).addXYZ P Q
```

This is useful for moving formulas into power-series coefficient rings.

## Answer to the construction question

For the formal group law route using

```text
P(t) = [t : -1 : w(t)]
```

use the **Projective** formulas, not the Jacobian formulas:

```lean
open WeierstrassCurve WeierstrassCurve.Projective

-- standard projective, ordinary weights (1,1,1)
#check WeierstrassCurve.Projective.addX
#check WeierstrassCurve.Projective.addY
#check WeierstrassCurve.Projective.addZ
#check WeierstrassCurve.Projective.addXYZ
```

The input ring can be a power series ring such as

```lean
MvPowerSeries (Fin 2) K
```

because the raw formulas only need `[CommRing R]`.

The main caveat is normalization.  `Projective.addXYZ` may output a representative with common vanishing factor, especially on diagonal/identity loci.  Therefore the formal group law must be extracted after the right local normalization/cancellation, not by blindly taking a coordinate quotient in a place where the raw representative is `![0,0,0]`.

## Short final answer

Yes: FLT-pinned Mathlib has standard-projective addition formulas over `CommRing` in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.  They are in namespace `WeierstrassCurve.Projective`, and include `addX`, `addY`, `addZ`, and `addXYZ`.  This is exactly the coordinate system for `[t:-1:w(t)]`; the Jacobian namespace is the weighted `(2,3,1)` system and is not the right one for that parametrization.
