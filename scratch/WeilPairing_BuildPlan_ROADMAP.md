## Bottom line

I found **no open/draft Mathlib4 PR or public branch that already provides the elliptic-curve Weil pairing** in the form you need:

```lean
e_m : E[m] × E[m] → μ_m
```

with bilinearity, alternatingness, nondegeneracy/surjectivity, and Galois equivariance.

The best existing Lean code to build on is **not in Mathlib master**, but in the **ImperialCollegeLondon/FLT** repo on `main`, specifically:

`https://github.com/ImperialCollegeLondon/FLT/blob/main/FLT/EllipticCurve/Torsion.lean`

That file already introduces:

```lean
WeierstrassCurve.nTorsion
WeierstrassCurve.n_torsion_card
WeierstrassCurve.n_torsion_dimension
WeierstrassCurve.galoisRepresentation
WeierstrassCurve.galoisRep
```

but several of the key results are currently `sorry`, and there is **no Weil pairing** there. The file explicitly says the finiteness/cardinality torsion theorems need division polynomials, are ongoing work of David Angdinata, and asks interested contributors to talk to KB/David first. fileciteturn57file0L46-L53 It also links the relevant Zulip thread on `n`-torsion / multiplication-by-`n` as an additive group hom. fileciteturn57file0L14-L22

## 1. Mathlib4 PRs / branches / WIP

I searched the Mathlib4 PR space and public code surface for:

```text
Weil pairing
weilPairing
WeierstrassCurve.weilPairing
EllipticCurve.weilPairing
elliptic curve torsion
nTorsion WeierstrassCurve
torsionGalois
division polynomial torsion
```

I did **not** find an open or draft Mathlib4 PR adding the Weil pairing, a determinant-cyclotomic-character theorem for elliptic-curve torsion, or a completed `E[n] ≃ (ZMod n)^2` theorem on Mathlib master. The reproducible PR searches I checked are:

```text
https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+%22Weil+pairing%22
https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+weilPairing
https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+%22elliptic+curve%22+torsion
https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+%22division+polynomial%22+elliptic
```

What Mathlib **does** currently have is the `Mathlib/AlgebraicGeometry/EllipticCurve` directory with `Affine`, `DivisionPolynomial`, `Jacobian`, `Projective`, and the Weierstrass infrastructure, but no `WeilPairing` or torsion Galois representation file in that directory. The current GitHub tree lists exactly those elliptic-curve subdirectories/files, including `Affine`, `DivisionPolynomial`, `Jacobian`, `Projective`, `LFunction.lean`, `Reduction.lean`, and `Weierstrass.lean`. citeturn838359view0

The closest WIP signal is **inside FLT**, not Mathlib: `FLT/EllipticCurve/Torsion.lean` says David Angdinata has already made “substantial progress” on the torsion results, but the file still has `sorry` for `n_torsion_finite`, `n_torsion_card`, the group-theory classification lemma, `Module.Finite`, the Galois action laws, and the actual continuous `galoisRep`. fileciteturn57file0L19-L22 fileciteturn57file0L46-L57 fileciteturn57file0L98-L119

So: **no PR/branch to drop in as a Weil-pairing implementation** was found; the realistic work-in-progress to coordinate with is David Angdinata’s torsion/division-polynomial work referenced in FLT.

## 2. ImperialCollegeLondon/FLT status

The FLT repo is highly relevant, but it does **not** already contain the Weil pairing. Its top-level `FLT.lean` imports:

```lean
public import FLT.EllipticCurve.Torsion
public import FLT.GaloisRepresentation.Cyclotomic
public import FLT.Deformations.RepresentationTheory.GaloisRep
```

among many other deformation/Galois/patching files. fileciteturn56file0L34-L49

### What FLT has

`FLT/EllipticCurve/Torsion.lean` defines the `n`-torsion subgroup of an elliptic curve over a field as:

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and gives it a `ZMod n`-module structure. fileciteturn57file0L33-L44

It then states, but does not prove, the expected algebraically closed-field cardinality result:

```lean
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry
```

and derives a stated `n_torsion_dimension` theorem:

```lean
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := ...
```

but that derivation depends on the earlier `sorry` facts. fileciteturn57file0L52-L74

It also defines the map on points induced by an algebra homomorphism and starts a Galois action:

```lean
WeierstrassCurve.Points.map
WeierstrassCurve.galoisRepresentationSmul
WeierstrassCurve.galoisRepresentation
WeierstrassCurve.galoisRep
```

but the action laws and the continuous representation are still `sorry`. fileciteturn57file0L76-L119

### What FLT does not have

I found no declaration in FLT named or corresponding to:

```lean
WeierstrassCurve.weilPairing
weilPairing
e_m
pairing_nondegenerate
det_torsionGaloisRep_eq_cyclotomicCharacter
```

The FLT file `GaloisRepresentation/Cyclotomic.lean` does build a `ZHat`-adic cyclotomic character using Mathlib’s `modularCyclotomicCharacter`; it proves an algebraically closed field has exactly `N` roots of unity and defines:

```lean
CyclotomicCharacterAux : (L ≃+* L) →* ZHat
CyclotomicCharacterZHat : (L ≃+* L) →* ZHatˣ
```

fileciteturn58file0L24-L31 fileciteturn58file0L46-L65

But the FLT repo does **not** connect this cyclotomic character to `det(E[n])`. The representation API itself is generic: `GaloisRep K A M` is defined as a continuous monoid hom from the absolute Galois group to `Module.End A M`. fileciteturn59file0L49-L54 It has framing/conjugation infrastructure, but no elliptic-curve determinant theorem. fileciteturn59file0L87-L139

### Mazur in FLT

FLT has `FLT/Assumptions/Mazur.lean`, but it is explicitly an assumption:

```lean
axiom Mazur_statement (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point : Set (E⁄ℚ).Point).ncard ≤ 16
```

fileciteturn61file0L105-L108

The comments explain how Mazur rules out reducibility of the Frey representation, but this is not a substitute for the Weil-pairing implication “full rational `m`-torsion implies rational `μ_m`.” fileciteturn61file0L61-L75

## 3. Other Lean 4 projects

I searched public web/GitHub-facing sources for:

```text
Lean Weil pairing
Lean4 Weil pairing
WeierstrassCurve Weil
rootsOfUnity WeierstrassCurve
AbelianVariety Weil pairing Lean
elliptic curve torsion Lean GitHub
```

I did **not** find another Lean 4 project with a completed elliptic-curve or abelian-variety Weil pairing. I also did not find a public Lean project providing `E[n] ≃ (ZMod n)^2` for elliptic curves outside the FLT `Torsion.lean` WIP skeleton.

The only directly relevant non-code artifact I found is David Angdinata and Junyan Xu’s Lean formalization paper on the Weierstrass elliptic-curve group law, which matches the Mathlib elliptic-curve point infrastructure now present in Mathlib. citeturn262643academia0

## 4. What Mathlib already has for building the Weil pairing

Mathlib has several useful pieces, but not yet the layer that makes the standard Weil-pairing construction short.

### Elliptic curves and group law

Mathlib has `WeierstrassCurve`, discriminant, base change, `twoTorsionPolynomial`, `IsElliptic`, and `j`. The docs list these as the main definitions in `Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass`. citeturn982557view0

Mathlib also has the affine nonsingular points and an abelian group law:

```lean
WeierstrassCurve.Affine.Point.instAddCommGroup
WeierstrassCurve.Affine.Point.map
WeierstrassCurve.Affine.Point.map_id
WeierstrassCurve.Affine.Point.map_map
```

The docs describe the point type, the group law, the coordinate ring `F[W]`, the addition-preserving injection into the ideal class group of the affine coordinate ring, and the proof of the abelian group structure. citeturn753325view0

This is a real foundation: you can talk about `E(K)` as an additive commutative group and form `Submodule.torsionBy ℤ`.

### Division polynomials

Mathlib has division polynomials in:

```lean
Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
```

with declarations including:

```lean
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ
```

The docs explicitly define `ψₙ`, `φₙ`, and related sequences, and note that `ωₙ` is still TODO. citeturn753325view1 The file is tagged “elliptic curve, division polynomial, torsion point.” citeturn753325view2

This is very relevant for proving:

```lean
Nat.card E[n] = n^2
E[n] ≃+ (ZMod n) × (ZMod n)
```

over separably/algebraically closed fields with `(n : k) ≠ 0`.

But division polynomials alone do **not** give the Weil pairing. They help describe torsion points and multiplication-by-`n`; the standard Weil pairing needs rational functions/divisors or an equivalent line-function/Miller-style construction.

### Roots of unity and cyclotomic character

Mathlib’s roots-of-unity API is mature enough for the target codomain. It defines:

```lean
rootsOfUnity n M
```

as a subgroup of units satisfying `ζ ^ n = 1`, proves cyclicity in integral domains, gives constructors like `rootsOfUnity.mkOfPowEq`, and has restriction of homomorphisms/equivalences to roots of unity. citeturn683648view0

Mathlib also has:

```lean
modularCyclotomicCharacter
modularCyclotomicCharacter'
cyclotomicCharacter
IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
```

The docs describe `modularCyclotomicCharacter` as the character by which automorphisms act on `μₙ`, i.e. `ζ ↦ ζ^j`. citeturn753325view3

So the target side `μ_m` is ready.

### Function fields and rational maps

Mathlib has general algebraic-geometry function fields:

```lean
AlgebraicGeometry.Scheme.functionField
AlgebraicGeometry.Scheme.germToFunctionField
```

defined for integral schemes as the stalk at the generic point, with field and fraction-ring instances. citeturn940203view0 It also has `AlgebraicGeometry.RationalMap`, but that module is just a thin import wrapper around `Mathlib.AlgebraicGeometry.Birational.RationalMap`. citeturn940203view1

The obstacle is that the elliptic-curve implementation in Mathlib is mostly **explicit Weierstrass/coordinate-ring/group-law machinery**, not a ready-made divisor/function-field theory for nonsingular projective curves specialized to elliptic curves.

## 5. Cleanest construction route

There are two plausible routes.

### Route A: divisor/function-field construction, mathematically canonical

The standard construction is:

1. For `P ∈ E[m]`, construct a rational function `f_P` with divisor
   ```text
   div(f_P) = m(P) - m(O)
   ```
   or the equivalent divisor attached to a degree-zero divisor representing `P`.

2. Define, for carefully chosen auxiliary `R`,
   ```text
   e_m(P,Q) = f_P(Q + R) / f_P(R)
   ```
   or one of the equivalent Weil-pairing formulas avoiding poles.

3. Prove well-definedness independent of `R`.

4. Prove bilinear, alternating, `e_m(P,P)=1`, nondegenerate, and values in `μ_m`.

5. Prove Galois equivariance:
   ```text
   σ(e_m(P,Q)) = e_m(σP, σQ)
   ```

6. Deduce that if `σP=P` and `σQ=Q` for all `P,Q∈E[m]`, then `σ` fixes the image of `e_m`; by nondegeneracy/surjectivity the image is all `μ_m`, so `μ_m` is rational.

This is the textbook proof and the one that will scale to abelian varieties/Tate modules.

**But** this route needs a real divisor theory on the projective nonsingular curve, principal divisors of rational functions, evaluation of rational functions at points, and the theorem identifying `Pic^0(E)` with `E`. I do not see those available in a ready-to-use elliptic-curve API. Mathlib has general `functionField`, but not the elliptic-curve divisor/Picard-function-field layer needed to make this short.

### Route B: explicit line-function / Miller-style construction

Instead of general divisors, define Miller functions recursively using the line functions that already underlie the Weierstrass group law:

```text
f_{a+b,P} = f_{a,P} f_{b,P} · ℓ_{aP,bP} / v_{(a+b)P}
```

Then define the Weil pairing by a Miller formula such as:

```text
e_m(P,Q) = (-1)^m · f_{m,P}(Q) / f_{m,Q}(P)
```

or a normalized variant.

This route may be more feasible in Lean because Mathlib’s group-law proof is already heavily explicit in the affine coordinate ring / ideal-class computations. But it is still a significant project: one must define the relevant rational functions, prove divisor identities or enough evaluation identities to get well-definedness, and prove nondegeneracy.

### Route C: determinant/cyclotomic-character theorem

For your immediate theorem, you do **not** need the pairing itself if you can prove:

```lean
det (E.torsionGaloisRep m σ) =
  modularCyclotomicCharacter ... σ
```

Then full rational torsion makes the left side trivial, so the cyclotomic character is trivial, so `μ_m` is rational.

But this determinant theorem is essentially another formulation of the Weil-pairing equivariance/nondegeneracy package. I found no existing Mathlib or FLT theorem with this content.

## 6. Practical recommendation

If the goal is just to discharge:

```lean
weil_pairing_primitive_root
```

then the shortest realistic path is **not** to start with full divisor theory. I would build a project-local theorem in stages:

```lean
-- Stage 1: torsion size/structure over algebraic closure
theorem n_torsion_dimension :
  Nonempty (E[n] ≃+ (ZMod n) × (ZMod n))
```

Coordinate with the FLT `Torsion.lean` WIP here, because it already states exactly this. fileciteturn57file0L52-L71

```lean
-- Stage 2: define a pairing as an abstract imported structure? 
structure WeilPairingPackage ... where
  e : E[n] → E[n] → rootsOfUnity n K
  bilinear : ...
  alternating : ...
  nondegenerate : ...
  galois_equivariant : ...
```

Then prove your rational-root consequence from the package. This isolates the exact missing theorem and lets the rest of FLT progress without forcing all analytic/divisor machinery immediately.

If you want the **actual formal construction**, the cleanest long-term path is probably the explicit Miller-function route, using Mathlib’s Weierstrass group law and coordinate ring, not the general scheme `functionField` route. The single biggest missing primitive is:

```lean
-- schematic
a usable theory of rational functions/divisors/evaluation on a Weierstrass elliptic curve,
with div(f_{m,P}) = m(P) - m(O), or an explicit Miller-function substitute.
```

Without that, you cannot prove the core properties of the Weil pairing. Division polynomials help prove torsion cardinality and multiplication-by-`n`; roots of unity and the cyclotomic character handle the target; FLT’s GaloisRep API handles continuous representations. The missing bridge is the **elliptic-curve pairing construction and its equivariance**.
