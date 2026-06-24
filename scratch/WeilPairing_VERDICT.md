## Verdict

This axiom is **not currently dischargeable from Mathlib by gluing existing elliptic-curve APIs**. Mathlib has a solid **roots-of-unity / cyclotomic-character** side, and it has a growing **Weierstrass-curve point/group-law/division-polynomial** side, but I do **not** see the missing bridge: an elliptic-curve Weil pairing, or an equivalent theorem saying  
`det(Gal action on E[m]) = cyclotomic character mod m`.

## 1. Weil pairing API status

I do **not** find a public Mathlib declaration named any of:

```lean
WeierstrassCurve.weilPairing
EllipticCurve.weilPairing
weilPairing
```

The top-level Mathlib docs have no match for either `Weil` or `weilPairing`; the only “Pairing” hits are unrelated generic/linear-algebra/topology pairing modules, not elliptic-curve Weil pairing. citeturn126020view0turn583720view1turn583720view2

What Mathlib **does** have on elliptic curves is mostly the Weierstrass infrastructure: `WeierstrassCurve`, `WeierstrassCurve.twoTorsionPolynomial`, `WeierstrassCurve.IsElliptic`, `WeierstrassCurve.j`, maps/base change, and related discriminant facts. citeturn963782view0 It also has nonsingular affine points with an abelian group law, including `WeierstrassCurve.Affine.Point.instAddCommGroup`, and Jacobian-coordinate points with `WeierstrassCurve.Jacobian.Point.instAddCommGroup` and `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`. citeturn963782view1turn963782view2 Mathlib also has division polynomials, with declarations such as `WeierstrassCurve.preΨ`, `WeierstrassCurve.ΨSq`, `WeierstrassCurve.Ψ`, `WeierstrassCurve.Φ`, `WeierstrassCurve.ψ`, and `WeierstrassCurve.φ`; the docs explicitly describe these as division polynomials and tag the file with “torsion point.” citeturn474187view2

But I do **not** see the key theorem package you need:

```lean
-- not found as existing Mathlib API
weilPairing :
  E[m] → E[m] → rootsOfUnity m ...

weilPairing_bilinear
weilPairing_alternating
weilPairing_nondegenerate
weilPairing_surjective
weilPairing_galois_equivariant
```

Nor do I see an existing `E[m] ≃ (ZMod m) × (ZMod m)` theorem, an elliptic-curve torsion Galois representation, or a determinant theorem connecting that representation to the cyclotomic character; the top-level docs have no `GaloisRepresentation` match. citeturn126020view1

## 2. Shorter route status

The **cyclotomic side is present**. Mathlib has `rootsOfUnity n M`, implemented as a subgroup of units satisfying `ζ ^ n = 1`, and it has `IsPrimitiveRoot ζ k` as the predicate that `ζ ^ k = 1` and `k ∣ l` whenever `ζ ^ l = 1`. citeturn991913view0turn963782view3 It also has a cyclotomic-character file with declarations including:

```lean
modularCyclotomicCharacter
modularCyclotomicCharacter'
cyclotomicCharacter
IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter
```

The docs describe `modularCyclotomicCharacter L n hn` as the homomorphism from ring automorphisms of `L` to `(ZMod n)ˣ` characterized by `g ζ = ζ^j` for all `n`-th roots of unity, assuming there are `n` such roots. citeturn648089view0turn648089view1

So the obstruction is **not** “Mathlib lacks roots of unity” or “Mathlib lacks a cyclotomic character.” It has those. The obstruction is that the elliptic-curve torsion side does not currently feed into them.

The “prove `m ≤ 2` and then produce the primitive root directly” route is mathematically valid, but it still needs a nontrivial theorem from `hfull`. Once you have `m ≤ 2`, the final root-of-unity step is easy: Mathlib has `IsPrimitiveRoot.one : IsPrimitiveRoot 1 1`, and it has `IsPrimitiveRoot.neg_one` giving `IsPrimitiveRoot (-1) 2` under the usual non-characteristic-2 hypotheses, which applies to `ℚ`. citeturn564799view0turn564799view1 But proving `m ≤ 2` from full rational `m`-torsion is essentially the same missing arithmetic input unless you import a torsion-classification theorem.

The Mazur route is also not available from vanilla Mathlib: the top-level Mathlib docs have no `Mazur` match. citeturn126020view3 Even if a project-specific Mazur assumption exists, you would still need glue showing that `HasFullRationalTorsion E m` gives a rational subgroup isomorphic to `(ZMod m)^2`, then use the classification to rule out `m > 2`.

## 3. Honest hardest missing piece

The single hardest missing piece is one of these equivalent bridges:

```lean
-- Weil-pairing bridge
theorem full_rational_torsion_implies_rational_rootsOfUnity
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m) (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

or, lower-level and more reusable:

```lean
-- missing package
WeierstrassCurve.weilPairing :
  E[m] → E[m] → rootsOfUnity m ...

theorem weilPairing_nondegenerate : ...
theorem weilPairing_surjective : ...
theorem weilPairing_galois_equivariant : ...
```

or the representation-theoretic replacement:

```lean
-- missing determinant theorem
theorem det_torsionGaloisRep_eq_modularCyclotomicCharacter
    (E : WeierstrassCurve K) [E.IsElliptic] {m : ℕ} ... :
    det (torsionGaloisRep E m σ) =
      modularCyclotomicCharacter ... σ
```

Given current Mathlib, the shortest practical discharge is probably **not** to build the whole Weil pairing from scratch inside your FLT development. The realistic options are:

1. keep this as a named arithmetic assumption;
2. add a project-local theorem exactly expressing “full rational torsion implies rational primitive roots,” justified externally by Weil pairing; or
3. if your project already imports a formal Mazur theorem plus enough torsion-subgroup structure, prove `m ≤ 2` and finish with `ζ = 1` or `ζ = -1`.

For a fully formal, axiom-free proof in Mathlib today, the missing deep piece is the elliptic-curve torsion/Weil-pairing/Galois-equivariance layer, not the rational roots-of-unity layer.
