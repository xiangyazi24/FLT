## Architectural verdict

The determinant/exterior-power route does **not** remove the Weil-pairing problem. It repackages it.

For elliptic curves, the statement

```lean
det ρ_E,n = χ_cyc
```

is normally proved from the Weil pairing via

```text
eₙ(σP, σQ) = σ(eₙ(P,Q))
eₙ(aP + bQ, cP + dQ) = eₙ(P,Q)^(ad - bc).
```

If `P,Q` are a `ZMod n`-basis of `E[n]`, then `ad - bc` is exactly the determinant. The exterior-power version says the same thing as a Galois-equivariant identification

```text
∧² E[n] ≃ μₙ.
```

But that identification **is the Weil pairing, in determinant-line form**. You can avoid formalizing every theorem about a fully bundled pairing, but you cannot avoid constructing/providing the canonical orientation map `∧²E[n] → μₙ` and its Galois equivariance. That is the hard arithmetic geometry.

For your specific axiom

```lean
full rational m-torsion ⟹ ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

the shortest route is actually **not** det=`χ_cyc`; it is the direct Weil-pairing value route:

```text
choose a basis P,Q of E[m];
ζ := e_m(P,Q);
nondegeneracy/perfectness ⇒ ζ is primitive;
P,Q rational + Galois equivariance / definition over ℚ ⇒ ζ ∈ ℚ.
```

That needs less linear-algebra infrastructure than a determinant theorem, but it still needs the same essential pairing primitive.

## 1. Does det=`χ_cyc` require the full Weil pairing?

Mathematically, yes, up to an equivalent replacement. There are three formulations:

```text
A. Weil pairing:
   eₙ : E[n] × E[n] → μₙ
   bilinear, alternating, perfect, Galois-equivariant.

B. determinant-line formulation:
   ∧² E[n] ≃ μₙ
   Galois-equivariant.

C. determinant character theorem:
   det ρ_E,n = χ_cyc.
```

`A ⇒ B ⇒ C` is short. But constructing `B` without constructing `A` is not much easier: a perfect alternating pairing on a rank-2 module is exactly a map out of the top exterior power. The only thing `B` avoids is carrying a two-variable pairing API; it does **not** avoid the geometric construction.

There is a group-scheme formulation via Cartier duality and the principal polarization of an elliptic curve:

```text
E[n] ≃ E[n]^D
```

and the Cartier dual of `Z/nZ` is `μₙ`. But that is again the Weil pairing in group-scheme language. I would not call this a shortcut in Lean; it probably requires even more scheme/group-scheme infrastructure than the explicit elliptic-curve Weil pairing.

## 2. Exterior-power route: what Mathlib has

Mathlib has exterior algebra:

```lean
ExteriorAlgebra R M
ExteriorAlgebra.exteriorPower R n M
⋀[R]^n M
ExteriorAlgebra.ι
ExteriorAlgebra.ιMulti
ExteriorAlgebra.map
ExteriorAlgebra.map_apply_ιMulti
ExteriorAlgebra.map_comp_map
```

The docs say `exteriorPower R n M` is the `n`th exterior power, with notation `⋀[R]^n M`, implemented as a submodule of `ExteriorAlgebra R M`. citeturn515383view0 They also list the map API, including `ExteriorAlgebra.map`, `map_apply_ι`, `map_apply_ιMulti`, and `map_comp_map`. citeturn272638view1

Mathlib also has determinant infrastructure:

```lean
LinearMap.det
LinearEquiv.det
LinearMap.det_comp
LinearMap.det_toMatrix
Module.Basis.det
Module.Basis.det_comp
AlternatingMap.eq_smul_basis_det
```

The determinant file explicitly says it defines `LinearMap.det` and `LinearEquiv.det`; `LinearMap.det` is a multiplicative homomorphism from endomorphisms to the base ring, and `LinearEquiv.det` is the determinant of a linear isomorphism. citeturn356841view0 The same docs list `LinearMap.det_comp`, `LinearMap.det_toMatrix`, `LinearEquiv.det`, `Module.Basis.det`, `Module.Basis.det_comp`, and `AlternatingMap.eq_smul_basis_det`. citeturn356841view0

However, I would **not** use `ExteriorAlgebra.exteriorPower` as the first implementation route. In Mathlib it is a submodule of the exterior algebra, so the “top exterior line is rank one and the action is determinant” theorem will need extra API. For rank `2`, `AlternatingMap` plus `Module.Basis.det` is much cleaner.

The practical Lean route for the determinant consequence is:

```lean
-- Given a basis b : Module.Basis (Fin 2) (ZMod n) M
-- and a pairing e with bilinear/alternating properties,
-- prove directly:
e (f P) (f Q) = e P Q ^ (LinearMap.det f).val
```

or, basis-explicitly,

```lean
let A := LinearMap.toMatrix b b f
-- prove exponent is Matrix.det A
```

That avoids top-exterior bookkeeping. It still uses the same pairing data.

One important subtlety: `μₙ` is multiplicative. Exterior powers and `AlternatingMap` are additive/linear. You either need to work with `Additive (rootsOfUnity n L)` and a `ZMod n`-module structure, or define a custom multiplicative bilinear pairing API. For the Weil pairing, the second option is usually more natural:

```lean
e (P₁ + P₂) Q = e P₁ Q * e P₂ Q
e P (Q₁ + Q₂) = e P Q₁ * e P Q₂
e (a • P) Q = e P Q ^ a.val
```

## 3. FLT repo: clean determinant statement in `GaloisRep`

FLT currently defines

```lean
GaloisRep K A M :=
  Γ K →ₜ* Module.End A M
```

where `Γ K` is the absolute Galois group. fileciteturn59file0L49-L54 It also has conjugation/framing infrastructure, including

```lean
GaloisRep.conj
GaloisRep.frame
```

where `frame` uses a chosen basis to realize the representation on `Aⁿ`. fileciteturn59file0L98-L139

For elliptic curves, FLT defines

```lean
WeierstrassCurve.nTorsion n :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and gives it a `ZMod n`-module structure. fileciteturn57file0L33-L44 It also states the expected algebraically closed torsion cardinality and dimension results, but these still depend on `sorry`; the dimension theorem currently gives an **additive** equivalence

```lean
Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n))
```

not a `ZMod n`-linear basis. fileciteturn57file0L52-L74 For determinant work, you should strengthen the target to one of:

```lean
Nonempty (Module.Basis (Fin 2) (ZMod n) (E.nTorsion n))
```

or

```lean
Nonempty (E.nTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n)).
```

An additive equivalence is not enough to define a determinant over `ZMod n`.

FLT also has a started Galois action and continuous Galois representation on torsion:

```lean
WeierstrassCurve.galoisRepresentationSmul
WeierstrassCurve.galoisRepresentation
WeierstrassCurve.galoisRep
```

but the action laws and the continuous representation are currently `sorry`. fileciteturn57file0L98-L119

### Recommended determinant helper

Add a generic helper in FLT, independent of elliptic curves:

```lean
namespace GaloisRep

noncomputable def asGL
    {K A M : Type*} [Field K] [CommRing A] [TopologicalSpace A]
    [AddCommGroup M] [Module A M]
    (ρ : GaloisRep K A M) (σ : Field.absoluteGaloisGroup K) :
    LinearMap.GeneralLinearGroup A M :=
  -- val := ρ σ
  -- inv := ρ σ⁻¹
  -- proofs from map_mul, mul_inv_cancel, inv_mul_cancel

noncomputable def detWithBasis
    {K A M ι : Type*} [Field K] [CommRing A] [TopologicalSpace A]
    [AddCommGroup M] [Module A M]
    [Fintype ι] [DecidableEq ι]
    (ρ : GaloisRep K A M) (b : Module.Basis ι A M) :
    Field.absoluteGaloisGroup K →* Aˣ :=
  -- σ ↦ LinearEquiv.det ((ρ.asGL σ).toLinearEquiv)
  -- or matrix determinant via LinearMap.toMatrix b b
```

You can avoid a continuity proof for the determinant character at first; a plain `→*` is enough for the theorem. If later you want it as a `GaloisRep K A A`, continuity into finite discrete `ZMod n` should be easy, but it is extra work.

### Recommended theorem statement

For finite level, do **not** use FLT’s `CyclotomicCharacterZHat` as the primary target. Use Mathlib’s finite-level character:

```lean
modularCyclotomicCharacter
```

Mathlib defines

```lean
modularCyclotomicCharacter L hn :
  (L ≃+* L) →* (ZMod n)ˣ
```

where `hn` proves that `L` has exactly `n` many `n`th roots of unity. The docs state that it sends an automorphism to the exponent by which it acts on `μₙ`. citeturn340370view0

A good theorem shape is:

```lean
theorem det_torsionGaloisRep_eq_modularCyclotomicCharacter
    (K : Type*) [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) [NeZero n]
    (hnK : (n : K) ≠ 0)
    -- Kbar shorthand
    (b : Module.Basis (Fin 2) (ZMod n)
          ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)) :
    ∀ σ : Field.absoluteGaloisGroup K,
      GaloisRep.detWithBasis
        (E.galoisRep n (Nat.pos_of_ne_zero (NeZero.ne n))) b σ
        =
      (modularCyclotomicCharacter
        (AlgebraicClosure K)
        (/* card μ_n = n */)
        (σ : AlgebraicClosure K ≃+* AlgebraicClosure K))
```

The exact coercion from `σ : Field.absoluteGaloisGroup K` to a ring equivalence of `AlgebraicClosure K` will need adjustment to FLT’s `Field.absoluteGaloisGroup` API, but the target should be `(ZMod n)ˣ`.

FLT’s `CyclotomicCharacterZHat` is useful for profinite/p-adic statements; it is defined as a map to `ZHatˣ`. fileciteturn58file0L46-L65 For finite `n`, `modularCyclotomicCharacter` is the cleanest comparison object.

## 4. For `weil_pairing_primitive_root`, direct pairing is shorter than det

The determinant route would be:

```text
full rational E[m]
⇒ ρ_E,m(σ) = identity for all σ
⇒ det ρ_E,m(σ) = 1
⇒ χ_cyc(σ) = 1
⇒ every μ_m element is Galois-fixed
⇒ μ_m ⊆ K
⇒ choose primitive ζ ∈ K.
```

The direct pairing route is:

```text
full rational E[m]
⇒ choose a rational basis P,Q of E[m]
⇒ ζ := e_m(P,Q) ∈ K
⇒ perfectness/nondegeneracy ⇒ ζ is primitive.
```

The direct route avoids:

```lean
LinearMap.det
GaloisRep.detWithBasis
ExteriorAlgebra
top exterior power
determinant-character comparison
```

It only needs the pairing plus the theorem that a basis pair evaluates to a primitive root.

For your specific theorem, I would define the minimal package as:

```lean
structure WeilPairingPackage
    (K : Type*) [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) [NeZero n] where
  pairing :
    E.nTorsion n → E.nTorsion n → rootsOfUnity n K

  map_add_left :
    ∀ P₁ P₂ Q, pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q
  map_add_right :
    ∀ P Q₁ Q₂, pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂
  alternating :
    ∀ P, pairing P P = 1

  -- strongest convenient form for the primitive-root axiom:
  exists_basis_pair_primitive :
    ∀ b : Module.Basis (Fin 2) (ZMod n) (E.nTorsion n),
      IsPrimitiveRoot ((pairing (b 0) (b 1) : rootsOfUnity n K) : K) n

  -- if working over Kbar:
  galois_equivariant :
    ...
```

If the points are genuinely `K`-rational and the pairing is defined over `K`, the primitive root is already in `K`; no fixed-field/descent theorem is needed. That is much cleaner than proving “fixed by all absolute Galois automorphisms implies lies in `K`.”

If your `HasFullRationalTorsion` is formulated over `Kbar`, then you will need a descent lemma. For `K = ℚ`, the pairing-over-`ℚ` formulation is preferable.

## Recommended build order

### Stage 0: strengthen FLT torsion linear algebra

Change or supplement FLT’s current additive torsion dimension theorem with a linear one:

```lean
theorem WeierstrassCurve.n_torsion_basis
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) (ZMod n) (E.nTorsion n))
```

The current FLT theorem only gives `≃+`, which is insufficient for determinants. fileciteturn57file0L62-L71

### Stage 1: prove the algebraic consequence from an abstract pairing

Before constructing the pairing geometrically, prove:

```lean
theorem full_rational_torsion_has_primitive_root
    (WP : WeilPairingPackage K E n)
    (hfull : HasFullRationalTorsion E n) :
    ∃ ζ : K, IsPrimitiveRoot ζ n
```

This directly discharges your axiom once a package exists.

### Stage 2: prove det=`χ_cyc` from the same package

Use a basis and matrix determinant:

```lean
theorem det_eq_cyclotomic_of_weilPairing
    (WP : WeilPairingPackage (AlgebraicClosure K) Ebar n)
    (b : Module.Basis (Fin 2) (ZMod n) Ebar.nTorsion) :
    ∀ σ, detWithBasis ρ b σ =
      modularCyclotomicCharacter (AlgebraicClosure K) hμ σ
```

This theorem should be a corollary of the pairing, not the foundation.

### Stage 3: construct the pairing

Only then decide whether to construct the actual Weil pairing by:

```text
A. divisors / rational functions / Pic⁰(E), mathematically canonical but heavy;
B. explicit Miller functions / line functions, probably more realistic with current Weierstrass APIs;
C. group-scheme Cartier duality / principal polarization, elegant but likely the heaviest in Lean.
```

Given current Mathlib/FLT, I would choose **B** long-term, and keep **Stage 1** as the formal interface.

## Final design decision

Build the **pairing interface first**, not the determinant interface first.

The determinant/exterior-power route is excellent as a later theorem:

```lean
WeilPairingPackage ⇒ det_torsionGaloisRep_eq_modularCyclotomicCharacter
```

but it is not a shortcut to avoid the Weil pairing. For the primitive-root axiom, the direct pairing-value route is shorter, cleaner, and avoids top-exterior and determinant API entirely. The single hard primitive remains the same:

```text
a Galois-compatible perfect alternating Weil pairing on E[n],
or equivalently a Galois-compatible isomorphism ∧²E[n] ≃ μₙ.
```
