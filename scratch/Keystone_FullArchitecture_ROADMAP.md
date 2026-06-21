Verdict: **David’s scaffold is the right foundation**, but I would refactor the API around it before building the two axiom discharges. The main changes are: make “points over an extension field” explicit, upgrade the rank-two theorem from `AddEquiv` to `ZMod n`-`LinearEquiv`, and avoid treating rational torsion finiteness as a consequence of geometric `E[n]` finiteness. The shared keystone should be built once:

```lean
E.geomNTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n)
```

or equivalently a basis of geometric `n`-torsion over `ZMod n`.

That keystone feeds both:

```lean
(A) det ρ_{E,n} = cyclotomicChar n
(B) E(ℚ)_tors ↪ E[N](ℚbar) ≃ (ZMod N)^2
```

but **(B) still needs an independent finiteness/exponent input**.

---

## 1. Recommended definition architecture

The current file already defines

```lean
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ (E⁄k).Point n
```

and gives it the natural `ZMod n` module structure using `AddCommGroup.zmodModule`. fileciteturn3file0L35-L46 That is the right basic choice: `Submodule.torsionBy ℤ A n` is more useful than a raw kernel predicate because it gives a subtype/submodule with inherited additive group structure and plays well with group-theory APIs.

I would **not** replace it with a hand-rolled `{P // n • P = 0}`. Instead, add aliases and simp lemmas so you can use either view.

Recommended layer:

```lean
namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (E : WeierstrassCurve K) [E.IsElliptic]

/-- Points of `E/K` over a field extension `L/K`. -/
abbrev PointsOver
    (L : Type*) [Field L] [Algebra K L] [DecidableEq L] : Type _ :=
  (E⁄L).Point

/-- The `n`-torsion submodule over `L`. Keep the submodule object. -/
abbrev nTorsionSubmodule
    (L : Type*) [Field L] [Algebra K L] [DecidableEq L]
    (n : ℕ) : Submodule ℤ (E.PointsOver L) :=
  Submodule.torsionBy ℤ (E.PointsOver L) n

/-- The type of `n`-torsion points over `L`. -/
abbrev nTorsionOver
    (L : Type*) [Field L] [Algebra K L] [DecidableEq L]
    (n : ℕ) : Type _ :=
  E.nTorsionSubmodule L n

/-- Geometric `n`-torsion. -/
abbrev geomNTorsion (n : ℕ) : Type _ :=
  E.nTorsionOver (AlgebraicClosure K) n

/-- Rational `n`-torsion for `K = ℚ`, or base-field `n`-torsion in general. -/
abbrev baseNTorsion (n : ℕ) : Type _ :=
  E.nTorsionOver K n

end WeierstrassCurve
```

Then keep the existing notation

```lean
E.nTorsion n
```

as a synonym for `E.baseNTorsion n` if that avoids churn.

The important design point is that **`nTorsion` over an arbitrary field is correct**. You need it for rational torsion, base change, reductions, and fixed-point statements. The Galois representation should then specialize it to the algebraic closure:

```lean
E.geomNTorsion n =
  ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n)
```

This is already the direction of the current scaffold: the final `galoisRep` target is the `nTorsion` of the base-changed curve over `AlgebraicClosure K`. fileciteturn3file0L118-L119

### Where `IsSepClosed` should live

Do **not** put `[IsSepClosed k]` on the definition of `nTorsion`. Put it only on the cardinality/rank theorem:

```lean
theorem n_torsion_card
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := ...
```

That is exactly how the current file is shaped. fileciteturn3file0L52-L55

For the Galois representation over `AlgebraicClosure K`, add a wrapper theorem:

```lean
theorem geom_n_torsion_card
    {n : ℕ} (hn : 0 < n) :
    Nat.card (E.geomNTorsion n) = n^2 := by
  -- use `n_torsion_card` over `AlgebraicClosure K`
  -- char zero for K = ℚ, or explicit `(n : AlgebraicClosure K) ≠ 0`
  ...
```

For general base fields, keep the hypothesis:

```lean
(hn : (n : AlgebraicClosure K) ≠ 0)
```

or, if typeclass style is smoother:

```lean
[NeZero (n : AlgebraicClosure K)]
```

For `ℚ`, expose a char-zero convenience lemma.

### One design flaw to fix: `AddEquiv` is not enough

David’s current theorem is:

```lean
theorem WeierstrassCurve.n_torsion_dimension
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n))
```

It is derived from the current `group_theory_lemma`, which also returns an `AddEquiv`. fileciteturn3file0L57-L73

For your infrastructure, this should be upgraded to a **linear** statement:

```lean
theorem WeierstrassCurve.n_torsion_rank_two_linear
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n)) := ...
```

or:

```lean
theorem WeierstrassCurve.geomNTorsion_basis
    {n : ℕ} (hn : 0 < n) :
    Nonempty (Module.Basis (Fin 2) (ZMod n) (E.geomNTorsion n)) := ...
```

You can probably derive linearity from the additive equivalence because the `ZMod n` module structure is the canonical one on an additive group killed by `n`. But make that conversion explicit:

```lean
def AddEquiv.toZModLinearEquivOfKilled
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {n : ℕ}
    (hA : ∀ a : A, n • a = 0)
    (hB : ∀ b : B, n • b = 0)
    (e : A ≃+ B) :
    A ≃ₗ[ZMod n] B := ...
```

Then immediately restate David’s theorem as a `LinearEquiv`. The determinant API in `GaloisRep` is module-linear; the repo’s `GaloisRep` is defined as a continuous monoid hom into `Module.End A M`, not merely additive endomorphisms. fileciteturn5file0L4-L4

### Another design flaw: avoid an unconditional `Module.Finite` instance

The current file has:

```lean
noncomputable instance (n : ℕ) :
    Module.Finite (ZMod n) (E.nTorsion n) := sorry
```

with no `0 < n` hypothesis. fileciteturn3file0L75-L76

That is too broad. For `n = 0`, `E[0]` is the whole point group, so this is not generally finite. Replace it with theorem-style API:

```lean
theorem WeierstrassCurve.nTorsion_moduleFinite
    {n : ℕ} (hn : 0 < n) :
    Module.Finite (ZMod n) (E.nTorsion n) := ...

theorem WeierstrassCurve.geomNTorsion_moduleFinite
    {n : ℕ} (hn : 0 < n) :
    Module.Finite (ZMod n) (E.geomNTorsion n) := ...
```

If you really need an instance, make it local or require a typeclass hypothesis:

```lean
noncomputable instance
    {n : ℕ} [Fact (0 < n)] :
    Module.Finite (ZMod n) (E.geomNTorsion n) := ...
```

---

## 2. Shared map/base-change layer

Build this before either axiom.

Mathlib already has the elliptic point group, map, base-change, and injectivity APIs. In particular, `Point.instAddCommGroup` exists for nonsingular affine points, and `Point.map`, `Point.baseChange`, and `Point.map_injective` exist for field maps. citeturn252397view1 citeturn252397view0

Add the torsion-restricted versions:

```lean
namespace WeierstrassCurve

noncomputable def nTorsionOver.map
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [DecidableEq L] [DecidableEq M]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (f : L →ₐ[K] M) :
    E.nTorsionOver L n →+ E.nTorsionOver M n := ...

noncomputable def nTorsionOver.mapLinear
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [DecidableEq L] [DecidableEq M]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (f : L →ₐ[K] M) :
    E.nTorsionOver L n →ₗ[ZMod n] E.nTorsionOver M n := ...

lemma nTorsionOver.map_injective
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [DecidableEq L] [DecidableEq M]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (f : L →ₐ[K] M) :
    Function.Injective (E.nTorsionOver.map n f) := ...

end WeierstrassCurve
```

For `K = ℚ`, define the rational-to-geometric injection once:

```lean
noncomputable def ratNTorsionToGeom
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) :
    E.baseNTorsion n →ₗ[ZMod n] E.geomNTorsion n :=
  E.nTorsionOver.mapLinear n (Algebra.ofId ℚ (AlgebraicClosure ℚ))
```

and:

```lean
lemma ratNTorsionToGeom_injective
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (n : ℕ) :
    Function.Injective (E.ratNTorsionToGeom n) := ...
```

This is the map used in both (A) and (B).

---

## 3. Lemma DAG for the shared `E[n] ≅ (Z/n)^2` keystone

### Existing Mathlib

Use:

```lean
WeierstrassCurve.Affine.Point.instAddCommGroup
WeierstrassCurve.Affine.Point.map
WeierstrassCurve.Affine.Point.map_id
WeierstrassCurve.Affine.Point.map_map
WeierstrassCurve.Affine.Point.map_injective
```

Mathlib also has the finite abelian group structure theorem:

```lean
AddCommGroup.equiv_directSum_zmod_of_finite
AddCommGroup.equiv_directSum_zmod_of_finite'
AddCommGroup.finite_of_fg_torsion
```

The docs state that `equiv_directSum_zmod_of_finite` gives a finite abelian group as a direct sum of prime-power `ZMod`s, and the primed version gives a direct sum of arbitrary `ZMod (n i)` with `1 < n i`. citeturn917412view0

### Existing FLT scaffold, but sorry

These are the current David scaffold sorries:

```lean
theorem WeierstrassCurve.n_torsion_finite
    {n : ℕ} (hn : 0 < n) :
    Finite (E.nTorsion n) := sorry
```

```lean
theorem WeierstrassCurve.n_torsion_card
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry
```

```lean
theorem group_theory_lemma
    {A : Type*} [AddCommGroup A] {n : ℕ}
    (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n →
      Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → ZMod n)) := sorry
```

These are exactly where the current file says division polynomials and pure finite-group theory enter. fileciteturn3file0L48-L59

Mathlib has division-polynomial definitions such as `WeierstrassCurve.Ψ`, `WeierstrassCurve.Φ`, and `WeierstrassCurve.ψ`, but not the finished cardinality theorem. citeturn252397view3 So `n_torsion_card` remains a genuine arithmetic-geometry/the-division-polynomial theorem, not a Mathlib one-liner.

### New wrappers/upgrades

Build these after David’s sorries:

```lean
theorem group_theory_lemma_linear
    {A : Type*} [AddCommGroup A]
    {n r : ℕ} (hn : 0 < n)
    [Module (ZMod n) (Submodule.torsionBy ℤ A n)]
    (h : ∀ d : ℕ, d ∣ n →
      Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃ₗ[ZMod n] (Fin r → ZMod n)) := ...
```

or derive from the additive version:

```lean
theorem WeierstrassCurve.n_torsion_rank_two_linear
    [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n)) := ...
```

Then specialize:

```lean
theorem WeierstrassCurve.geomNTorsion_rank_two_linear
    (E : WeierstrassCurve K) [E.IsElliptic]
    {n : ℕ} (hn : (n : AlgebraicClosure K) ≠ 0) :
    Nonempty (E.geomNTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n)) := ...
```

This is the keystone.

---

## 4. Galois representation layer

The current scaffold defines point maps and proves `map_id`/`map_comp`, then starts a `DistribMulAction` of field automorphisms on points, with the group-action laws still sorry. fileciteturn3file0L78-L113

I would split this into three layers.

### Layer 1: automorphism action on points

Rename/generalize mentally as:

```lean
instance WeierstrassCurve.Points.instDistribMulAction
    (K L : Type*) [Field K] [Field L]
    [Algebra K L] [DecidableEq L]
    (E : WeierstrassCurve K) [E.IsElliptic] :
    DistribMulAction (L ≃ₐ[K] L) (E.PointsOver L) := ...
```

The current `galoisRepresentation` instance is basically this. Fill the four easy sorries using `Point.map_id`, `Point.map_map`, `Point.map_zero`, and map-additivity.

### Layer 2: restricted action on `nTorsionOver`

```lean
instance WeierstrassCurve.nTorsionOver.instDistribMulAction
    (E : WeierstrassCurve K) [E.IsElliptic]
    (L : Type*) [Field L] [Algebra K L] [DecidableEq L]
    (n : ℕ) :
    DistribMulAction (L ≃ₐ[K] L) (E.nTorsionOver L n) := ...
```

The only proof obligation is preservation of `n • P = 0`.

### Layer 3: linear Galois representation on geometric torsion

For determinant work, define each automorphism as a `ZMod n`-linear automorphism/end:

```lean
noncomputable def WeierstrassCurve.geomNTorsion.galoisActionLinear
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    E.geomNTorsion n →ₗ[ZMod n] E.geomNTorsion n := ...
```

Then:

```lean
noncomputable def WeierstrassCurve.galoisRepHom
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) :
    Field.absoluteGaloisGroup K →*
      Module.End (ZMod n) (E.geomNTorsion n) := ...
```

Finally wrap it as continuous:

```lean
noncomputable def WeierstrassCurve.galoisRep
    (E : WeierstrassCurve K) [E.IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    GaloisRep K (ZMod n) (E.geomNTorsion n) := ...
```

The current `GaloisRep` file already has determinant, framing, conjugation, and base-change infrastructure for `GaloisRep`. fileciteturn5file0L4-L4 The continuity proof should be kept at the very end: for finite `n`, the target endomorphism monoid is finite/discrete once `E[n]` is finite.

---

## 5. DAG for axiom (A): full rational torsion implies primitive root in `ℚ`

Target:

```lean
theorem weil_pairing_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {m : ℕ} (hm : 0 < m)
    (hfull : FullRationalNTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m := ...
```

Define full rational torsion using the rational-to-geometric map:

```lean
def FullRationalNTorsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (m : ℕ) : Prop :=
  Function.Surjective (E.ratNTorsionToGeom m)
```

Then the DAG is:

1. **Existing/Mathlib:** point map/base-change/injectivity.
2. **New:** `ratNTorsionToGeom`.
3. **New:** rational points are Galois-fixed after base change:

   ```lean
   lemma galois_fixed_ratNTorsionToGeom
       (σ : Field.absoluteGaloisGroup ℚ)
       (P : E.baseNTorsion m) :
       σ • E.ratNTorsionToGeom m P =
       E.ratNTorsionToGeom m P := ...
   ```

4. **New:** full rational torsion implies the geometric representation is trivial:

   ```lean
   theorem galoisRep_eq_one_of_fullRationalNTorsion
       (hfull : FullRationalNTorsion E m) :
       E.galoisRep m hm = 1 := ...
   ```

5. **New/hard:** cyclotomic character mod `m`:

   ```lean
   def cyclotomicCharMod
       (K : Type*) [Field K] (m : ℕ) :
       Field.absoluteGaloisGroup K →ₜ* ZMod m := ...
   ```

   More canonically, it should land in `(ZMod m)ˣ`, then coerce to `ZMod m` if needed for comparison with `GaloisRep.det`.

6. **New/hard:** determinant-cyclotomic theorem:

   ```lean
   theorem det_galoisRep_eq_cyclotomicCharMod
       (E : WeierstrassCurve K) [E.IsElliptic]
       {m : ℕ} (hm : 0 < m)
       (hchar : (m : AlgebraicClosure K) ≠ 0) :
       (E.galoisRep m hm).det = cyclotomicCharMod K m := ...
   ```

   Mathematically this is usually proved from the Weil pairing. You can either implement a Weil-pairing layer and prove this theorem, or state/prove this as the theorem exported by that layer. For the two target axioms, **you do not need a full public Weil-pairing API** if you have this determinant theorem.

7. **New:** trivial cyclotomic character gives primitive root fixed by all Galois automorphisms:

   ```lean
   theorem primitiveRoot_fixed_of_cyclotomicChar_trivial
       {m : ℕ} (hm : 0 < m)
       (hχ : cyclotomicCharMod ℚ m = 1) :
       ∃ ζ : AlgebraicClosure ℚ,
         IsPrimitiveRoot ζ m ∧
         ∀ σ : Field.absoluteGaloisGroup ℚ, σ ζ = ζ := ...
   ```

8. **New or Mathlib lookup:** fixed-by-absolute-Galois descends to base field:

   ```lean
   theorem exists_rat_of_absoluteGalois_fixed
       {x : AlgebraicClosure ℚ}
       (hx : ∀ σ : Field.absoluteGaloisGroup ℚ, σ x = x) :
       ∃ q : ℚ, algebraMap ℚ (AlgebraicClosure ℚ) q = x := ...
   ```

9. Combine:

   ```lean
   hfull
   → galoisRep = 1
   → det galoisRep = 1
   → cyclotomicCharMod ℚ m = 1
   → fixed primitive m-th root in ℚbar
   → primitive m-th root in ℚ
   ```

For (A), the single hardest mathematical step is **determinant-cyclotomic**, i.e. the Weil-pairing theorem:

```lean
det ρ_{E,m} = χ_m.
```

The single hardest Lean/API step is making `E.geomNTorsion m` a finite free `ZMod m`-module of rank two, not just an additive group equivalent to `(ZMod m)^2`.

---

## 6. DAG for axiom (B): rational torsion has two invariant factors

Target:

```lean
theorem rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E := ...
```

### First point: (B) needs independent finiteness

You cannot get finiteness of `E(ℚ)_tors` merely from:

```lean
∀ n > 0, Finite E[n](ℚbar)
```

or even from:

```lean
E[n](ℚbar) ≃ (ZMod n)^2
```

for every `n`. The group `ℚ/ℤ` is the standard warning sign: every `n`-torsion subgroup is finite, but the total torsion group is infinite.

So (B) needs one of these as a dependency:

```lean
theorem rational_torsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (RatTors E)
```

or:

```lean
theorem mordell_weil_fg
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    AddGroup.FG (E.PointsOver ℚ)
```

then derive torsion finiteness using generic group theory. Mathlib has:

```lean
AddCommGroup.finite_of_fg_torsion
```

which says a finitely generated torsion additive commutative group is finite. citeturn917412view0

Mathematically, (B) does **not** require full Mordell–Weil; torsion finiteness can also be proved by reduction modulo two good primes. But that is a separate arithmetic development. The `E[n]` infrastructure alone will not supply it.

### Clean decomposition for (B)

Define:

```lean
abbrev RatPts (E : WeierstrassCurve ℚ) [E.IsElliptic] :=
  E.PointsOver ℚ

abbrev RatTors (E : WeierstrassCurve ℚ) [E.IsElliptic] :=
  AddCommGroup.torsion (RatPts E)
```

Then build:

#### B1. Finiteness

```lean
theorem rational_torsion_finite
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Finite (RatTors E) := ...
```

Source choices:

```lean
-- Route 1: easiest if available
mordell_weil_fg
  → subgroup of FG abelian group is FG
  → RatTors is FG
  → RatTors is torsion
  → AddCommGroup.finite_of_fg_torsion

-- Route 2: independent of Mordell-Weil, but much harder
good reduction at two primes
  → torsion injects into finite product of finite-field point groups
  → finite
```

#### B2. Exponent

Once `[Finite (RatTors E)]`, let:

```lean
let N := Nat.card (RatTors E)
```

or use the group exponent if you introduce one. The crude cardinal exponent is enough:

```lean
lemma ratTors_card_kills
    [Finite (RatTors E)] :
    ∀ T : RatTors E, Nat.card (RatTors E) • T = 0 := by
  -- use `card_nsmul_eq_zero`
```

Mathlib’s order-of-element API includes `addOrderOf_dvd_card`, `card_nsmul_eq_zero`, and related additive-order lemmas. citeturn977127view0

#### B3. Inject rational torsion into geometric `N`-torsion

```lean
noncomputable def RatTors.toGeomNTorsion
    [Finite (RatTors E)] :
    RatTors E →+ E.geomNTorsion (Nat.card (RatTors E)) := ...
```

This sends `T` to its underlying rational point, then base-changes to `ℚbar`, using `ratTors_card_kills`.

Prove:

```lean
lemma RatTors.toGeomNTorsion_injective
    [Finite (RatTors E)] :
    Function.Injective (RatTors.toGeomNTorsion E) := ...
```

using `Point.map_injective`.

#### B4. Geometric rank two

Use the shared keystone:

```lean
theorem geomNTorsion_rank_two_linear
    (hn : 0 < N) :
    Nonempty (E.geomNTorsion N ≃ₗ[ZMod N] (Fin 2 → ZMod N))
```

For the trivial torsion group, handle `N = 1` separately if needed. Avoid `N = 0`.

#### B5. Pure algebra: subgroup of `(ZMod N)^2` has two invariant factors

This is the pure group theorem you should add:

```lean
theorem finite_add_comm_group_embed_zmod_sq_invariantFactors
    {G : Type*} [AddCommGroup G] [Finite G]
    {N : ℕ} (hN : 0 < N)
    (ι : G →+ (ZMod N × ZMod N))
    (hι : Function.Injective ι) :
    ∃ m n : ℕ,
      0 < m ∧ 0 < n ∧ m ∣ n ∧
      Nonempty (G ≃+ ZMod m × ZMod n) := ...
```

This is often cleaner than first proving “two-generated” and then doing invariant-factor regrouping. Internally, prove it by finite abelian classification plus a two-column regrouping of elementary divisors. Mathlib gives the finite abelian group as a direct sum of cyclic factors, but not already in the final invariant-factor form with divisibility. citeturn917412view0

A useful intermediate theorem is:

```lean
theorem finite_add_comm_group_two_generated_invariantFactors
    {G : Type*} [AddCommGroup G] [Finite G]
    (h2 : ∃ a b : G,
      AddSubgroup.closure ({a, b} : Set G) = ⊤) :
    ∃ m n : ℕ,
      0 < m ∧ 0 < n ∧ m ∣ n ∧
      Nonempty (G ≃+ ZMod m × ZMod n) := ...
```

But for your application, the embedding theorem is more direct.

#### B6. Produce the packaged data

From:

```lean
e : RatTors E ≃+ ZMod m × ZMod n
```

build:

```lean
HasTorsionStructure E m n
```

Then:

```lean
HasRationalPointOfOrder E n
```

comes from the element corresponding to:

```lean
(0, 1 : ZMod n)
```

Use:

```lean
ZMod.addOrderOf_one
Prod.addOrderOf
AddEquiv.addOrderOf_eq
```

Finally:

```lean
(torsionSet E).ncard = m * n
```

is the cardinality transported across the equivalence.

### Minimal final shape

```lean
noncomputable theorem rational_torsion_two_invariant_factors
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    TorsionStructureData E := by
  classical

  have hfin : Finite (RatTors E) :=
    rational_torsion_finite E

  let N := Nat.card (RatTors E)

  have hkill : ∀ T : RatTors E, N • T = 0 :=
    ratTors_card_kills E

  let ι : RatTors E →+ E.geomNTorsion N :=
    RatTors.toGeomNTorsion E

  have hι : Function.Injective ι :=
    RatTors.toGeomNTorsion_injective E

  obtain ⟨φgeom⟩ :=
    E.geomNTorsion_rank_two_linear (N := N) ?hN

  let j : RatTors E →+ (ZMod N × ZMod N) :=
    (φgeom.toAddEquiv.toAddMonoidHom).comp ι

  have hj : Function.Injective j := ...

  obtain ⟨m, n, hmpos, hnpos, hmn, ⟨e⟩⟩ :=
    finite_add_comm_group_embed_zmod_sq_invariantFactors
      (G := RatTors E) ?hN j hj

  refine ⟨m, n, ?hasStruct, ?hasPointOrderN, ?card, hmn⟩
  · -- unwrap `HasTorsionStructure`
    exact ...
  · -- use `e.symm (0, 1)` as rational torsion point of order `n`
    exact ...
  · -- cardinality of torsionSet
    exact ...
```

For `N = 1`, the torsion group is trivial and you can return `m = 1`, `n = 1`.

---

## 7. Build order / critical path

I would build in this order.

### Phase 0: cleanup and API wrappers

Do first; mostly no hard math.

1. `PointsOver`
2. `nTorsionSubmodule`
3. `nTorsionOver`
4. `geomNTorsion`
5. `baseNTorsion`
6. `nTorsionOver.map`
7. `nTorsionOver.mapLinear`
8. `nTorsionOver.map_injective`
9. `ratNTorsionToGeom`
10. `galois_fixed_ratNTorsionToGeom`

This makes the rational/geometric distinction explicit and avoids future rewrites.

### Phase 1: finish the easy Galois action sorries

Fill:

```lean
WeierstrassCurve.galoisRepresentation.one_smul
WeierstrassCurve.galoisRepresentation.mul_smul
WeierstrassCurve.galoisRepresentation.smul_zero
WeierstrassCurve.galoisRepresentation.smul_add
```

These should be point-map functoriality proofs, not arithmetic geometry.

Then restrict the action to `nTorsion`.

### Phase 2: shared torsion keystone

This unlocks both axioms.

1. Fill or assume temporarily:

   ```lean
   n_torsion_finite
   n_torsion_card
   ```

2. Fill or upgrade:

   ```lean
   group_theory_lemma
   group_theory_lemma_linear
   ```

3. Prove:

   ```lean
   geomNTorsion_rank_two_linear
   geomNTorsion_basis
   geomNTorsion_moduleFinite
   geomNTorsion_moduleFree
   ```

This is the central shared substructure.

### Phase 3: rational torsion axiom (B)

If `mordell_weil_fg` is already an accepted separate axiom, use it here. Otherwise introduce:

```lean
rational_torsion_finite
```

as its own target theorem/axiom.

Then build:

```lean
RatTors.toGeomNTorsion
finite_add_comm_group_embed_zmod_sq_invariantFactors
rational_torsion_two_invariant_factors
```

This is probably the shortest axiom to discharge **after** the shared keystone and finiteness are available. It is not shortest before that.

### Phase 4: determinant/cyclotomic axiom (A)

Build:

```lean
cyclotomicCharMod
det_galoisRep_eq_cyclotomicCharMod
galoisRep_eq_one_of_fullRationalNTorsion
fixed_by_absoluteGalois_descends
weil_pairing_primitive_root
```

This is deeper than (B) because `det_galoisRep_eq_cyclotomicCharMod` is the Weil-pairing theorem in disguise.

---

## 8. What to reuse vs build fresh

Reuse:

```lean
Submodule.torsionBy ℤ (E⁄k).Point n
```

from David’s file. It is the right definition. fileciteturn3file0L35-L46

Reuse/fill David’s:

```lean
n_torsion_finite
n_torsion_card
group_theory_lemma
n_torsion_dimension
galoisRepresentation
galoisRep
```

but upgrade `n_torsion_dimension` to a linear/basis statement. fileciteturn3file0L50-L76

Reuse Mathlib’s:

```lean
Point.map
Point.map_injective
Point.instAddCommGroup
AddCommGroup.equiv_directSum_zmod_of_finite
AddCommGroup.finite_of_fg_torsion
card_nsmul_eq_zero
addOrderOf_dvd_card
```

Build fresh:

```lean
PointsOver
nTorsionOver.mapLinear
ratNTorsionToGeom
FullRationalNTorsion
galoisRep_trivial_of_full_rational_torsion
cyclotomicCharMod
det_galoisRep_eq_cyclotomicCharMod
fixed_by_absoluteGalois_descends
RatTors.toGeomNTorsion
finite_add_comm_group_embed_zmod_sq_invariantFactors
```

---

## Bottom line

The right architecture is:

```text
PointsOver / nTorsionOver / mapLinear / rational-to-geometric injection
        ↓
geometric n-torsion finite + card n²
        ↓
E[n](Kbar) ≃ₗ[ZMod n] (ZMod n)^2       ← shared keystone
        ↓                                  ↓
(B) rational torsion rank ≤ 2              (A) det Galois rep makes sense
    + independent finiteness                   + det = cyclotomic
    + pure invariant factors                    + full rational ⇒ trivial rep
        ↓                                  ↓
TorsionStructureData E                    primitive m-th root in ℚ
```

The **single most important build target** is the linear rank-two theorem for geometric torsion:

```lean
E.geomNTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n)
```

The **single most dangerous hidden dependency** for (B) is torsion finiteness. It cannot be recovered from individual `E[n]` finiteness alone. Use `mordell_weil_fg` if it is already a separate accepted axiom/theorem; otherwise split off `rational_torsion_finite` as an explicit dependency.
