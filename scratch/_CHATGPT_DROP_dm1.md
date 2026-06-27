# Q1355 (dm1/dm4): refactor `no_odd_prime_square_in_torsion` through `RealTorsionBridge`

## Recommendation

Modify `Axioms.lean` directly, but keep the actual real-torsion theorem in `RealTorsionBridge.lean`.

Do **not** create a parallel replacement theorem in a new file unless importing `RealTorsionBridge.lean` into `Axioms.lean` creates an import cycle. The theorem name `no_odd_prime_square_in_torsion` is part of the current API, so the clean refactor is:

1. Put/keep the geometric fact in `RealTorsionBridge.lean`:
   ```lean
   no_zmod_p_square_in_rational_points
   ```
2. Import `RealTorsionBridge` in `Axioms.lean`.
3. Replace only the proof body of `no_odd_prime_square_in_torsion`.
4. Delete the old `HasFullRationalTorsion → weil_pairing_primitive_root` path from that proof.

This keeps downstream files unchanged: they still use `no_odd_prime_square_in_torsion`.

## Core construction

If your hypothesis is an additive embedding into the torsion subtype,

```lean
ι : (ZMod p × ZMod p) ↪+ EQtors
```

where `EQtors` is a subtype of `(E⁄ℚ).Point`, build the embedding into rational points by projecting out of the subtype.

```lean
/-- Forget that the image lies in the torsion subtype. -/
noncomputable def torsionSquareEmbeddingToPointEmbedding
    {G : Type*} [AddCommGroup G]
    {p : ℕ}
    {T : Type*} [AddCommGroup T]
    [Coe T G]
    (ι : (ZMod p × ZMod p) ↪+ T)
    (hcoe_inj : Function.Injective (fun x : T => (x : G))) :
    (ZMod p × ZMod p) ↪+ G where
  toFun x := (ι x : G)
  map_zero' := by
    change ((ι 0 : T) : G) = 0
    rw [map_zero]
    rfl
  map_add' x y := by
    change ((ι (x + y) : T) : G) = ((ι x : T) : G) + ((ι y : T) : G)
    rw [map_add]
    rfl
  inj' := by
    intro x y hxy
    apply ι.injective
    exact hcoe_inj hxy
```

For a concrete subtype, you usually do not need the abstract helper. The proof is just:

```lean
let ιpts : (ZMod p × ZMod p) ↪+ (E⁄ℚ).Point where
  toFun x := (ι x).1
  map_zero' := by
    change (ι 0).1 = 0
    rw [map_zero]
    rfl
  map_add' x y := by
    change (ι (x + y)).1 = (ι x).1 + (ι y).1
    rw [map_add]
    rfl
  inj' := by
    intro x y hxy
    apply ι.injective
    exact Subtype.ext hxy
```

The only trick is the last line: equality in the ambient point group gives equality in the torsion subtype by `Subtype.ext`.

## Replacement proof shape

Use this shape inside `Axioms.lean`.

```lean
-- Old proof path:
--   full torsion -> Weil pairing primitive root -> p ≤ 2 -> contradiction
-- New proof path:
--   full torsion -> forget torsion subtype -> forbidden ZMod p square in E(ℚ)

theorem no_odd_prime_square_in_torsion
    -- keep your existing binders exactly as they are
    -- e.g. (E : WeierstrassCurve ℚ) [E.IsElliptic] {p : ℕ} ...
    : ¬ Nonempty ((ZMod p × ZMod p) ↪+ EQtors) := by
  rintro ⟨ι⟩

  let ιpts : (ZMod p × ZMod p) ↪+ (E⁄ℚ).Point where
    toFun x := (ι x).1
    map_zero' := by
      change (ι 0).1 = 0
      rw [map_zero]
      rfl
    map_add' x y := by
      change (ι (x + y)).1 = (ι x).1 + (ι y).1
      rw [map_add]
      rfl
    inj' := by
      intro x y hxy
      apply ι.injective
      exact Subtype.ext hxy

  exact no_zmod_p_square_in_rational_points
    -- pass the same E, p, primality/oddness hypotheses as required by your theorem
    ιpts
```

If `no_zmod_p_square_in_rational_points` is stated as a negated `Nonempty`, use:

```lean
  exact no_zmod_p_square_in_rational_points ⟨ιpts⟩
```

If it is stated with a raw map and injectivity hypothesis, use:

```lean
  exact no_zmod_p_square_in_rational_points
    (fun x => (ι x).1)
    (by
      intro x y hxy
      apply ι.injective
      exact Subtype.ext hxy)
```

If it is stated with an additive embedding, pass `ιpts` directly.

## Import-cycle rule

Use this decision rule:

```text
If RealTorsionBridge imports Axioms:
  do not import RealTorsionBridge into Axioms; that creates a cycle.
  Instead move no_zmod_p_square_in_rational_points to a lower-level file
  that imports only elliptic-curve/torsion basics, then import that lower-level file into Axioms.

If RealTorsionBridge does not import Axioms:
  import RealTorsionBridge in Axioms and refactor the existing theorem in place.
```

The best final dependency graph is:

```text
EllipticCurve/Torsion basics
        ↓
RealTorsionBridge.lean       Axioms.lean
        └──────────────────────↑
```

not

```text
Axioms.lean ↔ RealTorsionBridge.lean
```

## What to remove

Remove only the old proof-local chain:

```lean
HasFullRationalTorsion E p
weil_pairing_primitive_root
IsPrimitiveRoot ζ p
p ≤ 2
```

Keep the public theorem statement and all callers intact. The replacement proof should be shorter and should avoid any Weil-pairing dependency entirely.
