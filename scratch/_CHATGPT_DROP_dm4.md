# Q357 (dm4): finite morphism / dual-deformation shortcut for bridge-2

## Short answer

No: **finite + nonconstant is not enough** to rule out a nonzero dual deformation mapping to the same point.  What you need is **unramified** or **étale** at the point, equivalently injectivity on tangent directions.  For multiplication-by-`n` on an elliptic curve, that unramified/étale statement is proved by exactly the tangent computation

```text
d[n]_O = n.
```

So the proposed “finite morphism” shortcut does not avoid bridge-2.  It replaces the missing step 5 by the theorem “`[n]` is unramified at `P`,” whose proof is precisely the same formal tangent/local-parameter content.

## Why finite morphism is insufficient

The statement

```text
finite nonconstant morphism ⇒ finite fibers
```

is a statement about **ordinary geometric points**.  A nonzero dual deformation is not a second ordinary point of the fiber; it is a nonreduced infinitesimal thickening over the same underlying point:

```text
Spec K[ε]/(ε²) → X.
```

Finite fibers do not prohibit nilpotent tangent directions inside a scheme-theoretic fiber.  Those nilpotent directions are exactly ramification.

The basic counterexample is the finite nonconstant map

```text
A¹ → A¹,    t ↦ t².
```

At `0`, the nonzero dual deformation `t = ε` maps to

```text
t² = ε² = 0.
```

So it has the same image as the closed point `0`, even though the morphism is finite, nonconstant, and degree `2`.  This is ordinary ramification, not a contradiction.

For elliptic curves the same issue appears in characteristic `p`: the Frobenius and inseparable parts of `[p]` can kill tangent directions.  The condition `(n : K) ≠ 0` is exactly what should rule this out, and it does so through the differential.

## Correct replacement for the false claim

The false claim is:

```text
finite nonconstant maps send distinct dual deformations to distinct images.
```

The correct claim is:

```text
unramified maps send nonzero tangent vectors to nonzero tangent vectors.
```

or, in dual-number language:

```text
If f is unramified at P and Pε is a dual lift of P with nonzero tangent vector,
then f(Pε) cannot be the constant dual lift of f(P).
```

For `[n] : E → E`, the theorem you need is:

```text
[n] is unramified/étale at P when (n : K) ≠ 0.
```

The standard proof is:

1. translations identify `T_P E` and `T_O E`;
2. the differential of `[n]` commutes with translation;
3. `d[n]_O` is multiplication by `(n : K)`;
4. `(n : K) ≠ 0`, so the tangent map is injective.

That is exactly the `TangentO.nsmul₁` route.

## What the missing step 5 really is

Step 5 cannot be replaced by finiteness.  It should be formalized as the tangent/local-parameter compatibility theorem:

```lean
/-- Compatibility of the concrete local parameter with the abstract tangent map. -/
theorem coeff_localT_nsmul_dual_eq_TangentO_nsmul₁
    (W : WeierstrassCurve K) [W.IsElliptic]
    (n : ℕ) {x y : K} (hP : (W⁄K).Nonsingular x y)
    (Pε : DualAffinePoint W x y)
    (λ : K)
    (hλ : affineTangentCoord W x y Pε = λ) :
    coeffε (localT (nsmulDualJacobianRep W n Pε))
      = TangentO.nsmul₁ W n λ := by
  -- prove from definitions of the local parameter, translations, and the group law over dual numbers
  sorry
```

Then, for the scaled lift with tangent coordinate `λ = 1`:

```lean
have ht_coeff_tangent :
    coeffε (localT (nsmulDualJacobianRep W n Pε)) = TangentO.nsmul₁ W n 1 := by
  exact coeff_localT_nsmul_dual_eq_TangentO_nsmul₁
    (W := W) (n := n) hP Pε 1 hλ_one

have ht_coeff_nat :
    coeffε (localT (nsmulDualJacobianRep W n Pε)) = (n : K) := by
  calc
    coeffε (localT (nsmulDualJacobianRep W n Pε))
        = TangentO.nsmul₁ W n 1 := ht_coeff_tangent
    _ = (n : K) := by
        simpa using
          TangentO.nsmul₁_eq_natCast_mul
            (W := W) (n := n) (a := (1 : K))
```

This is the non-circular bridge.  If the projective formula plus derivative-zero gives the same coefficient as `0`, then `(n : K) = 0`, contradicting `hn`.

## What “finite morphism” looks like in Mathlib

Mathlib does have a scheme-level finite morphism API.  The file is:

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Finite
```

The core class is:

```lean
namespace AlgebraicGeometry

class IsFinite {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  finite_app (U : Y.Opens) (hU : IsAffineOpen U) :
    (f.app U).hom.Finite

end AlgebraicGeometry
```

There is also an affine-Spec characterization:

```lean
AlgebraicGeometry.IsFinite.SpecMap_iff
```

with shape:

```lean
IsFinite (Spec.map f) ↔ f.hom.Finite
```

and Mathlib’s file comment points to a finite-fiber theorem:

```lean
AlgebraicGeometry.IsFinite.finite_preimage_singleton
```

But this API is **not** the right endpoint for bridge-2:

* it concerns morphisms of `Scheme`, while the elliptic-curve group law in the files you are using is mostly point/formula-level;
* even if `[n]` is packaged as a `Scheme.Hom` and proved finite, finite fibers do not imply injectivity on dual-number points;
* to rule out the dual deformation, you need the unramified/étale API or a direct tangent calculation.

## If you tried to use the scheme route anyway

The correct scheme-level theorem would be something like:

```lean
-- schematic, not current local API
have het : IsEtale (nMulMorphism W n) := by
  -- prove from `d[n] = n` and `(n : K) ≠ 0`
  sorry

have hunram : IsUnramified (nMulMorphism W n) := by
  infer_instance -- or from `het`
```

Then use the formal infinitesimal lifting / tangent-space characterization of unramified morphisms to show that a nonzero tangent vector cannot be killed.

But this is not shorter.  Proving `het` is exactly the tangent map theorem in a more abstract wrapper.  If Mathlib eventually has a theorem saying multiplication-by-`n` on an elliptic curve is finite étale for `(n : K) ≠ 0`, then yes, it would close bridge-2.  In the current project architecture, that theorem would itself need a dependency audit, because it likely depends on the same `d[n] = n` computation or stronger isogeny theory.

## Correct non-circular proof structure

Keep the bridge-2 proof in the tangent/local-parameter language:

1. Assume `(W.preΨ' n).derivative.eval x = 0` at a root.
2. Use the dual Taylor lemma to get `preΨ'_n(xε) = 0` for a scaled nonzero tangent lift.
3. Use the parity bridge to get `ψ_n(Pε) = 0`.
4. Use the projective division-polynomial formula to make the `Z` coordinate of `[n]Pε` zero.
5. Therefore the concrete local parameter coefficient of `[n]Pε` is `0`.
6. Compare the same coefficient with `TangentO.nsmul₁ W n 1`.
7. Rewrite `TangentO.nsmul₁ W n 1 = (n : K)` and contradict `(n : K) ≠ 0`.

This is exactly the proof that `[n]` is unramified in the relevant tangent direction, but it avoids the heavy scheme-level finite/étale formalism.

## Recommendation

Do not spend time trying to formalize bridge-2 from `IsFinite`.  It is mathematically too weak and will not produce the needed dual-number injectivity.  The shortest non-circular path remains the explicit local-parameter/tangent comparison theorem.  In other words, step 5 is not optional; it is the precise Lean form of the statement that `[n]` has nonzero differential when `(n : K) ≠ 0`.
