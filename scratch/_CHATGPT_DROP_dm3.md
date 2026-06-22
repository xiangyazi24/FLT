# Q225 (dm3): Generic-point route for the division-polynomial doubling composition seam

Question: can the coordinate-ring composition law

```lean
mk_phi_psi_dup_doubling_cross (m : ℤ) :
  mk W.toAffine
    (W.φ (2*m) * dupDenBiv (W.φ m) ((W.ψ m)^2)
      - (W.ψ (2*m))^2 * dupNumBiv (W.φ m) ((W.ψ m)^2)) = 0
```

be proved by applying the already-proved pointwise doubling theorem to the **generic point** of `W` over the function field of the affine coordinate ring?

Short answer:

```text
Generic point existence:           YES, buildable in Mathlib.
Point.generic declaration:         NO, not currently exposed as a named theorem.
x([n]G) = Φₙ/ΨSqₙ in Mathlib:     NO.
Generic route shorter?:            NO, unless x([n]G)=Φₙ/ΨSqₙ is already available.
Real remaining gap:                the generic n-multiple coordinate formula.
```

The generic point is useful as a *semantic check* and may be useful as a final descent-from-function-field wrapper, but it does not remove the need to prove the division-polynomial coordinate formula.  Without that formula, applying the pointwise doubling theorem to `[m]G` only gives a statement about `x([m]G)`, not about `φ_m` and `ψ_m²`.

## 1. Does Mathlib support constructing the generic point?

There is no declaration I know of named

```lean
WeierstrassCurve.Affine.Point.generic
```

but the construction is available from existing pieces:

```lean
WeierstrassCurve.Affine.CoordinateRing
WeierstrassCurve.Affine.FunctionField
WeierstrassCurve.Affine.CoordinateRing.mk
WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing
WeierstrassCurve.Affine.equation_iff_nonsingular
WeierstrassCurve.Affine.Equation.map
IsFractionRing.injective
```

Mathlib defines

```lean
abbrev WeierstrassCurve.Affine.CoordinateRing (W : Affine R) :=
  AdjoinRoot W.polynomial

abbrev WeierstrassCurve.Affine.FunctionField (W : Affine R) :=
  FractionRing W.CoordinateRing
```

and the coordinate-ring map

```lean
noncomputable abbrev WeierstrassCurve.Affine.CoordinateRing.mk
    (W : Affine R) : R[X][Y] →+* W.CoordinateRing :=
  AdjoinRoot.mk W.polynomial
```

So for a field `k`, the generic coordinates are the classes of `X` and `Y`, mapped into the fraction field.

## 2. Generic point construction skeleton

This is the Lean shape I would use.  Some `simpa` details may need local adjustment, but there is no missing math here.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.FractionRing
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve
namespace Affine
namespace GenericPoint

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

local notation "A" => W.toAffine.CoordinateRing
local notation "K" => FractionRing A

/-- The generic `X` coordinate in the affine coordinate ring. -/
noncomputable def xCR : A :=
  CoordinateRing.mk W.toAffine (C X)

/-- The generic `Y` coordinate in the affine coordinate ring. -/
noncomputable def yCR : A :=
  CoordinateRing.mk W.toAffine Y

/-- The generic `X` coordinate in the function field. -/
noncomputable def xK : K :=
  algebraMap A K (xCR W)

/-- The generic `Y` coordinate in the function field. -/
noncomputable def yK : K :=
  algebraMap A K (yCR W)

/-- The coordinate-ring generic point satisfies the Weierstrass equation. -/
lemma generic_equation_CR :
    (W.toAffine.baseChange A).Equation (xCR W) (yCR W) := by
  -- This is the core quotient calculation:
  -- `W.polynomial` vanishes in `AdjoinRoot W.polynomial`.
  -- Expected proof shape:
  --   change ((W.toAffine.baseChange A).polynomial.evalEval (xCR W) (yCR W) = 0)
  --   simpa [xCR, yCR, CoordinateRing.mk, Affine.Equation,
  --          Affine.map_polynomial, Affine.baseChange,
  --          evalEval, Polynomial.aeval_def]
  --     using AdjoinRoot.aeval_eq W.toAffine.polynomial
  -- or equivalently `AdjoinRoot.mk_self` after rewriting eval at the two classes.
  --
  -- This is CLOSEABLE-NOW, but the exact `simpa` terms depend on the local
  -- normal form of `evalEval` and `CoordinateRing.mk`.
  sorry

/-- The generic point satisfies the equation after mapping to the function field. -/
lemma generic_equation_K :
    (W.toAffine.baseChange K).Equation (xK W) (yK W) := by
  -- Use `Affine.Equation.map` from `A` to `K`, then simplify the two-step base change.
  -- Exact proof shape:
  --   simpa [xK, yK, xCR, yCR, Affine.baseChange, WeierstrassCurve.map_map]
  --     using (generic_equation_CR W).map (algebraMap A K)
  --
  -- CLOSEABLE-NOW once `generic_equation_CR` is closed.
  sorry

/-- The generic point of `W` over the function field of its affine coordinate ring. -/
noncomputable def genericPoint :
    (W.toAffine.baseChange K).Point :=
  .some (xK W) (yK W) <|
    ((W.toAffine.baseChange K).equation_iff_nonsingular).mp
      (generic_equation_K W)

@[simp] lemma genericPoint_xRep_X
    -- Replace by project-local xRep if needed.
    : True := by
  -- If `xRep` maps `.some x y h` to `[x:1]`, this is immediate by `rfl`/`simp`.
  trivial

end GenericPoint
end Affine
end WeierstrassCurve
```

Status:

```text
generic point existence: CLOSEABLE-NOW.
Point.generic named API: MISSING-MATHLIB-API, but not a serious blocker.
```

The only slightly annoying proof is `generic_equation_CR`, but it is just the quotient relation in `AdjoinRoot`.  It does not require division polynomials or group law.

## 3. What the generic-point strategy would need next

To use the pointwise theorem on `[m]G`, one needs the formula

```lean
xRep ((m : ℤ) • genericPoint W) = [mk(Φ_m) : mk(ΨSq_m)]
```

or bivariately

```lean
xRep ((m : ℤ) • genericPoint W) = [mk(φ_m) : mk(ψ_m^2)]
```

in the function field.

A precise project-local statement would look like this:

```lean
namespace WeierstrassCurve
namespace Affine
namespace GenericPoint

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

local notation "A" => W.toAffine.CoordinateRing
local notation "K" => FractionRing A

/-- Missing bridge: coordinate formula for multiples of the generic point. -/
theorem xRep_zsmul_generic_same_φ_ψ
    (m : ℤ) :
    P1.Same
      (xRep (W.toAffine.baseChange K) (m • genericPoint W))
      (P1.mk
        (algebraMap A K (CoordinateRing.mk W.toAffine (W.φ m)))
        (algebraMap A K (CoordinateRing.mk W.toAffine ((W.ψ m)^2)))) := by
  -- NOT in Mathlib.
  -- This is essentially the same keystone bridge currently being built.
  sorry

/-- Equivalent univariate version using Mathlib's coordinate-ring congruences. -/
theorem xRep_zsmul_generic_same_Φ_ΨSq
    (m : ℤ) :
    P1.Same
      (xRep (W.toAffine.baseChange K) (m • genericPoint W))
      (P1.mk
        (algebraMap A K (CoordinateRing.mk W.toAffine (C (W.Φ m))))
        (algebraMap A K (CoordinateRing.mk W.toAffine (C (W.ΨSq m))))) := by
  -- Would follow from `xRep_zsmul_generic_same_φ_ψ` plus:
  --   CoordinateRing.mk_φ
  --   CoordinateRing.mk_ψ
  --   CoordinateRing.mk_Ψ_sq
  -- but the group-law coordinate formula is still missing.
  sorry

end GenericPoint
end Affine
end WeierstrassCurve
```

This theorem is **not** in Mathlib.  Mathlib has the coordinate-ring congruences among the polynomial definitions:

```lean
#check WeierstrassCurve.Affine.CoordinateRing.mk_ψ
#check WeierstrassCurve.Affine.CoordinateRing.mk_φ
#check WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq
```

but those say only that the bivariate and univariate division-polynomial definitions agree in the coordinate ring.  They do **not** connect the polynomials to the actual group-law multiple `m • P`.

## 4. Applying the pointwise doubling theorem to the generic point

Suppose the missing generic multiple formula were available for `m` and `2*m`.  Then your already-proved pointwise theorem would give the desired composition law in the function field.

Sketch:

```lean
namespace WeierstrassCurve
namespace Affine
namespace GenericPoint

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

local notation "A" => W.toAffine.CoordinateRing
local notation "K" => FractionRing A

-- Existing theorem, schematic name/types.
variable
  (xRep_two_nsmul_same_dup_affine :
    ∀ (P : (W.toAffine.baseChange K).Point),
      SameP1Vec ((2 • P).xRep)
        ![dupNumH P.xRep.1 P.xRep.2,
          dupDenH P.xRep.1 P.xRep.2])

/-- Function-field version of the doubling composition, assuming the missing generic formula. -/
lemma generic_dup_composition_in_function_field
    (m : ℤ)
    (hm : xRep_zsmul_generic_same_φ_ψ W m)
    (h2m : xRep_zsmul_generic_same_φ_ψ W (2*m)) :
    algebraMap A K
      (CoordinateRing.mk W.toAffine
        (W.φ (2*m) * dupDenBiv (W.φ m) ((W.ψ m)^2)
          - (W.ψ (2*m))^2 * dupNumBiv (W.φ m) ((W.ψ m)^2))) = 0 := by
  -- Apply pointwise duplication to `P = m • genericPoint W`.
  have hdup := xRep_two_nsmul_same_dup_affine (m • genericPoint W)

  -- Rewrite:
  --   2 • (m • G) = (2*m) • G
  -- and use `hm`, `h2m` to replace the xReps by `[φ_m : ψ_m²]` and
  -- `[φ_2m : ψ_2m²]`.
  -- Then unfold `SameP1Vec`, `dupNumH`, `dupDenH`, and clear the projective cross-product.
  -- This is algebraic and should close by `ring_nf`.
  sorry

end GenericPoint
end Affine
end WeierstrassCurve
```

Then descend from the function field to the coordinate ring by injectivity of the localization map:

```lean
namespace WeierstrassCurve
namespace Affine
namespace GenericPoint

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

local notation "A" => W.toAffine.CoordinateRing
local notation "K" => FractionRing A

lemma generic_field_zero_descends
    {a : A}
    (ha : algebraMap A K a = 0) :
    a = 0 := by
  exact (IsFractionRing.injective A K) ha

lemma mk_phi_psi_dup_doubling_cross_from_generic
    (m : ℤ)
    (hfield :
      algebraMap A K
        (CoordinateRing.mk W.toAffine
          (W.φ (2*m) * dupDenBiv (W.φ m) ((W.ψ m)^2)
            - (W.ψ (2*m))^2 * dupNumBiv (W.φ m) ((W.ψ m)^2))) = 0) :
    CoordinateRing.mk W.toAffine
      (W.φ (2*m) * dupDenBiv (W.φ m) ((W.ψ m)^2)
        - (W.ψ (2*m))^2 * dupNumBiv (W.φ m) ((W.ψ m)^2)) = 0 := by
  exact generic_field_zero_descends W hfield

end GenericPoint
end Affine
end WeierstrassCurve
```

Status:

```text
CLOSEABLE-NOW:
  descent from function field to coordinate ring via `IsFractionRing.injective`.

MISSING:
  function-field equality, because it needs `xRep_zsmul_generic_same_φ_ψ`.
```

## 5. Is `x([n]G)=Φₙ/ΨSqₙ` easier than the composition law?

No.  It is essentially the same theorem at a more semantic level.

To prove

```lean
xRep (n • genericPoint) = [Φₙ : ΨSqₙ]
```

one normally inducts using:

```text
x-only differential addition / doubling
+ recurrences for Φ, ΨSq, preΨ
```

The doubling step of that induction is exactly the composition assertion:

```text
[Φ₂m : ΨSq₂m] = dup([Φ_m : ΨSq_m]).
```

So using the generic point to prove the doubling composition would be circular if the generic formula is part of the same induction.  More explicitly:

```text
To prove composition for 2m via generic point, you need:
  x((2m)G) = [φ₂m : ψ₂m²]
and
  x(mG)    = [φ_m  : ψ_m²].

But `x((2m)G) = [φ₂m : ψ₂m²]` is precisely the doubled case of the n-multiple coordinate theorem, whose proof requires the composition lemma.
```

Therefore the generic route does not reduce the algebraic work.  It only repackages it.

## 6. Could one prove the generic formula by induction using the already-proven ladder?

Yes, but then the generic point is not doing the hard work.  The proof would be:

```text
1. Build x-only ladder for arbitrary points.
2. Prove ladder output equals Mathlib's Φ/ΨSq recurrences.
3. Specialize to the generic point.
```

That is the existing ladder route.

A simultaneous induction is possible:

```lean
-- schematic
mutual theorem xRep_zsmul_generic_same_φ_ψ, mk_phi_psi_dup_doubling_cross, ...
```

but it is not shorter.  The algebraic composition lemma remains one of the induction transitions.

## 7. Cleanest concrete path now

I would not switch to a generic-point proof for `mk_phi_psi_dup_doubling_cross`.  The cleaner path is:

```text
A. Use Mathlib EDS recurrence lemmas for preΨ/ΨSq/Φ.
B. Prove the bivariate/univariate duplication composition directly in the coordinate ring.
C. Use `CoordinateRing.mk_φ`, `CoordinateRing.mk_ψ`, `CoordinateRing.mk_Ψ_sq` to move between bivariate and univariate forms.
D. Use the already-proven pointwise duplication theorem in the *point-level* ladder, not as a shortcut for the coordinate-ring recurrence identity.
```

The generic point can still be useful as a final sanity theorem:

```lean
/-- Once the ladder theorem is proved, this should be an easy corollary. -/
theorem xRep_zsmul_generic_same_φ_ψ_corollary
    (m : ℤ) :
    P1.Same
      (xRep (W.toAffine.baseChange K) (m • genericPoint W))
      (P1.mk
        (algebraMap A K (CoordinateRing.mk W.toAffine (W.φ m)))
        (algebraMap A K (CoordinateRing.mk W.toAffine ((W.ψ m)^2)))) := by
  -- specialize the global ladder theorem to `genericPoint W`
  sorry
```

But proving this corollary first is not a shortcut.

## 8. Final verdict

```text
Generic point construction: viable and closeable.
Generic point as shortcut: not viable.
Real gap: x([n]G)=Φₙ/ΨSqₙ, which is exactly the group-law/division-polynomial bridge.
Recommended path: prove the coordinate-ring composition from EDS recurrences directly, or continue the ladder recurrence matching.  Do not detour through the generic point expecting it to remove the composition proof.
```

If you want one small generic-point lemma to de-risk independently, make it this:

```lean
lemma genericPoint_exists_and_equation
    {k : Type*} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic] :
    ∃ G : (W.toAffine.baseChange (FractionRing W.toAffine.CoordinateRing)).Point,
      True := by
  exact ⟨WeierstrassCurve.Affine.GenericPoint.genericPoint W, trivial⟩
```

That verifies the construction infrastructure.  But it will not prove `mk_phi_psi_dup_doubling_cross` without the missing generic n-multiple coordinate formula.
