# Q207: Division-polynomial doubling identity — raw polynomial vs coordinate-ring route

## Short answer

The identity

```text
Φ(2m) · dupDenP(Φ(m), ΨSq(m))
  = ΨSq(2m) · dupNumP(Φ(m), ΨSq(m))                    (*)
```

is mathematically expected to be a **raw polynomial identity in `R[X]` after the Weierstrass `b`-invariants are interpreted as the expressions attached to an actual curve**.

If instead you treat `b₂ b₄ b₆ b₈` as algebraically independent variables, then the identity only holds modulo the universal Weierstrass relation

```text
b₂ b₆ = b₄² + 4 b₈.
```

In Mathlib this relation is

```lean
W.b_relation : 4 * W.b₈ = W.b₂ * W.b₆ - W.b₄ ^ 2
```

so the corresponding zero form is

```lean
W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0.
```

If you fully unfold

```lean
b₂ b₄ b₆ b₈
```

to the `a₁ a₂ a₃ a₄ a₆` definitions and `ring` still leaves a nonzero residual, then the problem is probably **not** just `b_relation`. It usually means one of these is wrong:

* the cross multiplication is reversed;
* the denominator/numerator order in `dupNumP`/`dupDenP` is swapped;
* `dupNumP` or `dupDenP` has a sign/coefficient mismatch;
* the `Φ` parity branch was unfolded incorrectly;
* the `preΨ` indices in the `Φ` formula are off by one;
* a `ℕ`/`ℤ` cast changed `2*m+1`, `m+1`, or `m-1` incorrectly.

For a concrete sanity check, the case `m = 1` reduces to

```text
Φ₂ = dupNumP(X,1),   ΨSq₂ = dupDenP(X,1)
```

and the case `m = 2` reduces to zero modulo exactly

```text
b₂*b₆ - b₄^2 - 4*b₈.
```

So if your fully-unfolded `aᵢ` residual is nonzero, I would first check the `Φ` formula and the parity simplification rather than trying to find a mysterious curve-equation cofactor.

---

## The x-only duplication forms

```lean
import Mathlib

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Homogeneous numerator of the x-coordinate duplication map on the Kummer line. -/
def dupNumP (P Q : R[X]) : R[X] :=
  P ^ 4 - C W.b₄ * P ^ 2 * Q ^ 2 - C (2 * W.b₆) * P * Q ^ 3 - C W.b₈ * Q ^ 4

/-- Homogeneous denominator of the x-coordinate duplication map on the Kummer line. -/
def dupDenP (P Q : R[X]) : R[X] :=
  C 4 * P ^ 3 * Q + C W.b₂ * P ^ 2 * Q ^ 2 + C (2 * W.b₄) * P * Q ^ 3 + C W.b₆ * Q ^ 4

/-- Sanity check: the duplication numerator at `[X:1]` is `Φ₂`. -/
theorem Φ_two_eq_dupNumP_X_one :
    W.Φ 2 = W.dupNumP X 1 := by
  -- Expected proof:
  --   rw [WeierstrassCurve.Φ]
  --   simp [dupNumP, WeierstrassCurve.ΨSq, WeierstrassCurve.preΨ_two,
  --         WeierstrassCurve.preΨ_one, WeierstrassCurve.preΨ_three,
  --         WeierstrassCurve.Ψ₃, WeierstrassCurve.Ψ₂Sq]
  --   ring
  sorry

/-- Sanity check: the duplication denominator at `[X:1]` is `ΨSq₂`. -/
theorem ΨSq_two_eq_dupDenP_X_one :
    W.ΨSq 2 = W.dupDenP X 1 := by
  -- Expected proof:
  --   simp [dupDenP, WeierstrassCurve.ΨSq, WeierstrassCurve.Ψ₂Sq]
  sorry

end WeierstrassCurve
```

---

## Recommended raw-polynomial theorem

This is the theorem I would try to prove first. It should close by expanding the existing division-polynomial recurrences and then using `ring_nf`, **provided the duplication forms and the parity wrappers are correct**.

```lean
namespace WeierstrassCurve

universe u

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R)

/--
Raw x-only doubling identity for the division-polynomial representatives.

This is the Kummer-line identity
`x(2Q) = dup(x(Q))`, specialized to `Q = mP` and expressed using
`[Φ_m : ΨSq_m]`.
-/
theorem Φ_two_mul_dup_cross_raw
    (m : ℤ) :
    W.Φ (2 * m) * W.dupDenP (W.Φ m) (W.ΨSq m) =
      W.ΨSq (2 * m) * W.dupNumP (W.Φ m) (W.ΨSq m) := by
  -- Suggested proof script:
  --
  --   rw [Φ_even_expanded, ΨSq_even_expanded]
  --   rw [preΨ_even]
  --   -- If needed also expand `Φ m`, `ΨSq m` by parity cases on `m`.
  --   by_cases hm : Even m
  --   · simp [hm, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
  --           WeierstrassCurve.preΨ_even, WeierstrassCurve.preΨ_odd,
  --           dupNumP, dupDenP]
  --     ring_nf
  --   · simp [hm, WeierstrassCurve.Φ, WeierstrassCurve.ΨSq,
  --           WeierstrassCurve.preΨ_even, WeierstrassCurve.preΨ_odd,
  --           dupNumP, dupDenP]
  --     ring_nf
  --
  -- If the proof is carried out with `b₂ b₄ b₆ b₈` as independent symbols, the residual is a
  -- multiple of `W.b₂ * W.b₆ - W.b₄^2 - 4*W.b₈`.  Over an actual `WeierstrassCurve`, either
  -- unfold `b₂,b₄,b₆,b₈` to the `aᵢ` or use `W.b_relation`.
  sorry

end WeierstrassCurve
```

### If the residual is only the `b`-relation

If after all EDS recurrences are substituted the residual has the form

```text
C_m * (b₂*b₆ - b₄^2 - 4*b₈)
```

then in Lean do **not** try to hand-maintain a human-readable closed form for `C_m`. It is typically huge and depends on the expanded `preΨ` terms. Use one of these patterns:

```lean
namespace WeierstrassCurve

universe u

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R)

/-- Zero form of `W.b_relation`. -/
lemma b_relation_zero :
    W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by
  linear_combination W.b_relation

/--
Version where the residual has already been computed as a multiple of `b_relation_zero`.
The placeholder `C` is the quotient produced by polynomial reduction.
-/
theorem close_residual_by_b_relation
    (C residual : R[X])
    (hres : residual = C * C (W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈)) :
    residual = 0 := by
  rw [hres]
  simp [W.b_relation_zero]

end WeierstrassCurve
```

In practice, I recommend the stronger approach:

```lean
simp [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
ring_nf
```

because then `b_relation` is definitional and no cofactor is needed. If that still does not close, the candidate identity or one of its expansions is wrong.

---

## Why the identity should be raw after unfolding `bᵢ`

The duplication formula

```text
x(2P) = (x^4 - b₄x² - 2b₆x - b₈) / (4x³ + b₂x² + 2b₄x + b₆)
```

is already an x-only formula. The `y`-dependence has been eliminated using the Weierstrass equation and the definitions of the `b`-invariants. Once the `bᵢ` are actual invariants of a curve, there is no remaining hidden quotient by the curve equation in the univariate `x`-formula.

Another way to see this: if the equality holds in the affine coordinate ring and both sides are in the image of `R[X]`, then it holds as a polynomial in `R[X]`, because the coordinate ring is free of rank two over `R[X]` with basis `{1,Y}` and the map `R[X] → R[W]` is injective in the nonsingular/domain setting. Mathlib's affine coordinate ring file has the relevant basis/injectivity-style lemmas, e.g. `CoordinateRing.basis`, `CoordinateRing.smul_basis_eq_zero`, and `CoordinateRing.exists_smul_basis_eq`.

---

## Coordinate-ring route skeleton

The coordinate-ring route is safer conceptually, but it is usually **heavier** in Lean. It avoids manually manipulating the huge raw polynomial identity, but it requires using the bivariate division-polynomial congruences and the actual group-law/duplication theorem in the affine coordinate ring.

Existing Mathlib congruence lemmas include:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq
WeierstrassCurve.Affine.CoordinateRing.mk_ψ
WeierstrassCurve.Affine.CoordinateRing.mk_φ
```

The intended proof shape is:

```lean
import Mathlib

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {F : Type u} [Field F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

namespace Affine.CoordinateRing

/--
Coordinate-ring Kummer representative of `x(nP)`: `[φ_n : ψ_n^2]` equals `[Φ_n : ΨSq_n]`.
-/
theorem mk_phi_psiSq_eq_Phi_PsiSq
    (n : ℤ) :
    -- Schematic statement.  In the coordinate ring, the bivariate pair
    -- `(φ_n, ψ_n^2)` is equal to the univariate pair `(Φ_n, ΨSq_n)`.
    True := by
  -- Use existing lemmas:
  --   mk_φ : mk W (W.φ n) = mk W (C (W.Φ n))
  --   mk_ψ : mk W (W.ψ n) = mk W (W.Ψ n)
  --   definition/lemma for `ΨSq` congruent to `Ψ^2`
  --   mk_ψ₂_sq for the even ψ₂ factor.
  trivial

/--
Coordinate-ring duplication identity for the bivariate representatives.

This is the conceptual theorem: the x-coordinate of twice a point with x-coordinate represented by
`[φ_m:ψ_m^2]` is represented by `[φ_{2m}:ψ_{2m}^2]`.
-/
theorem mk_dup_phi_psi_cross
    (m : ℤ) :
    -- Schematic cross-multiplied identity in the coordinate ring.
    True := by
  -- Use the actual affine group-law/duplication theorem plus the bivariate division-polynomial
  -- interpretation of `φ_m` and `ψ_m`.
  -- This avoids a massive raw `ring_nf`, but requires stronger EC point/function-field API.
  trivial

end Affine.CoordinateRing

/--
Evaluation version at a curve point.  This is often enough for the ladder correctness theorem.
-/
theorem doubleVec_phiPsi_same_at_point
    {x y : F} (hxy : (W⁄F).Nonsingular x y)
    (m : ℤ) :
    SameP1Vec
      -- repo's x-only double vector applied to `[Φ_m(x):ΨSq_m(x)]`
      -- `(doubleVec W ![(W.Φ m).eval x, (W.ΨSq m).eval x])`
      ![(0 : F), 1]
      -- target `[Φ_{2m}(x):ΨSq_{2m}(x)]`
      ![(W.Φ (2 * m)).eval x, (W.ΨSq (2 * m)).eval x] := by
  -- Schematic only: replace dummy source vector by repo's `doubleVec`.
  -- Proof route:
  -- 1. Use `mk_phi_psiSq_eq_Phi_PsiSq` to replace univariate reps with bivariate reps.
  -- 2. Use `mk_dup_phi_psi_cross` / point-level duplication theorem.
  -- 3. Evaluate at `(x,y)` using `hxy`.
  -- 4. Conclude `SameP1Vec` by the projective equality/cross-product lemma.
  sorry

end WeierstrassCurve
```

### Feasibility comparison

**Raw-ring identity is more feasible** if your goal is the ladder/EDS coordinate identity. It is a pure polynomial theorem, independent of points, torsion, denominators, and separability. The main cost is a large `ring_nf` proof and careful parity/index management.

**Coordinate-ring route is more robust conceptually** but requires more Mathlib infrastructure:

```lean
mk_φ
mk_ψ
mk_Ψ_sq / ψ₂_sq handling
actual duplication theorem in the affine coordinate ring
possibly localization/function-field reasoning if denominators are involved
```

If the raw identity only fails by `b_relation`, fix the raw proof. If it fails even after unfolding `b₂,b₄,b₆,b₈`, debug the formulas before switching routes.

---

## Debug checklist for the residual

1. Test `m = 1`:

```lean
Φ₂ = dupNumP X 1
ΨSq₂ = dupDenP X 1
```

2. Test `m = 2` after reducing by

```lean
W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0.
```

3. Confirm the `Φ` parity formula:

```text
Φ_n = X*ΨSq_n - preΨ_{n+1}*preΨ_{n-1}          if n even
Φ_n = X*ΨSq_n - preΨ_{n+1}*preΨ_{n-1}*Ψ₂Sq    if n odd
```

4. Confirm the `ΨSq` parity formula:

```text
ΨSq_n = preΨ_n^2 * Ψ₂Sq   if n even
ΨSq_n = preΨ_n^2          if n odd
```

5. Confirm the cross product orientation:

```lean
W.Φ (2*m) * dupDenP (W.Φ m) (W.ΨSq m)
  = W.ΨSq (2*m) * dupNumP (W.Φ m) (W.ΨSq m)
```

6. If using `ℕ`, convert to `ℤ` early and prove arithmetic equalities explicitly. Most EDS recurrences in Mathlib's univariate `preΨ` API are indexed by `ℤ`; accidental `Nat` arithmetic around `m - 1` is a common source of false residuals.
