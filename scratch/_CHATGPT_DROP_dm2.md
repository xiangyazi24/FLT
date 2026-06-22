# Q224: differential-addition identity for division-polynomial representatives

## Executive answer

I do **not** think the requested raw differential-addition cross identity is currently provable from public Mathlib by only rewriting `mk_φ`, `mk_ψ`, and `mk_Ψ_sq`.

The precise missing theorem is not `mk_φ`/`mk_ψ`; those are the transport lemmas. The missing theorem is the **bivariate division-polynomial differential-addition identity in the affine coordinate ring**, equivalently the EDS addition law for the bivariate `ψ` sequence plus the corresponding x-coordinate addition identity.

The smallest missing lemma to add is:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_psi_add_sub
```

or, more directly for this goal:

```lean
WeierstrassCurve.Affine.CoordinateRing.mk_diffAdd_phi_psi_adjacent_cross
```

Once that lemma exists, the descent to the raw `R[X]` identity is routine using the rank-two coordinate-ring basis over `R[X]` and injectivity of constants/univariate polynomials into the coordinate ring.

Below is the full scaffold, with the missing lemmas isolated by exact signatures. The only parts marked `sorry` are the genuinely missing Mathlib/repo API lemmas and routine expansion lemmas whose proof is a finite `rw`/`ring` once the missing coordinate-ring identity exists.

---

## Lean scaffold

```lean
import Mathlib

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R)

/-!
## Homogeneous x-only differential-addition forms

All of these are univariate homogeneous forms in the two Kummer representatives
`A = [XA : ZA]`, `B = [XB : ZB]`, and the known difference `D = [XD : ZD]`.
-/

/-- `XA*ZB - XB*ZA`. -/
def diffAddDeltaP (XA ZA XB ZB : R[X]) : R[X] :=
  XA * ZB - XB * ZA

/--
The symmetric numerator appearing in the x-only differential-addition formula.
-/
def diffAddSumNumP (XA ZA XB ZB : R[X]) : R[X] :=
  C 2 * XA * XB * (XA * ZB + XB * ZA)
    + C W.b₂ * XA * XB * ZA * ZB
    + C W.b₄ * ZA * ZB * (XA * ZB + XB * ZA)
    + C W.b₆ * ZA ^ 2 * ZB ^ 2

/-- Numerator of differential addition, with difference representative `[XD:ZD]`. -/
def diffAddNumP (XA ZA XB ZB XD ZD : R[X]) : R[X] :=
  W.diffAddSumNumP XA ZA XB ZB * ZD
    - (W.diffAddDeltaP XA ZA XB ZB) ^ 2 * XD

/-- Denominator of differential addition, with difference representative `[XD:ZD]`. -/
def diffAddDenP (XA ZA XB ZB XD ZD : R[X]) : R[X] :=
  (W.diffAddDeltaP XA ZA XB ZB) ^ 2 * ZD

/-- Raw target numerator for adjacent differential addition. -/
def diffAddAdjacentNum (m : ℤ) : R[X] :=
  W.diffAddNumP
    (W.Φ m) (W.ΨSq m)
    (W.Φ (m + 1)) (W.ΨSq (m + 1))
    X 1

/-- Raw target denominator for adjacent differential addition. -/
def diffAddAdjacentDen (m : ℤ) : R[X] :=
  W.diffAddDenP
    (W.Φ m) (W.ΨSq m)
    (W.Φ (m + 1)) (W.ΨSq (m + 1))
    X 1

/-- The raw univariate cross-polynomial whose vanishing is desired. -/
def diffAddAdjacentCrossResidual (m : ℤ) : R[X] :=
  W.diffAddAdjacentNum m * W.ΨSq (2 * m + 1)
    - W.Φ (2 * m + 1) * W.diffAddAdjacentDen m

/-!
## Coordinate-ring bivariate forms

These are the same forms but in `R[X][Y]`.  They allow us to state the coordinate-ring theorem in
terms of bivariate `φ` and `ψ` before transporting to `Φ` and `ΨSq`.
-/

/-- Bivariate version of `diffAddDeltaP`. -/
def diffAddDeltaBiv (XA ZA XB ZB : R[X][Y]) : R[X][Y] :=
  XA * ZB - XB * ZA

/-- Bivariate version of `diffAddSumNumP`. -/
def diffAddSumNumBiv (XA ZA XB ZB : R[X][Y]) : R[X][Y] :=
  C (C (2 : R)) * XA * XB * (XA * ZB + XB * ZA)
    + C (C W.b₂) * XA * XB * ZA * ZB
    + C (C W.b₄) * ZA * ZB * (XA * ZB + XB * ZA)
    + C (C W.b₆) * ZA ^ 2 * ZB ^ 2

/-- Bivariate differential-addition numerator. -/
def diffAddNumBiv (XA ZA XB ZB XD ZD : R[X][Y]) : R[X][Y] :=
  W.diffAddSumNumBiv XA ZA XB ZB * ZD
    - (W.diffAddDeltaBiv XA ZA XB ZB) ^ 2 * XD

/-- Bivariate differential-addition denominator. -/
def diffAddDenBiv (XA ZA XB ZB XD ZD : R[X][Y]) : R[X][Y] :=
  (W.diffAddDeltaBiv XA ZA XB ZB) ^ 2 * ZD

/-- Bivariate adjacent numerator built from `[φ_m : ψ_m²]`, `[φ_{m+1} : ψ_{m+1}²]`, `[X:1]`. -/
def diffAddAdjacentNumBiv (m : ℤ) : R[X][Y] :=
  W.diffAddNumBiv
    (W.φ m) (W.ψ m ^ 2)
    (W.φ (m + 1)) (W.ψ (m + 1) ^ 2)
    (C X) 1

/-- Bivariate adjacent denominator built from `[φ_m : ψ_m²]`, `[φ_{m+1} : ψ_{m+1}²]`, `[X:1]`. -/
def diffAddAdjacentDenBiv (m : ℤ) : R[X][Y] :=
  W.diffAddDenBiv
    (W.φ m) (W.ψ m ^ 2)
    (W.φ (m + 1)) (W.ψ (m + 1) ^ 2)
    (C X) 1

/-!
## Missing coordinate-ring theorem

This is the genuinely missing theorem.  It is the x-coordinate adjacent differential-addition
identity expressed with bivariate division polynomials.

Mathematically it follows from:

* the EDS addition recurrence
  `ψ_{a+b} ψ_{a-b} = ψ_{a+1} ψ_{a-1} ψ_b^2 - ψ_{b+1} ψ_{b-1} ψ_a^2`,
* the definition `φ_n = X ψ_n^2 - ψ_{n+1} ψ_{n-1}`,
* the Weierstrass curve relation, equivalently `ψ₂_sq`, inside the coordinate ring.

For the adjacent case `a=m+1`, `b=m`, `a-b=1`, so the denominator identity is essentially

```text
φ_m ψ_{m+1}² - φ_{m+1} ψ_m² = ψ_{2m+1}
```

in the coordinate ring, with sign determined by the convention for `ψ_{-1}`.
-/
namespace Affine.CoordinateRing

/--
MISSING-MATHLIB-API.

Bivariate adjacent differential-addition cross identity in the affine coordinate ring.
This is the smallest theorem that makes the raw univariate identity routine.
-/
theorem mk_diffAddAdjacent_phi_psi_cross
    (m : ℤ) :
    mk W
      (W.diffAddAdjacentNumBiv m * W.ψ (2 * m + 1) ^ 2
        - W.φ (2 * m + 1) * W.diffAddAdjacentDenBiv m) = 0 := by
  -- Missing proof outline:
  -- 1. Prove denominator identity in the coordinate ring:
  --      mk W (W.diffAddDeltaBiv (W.φ m) (W.ψ m^2)
  --        (W.φ (m+1)) (W.ψ (m+1)^2)) = mk W (W.ψ (2*m+1)).
  --    This is the EDS addition recurrence with `(a,b)=(m+1,m)` plus `φ` definition.
  --
  -- 2. Prove numerator identity in the coordinate ring:
  --      mk W (W.diffAddSumNumBiv ...)
  --        = mk W (C X * W.ψ (2*m+1)^2 + W.φ (2*m+1)).
  --    Equivalently, after subtracting `X*delta^2`, the numerator is `φ_{2m+1}`.
  --
  -- 3. Use `ψ₂_sq` / `mk_ψ₂_sq` to eliminate every `Y^2` term by the curve relation.
  --
  -- 4. Finish by `ring_nf` in the coordinate ring.
  --
  -- This theorem is not currently exposed by Mathlib's division-polynomial API.
  sorry

end Affine.CoordinateRing

/-!
## Transport from bivariate `φ,ψ` to univariate `Φ,ΨSq`

These lemmas are routine once the exact Mathlib names are available:

* `Affine.CoordinateRing.mk_φ`
* `Affine.CoordinateRing.mk_ψ`
* `Affine.CoordinateRing.mk_Ψ_sq`
* `Affine.CoordinateRing.mk_ψ₂_sq`

The names may need namespace adjustment depending on imports.
-/

namespace Affine.CoordinateRing

/--
Transport the adjacent differential-addition numerator from bivariate `φ,ψ` to univariate `Φ,ΨSq`.
-/
theorem mk_diffAddAdjacentNumBiv_eq_mk_C_diffAddAdjacentNum
    (m : ℤ) :
    mk W (W.diffAddAdjacentNumBiv m) = mk W (C (W.diffAddAdjacentNum m)) := by
  -- Expected proof:
  --   simp [WeierstrassCurve.diffAddAdjacentNumBiv,
  --         WeierstrassCurve.diffAddAdjacentNum,
  --         WeierstrassCurve.diffAddNumBiv,
  --         WeierstrassCurve.diffAddNumP,
  --         WeierstrassCurve.diffAddSumNumBiv,
  --         WeierstrassCurve.diffAddSumNumP,
  --         WeierstrassCurve.diffAddDeltaBiv,
  --         WeierstrassCurve.diffAddDeltaP,
  --         mk_φ, mk_ψ, mk_Ψ_sq]
  --
  -- Main issue: exact namespace/name of `mk_Ψ_sq` in current Mathlib.
  sorry

/--
Transport the adjacent differential-addition denominator from bivariate `φ,ψ` to univariate `Φ,ΨSq`.
-/
theorem mk_diffAddAdjacentDenBiv_eq_mk_C_diffAddAdjacentDen
    (m : ℤ) :
    mk W (W.diffAddAdjacentDenBiv m) = mk W (C (W.diffAddAdjacentDen m)) := by
  -- Same proof pattern as numerator transport.
  sorry

/-- Transport `ψ_{2m+1}²` to `ΨSq_{2m+1}`. -/
theorem mk_psi_sq_adjacent_eq_mk_C_ΨSq
    (m : ℤ) :
    mk W (W.ψ (2 * m + 1) ^ 2) = mk W (C (W.ΨSq (2 * m + 1))) := by
  -- Expected one-liner from `mk_ψ` and `mk_Ψ_sq`.
  -- If `mk_Ψ_sq` is not present, prove from `mk_ψ` plus the parity definition of `Ψ`/`ΨSq`.
  sorry

end Affine.CoordinateRing

/-!
## Coordinate-ring vanishing of the raw univariate residual
-/

/--
Coordinate-ring vanishing of the raw adjacent differential-addition residual.
-/
theorem mk_C_diffAddAdjacentCrossResidual_eq_zero
    (m : ℤ) :
    Affine.CoordinateRing.mk W (C (W.diffAddAdjacentCrossResidual m)) = 0 := by
  -- Proof after the missing theorem and transport lemmas:
  --
  -- 1. Start from `Affine.CoordinateRing.mk_diffAddAdjacent_phi_psi_cross W m`.
  -- 2. Rewrite `mk` of bivariate numerator/denominator via
  --    `mk_diffAddAdjacentNumBiv_eq_mk_C_diffAddAdjacentNum` and denominator version.
  -- 3. Rewrite `mk ψ²` by `mk_psi_sq_adjacent_eq_mk_C_ΨSq`.
  -- 4. Rewrite `mk φ` by `mk_φ`.
  -- 5. Use ring hom properties to collect as `mk W (C residual) = 0`.
  have h := Affine.CoordinateRing.mk_diffAddAdjacent_phi_psi_cross (W := W) m
  -- The following is the expected final proof shape, modulo exact names of `mk_φ` and `mk_Ψ_sq`:
  --   simpa [diffAddAdjacentCrossResidual, map_sub, map_mul,
  --          Affine.CoordinateRing.mk_diffAddAdjacentNumBiv_eq_mk_C_diffAddAdjacentNum,
  --          Affine.CoordinateRing.mk_diffAddAdjacentDenBiv_eq_mk_C_diffAddAdjacentDen,
  --          Affine.CoordinateRing.mk_psi_sq_adjacent_eq_mk_C_ΨSq,
  --          Affine.CoordinateRing.mk_φ] using h
  sorry

/-!
## Descent from coordinate ring to `R[X]`

For fields this is easiest: the coordinate ring is a domain/free rank two over `R[X]`, and the
constant/univariate inclusion is injective. For a general `CommRing R`, this injectivity may require
nontriviality/domain hypotheses. Since the target elliptic-curve applications are over a field, state
the final raw theorem over a field.
-/

namespace Affine.CoordinateRing

/--
MISSING/TO-CONFIRM API.

Injectivity of the univariate polynomial inclusion `R[X] -> R[W]`, expressed as `mk W (C f)`.
For fields/nontrivial rings this follows from the free `R[X]`-basis `{1,Y}` of the coordinate ring.
-/
theorem mk_C_injective
    {F : Type u} [Field F]
    (W : WeierstrassCurve F)
    {f g : F[X]} :
    mk W (C f) = mk W (C g) → f = g := by
  -- Small proof sketch:
  -- 1. `mk W (C f) = mk W (C g)` implies `(f-g) • 1 + 0 • Y = 0` in the coordinate ring.
  -- 2. Apply `CoordinateRing.smul_basis_eq_zero`.
  -- 3. Extract `f-g=0`.
  -- Existing relevant API:
  --   CoordinateRing.basis
  --   CoordinateRing.smul_basis_eq_zero
  --   CoordinateRing.smul
  sorry

end Affine.CoordinateRing

/--
Raw univariate adjacent differential-addition cross identity.

This is the desired final theorem, over a field where `mk W (C ·)` is injective.
-/
theorem diffAddAdjacentCrossResidual_eq_zero
    {F : Type u} [Field F]
    (W : WeierstrassCurve F)
    (m : ℤ) :
    W.diffAddAdjacentCrossResidual m = 0 := by
  apply Affine.CoordinateRing.mk_C_injective W
  simpa using W.mk_C_diffAddAdjacentCrossResidual_eq_zero m

/-- Final cross-multiplied raw identity in the requested orientation. -/
theorem diffAddAdjacent_cross_identity
    {F : Type u} [Field F]
    (W : WeierstrassCurve F)
    (m : ℤ) :
    W.diffAddAdjacentNum m * W.ΨSq (2 * m + 1)
      = W.Φ (2 * m + 1) * W.diffAddAdjacentDen m := by
  have h := W.diffAddAdjacentCrossResidual_eq_zero m
  simpa [diffAddAdjacentCrossResidual, sub_eq_zero] using h

end WeierstrassCurve
```

---

## The smallest missing proof: bivariate EDS addition

If you want to split the missing coordinate-ring identity into smaller lemmas, add these first.

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

universe u

variable {R : Type u} [CommRing R]
variable (W : WeierstrassCurve R)

namespace Affine.CoordinateRing

/--
MISSING-MATHLIB-API.

The EDS addition recurrence for bivariate division polynomials in the affine coordinate ring.
This is the direct analogue of `IsEllSequence` for the sequence `n ↦ mk W (W.ψ n)`.
-/
theorem mk_ψ_add_sub
    (a b : ℤ) :
    mk W (W.ψ (a + b) * W.ψ (a - b)) =
      mk W
        (W.ψ (a + 1) * W.ψ (a - 1) * W.ψ b ^ 2
          - W.ψ (b + 1) * W.ψ (b - 1) * W.ψ a ^ 2) := by
  -- This is not currently exposed by Mathlib.
  -- Smallest proof route:
  -- * prove the sequence `fun n => mk W (W.ψ n)` satisfies `IsEllSequence`;
  -- * specialize the EDS identity with `r = 1` and `ψ_1 = 1`;
  -- * use `ring` for the coordinate-ring rearrangement.
  sorry

/-- Adjacent denominator identity. -/
theorem mk_adjacent_delta_eq_ψ
    (m : ℤ) :
    mk W
      (W.diffAddDeltaBiv
        (W.φ m) (W.ψ m ^ 2)
        (W.φ (m + 1)) (W.ψ (m + 1) ^ 2)) =
      mk W (W.ψ (2 * m + 1)) := by
  -- Expand `φ_n = X ψ_n² - ψ_{n+1} ψ_{n-1}`.
  -- Use `mk_ψ_add_sub` with `(a,b)=(m+1,m)` and sign convention for `ψ (-1)`.
  sorry

/-- Adjacent sum-numerator identity. -/
theorem mk_adjacent_sumNum_eq_phi_add_Xψsq
    (m : ℤ) :
    mk W
      (W.diffAddSumNumBiv
        (W.φ m) (W.ψ m ^ 2)
        (W.φ (m + 1)) (W.ψ (m + 1) ^ 2)) =
      mk W (W.φ (2 * m + 1) + C X * W.ψ (2 * m + 1) ^ 2) := by
  -- This is the heavier companion.  It is the actual x-only differential-addition formula in
  -- bivariate division-polynomial representatives.
  -- Proof route:
  -- * expand `diffAddSumNumBiv`, `φ`;
  -- * use `mk_adjacent_delta_eq_ψ` and `mk_ψ_add_sub` for the required EDS identities;
  -- * use `ψ₂_sq` / curve relation for all `Y²` reductions;
  -- * finish by `ring` in the coordinate ring.
  sorry

end Affine.CoordinateRing

end WeierstrassCurve
```

Once these three lemmas exist, `mk_diffAddAdjacent_phi_psi_cross` is just algebra:

```text
diffNum = sumNum - delta² * X
        = (φ_{2m+1} + X ψ_{2m+1}²) - X ψ_{2m+1}²
        = φ_{2m+1}

diffDen = delta² = ψ_{2m+1}².
```

---

## Nonzero/no-common-root conjunct

The nonzero target vector

```lean
![(W.Φ (2*m+1)).eval x, (W.ΨSq (2*m+1)).eval x]
```

under `[W.IsElliptic]` does **not** fall out from the coordinate-ring cross identity alone. It needs a separate no-simultaneous-vanishing theorem:

```lean
theorem Φ_ΨSq_no_common_eval_root
    {F : Type u} [Field F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    (n : ℤ) (x : F) :
    ¬ ((W.Φ n).eval x = 0 ∧ (W.ΨSq n).eval x = 0)
```

For the division-polynomial application, this is usually proved from the point-coordinate theorem:
`[Φ_n:ΨSq_n]` is the x-coordinate representative of `[n]P`; the vector cannot be `[0:0]`. Purely polynomial proofs are possible but require resultant/no-common-factor facts. Therefore I recommend keeping this as a separate lemma; do not expect it from the cross identity.

---

## Feasibility verdict

### More feasible now

Use the raw polynomial identity if your `ring_nf` can close after:

```lean
simp [b₂, b₄, b₆, b₈]
ring_nf
```

or after one `linear_combination` with `W.b_relation`. That is fastest if the formulas are correct.

### More robust but missing one theorem

Use the coordinate-ring route, but first add:

```lean
Affine.CoordinateRing.mk_diffAddAdjacent_phi_psi_cross
```

or its smaller components:

```lean
Affine.CoordinateRing.mk_ψ_add_sub
Affine.CoordinateRing.mk_adjacent_delta_eq_ψ
Affine.CoordinateRing.mk_adjacent_sumNum_eq_phi_add_Xψsq
```

This is the conceptually correct theorem, but it is not currently exposed by Mathlib.

## Connected proof strategy after adding missing lemma

1. Prove `mk_ψ_add_sub` for bivariate division polynomials in the coordinate ring.
2. Derive `mk_adjacent_delta_eq_ψ`.
3. Derive `mk_adjacent_sumNum_eq_phi_add_Xψsq`.
4. Prove `mk_diffAddAdjacent_phi_psi_cross`.
5. Transport through `mk_φ`, `mk_ψ`, `mk_Ψ_sq` to univariate `Φ`, `ΨSq`.
6. Descend by `mk_C_injective`.
7. Use the resulting raw cross identity in the Kummer ladder proof.
