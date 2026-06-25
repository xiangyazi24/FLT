# Q291 (dm3): General-`m` `addX` identity — direct algebraic proof skeleton

## Bottom line

The direct algebraic route is the right one, but there is one important correction
to the proposed proof plan:

```lean
hω := W.two_mul_ψ_mul_ωProto m
heven := W.ψ_even m
```

are **not by themselves** the right local hypotheses for the final `ring` proof of
`addX`.  They are enough only after you package the actual slope-numerator bridge.
The clean final proof should use the following intermediate lemma:

```lean
omegaSlope_mul_ψ₂
```

This lemma is the exact symbolic identity that the `addX` proof needs.  Once it is
available, the `addX` coordinate-ring proof is short, uniform in `m`, and closes
by `ring1`/`ring_nf`.  The cofactor of the curve equation is

```lean
-4 * W.ψ m ^ 4
```

for the doubled identity

```lean
2 * (addX(P,R_m) - ψ_{m-1}^2 * φ_{m+1}).
```

Equivalently, the algebraic normal form is

```text
2·(addX(P,R_m) - ψ_{m-1}² φ_{m+1})
  = -4·ψ_m^4·F_W
    - ψ_m · ( omegaSlope_m·ψ₂
        - (2·ψ_{m-1}²·ψ_{m+2}
             - ψ_m·ψ_{m-1}·ψ_{m+1}·(6X² + b₂X + b₄)) ).
```

Thus after applying `omegaSlope_mul_ψ₂`, the remaining cofactor is exactly
`-4·ψ_m^4`.

If your theorem `W.two_mul_ψ_mul_ωProto m` already states this slope-numerator
identity under another name, use it directly as `hSlope`.  If it instead states
only the normalization

```text
ψ_{2m} = 2ψ_mω_m + a₁φ_mψ_m² + a₃ψ_m⁴,
```

then it must be combined with the even recurrence and the companion symmetric Ward
identity to prove `omegaSlope_mul_ψ₂` first.  Without that bridge, `ring` leaves a
real residual term; this is not a tactic issue.

---

## Imports

Use the files that expose the coordinate ring, division polynomials, and Jacobian
`addX` formula.  In the project file, replace the scratch imports by the actual
local filenames containing `ωProto`.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

-- Project-local imports, adjust names to your tree:
-- import FLT.Scratch.KeystoneOmega
-- import FLT.Scratch.KeystoneProjectiveZ
```

---

## Complete Lean skeleton

This is written so the final `addX` theorem is uniform in `m`.  The only theorem
that must already exist, or be proved just above it, is `omegaSlope_mul_ψ₂`.

```lean
namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]

namespace ProjectiveFormula

/-- Bivariate polynomial ring `k[X][Y]`. -/
abbrev Bivar (k : Type*) [CommSemiring k] := Polynomial (Polynomial k)

local notation "kXY" => Bivar k

/-- The embedded affine `X` variable in `k[X][Y]`. -/
noncomputable abbrev XX : kXY :=
  Polynomial.C Polynomial.X

/-- The affine `Y` variable in `k[X][Y]`. -/
noncomputable abbrev YY : kXY :=
  Polynomial.X

/-- A scalar coefficient as a bivariate constant. -/
noncomputable abbrev CC (a : k) : kXY :=
  Polynomial.C (Polynomial.C a)

/-- The half-derivative of `Ψ₂Sq`: `6X² + b₂X + b₄`. -/
noncomputable def halfDblXPoly (W : WeierstrassCurve k) : Polynomial k :=
  6 * Polynomial.X ^ 2 + Polynomial.C W.b₂ * Polynomial.X + Polynomial.C W.b₄

/-- The same polynomial embedded in `k[X][Y]`. -/
noncomputable def halfDblXPolyBivar (W : WeierstrassCurve k) : kXY :=
  Polynomial.C (halfDblXPoly W)

/-- The point `P = [X,Y,1]` as a Jacobian representative over `k[X][Y]`. -/
noncomputable def PJac : Fin 3 → kXY :=
  ![XX, YY, 1]

/-- The projective division-polynomial representative `R_m = [φ_m,ω_m,ψ_m]`. -/
noncomputable def RJac (W : WeierstrassCurve k) (m : ℤ) : Fin 3 → kXY :=
  ![W.φ m, W.ωProto m, W.ψ m]

/--
`addX(P,R_m)` as a bivariate polynomial.

This uses the Jacobian formula over the base-changed curve.  The abbreviation is
only to keep the final theorem readable.
-/
noncomputable def addX_PR (W : WeierstrassCurve k) (m : ℤ) : kXY :=
  (W⁄kXY).toJacobian.addX (PJac (k := k)) (RJac W m)

/-- The affine equation polynomial `F_W(X,Y)`. -/
noncomputable def FW (W : WeierstrassCurve k) : kXY :=
  W.toAffine.polynomial

/--
The slope numerator that the `addX` identity actually needs.

It is

```text
N_m = 2(ω_m - Y ψ_m^3) - a₁ ψ_m ψ_{m-1} ψ_{m+1}.
```

The sign convention matches Mathlib's Jacobian `addX` formula for
`addX(P,R_m)`.
-/
noncomputable def omegaSlope (W : WeierstrassCurve k) (m : ℤ) : kXY :=
  2 * (W.ωProto m - YY * W.ψ m ^ 3)
    - CC W.a₁ * W.ψ m * W.ψ (m - 1) * W.ψ (m + 1)

/--
The exact symbolic bridge needed for the `addX` proof.

This is the lemma that should be proved from your `ω` normalization plus the Ward
recurrences.  Once it is available, the final `addX` coordinate-ring identity is
immediate by `ring`.

If your local theorem `two_mul_ψ_mul_ωProto` already has this statement, make this
lemma a wrapper around it.
-/
theorem omegaSlope_mul_ψ₂
    (W : WeierstrassCurve k) (m : ℤ) :
    omegaSlope W m * W.ψ₂
      = 2 * W.ψ (m - 1) ^ 2 * W.ψ (m + 2)
          - W.ψ m * W.ψ (m - 1) * W.ψ (m + 1) * halfDblXPolyBivar W := by
  /-
  Recommended local proof shape:

  1. `have hω := W.two_mul_ψ_mul_ωProto m`
  2. `have heven := W.ψ_even m`
  3. combine them with the companion symmetric Ward identity

       ψ_{m-1}²ψ_{m+2} + ψ_{m-2}ψ_{m+1}² + ψ_m³Ψ₂Sq
         = ψ_mψ_{m-1}ψ_{m+1}(6X²+b₂X+b₄)

     or with whatever local lemma already encodes this identity.

  `hω` and `heven` alone generally leave the symmetric residual term above.
  -/
  sorry

/--
Expanded polynomial identity behind the coordinate-ring `addX` proof.

This lemma is intentionally pure polynomial algebra.  It is the place where the
cofactor is visible:

```text
-4 * ψ_m^4
```

After rewriting by `omegaSlope_mul_ψ₂`, the proof is only `ring1`.
-/
theorem two_mul_addX_PR_sub_sq_φ_succ_eq
    (W : WeierstrassCurve k) (m : ℤ) :
    2 * (addX_PR W m - W.ψ (m - 1) ^ 2 * W.φ (m + 1))
      = (-4 * W.ψ m ^ 4) * FW W := by
  have hSlope := omegaSlope_mul_ψ₂ (W := W) (m := m)

  /-
  If `simp` does not unfold `W⁄kXY` far enough, add the same base-change simp
  lemmas used elsewhere in the project:

    WeierstrassCurve.map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    WeierstrassCurve.map_b₂, map_b₄,
    Algebra.algebraMap_self_apply

  The important simplification list is:

    addX_PR, PJac, RJac, Jacobian.addX,
    omegaSlope, halfDblXPolyBivar, halfDblXPoly,
    FW, Affine.polynomial,
    WeierstrassCurve.φ, WeierstrassCurve.ψ₂,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄
  -/
  linear_combination (norm :=
    (simp [addX_PR, PJac, RJac, Jacobian.addX,
      omegaSlope, halfDblXPolyBivar, halfDblXPoly,
      FW, Affine.polynomial,
      WeierstrassCurve.φ, WeierstrassCurve.ψ₂,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      CC, XX, YY]; ring1))
    - W.ψ m * hSlope

/--
The desired coordinate-ring statement for the X-coordinate, with the harmless
factor `2` included.
-/
theorem mk_two_mul_addX_PR_sub_sq_φ_succ
    (W : WeierstrassCurve k) (m : ℤ) :
    WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
      (2 * (addX_PR W m - W.ψ (m - 1) ^ 2 * W.φ (m + 1))) = 0 := by
  rw [AdjoinRoot.mk_eq_zero]
  refine ⟨-4 * W.ψ m ^ 4, ?_⟩
  exact two_mul_addX_PR_sub_sq_φ_succ_eq (W := W) (m := m)

end ProjectiveFormula
end WeierstrassCurve
```

---

## If `addX_PR` does not simplify because of base change

If Lean does not reduce

```lean
(W⁄kXY).toJacobian.addX (PJac (k := k)) (RJac W m)
```

to the raw polynomial formula, define the raw formula directly and prove a bridge
lemma once.

```lean
namespace WeierstrassCurve
namespace ProjectiveFormula

open Polynomial

variable {k : Type*} [Field k]

/-- Raw expanded `addX(P,R_m)` formula, avoiding base-change reducibility issues. -/
noncomputable def addX_PR_raw (W : WeierstrassCurve k) (m : ℤ) : kXY :=
  XX * (W.φ m) ^ 2
    - 2 * YY * W.ωProto m * W.ψ m
    + XX ^ 2 * W.φ m * W.ψ m ^ 2
    - CC W.a₁ * XX * W.ωProto m * W.ψ m
    - CC W.a₁ * YY * W.φ m * W.ψ m ^ 2
    + 2 * CC W.a₂ * XX * W.φ m * W.ψ m ^ 2
    - CC W.a₃ * W.ωProto m * W.ψ m
    - CC W.a₃ * YY * W.ψ m ^ 4
    + CC W.a₄ * W.φ m * W.ψ m ^ 2
    + CC W.a₄ * XX * W.ψ m ^ 4
    + 2 * CC W.a₆ * W.ψ m ^ 4

/-- Bridge from the raw formula to Mathlib's `Jacobian.addX`. -/
theorem addX_PR_eq_raw (W : WeierstrassCurve k) (m : ℤ) :
    addX_PR W m = addX_PR_raw W m := by
  simp [addX_PR, addX_PR_raw, PJac, RJac, Jacobian.addX,
    CC, XX, YY]
  ring1

/-- Raw version of the polynomial identity. -/
theorem two_mul_addX_PR_raw_sub_sq_φ_succ_eq
    (W : WeierstrassCurve k) (m : ℤ) :
    2 * (addX_PR_raw W m - W.ψ (m - 1) ^ 2 * W.φ (m + 1))
      = (-4 * W.ψ m ^ 4) * FW W := by
  have hSlope := omegaSlope_mul_ψ₂ (W := W) (m := m)
  linear_combination (norm :=
    (simp [addX_PR_raw, omegaSlope, halfDblXPolyBivar, halfDblXPoly,
      FW, Affine.polynomial,
      WeierstrassCurve.φ, WeierstrassCurve.ψ₂,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      CC, XX, YY]; ring1))
    - W.ψ m * hSlope

end ProjectiveFormula
end WeierstrassCurve
```

Then the non-raw theorem is just:

```lean
  rw [addX_PR_eq_raw]
  exact two_mul_addX_PR_raw_sub_sq_φ_succ_eq (W := W) (m := m)
```

This raw version is often more robust in scratch files, because it avoids any
unfolding fragility around `W⁄kXY`.

---

## Why `hω` + `heven` alone do not close

Let

```text
q = ψ_m,     r = ψ_{m-1},     s = ψ_{m+1},     t = ψ_{m+2},
φ = Xq² - sr,      w = ω_m,
ψ₂ = 2Y + a₁X + a₃,
M = 6X² + b₂X + b₄.
```

The raw Jacobian `addX(P,R_m)` formula satisfies the formal identity

```text
2(addX(P,R_m) - r²(Xs² - tq))
  = -4q⁴F_W
    - q · ((2(w - Yq³) - a₁qrs)ψ₂ - (2r²t - qrsM)).
```

This is the exact algebraic identity that `ring1` proves.

Therefore the final proof needs precisely

```text
(2(w - Yq³) - a₁qrs)ψ₂ = 2r²t - qrsM.
```

That is `omegaSlope_mul_ψ₂`.

The normalization identity

```text
ψ_{2m} = 2q w + a₁φq² + a₃q⁴
```

and the even recurrence

```text
ψ_{2m}ψ₂ = q(r²t - u s²)
```

still leave the symmetric residual

```text
r²t + u s² + q³Ψ₂Sq - qrs(6X²+b₂X+b₄),
```

unless you also supply the companion symmetric Ward identity.  So if Lean leaves a
nonzero residual after `linear_combination hω ... + heven ...`, the missing lemma
is not a simplifier; it is this symmetric/slope identity.

---

## Recommended implementation order

1. Add `halfDblXPoly`, `omegaSlope`.
2. Prove `omegaSlope_mul_ψ₂` as a wrapper around your local `ω` normalization plus
   the symmetric Ward identity.  If your current `two_mul_ψ_mul_ωProto` already
   states it, just `simpa [omegaSlope, halfDblXPolyBivar, halfDblXPoly] using ...`.
3. Add `addX_PR_raw` and prove `two_mul_addX_PR_raw_sub_sq_φ_succ_eq` by the
   one-line `linear_combination` above.
4. Add the coordinate-ring `mk` theorem via `AdjoinRoot.mk_eq_zero` with cofactor
   `-4 * W.ψ m ^ 4`.
5. Only afterwards bridge `addX_PR_raw` to `(W⁄kXY).toJacobian.addX` if needed.

This gives an all-`m` proof and avoids per-`m` CAS certificates.  The only new
mathematical ingredient is the slope-numerator identity `omegaSlope_mul_ψ₂`.
