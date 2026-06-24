# Q183 (dm1): final audit — `ωₙ` and projective division-polynomial identities

## Executive answer

The plan is viable, but the induction should be phrased as **polynomial representative identities**, not as point equalities at every specialization.  The raw Jacobian formulas can return the zero representative in degenerate cases, so statements like

```text
addXYZ([φ_m:ω_m:ψ_m], [x:y:1]) ≈ [φ_{m+1}:ω_{m+1}:ψ_{m+1}]
```

are only honest as projective equivalences when the scalar is a unit/nonzero.  The universal induction identity you want is instead:

```text
addXYZ([x:y:1], [φ_m:ω_m:ψ_m]) = ψ_{m-1} • [φ_{m+1}:ω_{m+1}:ψ_{m+1}]
```

as a coordinate-ring/polynomial identity, where `u • [X:Y:Z] = [u²X:u³Y:uZ]` is weighted Jacobian scaling.  The scalar `ψ_{m-1}` may vanish at some special points; that is fine for a polynomial identity, but not fine if used as a point equivalence.

For doubling, the clean identity is even better:

```text
dblXYZ([φ_m:ω_m:ψ_m]) = [φ_{2m}:ω_{2m}:ψ_{2m}]
```

again as a coordinate-ring/polynomial identity.  The `Z`-coordinate of this doubling identity is exactly the normalization identity for `ω_m`:

```text
ψ_{2m} = ψ_m * (2ω_m + a₁ φ_m ψ_m + a₃ ψ_m³).
```

This is a very good sanity check: if your `ω` definition does not make `dblZ` reduce to `ψ_{2m}`, the normalization is wrong.

The biggest hidden trap is therefore: **do not prove the projective formula by naive point-level induction using `addXYZ` as if it always returned a nonzero representative.**  Prove coordinate identities in the coordinate ring, then use them only in contexts where the relevant representative is known nonzero/unit.

---

## Notation for the exact identities

Work in the bivariate polynomial ring `K[X][Y]`; in Lean the affine `x` coordinate is `C X` and the affine `y` coordinate is `Y`.

Let

```text
R_m := ![φ_m, ω_m, ψ_m]
P   := ![X,   Y,   1]
```

where in Lean this means

```lean
![W.φ m, W.ω m, W.ψ m]        -- bivariate polynomials
![C X,   Y,   1]
```

and let `F_W(X,Y)=0` be the affine Weierstrass equation.  All `X`/`Y` identities below should be read modulo `F_W`; equivalently after applying `Affine.CoordinateRing.mk W`.  The `Z` identities are usually exact, but stating them in the coordinate ring is harmless and keeps the interface uniform.

---

## (1) Addition identity `[1]P + [m]P = [m+1]P`

Use the orientation

```text
addXYZ(P, R_m), not addXYZ(R_m, P).
```

This avoids the global minus sign.  Since Mathlib’s `Jacobian.addZ` is

```text
addZ(P,Q) = P_X * Q_Z² - Q_X * P_Z²,
```

we get

```text
addZ(P, R_m)
  = X * ψ_m² - φ_m
  = ψ_{m+1} ψ_{m-1}
```

by the definition of `φ_m`.

Therefore the exact weighted representative identity is:

```text
addXYZ(P, R_m) = ψ_{m-1} • R_{m+1}.
```

Componentwise:

```text
addZ(P, R_m) = ψ_{m-1} ψ_{m+1}

addX(P, R_m) ≡ ψ_{m-1}² φ_{m+1}       mod F_W

addY(P, R_m) ≡ ψ_{m-1}³ ω_{m+1}       mod F_W
```

This is the identity to CAS-check and then port to Lean.

### Lean target shape

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Projective division-polynomial representative. -/
noncomputable def divPolyRep (m : ℤ) : Fin 3 → K[X][Y] :=
  ![W.φ m, W.ω m, W.ψ m]

/-- Affine generic point as a Jacobian representative. -/
def genericAffineRep : Fin 3 → K[X][Y] :=
  ![C X, Y, 1]

/-- Addition step: `[1]P + [m]P = [m+1]P`, as a representative identity. -/
theorem addXYZ_generic_divPolyRep
    (m : ℤ) :
    W.toJacobian.addXYZ (genericAffineRep (K := K)) (W.divPolyRep m)
      = W.ψ (m - 1) • W.divPolyRep (m + 1) := by
  -- Best proved componentwise.
  -- Z component is immediate from `φ`:
  --   X*ψ_m^2 - φ_m = ψ_{m+1}ψ_{m-1}`.
  -- X/Y components are coordinate-ring polynomial identities modulo the curve equation.
  -- Depending on how equality in representatives is packaged, use either literal equality
  -- after quotienting by `Affine.CoordinateRing.mk`, or store separate component lemmas.
  sorry

end

end WeierstrassCurve
```

In practice I recommend not proving the vector equality first.  Prove the three component lemmas:

```lean
theorem addXYZ_generic_divPolyRep_Z (m : ℤ) :
    (W.toJacobian.addXYZ genericAffineRep (W.divPolyRep m)) 2
      = W.ψ (m - 1) * W.ψ (m + 1) := by
  simp [genericAffineRep, divPolyRep, Jacobian.addXYZ_Z, Jacobian.addZ, WeierstrassCurve.φ]
  ring

/-- X component, modulo the affine equation. -/
theorem mk_addXYZ_generic_divPolyRep_X (m : ℤ) :
    Affine.CoordinateRing.mk W.toAffine
      ((W.toJacobian.addXYZ genericAffineRep (W.divPolyRep m)) 0
        - W.ψ (m - 1)^2 * W.φ (m + 1)) = 0 := by
  sorry

/-- Y component, modulo the affine equation. -/
theorem mk_addXYZ_generic_divPolyRep_Y (m : ℤ) :
    Affine.CoordinateRing.mk W.toAffine
      ((W.toJacobian.addXYZ genericAffineRep (W.divPolyRep m)) 1
        - W.ψ (m - 1)^3 * W.ω (m + 1)) = 0 := by
  sorry
```

### Expanded CAS identity for the X component

Let

```text
A = φ_m,
B = ω_m,
C = ψ_m.
```

With `P=[X,Y,1]`, `Q=[A,B,C]`, Mathlib’s `addX(P,Q)` expands to

```text
X*A^2
- 2*Y*B*C
+ X^2*A*C^2
- a1*X*B*C
- a1*Y*A*C^2
+ 2*a2*X*A*C^2
- a3*B*C
- a3*Y*C^4
+ a4*A*C^2
+ a4*X*C^4
+ 2*a6*C^4.
```

The CAS check is:

```text
addX(P,R_m) - ψ_{m-1}^2 * φ_{m+1} ∈ (F_W).
```

For the Y component, use Mathlib’s `Jacobian.addY` definition directly; it is large, and copying it by hand is not useful.  The CAS check is:

```text
addY(P,R_m) - ψ_{m-1}^3 * ω_{m+1} ∈ (F_W).
```

### Literature status

This is the standard division-polynomial addition formula underlying Silverman, *Arithmetic of Elliptic Curves*, Chapter III, §2, where

```text
[n]P = (φ_n(P)/ψ_n(P)^2, ω_n(P)/ψ_n(P)^3).
```

The exact `addXYZ` component formulas above are usually not printed in expanded form; they are the homogeneous/Jacobian-coordinate algebra obtained by applying the chord-and-tangent addition formula to the standard division-polynomial representatives.

---

## Important warning about the addition identity

The scalar in the addition identity is `ψ_{m-1}`.  It can vanish at special points.  Therefore

```text
addXYZ(P,R_m) = ψ_{m-1} • R_{m+1}
```

is **not** always a projective equivalence of nonzero representatives after evaluation.  If `ψ_{m-1}(P)=0`, both sides may evaluate to the zero vector.

This is fine for polynomial induction, but it means you should not use this lemma alone as a point-level group law statement.  For point-level use, either restrict to the open where the scalar is nonzero, or use the final canonical representative `R_{m+1}` directly after it has been established independently.

This is the main reason a naive induction

```text
[m+1]P = [m]P + P
```

using raw `addXYZ` can silently fail in Lean.

---

## (2) Doubling identity `[m]P + [m]P = [2m]P`

The clean identity is:

```text
dblXYZ(R_m) = R_{2m}.
```

Componentwise:

```text
dblZ(R_m) ≡ ψ_{2m}        mod F_W

dblX(R_m) ≡ φ_{2m}        mod F_W

dblY(R_m) ≡ ω_{2m}        mod F_W
```

The `Z` component is the key normalization check.  Mathlib’s raw formula is

```text
dblZ(R_m) = ψ_m * (ω_m - negY(R_m)).
```

Since

```text
negY([φ_m,ω_m,ψ_m]) = -ω_m - a₁ φ_m ψ_m - a₃ ψ_m³,
```

we get

```text
dblZ(R_m)
  = ψ_m * (2ω_m + a₁ φ_m ψ_m + a₃ ψ_m³)
  = ψ_{2m}
```

exactly by the defining identity for `ω_m`:

```text
2 ψ_m ω_m = ψ_{2m} - ψ_m²(a₁ φ_m + a₃ ψ_m²).
```

So the doubling `Z` proof should be short and should be written immediately after the `ω` normalization theorem.

### Lean target shape

```lean
namespace WeierstrassCurve

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Doubling step for the projective division-polynomial representative. -/
theorem dblXYZ_divPolyRep (m : ℤ) :
    W.toJacobian.dblXYZ (W.divPolyRep m) = W.divPolyRep (2 * m) := by
  -- Again, prove componentwise.  Z uses `two_mul_psi_mul_ω` directly.
  -- X/Y are polynomial identities modulo the curve equation.
  sorry

/-- Z component sanity check for doubling. -/
theorem dblXYZ_divPolyRep_Z (h2 : (2 : K) ≠ 0) (m : ℤ) :
    (W.toJacobian.dblXYZ (W.divPolyRep m)) 2 = W.ψ (2 * m) := by
  -- expand `dblZ`, `negY`, `divPolyRep`; use `two_mul_ψ_mul_ω h2 m`.
  sorry

end

end WeierstrassCurve
```

### Is doubling easier than addition?

The `Z` component is much easier than addition and is the best normalization test for `ω`.  The `X` and `Y` components are still large polynomial identities.  Overall, doubling is probably slightly easier than addition because there is no scalar factor `ψ_{m-1}` and no orientation/sign trap, but the `dblX`/`dblY` algebra is still substantial.

Recommended coding order:

```text
1. doubling Z component
2. addition Z component
3. local parameter algebra using abstract projective formula
4. doubling X/Y and addition X/Y only when needed for full projective formula
```

---

## (3) Missing atoms and normalization traps

### Trap 1: `n = 0`, `n = 1`, and negative indices

Do not start with a fully integer-indexed projective formula unless you need it immediately.

* `ψ_0 = 0`, `φ_0 = 1`, so the representative for `[0]P = O` should be something like `[1:ω_0:0]`; you need `ω_0 = 1` or another nonzero value compatible with the point at infinity.
* Negative indices are subtle: `ψ_{-n} = -ψ_n` and `φ_{-n}=φ_n`, but `ω_{-n}` is not simply `-ω_n`; negating a point changes the Jacobian `Y` coordinate by `negY`, involving `a₁` and `a₃`.

Recommendation: first prove the theorem for `n : ℕ`, with explicit base cases `0,1,2,3,4`.  Add `Int` symmetry only later.

### Trap 2: `ω₀` normalization

Using `ψTwoMulQuot` from `complEDS₂` is good because `complEDS₂_zero = 2`, so the char-zero prototype gives

```text
ω_0 = 1.
```

That matches the point at infinity convention.  Check this early:

```lean
@[simp] theorem ω_zero (h2 : (2 : K) ≠ 0) : W.ω 0 = 1 := by
  -- should follow from `complEDS₂_zero` and the definition of `ω`.
  sorry
```

### Trap 3: weighted scalar action

Jacobian scalar equivalence is weighted:

```text
u • [X:Y:Z] = [u²X : u³Y : uZ].
```

So addition by `P` with orientation `[X:Y:1] + R_m` gives:

```text
X component scalar: ψ_{m-1}²
Y component scalar: ψ_{m-1}³
Z component scalar: ψ_{m-1}
```

If you reverse the order, the scalar becomes `-ψ_{m-1}` and the Y component sign changes.  Pick one orientation and never mix them.

### Trap 4: coordinate-ring equality vs literal polynomial equality

Many identities only hold modulo the curve equation.  The safe Lean shape is:

```lean
Affine.CoordinateRing.mk W.toAffine (lhs - rhs) = 0
```

or an equivalent statement using membership in the ideal generated by the affine equation.

The `Z` identities often hold literally; the `X` and `Y` identities generally should be treated modulo the equation.

### Trap 5: `φ_n(P) ≠ 0` is not supplied by `mk_φ`

You said Seam C is already proven in the repo.  Good.  Keep it as an explicit dependency.  `mk_φ` reduces `φ_n(P)` at `ψ_n(P)=0` to adjacent division-polynomial values, but the adjacent nonvanishing is the real theorem.

### Trap 6: `ω_n(P) ≠ 0` needs the representative to satisfy the projective equation

To prove `ω_n(P) ≠ 0` from `φ_n(P) ≠ 0`, you need to know

```text
[φ_n(P):ω_n(P):ψ_n(P)]
```

satisfies the Jacobian/projective equation.  This follows from the projective formula or can be proved separately as a polynomial identity:

```text
Jacobian.Equation (![φ_n,ω_n,ψ_n])
```

modulo the affine equation.  Add this as an atom if the projective formula theorem does not expose it.

Suggested atom:

```lean
theorem divPolyRep_equation (m : ℤ) :
    -- W.toJacobian.Equation (W.divPolyRep m), modulo the affine equation
    True := by
  -- follows from the projective formula or can be proved directly by polynomial identity
  sorry
```

### Trap 7: local parameter sign

For Jacobian coordinates,

```text
x = X/Z²,
y = Y/Z³,
t = -x/y = -X*Z/Y.
```

Use exactly this convention in the bridge.  If your `TangentO` convention differs by a sign, insert a one-line sign-conversion lemma once, not throughout the proof.

### Trap 8: full `ψ_n` vs reduced `preΨ'_n`

The local parameter formula uses full bivariate `ψ_n`.  The separability theorem is about reduced univariate `preΨ'_n`.  At non-2-torsion dual points, the conversion uses the unit `ψ₂(Pε)` and the coordinate-ring congruence `mk_ψ`/`Ψ`.

Keep this as a separate atom.  Do not bury it inside the projective formula proof.

---

## Final recommended atom sequence before coding

```text
A0. eval wrappers for K[X][Y] and dual-number points                     easy
A1. ψTwoMulQuot via complEDS₂, plus ψ*quot = ψ₂ₙ                         easy
A2. char-zero ω definition and two_mul_ψ_mul_ω normalization              easy/moderate
A3. ω₀, ω₁, small sanity checks                                          easy
A4. divPolyRep and weighted scalar orientation lemmas                    easy
A5. doubling Z component: dblZ(R_m)=ψ₂ₘ                                  moderate, crucial sanity check
A6. addition Z component: addZ(P,R_m)=ψ_{m-1}ψ_{m+1}                     easy
A7. abstract local-parameter algebra from [φ:ω:ψ]                        easy/moderate
A8. full-vs-reduced ψ coefficient lemma                                  moderate
A9. projective representative equation / ω≠0 from φ≠0                    moderate
A10. doubling X/Y and addition X/Y projective identities                 hard
A11. final assembly                                                       easy once A7-A10 exist
```

The only atom I would postpone is A10 if you can first prove the exact local bridge you need from weaker evaluated/projective assumptions.  But for a complete reusable projective formula, A10 is the core hard block.

## Final verdict

The exact addition identity is

```text
addXYZ([X:Y:1], [φ_m:ω_m:ψ_m]) = ψ_{m-1} • [φ_{m+1}:ω_{m+1}:ψ_{m+1}].
```

The exact doubling identity is

```text
dblXYZ([φ_m:ω_m:ψ_m]) = [φ_{2m}:ω_{2m}:ψ_{2m}].
```

Both are standard division-polynomial coordinate identities, but they are usually cited via the final formula `[n]P=(φ_n/ψ_n²,ω_n/ψ_n³)` rather than printed as expanded `addXYZ`/`dblXYZ` component polynomials.  Doubling is slightly easier, especially the `Z` component, because it is exactly the `ω` normalization identity.  The biggest missing atom is still the `X/Y` projective identity proof modulo the Weierstrass equation, with careful weighted-scalar normalization.
