# Q2014 (dm4): Mathlib division polynomials and the Weil-pairing shortcut question

## Scope checked

Project branch:

```text
repo:   xiangyazi24/FLT
branch: ai-scratch
```

The project pins Mathlib at commit:

```text
96fd0fff3b8837985ae21dd02e712cb5df72ec05
```

Relevant Mathlib files at that commit:

```text
Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean
Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
```

## Executive answer

Mathlib has division-polynomial definitions, but the current API is **not** a shortcut to a formal Weil pairing.

The exact division-polynomial declarations are Unicode-name based:

```lean
WeierstrassCurve.ψ₂
WeierstrassCurve.Ψ₂Sq
WeierstrassCurve.Ψ₃
WeierstrassCurve.preΨ₄
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ
WeierstrassCurve.ΨSq
WeierstrassCurve.Ψ
WeierstrassCurve.Φ
WeierstrassCurve.ψ
WeierstrassCurve.φ
```

I did **not** find a declaration literally named `divisionPolynomial`, nor ASCII declarations named `psi` or `phi`.

Also, `ω_n` is explicitly marked TODO in the file, and I did not find a ready theorem saying that evaluating `ψ_m` at a point is equivalent to `[m]P = 0`.

For the Mazur proof, the minimal route is still to axiomatize the final Weil-pairing consequence:

```lean
axiom full_rational_torsion_forces_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

That is the exact implication needed downstream:

```text
full rational m-torsion over Q  ==>  Q contains a primitive m-th root of unity.
```

## (1) Exact Mathlib definitions found

### `ψ₂`

```lean
/-- The `2`-division polynomial `ψ₂ = Ψ₂`. -/
noncomputable def ψ₂ : R[X][Y] :=
  W.toAffine.polynomialY
```

For a general Weierstrass curve, this is the affine polynomial `2Y + a₁X + a₃`.

### `Ψ₂Sq`

```lean
/-- The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`. -/
noncomputable def Ψ₂Sq : R[X] :=
  C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆
```

Useful lemmas include:

```lean
C_Ψ₂Sq
ψ₂_sq
Affine.CoordinateRing.mk_ψ₂_sq
Ψ₂Sq_eq
```

### `Ψ₃`

```lean
/-- The `3`-division polynomial `ψ₃ = Ψ₃`. -/
noncomputable def Ψ₃ : R[X] :=
  3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 +
    3 * C W.b₆ * X + C W.b₈
```

### `preΨ₄`

```lean
/-- The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial
`ψ₄ = Ψ₄ = preΨ₄ψ₂`. -/
noncomputable def preΨ₄ : R[X] :=
  2 * X ^ 6 + C W.b₂ * X ^ 5 + 5 * C W.b₄ * X ^ 4 +
    10 * C W.b₆ * X ^ 3 + 10 * C W.b₈ * X ^ 2 +
    C (W.b₂ * W.b₈ - W.b₄ * W.b₆) * X +
    C (W.b₄ * W.b₈ - W.b₆ ^ 2)
```

### `preΨ'` and `preΨ`

```lean
noncomputable def preΨ' (n : ℕ) : R[X] :=
  preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n

noncomputable def preΨ (n : ℤ) : R[X] :=
  preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
```

There are simp lemmas for `0`, `1`, `2`, `3`, `4`, negation, and the even/odd recurrences.

### `ΨSq`

```lean
/-- The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`. -/
noncomputable def ΨSq (n : ℤ) : R[X] :=
  W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1
```

Important coordinate-ring lemma:

```lean
Affine.CoordinateRing.mk_Ψ_sq
```

### `Ψ`

```lean
/-- The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`. -/
protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=
  C (W.preΨ n) * if Even n then W.ψ₂ else 1
```

### `Φ`

```lean
/-- The univariate polynomials `Φₙ` congruent to `φₙ`. -/
protected noncomputable def Φ (n : ℤ) : R[X] :=
  X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) *
    if Even n then 1 else W.Ψ₂Sq
```

### `ψ`

```lean
/-- The bivariate `n`-division polynomials `ψₙ`. -/
protected noncomputable def ψ (n : ℤ) : R[X][Y] :=
  normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
```

Important lemmas include:

```lean
ψ_zero, ψ_one, ψ_two, ψ_three, ψ_four
ψ_neg, ψ_even, ψ_odd
Affine.CoordinateRing.mk_ψ
```

### `φ`

```lean
/-- The bivariate polynomials `φₙ`. -/
protected noncomputable def φ (n : ℤ) : R[X][Y] :=
  C X * W.ψ n ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)
```

Important lemma:

```lean
Affine.CoordinateRing.mk_φ
```

### `ω`

`Basic.lean` explicitly says `TODO: the bivariate polynomials ω_n`.  So the full multiplication-by-n coordinate package is not finished in this file.

### `Degree.lean`

`Degree.lean` proves leading coefficient and degree statements for `preΨ`, `ΨSq`, and `Φ`, for example:

```lean
natDegree_preΨ_le
coeff_preΨ
natDegree_preΨ
leadingCoeff_preΨ
natDegree_ΨSq_le
coeff_ΨSq
natDegree_ΨSq
leadingCoeff_ΨSq
natDegree_Φ_le
coeff_Φ
natDegree_Φ
leadingCoeff_Φ
```

This is degree infrastructure, not pairing infrastructure.

## What I did not find

I did not find ready-made declarations with names like:

```lean
mem_torsion_iff_psi_eq_zero
psi_roots_eq_torsion
divisionPolynomial_roots
weil_pairing
miller
```

The current Mathlib files define the polynomials, prove recurrence/congruence/base-change facts, and prove degree facts.  They do not currently construct the Weil pairing.

## (2) Can Miller functions be defined purely using division polynomials?

Not in a way that avoids the real missing work.

Division polynomials mainly give the multiplication-by-n map.  Classically one has formulas of the form

```text
x([n]R) = φ_n(R) / ψ_n(R)^2
```

and a corresponding `y`-coordinate formula involving `ω_n`.  But the Miller function used in the Weil pairing is a rational function attached to a chosen point `P`, with divisor data depending on `P`.  It is normally built by products of tangent/secant line functions along an addition chain.

The global polynomial `ψ_m` vanishes on the whole m-torsion locus.  It does not, by itself, give the function attached to a single divisor such as `m[P] - m[O]`.

You could define a computational Miller-value function on affine points using explicit line evaluations and many nonzero-denominator hypotheses.  But proving independence of choices, bilinearity, alternatingness, Galois equivariance, and primitive-root output would essentially reprove divisor/function-field facts in coordinates.

So for the Mazur proof, this is not shorter than keeping the theorem-level axiom.

## (3) Is there a self-contained formula for `e_m` just from `ψ_n` evaluations?

Not a clean generic one in the current Mathlib API.

There are explicit computational formulas for pairings, but they use more than the standard one-point division polynomials `ψ_n`.  They need line functions, denominator choices, addition formulas, or generalized two-point objects such as elliptic nets / net polynomials.

The standard `ψ_n`, `φ_n`, and `ω_n` package gives multiplication-by-n coordinates, not directly the alternating pairing

```text
E[m] × E[m] → μ_m.
```

For small `m` one can write special coordinate formulas, but that does not give a uniform formal route for arbitrary `m` in the Mazur proof.

## Practical recommendation

Do **not** try to discharge the Weil-pairing axiom by building Miller functions from division polynomials right now.

Keep the minimal axiom:

```lean
axiom full_rational_torsion_forces_primitive_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {m : ℕ}
    (hm : 0 < m)
    (hfull : HasFullRationalTorsion E m) :
    ∃ ζ : ℚ, IsPrimitiveRoot ζ m
```

Document it as the determinant/cyclotomic-character consequence of the Weil pairing.  The existing division-polynomial API may eventually help formalize multiplication-by-n and torsion schemes, but it is not yet a short path to a formal Weil pairing.
