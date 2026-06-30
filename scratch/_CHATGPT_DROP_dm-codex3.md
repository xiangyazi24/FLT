# Q2405 drop: can `FourRatSquaresAPConst` be proved from `DoubleLegRightTrianglesDegenerate`?

Target proposed shortcut:

```lean
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, y^2 = x^4 - x^2 + 1 → x = 0 ∨ x^2 = 1

def DoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h^2 = x^2 + y^2 →
    k^2 = (2*x)^2 + y^2 →
    x = 0 ∨ y = 0

def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2
```

## Bottom line

I do **not** recommend adding

```lean
theorem fourRatSquaresAPConst_of_doubleLeg
    (hDL : DoubleLegRightTrianglesDegenerate) : FourRatSquaresAPConst := ...
```

unless you first prove an additional nontrivial bridge from a nonconstant four-square AP to a nondegenerate double-leg pair.

The natural algebra from a four-square AP gives **two rational right triangles of the same area**, not two right triangles sharing a leg with the other leg doubled.  Parametrizing the first triangle and imposing the fourth square lands in the quartic

```text
s^2 = t^4 - 8*t^3 + 2*t^2 + 8*t + 1,
```

whereas `DoubleLegRightTrianglesDegenerate` is equivalent, after parametrizing the first right triangle, to the Eisenstein quartic

```text
S^2 = u^4 - u^2 + 1
```

or, after a linear fractional change, to the Ljunggren/Pocklington quartic

```text
S^2 = u^4 + 14*u^2 + 1.
```

So `hDL` alone is not an explicit rational-algebra proof of `FourRatSquaresAPConst`.  A bridge between the AP quartic and the Eisenstein/double-leg quartic may exist as a classical descent/birational theorem, but that bridge is exactly an extra theorem.  It should not be hidden as a small `ring_nf` wrapper.

No `E1` point classification is used below.

---

## 1. Lean definitions for the audit

```lean
import Mathlib

namespace FLT.Mazur.N12.FourAPDoubleLegAudit

noncomputable section

/-- Four rational squares in arithmetic progression are constant. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2

/-- Double-leg right-triangle obstruction. -/
def DoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h^2 = x^2 + y^2 →
    k^2 = (2*x)^2 + y^2 →
    x = 0 ∨ y = 0

/-- The explicit bridge one would still need in order to derive four-square AP
constancy from the double-leg theorem alone. -/
def FourAPToDoubleLegBridge : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    ¬ (w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2) →
    ∃ X Y H K : ℚ,
      X ≠ 0 ∧ Y ≠ 0 ∧
      H^2 = X^2 + Y^2 ∧
      K^2 = (2*X)^2 + Y^2
```

With this bridge, the implication is a trivial wrapper:

```lean
theorem fourRatSquaresAPConst_of_doubleLeg_and_bridge
    (hDL : DoubleLegRightTrianglesDegenerate)
    (hbridge : FourAPToDoubleLegBridge) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  by_contra hnonconst
  rcases hbridge h1 h2 hnonconst with
    ⟨X, Y, H, K, hX, hY, hH, hK⟩
  have hdeg := hDL (x := X) (y := Y) (h := H) (k := K) hH hK
  rcases hdeg with hX0 | hY0
  · exact hX hX0
  · exact hY hY0
```

The question is therefore whether `FourAPToDoubleLegBridge` has a small explicit proof.  The answer from the natural algebra is no.

---

## 2. What a four-square AP gives by direct algebra

Assume

```text
x^2 - w^2 = y^2 - x^2,
y^2 - x^2 = z^2 - y^2.
```

Then

```text
w^2 + y^2 = 2*x^2,
x^2 + z^2 = 2*y^2.
```

Hence the two triples

```text
(y-w, y+w, 2*x),
(z-x, z+x, 2*y)
```

are rational right triangles:

```text
(y-w)^2 + (y+w)^2 = (2*x)^2,
(z-x)^2 + (z+x)^2 = (2*y)^2.
```

Their areas are equal, because

```text
(y-w)*(y+w) = y^2 - w^2 = 2*(y^2 - x^2),
(z-x)*(z+x) = z^2 - x^2 = 2*(y^2 - x^2).
```

Lean wrappers:

```lean
theorem fourAP_to_equalArea_right_triangles
    {w x y z : ℚ}
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2) :
    ((y - w)^2 + (y + w)^2 = (2*x)^2) ∧
    ((z - x)^2 + (z + x)^2 = (2*y)^2) ∧
    ((y - w) * (y + w) = (z - x) * (z + x)) := by
  constructor
  · nlinarith [h1]
  constructor
  · nlinarith [h2]
  · nlinarith [h1, h2]
```

This is useful, but it is **not** the double-leg shape.  The double-leg shape would require, for some rational `X,Y,H,K`,

```text
H^2 = X^2 + Y^2,
K^2 = (2X)^2 + Y^2.
```

The equal-area pair above has neither a common leg nor a doubled leg.  Converting a pair of same-area rational right triangles into a double-leg pair is an additional concordant-forms/descent transformation, not a direct consequence of the displayed identities.

---

## 3. The standard parametrization lands in the wrong quartic

The first AP equation

```text
w^2 + y^2 = 2*x^2
```

is parametrized by

```text
w = λ * (1 - 2*t - t^2),
x = λ * (1 + t^2),
y = λ * (1 + 2*t - t^2).
```

Indeed,

```text
(1 - 2*t - t^2)^2 + (1 + 2*t - t^2)^2
  = 2*(1 + t^2)^2.
```

The fourth-square condition is

```text
z^2 = 2*y^2 - x^2,
```

so it becomes

```text
z^2 = λ^2 * (t^4 - 8*t^3 + 2*t^2 + 8*t + 1).
```

Lean statement for the identity:

```lean
abbrev APQuartic (t : ℚ) : ℚ :=
  t^4 - 8*t^3 + 2*t^2 + 8*t + 1

theorem threeSquareAP_param_identity (t : ℚ) :
    (1 - 2*t - t^2)^2 + (1 + 2*t - t^2)^2
      = 2 * (1 + t^2)^2 := by
  ring

theorem AP_fourth_condition_quartic
    (λ t z : ℚ)
    (hz : z^2 = 2*(λ * (1 + 2*t - t^2))^2
                  - (λ * (1 + t^2))^2) :
    z^2 = λ^2 * APQuartic t := by
  unfold APQuartic
  nlinarith [hz]
```

By contrast, the double-leg theorem parametrizes as follows.  If the first triangle is nondegenerate, write

```text
X = μ * (1 - u^2),
Y = μ * (2*u),
H = μ * (1 + u^2).
```

Then the second double-leg equation becomes

```text
K^2 = (2X)^2 + Y^2
    = 4*μ^2*(u^4 - u^2 + 1).
```

Lean identity:

```lean
abbrev EisensteinQuartic (u : ℚ) : ℚ := u^4 - u^2 + 1

theorem doubleLeg_param_quartic_identity (μ u : ℚ) :
    (2*(μ * (1 - u^2)))^2 + (μ * (2*u))^2
      = (2*μ)^2 * EisensteinQuartic u := by
  unfold EisensteinQuartic
  ring
```

The two quartics are visibly different:

```text
AP quartic:          t^4 - 8*t^3 + 2*t^2 + 8*t + 1,
Eisenstein quartic:  u^4 - u^2 + 1.
```

A linear-fractional variant of the double-leg quartic gives

```text
u^4 + 14*u^2 + 1,
```

not the AP quartic either:

```lean
theorem eisenstein_lft_to_ljunggren14 (u : ℚ) :
    (u + 1)^4 - (u + 1)^2 * (u - 1)^2 + (u - 1)^4
      = u^4 + 14*u^2 + 1 := by
  ring
```

Thus the natural parametrization route does not yield a double-leg instance by algebraic simplification.

---

## 4. Why the requested shortcut is not currently valid

A nonconstant four-square AP gives:

```text
right triangle 1: legs y-w, y+w, hypotenuse 2*x,
right triangle 2: legs z-x, z+x, hypotenuse 2*y,
same area:       (y-w)(y+w) = (z-x)(z+x).
```

`DoubleLegRightTrianglesDegenerate` applies only to:

```text
right triangle 1: legs X,  Y, hypotenuse H,
right triangle 2: legs 2X, Y, hypotenuse K.
```

These are different concordant-form problems.  The missing operation is not `ring`; it is a transformation from an equal-area pair / AP quartic to the double-leg / Eisenstein quartic.  If this transformation is proved, it should be named explicitly, for example:

```lean
def FourAPToDoubleLegBridge : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
    ¬ (w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2) →
    ∃ X Y H K : ℚ,
      X ≠ 0 ∧ Y ≠ 0 ∧
      H^2 = X^2 + Y^2 ∧
      K^2 = (2*X)^2 + Y^2
```

Then `fourRatSquaresAPConst_of_doubleLeg_and_bridge` above is the correct Lean theorem.  But without this bridge, the theorem

```lean
theorem fourRatSquaresAPConst_of_doubleLeg
    (hDL : DoubleLegRightTrianglesDegenerate) : FourRatSquaresAPConst
```

has no honest algebraic proof from the displayed hypotheses alone.

---

## 5. Adversarial circularity warning for the FLT N=12 route

The full-cover `E1` assembly used two global inputs in Q2387/Q2383:

```text
FourRatSquaresAPConst
DoubleLegRightTrianglesDegenerate
```

It is tempting to reduce both to `RatQuarticEisensteinXClassification`, because `DoubleLegRightTrianglesDegenerate` does reduce cleanly to Eisenstein.  But the AP residual does **not** reduce to `DoubleLegRightTrianglesDegenerate` by the same small parametrization.  It reduces first to the AP quartic

```text
t^4 - 8*t^3 + 2*t^2 + 8*t + 1.
```

If you prove that this AP quartic has only the degenerate rational points using the existing N=12/E1 rational-point classification, that would be circular for the `E1` full-cover route.  If you prove an independent birational/descent bridge from this quartic to Eisenstein, then record it as a separate theorem; it is not just `hDL`.

Recommended current dependency boundary:

```lean
structure E1FullCoverGlobalInputs : Prop where
  fourAP : FourRatSquaresAPConst
  doubleLeg : DoubleLegRightTrianglesDegenerate
```

Possible future compressed boundary, only after proving the bridge independently:

```lean
structure E1FullCoverGlobalInputsCompressed : Prop where
  doubleLeg : DoubleLegRightTrianglesDegenerate
  ap_to_doubleLeg : FourAPToDoubleLegBridge
```

Then derive:

```lean
theorem fourAP_from_compressed
    (c : E1FullCoverGlobalInputsCompressed) : FourRatSquaresAPConst :=
  fourRatSquaresAPConst_of_doubleLeg_and_bridge c.doubleLeg c.ap_to_doubleLeg
```

---

## 6. Final recommendation

Do **not** replace `FourRatSquaresAPConst` by `DoubleLegRightTrianglesDegenerate` in the E1 cover certificate yet.

Keep `FourRatSquaresAPConst` as an independent global arithmetic residual unless/until you have a checked theorem `FourAPToDoubleLegBridge` or a direct independent proof of the AP quartic classification.  The only Lean theorem that is honest today is the bridge-parametrized wrapper:

```lean
theorem fourRatSquaresAPConst_of_doubleLeg_and_bridge
    (hDL : DoubleLegRightTrianglesDegenerate)
    (hbridge : FourAPToDoubleLegBridge) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  by_contra hnonconst
  rcases hbridge h1 h2 hnonconst with
    ⟨X, Y, H, K, hX, hY, hH, hK⟩
  have hdeg := hDL (x := X) (y := Y) (h := H) (k := K) hH hK
  rcases hdeg with hX0 | hY0
  · exact hX hX0
  · exact hY hY0
```

```lean
end
end FLT.Mazur.N12.FourAPDoubleLegAudit
```
