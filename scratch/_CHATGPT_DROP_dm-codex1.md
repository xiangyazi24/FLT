# Q2386 (dm-codex1): dependency roadmap for AP and double-leg residuals

Question: can both Q2383 global facts

```text
A. FourRatSquaresAPConst
B. DoubleLegRightTrianglesDegenerate
```

be derived from the existing Eisenstein quartic residual

```lean
EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c^2 = m^4 - m^2*n^2 + n^4 →
      m = 0 ∨ n = 0 ∨ m^2 = n^2
```

or from the rational interface

```lean
RatQuarticEisensteinXClassification :
  ∀ {x y : ℚ}, y^2 = x^4 - x^2 + 1 → x = 0 ∨ x^2 = 1
```

Answer:

* **B yes.**  The double-leg right-triangle obstruction is a direct algebraic consequence of `RatQuarticEisensteinXClassification`.  The reduction is explicit and Lean-friendly.
* **A no, not from that interface alone by the same elementary reduction.**  Four rational squares in AP reduce naturally to a different quartic
  ```text
  s^2 = r^4 + 8r^3 + 2r^2 - 8r + 1,
  ```
  not to `s^2 = r^4 - r^2 + 1`.  Killing that AP quartic is exactly Fermat's four-squares-in-AP descent.  If one proves it by mapping to the target elliptic curve `E1`, that is circular for the N=12 rational-point route.
* Minimal safe Lean frontier: expose `RatQuarticEisensteinXClassification` plus `FourRatSquaresAPConst`.  Derive `DoubleLegRightTrianglesDegenerate` from the Eisenstein theorem, not as an extra axiom.

---

## 0. Lean namespace and interfaces

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

namespace FLT.Mazur.N12

/-- Rational Eisenstein quartic classification.  This may be derived from the
integer `EisensteinQuarticSquareClassification` by denominator clearing. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ},
    y^2 = x^4 - x^2 + 1 → x = 0 ∨ x^2 = 1

/-- Fermat four-rational-squares-in-arithmetic-progression theorem. -/
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

end FLT.Mazur.N12
```

---

## 1. B from Eisenstein: exact parameterization and quartic identity

### 1.1 Algebraic parameterization of the first right triangle

Assume

```text
h^2 = x^2 + y^2.
```

If `y = 0`, the desired double-leg conclusion is already true.  So assume `y ≠ 0`.

Set

```text
u := h + x,
v := y,
λ := 1 / (2*u).
```

Then `u ≠ 0`: if `u = 0`, then `h = -x`, hence `h^2 = x^2`; from `h^2 = x^2 + y^2` we get `y^2 = 0`, contradiction to `y ≠ 0`.

The standard rational right-triangle parameterization is then not an extra theorem; it is just the following identities:

```text
x = λ * (u^2 - v^2),
y = λ * (2*u*v),
h = λ * (u^2 + v^2).
```

Indeed:

```text
u^2 - v^2
  = (h+x)^2 - y^2
  = h^2 + 2hx + x^2 - y^2
  = (x^2+y^2) + 2hx + x^2 - y^2
  = 2x(h+x)
  = 2ux,
```

and similarly

```text
u^2 + v^2 = 2u h,
2uv = 2u y.
```

Since `λ = 1/(2u)`, the formulas follow.

### 1.2 The second right triangle gives the Eisenstein quartic

Now also assume

```text
k^2 = (2*x)^2 + y^2.
```

Substitute the parameterization:

```text
k^2
  = 4*x^2 + y^2
  = 4*λ^2*(u^2-v^2)^2 + λ^2*(2uv)^2
  = 4*λ^2*(u^4 - u^2*v^2 + v^4).
```

Because `u ≠ 0`, `λ ≠ 0`.  Equivalently,

```text
(k / (2*λ))^2 = u^4 - u^2*v^2 + v^4.
```

Since `2*λ = 1/u`, this is the homogeneous identity

```text
(k*u)^2 = u^4 - u^2*v^2 + v^4.
```

Since `v = y ≠ 0`, divide by `v^4`.  Put

```text
r := u / v = (h+x)/y,
s := k*u / v^2 = k*(h+x)/y^2.
```

Then

```text
s^2 = r^4 - r^2 + 1.
```

Apply `RatQuarticEisensteinXClassification`:

```text
r = 0  or  r^2 = 1.
```

The branch `r = 0` gives `u = 0`, impossible.  Hence `r^2 = 1`, so `u^2 = v^2`.  But we already have

```text
u^2 - v^2 = 2*u*x.
```

Thus `2*u*x = 0`.  Since `u ≠ 0`, `x = 0`.  Therefore `x = 0 ∨ y = 0`.

### 1.3 Lean theorem skeleton

This is the recommended theorem to actually prove from the rational Eisenstein interface.

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

namespace FLT.Mazur.N12

/-- The double-leg obstruction follows from the rational Eisenstein quartic. -/
theorem doubleLeg_of_ratQuarticEisenstein
    (HE : RatQuarticEisensteinXClassification) :
    DoubleLegRightTrianglesDegenerate := by
  intro x y h k hh hk
  by_cases hy : y = 0
  · exact Or.inr hy
  · left
    let u : ℚ := h + x
    have hu : u ≠ 0 := by
      intro hu0
      have hy2 : y^2 = 0 := by
        -- from `u = h+x = 0`, get `h = -x`, then use `hh`.
        unfold u at hu0
        nlinarith [hh, hu0]
      exact hy (sq_eq_zero_iff.mp hy2)

    let r : ℚ := u / y
    let s : ℚ := k * u / y^2

    have h_quartic : s^2 = r^4 - r^2 + 1 := by
      -- The field identity is exactly:
      --   (k*u/y^2)^2 = (u/y)^4 - (u/y)^2 + 1
      -- after using
      --   hh : h^2 = x^2 + y^2,
      --   hk : k^2 = (2*x)^2 + y^2,
      --   u = h+x.
      -- A robust proof route is `field_simp [r, s, u, hy]` followed by `ring_nf`/`nlinarith`.
      field_simp [r, s, u, hy]
      ring_nf
      nlinarith [hh, hk]

    rcases HE h_quartic with hr0 | hr2
    · exfalso
      have hu0 : u = 0 := by
        -- `r = u/y = 0`, `y ≠ 0`.
        field_simp [r, hy] at hr0
        exact hr0
      exact hu hu0
    · have huv : u^2 = y^2 := by
        -- `r^2 = 1`, `r = u/y`, `y ≠ 0`.
        field_simp [r, hy] at hr2
        nlinarith [hr2]
      have hux : u^2 - y^2 = 2*u*x := by
        -- `(h+x)^2 - y^2 = 2*x*(h+x)` using `hh`.
        unfold u
        nlinarith [hh]
      have hmul : (2*u) * x = 0 := by
        nlinarith [huv, hux]
      exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hu)

end FLT.Mazur.N12
```

Notes for implementation:

* If `field_simp` is too aggressive, isolate the identity as a small lemma with explicit nonzero denominators `hy : y ≠ 0`.
* The proof uses only `RatQuarticEisensteinXClassification` plus field/ring algebra.
* No elliptic-curve API is involved.

---

## 2. A: four rational squares in AP naturally reduce to a different quartic

Start from four squares in AP:

```text
x^2 - w^2 = y^2 - x^2,
y^2 - x^2 = z^2 - y^2.
```

The first equation is

```text
w^2 + y^2 = 2*x^2.
```

A rational parameterization of the conic `W^2 + Y^2 = 2 X^2` is:

```text
w = λ * (u^2 - 2*u*v - v^2),
x = λ * (u^2 + v^2),
y = λ * (u^2 + 2*u*v - v^2).
```

Check:

```text
(u^2 - 2uv - v^2)^2 + (u^2 + 2uv - v^2)^2
  = 2*(u^2 + v^2)^2.
```

The second AP equation gives

```text
z^2 = 2*y^2 - x^2.
```

Substituting the parameterization yields

```text
z^2 = λ^2 * (u^4 + 8*u^3*v + 2*u^2*v^2 - 8*u*v^3 + v^4).
```

So, when `λ ≠ 0` and `v ≠ 0`, with

```text
r := u / v,
s := z / (λ*v^2),
```

we get the AP quartic

```text
s^2 = r^4 + 8*r^3 + 2*r^2 - 8*r + 1.        (APQ)
```

This is **not** the Eisenstein quartic

```text
s^2 = r^4 - r^2 + 1.                          (EIS)
```

The constant-AP cases correspond to

```text
v = 0       -- point at infinity in the r-parameter,
r = 0,
r^2 = 1.
```

Thus an AP-quartic classification sufficient for A would be:

```lean
namespace FLT.Mazur.N12

/-- The quartic obtained from four rational squares in AP. -/
def RatAPQuarticClassification : Prop :=
  ∀ {r s : ℚ},
    s^2 = r^4 + 8*r^3 + 2*r^2 - 8*r + 1 →
      r = 0 ∨ r^2 = 1

end FLT.Mazur.N12
```

`RatAPQuarticClassification` implies `FourRatSquaresAPConst` by the parameterization above, plus the degenerate cases `λ = 0` or `v = 0`.

### 2.1 Lean-friendly AP parameterization theorem

This is the useful conic parameterization boundary if you want to prove AP from the AP quartic instead of exposing `FourRatSquaresAPConst` directly.

```lean
namespace FLT.Mazur.N12

/-- A rational parameterization of `w^2 + y^2 = 2*x^2`.
The disjunction isolates the zero solution to avoid denominator bookkeeping. -/
theorem threeSquaresAP_param
    {w x y : ℚ}
    (h : x^2 - w^2 = y^2 - x^2) :
    (w = 0 ∧ x = 0 ∧ y = 0) ∨
    ∃ u v λ : ℚ,
      w = λ * (u^2 - 2*u*v - v^2) ∧
      x = λ * (u^2 + v^2) ∧
      y = λ * (u^2 + 2*u*v - v^2) := by
  -- Conic parameterization of `w^2 + y^2 = 2*x^2` through `(1,1,1)`.
  -- One possible direct choice when `x + w ≠ 0` is obtained by the slope of
  -- the line through the base point after normalizing by x.
  -- This is elementary conic algebra, not the hard descent.
  sorry

/-- Four squares in AP reduce to the AP quartic. -/
theorem fourSquaresAP_of_APQuartic
    (HAPQ : RatAPQuarticClassification) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  -- Use `threeSquaresAP_param h1`.
  -- Degenerate zero branch is immediate.
  -- In the parameterized branch, use
  --   z^2 = 2*y^2 - x^2
  -- and the identity
  --   2*(u^2 + 2uv - v^2)^2 - (u^2 + v^2)^2
  --     = u^4 + 8u^3v + 2u^2v^2 - 8uv^3 + v^4.
  -- If `λ = 0`, all first three terms are zero and then `z^2 = 0`.
  -- If `v = 0`, then `w^2=x^2=y^2`, and h2 gives `z^2=y^2`.
  -- If `λ ≠ 0` and `v ≠ 0`, define
  --   r = u/v,
  --   s = z/(λ*v^2),
  -- apply `HAPQ`, and check `r=0` or `r^2=1` makes
  --   w^2=x^2=y^2=z^2`.
  sorry

end FLT.Mazur.N12
```

The hard theorem in this route is `RatAPQuarticClassification`, not the conic parameterization.

---

## 3. Why A should not be claimed from `RatQuarticEisensteinXClassification` alone

The Eisenstein theorem classifies rational points on

```text
EIS:  S^2 = R^4 - R^2 + 1.
```

Four squares in AP reduce to

```text
APQ:  S^2 = R^4 + 8R^3 + 2R^2 - 8R + 1.
```

These are different quartics.  There is no direct instance of `RatQuarticEisensteinXClassification` after the standard AP parameterization.

A particularly quick sanity check: the binary quartic

```text
R^4 - R^2 + 1
```

has no real projective roots.  The AP quartic

```text
R^4 + 8R^3 + 2R^2 - 8R + 1
```

has real projective roots, since after dividing by `R^2` and setting `q = R - 1/R`,

```text
R^-2 * APQ(R) = q^2 + 8q + 4,
```

and `q^2 + 8q + 4` has real roots `q = -4 ± 2*sqrt(3)`.  Therefore the AP quartic is not obtained from the Eisenstein quartic by a real/rational fractional-linear change of variable times a square factor.  Any reduction from APQ to EIS would require an additional nontrivial rational map/descent theorem.  That theorem would itself be a new global arithmetic input, not an algebraic `ring` wrapper around the existing Eisenstein classifier.

For Lean dependency management, this means:

```text
RatQuarticEisensteinXClassification
  ⟹ DoubleLegRightTrianglesDegenerate

RatQuarticEisensteinXClassification
  ⟹/ FourRatSquaresAPConst   -- not by the elementary cover algebra above
```

A can certainly be proved by classical Fermat descent, and it may be expressible through another genus-one/quartic model.  But unless you provide and prove a separate map/classification for `APQ`, exposing only `RatQuarticEisensteinXClassification` is not enough to close the `(3,2,6)` and `(-1,-2,2)` cover residuals.

---

## 4. Circularity warning for the N=12 route

Be careful about the source of `RatQuarticEisensteinXClassification`.

Safe dependency:

```text
external integer EisensteinQuarticSquareClassification
  -> denominator-cleared RatQuarticEisensteinXClassification
  -> DoubleLegRightTrianglesDegenerate
  -> degenerate cover residuals (1,1,1), (-3,-1,3)
```

Unsafe circular dependency:

```text
E1 affine rational-point classification
  -> E24 / quartic rational classification
  -> RatQuarticEisensteinXClassification
  -> residual cover classification
  -> E1 affine rational-point classification
```

If the goal is to prove `E1` rational points using the full-2-cover route, then `RatQuarticEisensteinXClassification` must come from the external integer Eisenstein theorem or another independent proof, not from the `E1` theorem currently being assembled.

Similarly, proving `FourRatSquaresAPConst` by mapping the four-AP curve back to `E1` and invoking the target `E1` point classification is circular.  It is safe only if `FourRatSquaresAPConst` is supplied as an independent Fermat descent theorem or proved from a separately accepted residual such as `RatAPQuarticClassification`.

---

## 5. Recommended minimal residual set

### Recommended frontend assumptions

Expose exactly these two global arithmetic assumptions in the N=12 file:

```lean
namespace FLT.Mazur.N12

/-- Existing or denominator-cleared external Eisenstein theorem. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ},
    y^2 = x^4 - x^2 + 1 → x = 0 ∨ x^2 = 1

/-- Independent Fermat theorem: four rational squares in AP are constant. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x^2 - w^2 = y^2 - x^2 →
    y^2 - x^2 = z^2 - y^2 →
      w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2

end FLT.Mazur.N12
```

Then prove internally:

```lean
namespace FLT.Mazur.N12

theorem doubleLeg_of_ratQuarticEisenstein
    (HE : RatQuarticEisensteinXClassification) :
    DoubleLegRightTrianglesDegenerate := by
  -- Section 1 proof.
  sorry

end FLT.Mazur.N12
```

### Use in the four residual covers

* `(3,2,6)` and `(-1,-2,2)` consume `FourRatSquaresAPConst` directly.
* `(1,1,1)` and `(-3,-1,3)` consume `doubleLeg_of_ratQuarticEisenstein HE`.

So the cover layer should depend on:

```text
HE   : RatQuarticEisensteinXClassification
HAP  : FourRatSquaresAPConst
```

not on four opaque cover axioms and not on `DoubleLegRightTrianglesDegenerate` as a third independent assumption.

### Alternative residual interface

If you prefer quartic residuals over AP wording, replace `FourRatSquaresAPConst` by:

```lean
namespace FLT.Mazur.N12

def RatAPQuarticClassification : Prop :=
  ∀ {r s : ℚ},
    s^2 = r^4 + 8*r^3 + 2*r^2 - 8*r + 1 →
      r = 0 ∨ r^2 = 1

end FLT.Mazur.N12
```

and prove `FourRatSquaresAPConst` from it by conic parameterization.  This is more work in Lean than assuming the clean AP theorem, and it is not the same as the Eisenstein quartic classifier.

---

## 6. Final dependency DAG

```text
EisensteinQuarticSquareClassification (integer, external)
   |
   v
RatQuarticEisensteinXClassification
   |
   v
DoubleLegRightTrianglesDegenerate
   |
   v
Degenerate residual covers:
  (1,1,1), (-3,-1,3)

FourRatSquaresAPConst (independent Fermat AP theorem)
   |
   v
Nonzero residual covers:
  (3,2,6), (-1,-2,2)

[finite S23 local congruence/sign obstructions]
   |
   v
E1 affine rational-point classification
```

Do not close the `FourRatSquaresAPConst` box using the final `E1` theorem.  That would make the full-2-cover route circular.
