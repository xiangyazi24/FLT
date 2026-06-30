# Q2393 (dm-codex1): tactic-level proof of `doubleLeg_of_ratQuarticEisenstein`

This drop gives a no-`sorry`, no-`axiom` Lean block for the rational algebra lemma from Q2386.

I could not fetch `FLT/Assumptions/MazurProof/RationalPointsN12.lean` through the connector path, so the code below is written against the exact namespace and interface names in the prompt:

```lean
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y^2 = x^4 - x^2 + 1

def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x^2 = 1
```

Paste this after those definitions in namespace `MazurProof.RationalPointsN12`.  If `DoubleLegRightTrianglesDegenerate` already exists, omit its `def` line and keep the helper lemmas plus theorem.

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Double-leg right-triangle obstruction. -/
def DoubleLegRightTrianglesDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h^2 = x^2 + y^2 →
    k^2 = (2*x)^2 + y^2 →
      x = 0 ∨ y = 0

/-- If `u = h+x` and `h^2 = x^2 + y^2`, then
`u^2 - y^2 = 2*x*u`.  This is the local algebraic identity behind the
right-triangle parametrization with `u = h+x`. -/
private lemma doubleLeg_u_sq_sub_y_sq
    {x y h u : ℚ}
    (hu : u = h + x)
    (hh : h^2 = x^2 + y^2) :
    u^2 - y^2 = 2*x*u := by
  subst u
  ring_nf
  nlinarith [hh]

/-- Denominator-free quartic numerator identity.

With `u = h+x`, the two right-triangle equations imply

`k^2*u^2 = u^4 - u^2*y^2 + y^4`.

After division by `y^4`, this is exactly the Eisenstein quartic for
`r = u/y`, `s = k*u/y^2`. -/
private lemma doubleLeg_quartic_num
    {x y h k u : ℚ}
    (hu : u = h + x)
    (hh : h^2 = x^2 + y^2)
    (hk : k^2 = (2*x)^2 + y^2) :
    k^2 * u^2 = u^4 - u^2*y^2 + y^4 := by
  have hux : u^2 - y^2 = 2*x*u :=
    doubleLeg_u_sq_sub_y_sq (x := x) (y := y) (h := h) (u := u) hu hh
  calc
    k^2 * u^2 = ((2*x)^2 + y^2) * u^2 := by
      rw [hk]
    _ = (2*x*u)^2 + y^2*u^2 := by
      ring
    _ = (u^2 - y^2)^2 + y^2*u^2 := by
      rw [← hux]
    _ = u^4 - u^2*y^2 + y^4 := by
      ring

/-- The double-leg obstruction follows from the rational Eisenstein quartic
classification.

Math summary:
* If `y = 0`, done.
* Put `u = h+x`.  If `u = 0`, then `h = -x`; the first right-triangle equation
  forces `y = 0`, contradiction.
* Put `r = u/y`, `s = k*u/y^2`.  The helper `doubleLeg_quartic_num` proves
  `RatQuarticEisenstein r s` after clearing denominators.
* The Eisenstein classification gives `r=0` or `r^2=1`.
  The first contradicts `u ≠ 0`; the second gives `u^2=y^2`.
* Since `u^2-y^2 = 2*x*u` and `u ≠ 0`, conclude `x=0`. -/
theorem doubleLeg_of_ratQuarticEisenstein
    (HE : RatQuarticEisensteinXClassification) :
    DoubleLegRightTrianglesDegenerate := by
  intro x y h k hh hk
  by_cases hy : y = 0
  · exact Or.inr hy
  · left
    let u : ℚ := h + x
    have hu_def : u = h + x := rfl
    have hu : u ≠ 0 := by
      intro hu0
      have hhx : h = -x := by
        nlinarith [hu_def, hu0]
      have hy2 : y^2 = 0 := by
        nlinarith [hh, hhx]
      exact hy (sq_eq_zero_iff.mp hy2)

    let r : ℚ := u / y
    let s : ℚ := k * u / y^2

    have hnum : k^2 * u^2 = u^4 - u^2*y^2 + y^4 :=
      doubleLeg_quartic_num (x := x) (y := y) (h := h) (k := k) (u := u)
        hu_def hh hk

    have hquartic_eq : s^2 = r^4 - r^2 + 1 := by
      have hy2_ne : y^2 ≠ 0 := pow_ne_zero 2 hy
      dsimp [r, s]
      field_simp [hy, hy2_ne]
      ring_nf at hnum ⊢
      nlinarith [hnum]

    have hquartic : RatQuarticEisenstein r s := by
      simpa [RatQuarticEisenstein] using hquartic_eq

    rcases HE hquartic with hr0 | hr2
    · have hu0 : u = 0 := by
        have hr0' : u / y = 0 := by
          simpa [r] using hr0
        field_simp [hy] at hr0'
        nlinarith [hr0']
      exact (hu hu0).elim
    · have hu2 : u^2 = y^2 := by
        have hr2' : (u / y)^2 = 1 := by
          simpa [r] using hr2
        field_simp [hy] at hr2'
        ring_nf at hr2'
        nlinarith [hr2']
      have hux : u^2 - y^2 = 2*x*u :=
        doubleLeg_u_sq_sub_y_sq (x := x) (y := y) (h := h) (u := u) hu_def hh
      have hmul : (2*u) * x = 0 := by
        nlinarith [hu2, hux]
      have h2u : (2*u) ≠ 0 := by
        exact mul_ne_zero (by norm_num) hu
      exact (mul_eq_zero.mp hmul).resolve_left h2u

end MazurProof.RationalPointsN12
```

## If `field_simp` is fragile in your local Mathlib

The only delicate block is:

```lean
have hquartic_eq : s^2 = r^4 - r^2 + 1 := by
  have hy2_ne : y^2 ≠ 0 := pow_ne_zero 2 hy
  dsimp [r, s]
  field_simp [hy, hy2_ne]
  ring_nf at hnum ⊢
  nlinarith [hnum]
```

A robust fallback is to keep `doubleLeg_quartic_num` exactly as above and replace the block by an explicitly denominator-cleared helper lemma:

```lean
private lemma doubleLeg_quartic_of_num
    {y k u : ℚ}
    (hy : y ≠ 0)
    (hnum : k^2 * u^2 = u^4 - u^2*y^2 + y^4) :
    (k*u / y^2)^2 = (u/y)^4 - (u/y)^2 + 1 := by
  have hy2_ne : y^2 ≠ 0 := pow_ne_zero 2 hy
  field_simp [hy, hy2_ne]
  ring_nf at hnum ⊢
  nlinarith [hnum]
```

Then in the theorem use:

```lean
have hquartic_eq : s^2 = r^4 - r^2 + 1 := by
  simpa [r, s] using doubleLeg_quartic_of_num (y := y) (k := k) (u := u) hy hnum
```

This fallback is also no-`sorry` and keeps the division proof isolated from the main theorem.
