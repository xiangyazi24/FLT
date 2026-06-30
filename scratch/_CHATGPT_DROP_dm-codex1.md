# Q2383 (dm-codex1): adversarial audit of the four residual full-2-cover equations

This drop replaces the Q2378 `coverQ_*` axiom stubs by a sharper boundary.

Bottom line:

* The four Q2378 classifications are **not** consequences of `ring`, `nlinarith`, or order facts alone.
* I do **not** see a rational counterexample to the stated `T != 0` versions.  The statements are true over `Q`, but two different classical descent inputs are needed.
* The two nonzero covers reduce exactly to Fermat's theorem that there are no four distinct rational squares in arithmetic progression.
* The two degenerate torsion covers reduce exactly to the classical double-leg right-triangle obstruction, equivalently a Ljunggren/Pocklington/Eisenstein quartic descent.
* There is no hidden squareclass/product/primitive condition missing for these four residuals, except that `T != 0` is essential for the `(1,1,1)` conclusion `B = 0`.

The finite local-congruence machinery from Q2378 should **not** try to kill these four covers: each has rational points.  What remains here is genuinely global arithmetic descent, not local solubility.

---

## Definitions

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

namespace FLT.Mazur.N12.ResidualCovers

/-- Rational full-2-cover equations for fixed squareclass representatives. -/
def CoverQ (d0 d1 d3 : Int) (A B C T : ℚ) : Prop :=
  ((d0 : ℚ) * A^2 - (d1 : ℚ) * B^2 = T^2) ∧
  ((d3 : ℚ) * C^2 - (d0 : ℚ) * A^2 = (3 : ℚ) * T^2)

end FLT.Mazur.N12.ResidualCovers
```

---

## Required global arithmetic inputs

These are the two honest residual descent facts.  Everything after them is just algebra.

### A. Fermat four-rational-squares-in-AP theorem

Use this for `(3,2,6)` and `(-1,-2,2)`.

```lean
namespace FLT.Mazur.N12.ResidualCovers

/-- Fermat: four rational squares in arithmetic progression are constant.

Equivalently, there is no nonconstant arithmetic progression

  w^2, x^2, y^2, z^2

over `ℚ`.

This is a genuine infinite descent theorem.  A standard Lean route is:
clear denominators to primitive integers, reduce to Fermat's theorem that four
integer squares cannot form a nonconstant AP, then divide back.
-/
theorem four_rat_squares_AP_const
    {w x y z : ℚ}
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2) :
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2 := by
  -- descent theorem, not `ring`/`nlinarith`
  sorry

end FLT.Mazur.N12.ResidualCovers
```

A lower-level integer theorem, if preferred, is:

```lean
/-- Integer Fermat AP theorem, primitive or nonprimitive version. -/
theorem int_four_squares_AP_const
    {w x y z : ℤ}
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2) :
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2 := by
  sorry
```

The rational version follows by writing all four rationals over a common positive denominator `D`, multiplying by `D^2`, and applying the integer theorem.

### B. Double-leg right-triangle obstruction

Use this for `(1,1,1)` and `(-3,-1,3)`.

```lean
namespace FLT.Mazur.N12.ResidualCovers

/-- Fermat/Ljunggren/Pocklington double-leg obstruction.

There are no nondegenerate rational right triangles sharing one leg `y` while
the other leg is doubled from `x` to `2*x`:

  h^2 = x^2 + y^2,
  k^2 = (2*x)^2 + y^2.

Therefore one of the legs is zero.

This is equivalent to the classical homogeneous Ljunggren/Pocklington quartic

  W^2 = U^4 + 14 U^2 V^2 + V^4

having only the diagonal solutions `U^2 = V^2`; it is also obtained from the
Eisenstein quartic

  Z^2 = u^4 - u^2 v^2 + v^4

by parametrizing the first Pythagorean triangle.
-/
theorem rat_double_leg_right_triangles_degenerate
    {x y h k : ℚ}
    (h1 : h^2 = x^2 + y^2)
    (h2 : k^2 = (2*x)^2 + y^2) :
    x = 0 ∨ y = 0 := by
  -- descent theorem, not `ring`/`nlinarith`
  sorry

end FLT.Mazur.N12.ResidualCovers
```

A useful exact reduction to the Eisenstein quartic is this:

```text
Assume h^2 = x^2 + y^2.
Parametrize the rational right triangle, after clearing denominators, as

  x = λ * (u^2 - v^2),
  y = λ * (2*u*v),
  h = λ * (u^2 + v^2).

Then k^2 = (2*x)^2 + y^2 gives

  (k / (2*λ))^2 = u^4 - u^2*v^2 + v^4.

The Ljunggren/Eisenstein theorem

  z^2 = u^4 - u^2*v^2 + v^4
  -> u = 0 ∨ v = 0 ∨ u^2 = v^2

implies `y = 0` in the first two cases and `x = 0` in the third case.
```

So if the repository already has the Eisenstein quartic theorem from the N=12 route, prove `rat_double_leg_right_triangles_degenerate` once and reuse it for both degenerate covers.

A direct homogeneous coefficient-14 interface is also clean:

```lean
/-- Homogeneous Ljunggren/Pocklington form. -/
theorem rat_ljunggren_14_diagonal
    {U V W : ℚ}
    (h : W^2 = U^4 + 14*U^2*V^2 + V^4) :
    U^2 = V^2 := by
  sorry
```

Then set `U = h + y`, `V = x`, or use the standard unit-circle parametrization; either way it gives the double-leg obstruction.  I recommend the double-leg theorem as the Lean-facing interface because the cover proofs below become one-line algebra after it.

---

## Residual 1: `(3,2,6)`

Cover equations:

```text
3*A^2 - 2*B^2 = T^2
6*C^2 - 3*A^2 = 3*T^2
```

The second equation is equivalent to

```text
2*C^2 - A^2 = T^2.
```

Then the four squares

```text
B^2, A^2, C^2, T^2
```

are in arithmetic progression:

```text
A^2 - B^2 = C^2 - A^2,
C^2 - A^2 = T^2 - C^2.
```

By Fermat four-squares AP, the progression is constant, so

```text
A^2 = B^2 = C^2 = T^2.
```

Lean wrapper:

```lean
namespace FLT.Mazur.N12.ResidualCovers

theorem coverQ_3_2_6_from_fourSquaresAP
    {A B C T : ℚ}
    (h : CoverQ 3 2 6 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have h2' : 2*C^2 - A^2 = T^2 := by
    nlinarith
  have hap1 : A^2 - B^2 = C^2 - A^2 := by
    nlinarith [h1, h2']
  have hap2 : C^2 - A^2 = T^2 - C^2 := by
    nlinarith [h2']
  have hAP := four_rat_squares_AP_const
    (w := B) (x := A) (y := C) (z := T) hap1 hap2
  rcases hAP with ⟨hBA, hAC, hCT⟩
  constructor
  · nlinarith [hAC, hCT]
  constructor
  · nlinarith [hBA, hAC, hCT]
  · nlinarith [hCT]

end FLT.Mazur.N12.ResidualCovers
```

This classification is true from the two equations over `Q`, but only through the AP descent theorem.  It is not a `ring` consequence.

---

## Residual 2: `(-1,-2,2)`

Cover equations:

```text
-A^2 + 2*B^2 = T^2
2*C^2 + A^2 = 3*T^2
```

The four squares

```text
A^2, B^2, T^2, C^2
```

are in arithmetic progression:

```text
B^2 - A^2 = T^2 - B^2,
T^2 - B^2 = C^2 - T^2.
```

By Fermat four-squares AP, the progression is constant, so

```text
A^2 = B^2 = T^2 = C^2.
```

Lean wrapper:

```lean
namespace FLT.Mazur.N12.ResidualCovers

theorem coverQ_neg1_neg2_2_from_fourSquaresAP
    {A B C T : ℚ}
    (h : CoverQ (-1) (-2) 2 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hap1 : B^2 - A^2 = T^2 - B^2 := by
    nlinarith [h1]
  have hap2 : T^2 - B^2 = C^2 - T^2 := by
    nlinarith [h1, h2]
  have hAP := four_rat_squares_AP_const
    (w := A) (x := B) (y := T) (z := C) hap1 hap2
  rcases hAP with ⟨hAB, hBT, hTC⟩
  constructor
  · nlinarith [hAB, hBT]
  constructor
  · exact hBT
  · nlinarith [hTC]

end FLT.Mazur.N12.ResidualCovers
```

Again, this is true from the two equations over `Q`, but the nontrivial ingredient is the global AP descent theorem.

---

## Residual 3: `(1,1,1)`

Cover equations:

```text
A^2 - B^2 = T^2
C^2 - A^2 = 3*T^2
```

Equivalently,

```text
A^2 = T^2 + B^2,
C^2 = (2*T)^2 + B^2.
```

Thus there are two rational right triangles sharing the leg `B`, with the other leg doubled from `T` to `2*T`.  The double-leg theorem gives

```text
T = 0 ∨ B = 0.
```

The residual cover theorem assumes `T != 0`, hence `B = 0`.  Then the equations immediately give

```text
A^2 = T^2,
C^2 = 4*T^2.
```

Lean wrapper:

```lean
namespace FLT.Mazur.N12.ResidualCovers

theorem coverQ_1_1_1_from_doubleLeg
    {A B C T : ℚ}
    (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) :
    B = 0 ∧ A^2 = T^2 ∧ C^2 = (4 : ℚ) * T^2 := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : A^2 = T^2 + B^2 := by
    nlinarith [h1]
  have hpy2 : C^2 = (2*T)^2 + B^2 := by
    nlinarith [h1, h2]
  have hdeg := rat_double_leg_right_triangles_degenerate
    (x := T) (y := B) (h := A) (k := C) hpy1 hpy2
  rcases hdeg with hTzero | hBzero
  · exact (hT hTzero).elim
  · have hA : A^2 = T^2 := by
      nlinarith [h1, hBzero]
    have hC : C^2 = (4 : ℚ) * T^2 := by
      nlinarith [h2, hA]
    exact ⟨hBzero, hA, hC⟩

end FLT.Mazur.N12.ResidualCovers
```

Important adversarial note: the assumption `T != 0` is essential here.  If it is dropped, the claimed conclusion `B = 0` is false.  For example,

```text
A = 1, B = 1, C = 1, T = 0
```

satisfies

```text
A^2 - B^2 = T^2,
C^2 - A^2 = 3*T^2,
```

but `B != 0`.

So the Q2378 version with `hT : T != 0` is the correct shape; without `hT`, it is false.

---

## Residual 4: `(-3,-1,3)`

Cover equations:

```text
-3*A^2 + B^2 = T^2
3*C^2 + 3*A^2 = 3*T^2
```

Equivalently,

```text
T^2 = A^2 + C^2,
B^2 = (2*A)^2 + C^2.
```

Thus there are two rational right triangles sharing the leg `C`, with the other leg doubled from `A` to `2*A`.  The double-leg theorem gives

```text
A = 0 ∨ C = 0.
```

If `A = 0`, the equations give

```text
B^2 = T^2,
C^2 = T^2.
```

If `C = 0`, the equations give

```text
A^2 = T^2,
B^2 = 4*T^2.
```

Lean wrapper:

```lean
namespace FLT.Mazur.N12.ResidualCovers

theorem coverQ_neg3_neg1_3_from_doubleLeg
    {A B C T : ℚ}
    (h : CoverQ (-3) (-1) 3 A B C T) :
    (A = 0 ∧ B^2 = T^2 ∧ C^2 = T^2) ∨
    (C = 0 ∧ A^2 = T^2 ∧ B^2 = (4 : ℚ) * T^2) := by
  unfold CoverQ at h
  rcases h with ⟨h1, h2⟩
  norm_num at h1 h2
  have hpy1 : T^2 = A^2 + C^2 := by
    nlinarith [h2]
  have hpy2 : B^2 = (2*A)^2 + C^2 := by
    nlinarith [h1, h2]
  have hdeg := rat_double_leg_right_triangles_degenerate
    (x := A) (y := C) (h := T) (k := B) hpy1 hpy2
  rcases hdeg with hAzero | hCzero
  · left
    have hB : B^2 = T^2 := by
      nlinarith [h1, hAzero]
    have hC : C^2 = T^2 := by
      nlinarith [h2, hAzero]
    exact ⟨hAzero, hB, hC⟩
  · right
    have hA : A^2 = T^2 := by
      nlinarith [h2, hCzero]
    have hB : B^2 = (4 : ℚ) * T^2 := by
      nlinarith [h1, hA]
    exact ⟨hCzero, hA, hB⟩

end FLT.Mazur.N12.ResidualCovers
```

Here `T != 0` is not needed for the logical disjunction, although the original nonzero-cover extraction usually has `T != 0` anyway.

---

## What exactly was too optimistic in Q2378?

The Q2378 residual theorem statements were not false as `Q`-theorems, but labeling them as if they were small algebraic consequences was too optimistic.

Correct classification of residual difficulty:

| triple | Q2378 classification | true from equations over `Q`? | proof input needed |
|---:|---|---:|---|
| `(3,2,6)` | `A^2=B^2=C^2=T^2` | yes | Fermat no four rational squares in AP |
| `(-1,-2,2)` | `A^2=B^2=C^2=T^2` | yes | Fermat no four rational squares in AP |
| `(1,1,1)` | `B=0`, `A^2=T^2`, `C^2=4T^2`, assuming `T!=0` | yes | double-leg / Ljunggren quartic descent; `T!=0` essential |
| `(-3,-1,3)` | `A=0` or `C=0` branches | yes | double-leg / Ljunggren quartic descent |

So these four covers are not finite local checks.  They are exactly where the remaining global arithmetic lives.

---

## Recommended Lean replacement boundary

Do **not** keep four opaque `coverQ_*` axioms.  Replace them by two reusable arithmetic frontiers plus four algebraic wrappers:

```lean
namespace FLT.Mazur.N12.ResidualCovers

-- Global descent frontier 1.
theorem four_rat_squares_AP_const
    {w x y z : ℚ}
    (h1 : x^2 - w^2 = y^2 - x^2)
    (h2 : y^2 - x^2 = z^2 - y^2) :
    w^2 = x^2 ∧ x^2 = y^2 ∧ y^2 = z^2 := by
  sorry

-- Global descent frontier 2.
theorem rat_double_leg_right_triangles_degenerate
    {x y h k : ℚ}
    (h1 : h^2 = x^2 + y^2)
    (h2 : k^2 = (2*x)^2 + y^2) :
    x = 0 ∨ y = 0 := by
  sorry

-- Algebraic wrappers from the two frontiers.
theorem coverQ_3_2_6_from_fourSquaresAP
    {A B C T : ℚ}
    (h : CoverQ 3 2 6 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2 := by
  -- wrapper above
  sorry

theorem coverQ_neg1_neg2_2_from_fourSquaresAP
    {A B C T : ℚ}
    (h : CoverQ (-1) (-2) 2 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2 := by
  -- wrapper above
  sorry

theorem coverQ_1_1_1_from_doubleLeg
    {A B C T : ℚ}
    (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) :
    B = 0 ∧ A^2 = T^2 ∧ C^2 = (4 : ℚ) * T^2 := by
  -- wrapper above
  sorry

theorem coverQ_neg3_neg1_3_from_doubleLeg
    {A B C T : ℚ}
    (h : CoverQ (-3) (-1) 3 A B C T) :
    (A = 0 ∧ B^2 = T^2 ∧ C^2 = T^2) ∨
    (C = 0 ∧ A^2 = T^2 ∧ B^2 = (4 : ℚ) * T^2) := by
  -- wrapper above
  sorry

end FLT.Mazur.N12.ResidualCovers
```

This is the honest Lean-checkable boundary:

* prove the two global descent frontiers once;
* close all four residual `CoverQ` classifications by `nlinarith` wrappers;
* no elliptic-curve group API is required for these four residuals.

I did not run Lean in this connector-only drop, so the wrapper code should be treated as a precise skeleton.  The identities and theorem dependencies above are the important part; small syntactic adjustments may be needed around `norm_num at h1 h2` and power normalization in the actual repository file.
