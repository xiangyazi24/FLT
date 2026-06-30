# Q2345: correct no-solution theorem for the Eisenstein/Ljunggren residual

## Bottom line

The statement

```lean
∀ {m n c : ℤ},
  m * n ≠ 0 →
  Int.gcd m n = 1 →
  c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
  False
```

is **false**.  The primitive diagonal solutions survive:

```lean
import Mathlib

example :
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  refine ⟨1, 1, 1, ?_, ?_, ?_⟩ <;> norm_num

example :
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  refine ⟨1, -1, -1, ?_, ?_, ?_⟩ <;> norm_num
```

So the current residual statement

```lean
∃ m n c : ℤ,
  m * n ≠ 0 ∧
  Int.gcd m n = 1 ∧
  c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4
```

is satisfiable.  It cannot be the final contradiction target.

## Correct classical statement

The classical theorem normally used here is the Ljunggren/Eisenstein quartic classification:

> If integers `m n c` satisfy
> `c^2 = m^4 - m^2*n^2 + n^4`, then the solution is trivial: either
> `m = 0`, or `n = 0`, or `m^2 = n^2`.

Equivalently, in primitive nonzero form, every solution has `m^2 = n^2`; with `Int.gcd m n = 1`, that means `m,n = ±1` and `c = ±1`.

Thus the no-solution theorem becomes correct only after excluding the diagonal case:

```lean
∀ {m n c : ℤ},
  m * n ≠ 0 →
  Int.gcd m n = 1 →
  m ^ 2 ≠ n ^ 2 →
  c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
  False
```

No sign normalization is needed.  No ordering hypothesis such as `|m| > |n|` is needed if the hypothesis is stated as `m ^ 2 ≠ n ^ 2`.  If one wants a positive-natural-number theorem instead, the analogous extra condition is `m ≠ n`, because positivity already removes signs.

Small checks:

```text
(m,n) = (1,0):  RHS = 1,  c = ±1, but m*n = 0.
(m,n) = (0,1):  RHS = 1,  c = ±1, but m*n = 0.
(m,n) = (1,1):  RHS = 1,  c = ±1, primitive nonzero diagonal.
(m,n) = (1,-1): RHS = 1,  c = ±1, primitive nonzero diagonal.
(m,n) = (2,1):  RHS = 13, not a square.
(m,n) = (3,1):  RHS = 73, not a square.
(m,n) = (3,2):  RHS = 61, not a square.
(m,n) = (4,3):  RHS = 193, not a square.
```

The residual curve is the affine part of

```text
Y^2 = X^4 - X^2 + 1,
```

with `X = m/n` and `Y = c/n^2`; the rational points relevant here are the zero, diagonal, and infinity/trivial points.  In homogeneous integer variables this is exactly the classification `m = 0 ∨ n = 0 ∨ m^2 = n^2`.

## Recommended Lean interfaces

I recommend adding the external theorem as a classification, not as a false `¬ residual` theorem.

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Strong classical classification form of the Eisenstein/Ljunggren quartic.
This is the cleanest external theorem to import or assume from a separate file. -/
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

/-- Slightly weaker primitive form, exactly tailored to the residual parameters. -/
def EisensteinQuarticPrimitiveClassification : Prop :=
  ∀ {m n c : ℤ},
    Int.gcd m n = 1 →
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2

/-- Direct no-nondiagonal primitive interface.  This is the most convenient
form for the final contradiction, but it hides the diagonal exceptions in the
hypothesis `m ^ 2 ≠ n ^ 2`. -/
def EisensteinQuarticNoNontrivialPrimitive : Prop :=
  ∀ {m n c : ℤ},
    m * n ≠ 0 →
    Int.gcd m n = 1 →
    m ^ 2 ≠ n ^ 2 →
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    False

/-- Strong classification implies the primitive classification. -/
theorem eisensteinQuarticPrimitiveClassification_of_squareClassification
    (hClass : EisensteinQuarticSquareClassification) :
    EisensteinQuarticPrimitiveClassification := by
  intro m n c _hcop hc
  exact hClass (m := m) (n := n) (c := c) hc

/-- Primitive classification implies the no-nondiagonal primitive interface. -/
theorem eisensteinQuarticNoNontrivialPrimitive_of_primitiveClassification
    (hClass : EisensteinQuarticPrimitiveClassification) :
    EisensteinQuarticNoNontrivialPrimitive := by
  intro m n c hmn0 hcop hdiag hc
  rcases hClass (m := m) (n := n) (c := c) hcop hc with hm0 | hn0 | hsq
  · exact hmn0 (by simp [hm0])
  · exact hmn0 (by simp [hn0])
  · exact hdiag hsq

/-- Strong classification also implies the no-nondiagonal primitive interface. -/
theorem eisensteinQuarticNoNontrivialPrimitive_of_squareClassification
    (hClass : EisensteinQuarticSquareClassification) :
    EisensteinQuarticNoNontrivialPrimitive := by
  exact
    eisensteinQuarticNoNontrivialPrimitive_of_primitiveClassification
      (eisensteinQuarticPrimitiveClassification_of_squareClassification hClass)

end MazurProof.RationalPointsN12
```

## What must change in the QuarticA residual pipeline

The already assembled theorem

```lean
theorem quarticA_to_eisenstein_residual_statement_checked
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4
```

is not enough for a contradiction, because it is compatible with `m = ±1`, `n = ±1`, `c = ±1`.

You need either:

1. strengthen the residual theorem to include `m ^ 2 ≠ n ^ 2`, or
2. prove a separate project-specific lemma showing that the residual parameters obtained from a nondegenerate `QuarticA` solution cannot be diagonal.

The clean strengthened target is:

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Recommended strengthened residual statement for the QuarticA reduction. -/
def QuarticAToNontrivialEisensteinResidualStatement : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    QuarticA u v Z →
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      m ^ 2 ≠ n ^ 2 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4

/-- Final contradiction wrapper from the correct no-nondiagonal theorem and a
strengthened QuarticA residual reduction. -/
theorem quarticA_no_solution_of_nontrivial_eisenstein_residual
    (hNo : EisensteinQuarticNoNontrivialPrimitive)
    (hResidual : QuarticAToNontrivialEisensteinResidualStatement)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  obtain ⟨m, n, c, hmn0, hmncop, hdiag, hc⟩ :=
    hResidual (u := u) (v := v) (Z := Z) hcop huv0 hne hA
  exact hNo (m := m) (n := n) (c := c) hmn0 hmncop hdiag hc

/-- Same final wrapper if the imported classical theorem is the classification
form rather than the direct no-nondiagonal form. -/
theorem quarticA_no_solution_of_eisensteinQuarticSquareClassification
    (hClass : EisensteinQuarticSquareClassification)
    (hResidual : QuarticAToNontrivialEisensteinResidualStatement)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    False := by
  exact
    quarticA_no_solution_of_nontrivial_eisenstein_residual
      (eisensteinQuarticNoNontrivialPrimitive_of_squareClassification hClass)
      hResidual
      (u := u) (v := v) (Z := Z)
      hcop huv0 hne hA

end MazurProof.RationalPointsN12
```

## Final recommendation

Use this as the external theorem/interface:

```lean
def EisensteinQuarticSquareClassification : Prop :=
  ∀ {m n c : ℤ},
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 →
    m = 0 ∨ n = 0 ∨ m ^ 2 = n ^ 2
```

Then make the QuarticA residual reduction produce a **non-diagonal** residual:

```lean
m ^ 2 ≠ n ^ 2
```

Do **not** add a theorem of type `¬ EisensteinQuarticResidual` if `EisensteinQuarticResidual` is merely the existence of nonzero coprime residual parameters, because that proposition is false: `(m,n,c)=(1,1,1)` is already a witness.
