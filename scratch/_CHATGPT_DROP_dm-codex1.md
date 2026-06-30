# Q2353 (dm-codex1): non-diagonal Eisenstein residual from `u^2 ≠ v^2`

## Bottom line

The proposed strengthened lemma is **true**.  The diagonal case in the residual parameters is incompatible with the input hypothesis

```lean
hne : u ^ 2 ≠ v ^ 2
```

provided the residual parameters came from the same signed-square factors used in the `QuarticAEisensteinParam` equation.

The short mathematical proof is:

* In either signed-square branch, `m ^ 2 = n ^ 2` implies `a = b`.
* If `a = b`, then
  ```text
  a^2 - a*b + b^2 = a*b.
  ```
* Therefore `hu : u^2 = a^2 - a*b + b^2` and `hab_square : a*b = v^2` imply `u^2 = v^2`, contradicting `hne`.

So the existing construction that chooses `c = u` and takes `m,n` from `SameSignSquareFactors a b` does produce a **non-diagonal** Eisenstein residual when it is fed the nondegeneracy hypothesis `u ^ 2 ≠ v ^ 2`.

I could not fetch `FLT/Assumptions/MazurProof/RationalPointsN12.lean` from either `main` or `scratch` through the connector, so the code below is written against the signatures in the prompt.  If pasting directly inside `RationalPointsN12.lean`, omit the self-import line.

## Core drop-in code

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- The strengthened residual target: primitive nonzero and non-diagonal. -/
def NontrivialEisensteinQuarticResidual : Prop :=
  ∃ m n c : ℤ,
    m * n ≠ 0 ∧ Int.gcd m n = 1 ∧ m ^ 2 ≠ n ^ 2 ∧
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4

/-- In either signed-square branch, diagonal squares force the two factors equal. -/
private theorem sameSignSquareFactors_eq_of_diag
    {a b m n : ℤ}
    (hdiag : m ^ 2 = n ^ 2)
    (hsign :
      (a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2))) :
    a = b := by
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨ha, hb⟩
    rw [ha, hb, hdiag]
  · rcases hneg with ⟨ha, hb⟩
    rw [ha, hb, hdiag]

/-- If the two factors are equal, the Eisenstein norm expression collapses to `a*b`. -/
private theorem square_eq_of_param_of_ab_eq
    {u v a b : ℤ}
    (hab_eq : a = b)
    (hab_square : a * b = v ^ 2)
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2) :
    u ^ 2 = v ^ 2 := by
  calc
    u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
    _ = a * b := by
      rw [hab_eq]
      ring
    _ = v ^ 2 := hab_square

/--
Lean-friendly form of the requested non-diagonal lemma after the `m,n` witnesses
have been extracted from `SameSignSquareFactors`.

This is the exact contradiction: a diagonal signed-square factorization would
force `u^2 = v^2`.
-/
theorem sameSignSquareFactors_nondiagonal_of_quarticA_ne
    {u v a b m n : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hab_square : a * b = v ^ 2)
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsign :
      (a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2))) :
    m ^ 2 ≠ n ^ 2 := by
  intro hdiag
  have hab_eq : a = b :=
    sameSignSquareFactors_eq_of_diag (a := a) (b := b) hdiag hsign
  have huv : u ^ 2 = v ^ 2 :=
    square_eq_of_param_of_ab_eq
      (u := u) (v := v) (a := a) (b := b)
      hab_eq hab_square hu
  exact hne huv

/--
Version with the original existential `SameSignSquareFactors` input: it returns
the extracted witnesses together with the proved non-diagonal condition.
-/
theorem sameSignSquareFactors_nondiagonal_witnesses_of_quarticA_ne
    {u v a b : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hab_square : a * b = v ^ 2)
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsq : SameSignSquareFactors a b) :
    ∃ m n : ℤ,
      m * n ≠ 0 ∧
      Int.gcd m n = 1 ∧
      m ^ 2 ≠ n ^ 2 ∧
      ((a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2))) := by
  rcases hsq with ⟨m, n, hmn0, hcop, hsign⟩
  refine ⟨m, n, hmn0, hcop, ?_, hsign⟩
  exact sameSignSquareFactors_nondiagonal_of_quarticA_ne
    (u := u) (v := v) (a := a) (b := b) (m := m) (n := n)
    hne hab_square hu hsign

/-- The residual equation obtained from the signed-square factorization. -/
private theorem eisenstein_quartic_eq_of_signedSquares
    {u a b m n : ℤ}
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsign :
      (a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2))) :
    u ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = (m ^ 2) ^ 2 - (m ^ 2) * (n ^ 2) + (n ^ 2) ^ 2 := by
        rw [ha, hb]
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        ring
  · rcases hneg with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = (-(m ^ 2)) ^ 2 - (-(m ^ 2)) * (-(n ^ 2)) + (-(n ^ 2)) ^ 2 := by
        rw [ha, hb]
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        ring

/--
Strengthened residual construction.

Compared with `eisensteinQuarticResidual_of_param_of_signedSquares`, this adds
`m ^ 2 ≠ n ^ 2`, using `hne : u^2 ≠ v^2`.
-/
theorem nontrivialEisensteinQuarticResidual_of_param_of_signedSquares
    {u v a b : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hab_square : a * b = v ^ 2)
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsq : SameSignSquareFactors a b) :
    NontrivialEisensteinQuarticResidual := by
  rcases hsq with ⟨m, n, hmn0, hcop, hsign⟩
  refine ⟨m, n, u, hmn0, hcop, ?_, ?_⟩
  · exact sameSignSquareFactors_nondiagonal_of_quarticA_ne
      (u := u) (v := v) (a := a) (b := b) (m := m) (n := n)
      hne hab_square hu hsign
  · exact eisenstein_quartic_eq_of_signedSquares
      (u := u) (a := a) (b := b) (m := m) (n := n)
      hu hsign

end MazurProof.RationalPointsN12
```

## Wrappers from `QuarticAEisensteinParam`

The wrapper below is intentionally parameterized by the square-factor theorem.  In your file, replace `hFactor` by the existing theorem already used to produce `SameSignSquareFactors a b` from

```lean
a * b ≠ 0, Int.gcd a b = 1, a * b = v ^ 2
```

This keeps the code axiom-free and avoids guessing the local name of that existing factorization lemma.

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Interface for the existing coprime-square-product factorization lemma. -/
def CoprimeSquareProductToSameSignSquareFactors : Prop :=
  ∀ {a b t : ℤ},
    a * b ≠ 0 →
    Int.gcd a b = 1 →
    a * b = t ^ 2 →
    SameSignSquareFactors a b

/-- From a `QuarticAEisensteinParam` and the square-factor lemma to the strengthened residual. -/
theorem nontrivialEisensteinQuarticResidual_of_param
    (hFactor : CoprimeSquareProductToSameSignSquareFactors)
    {u v : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hparam : QuarticAEisensteinParam u v) :
    NontrivialEisensteinQuarticResidual := by
  rcases hparam with ⟨a, b, hab0, hcop, hab_square, hu⟩
  exact nontrivialEisensteinQuarticResidual_of_param_of_signedSquares
    (u := u) (v := v) (a := a) (b := b)
    hne hab_square hu
    (hFactor (a := a) (b := b) (t := v) hab0 hcop hab_square)

end MazurProof.RationalPointsN12
```

If the existing factorization theorem has, for example, the shape

```lean
sameSignSquareFactors_of_coprime_square_product
  {a b t : ℤ} :
  a * b ≠ 0 →
  Int.gcd a b = 1 →
  a * b = t ^ 2 →
  SameSignSquareFactors a b
```

then the non-parameterized wrapper is just:

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

theorem nontrivialEisensteinQuarticResidual_of_param_checked
    {u v : ℤ}
    (hne : u ^ 2 ≠ v ^ 2)
    (hparam : QuarticAEisensteinParam u v) :
    NontrivialEisensteinQuarticResidual := by
  rcases hparam with ⟨a, b, hab0, hcop, hab_square, hu⟩
  exact nontrivialEisensteinQuarticResidual_of_param_of_signedSquares
    (u := u) (v := v) (a := a) (b := b)
    hne hab_square hu
    (sameSignSquareFactors_of_coprime_square_product
      (a := a) (b := b) (t := v) hab0 hcop hab_square)

end MazurProof.RationalPointsN12
```

Only the last theorem name needs adjustment to the actual local factorization theorem name.

## Wrappers from `QuarticAParamBridge_checked`

Assuming the bridge has the expected type

```lean
∀ {u v Z : ℤ},
  Int.gcd u v = 1 →
  u * v ≠ 0 →
  u ^ 2 ≠ v ^ 2 →
  QuarticA u v Z →
  QuarticAEisensteinParam u v
```

or is a theorem of a reducible proposition with this body, the wrapper is:

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- General bridge wrapper, useful if the checked bridge theorem is packaged under another name. -/
theorem nontrivialEisensteinQuarticResidual_of_quarticAParamBridge
    (hFactor : CoprimeSquareProductToSameSignSquareFactors)
    (hBridge :
      ∀ {u v Z : ℤ},
        Int.gcd u v = 1 →
        u * v ≠ 0 →
        u ^ 2 ≠ v ^ 2 →
        QuarticA u v Z →
        QuarticAEisensteinParam u v)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    NontrivialEisensteinQuarticResidual := by
  exact nontrivialEisensteinQuarticResidual_of_param
    hFactor hne (hBridge hcop huv0 hne hA)

/-- Checked bridge wrapper. -/
theorem nontrivialEisensteinQuarticResidual_of_QuarticAParamBridge_checked
    (hFactor : CoprimeSquareProductToSameSignSquareFactors)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    NontrivialEisensteinQuarticResidual := by
  exact nontrivialEisensteinQuarticResidual_of_quarticAParamBridge
    hFactor
    (fun {u v Z : ℤ} hcop huv0 hne hA =>
      QuarticAParamBridge_checked
        (u := u) (v := v) (Z := Z) hcop huv0 hne hA)
    hcop huv0 hne hA

/-- Proposition version matching the earlier residual-statement style. -/
def QuarticAToNontrivialEisensteinResidualStatement : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    QuarticA u v Z →
    NontrivialEisensteinQuarticResidual

/-- Checked statement wrapper. -/
theorem quarticA_to_nontrivial_eisenstein_residual_statement_checked
    (hFactor : CoprimeSquareProductToSameSignSquareFactors) :
    QuarticAToNontrivialEisensteinResidualStatement := by
  intro u v Z hcop huv0 hne hA
  exact nontrivialEisensteinQuarticResidual_of_QuarticAParamBridge_checked
    hFactor hcop huv0 hne hA

end MazurProof.RationalPointsN12
```

After substituting the local square-factor theorem for `hFactor`, the final theorem becomes a direct replacement for the old residual statement, but with the necessary extra conjunct:

```lean
m ^ 2 ≠ n ^ 2
```

## Why this fixes the false residual contradiction

The naive proposition

```lean
∃ m n c : ℤ,
  m * n ≠ 0 ∧
  Int.gcd m n = 1 ∧
  c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4
```

is false as a contradiction target because diagonal witnesses such as `(m,n,c) = (1,1,1)` exist.

The construction from a nondegenerate `QuarticAEisensteinParam` solution, however, cannot land on those diagonal witnesses: if it did, the signed-square factors would have `a = b`, and the defining norm equation would collapse to `u ^ 2 = a*b = v ^ 2`, contradicting `hne`.

Thus the correct strengthened pipeline is:

```text
QuarticA + primitive/nonzero/nondegenerate
  → QuarticAEisensteinParam u v
  → signed-square factors a,b
  → NontrivialEisensteinQuarticResidual
```

where “nontrivial” means exactly `m ^ 2 ≠ n ^ 2` in addition to the old primitive nonzero residual conditions.
