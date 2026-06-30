# Q2299 (dm-codex2): QuarticA to Eisenstein/Ljunggren residual

## Bottom line

For `QuarticA`, the safe target is the Eisenstein/Ljunggren residual

```lean
∃ m n c : ℤ,
  m * n ≠ 0 ∧ Int.gcd m n = 1 ∧
  c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4
```

not the existing `pythagoreanQuarticRhs` residual.

The exact residual statement is not too strong **provided** the Pythagorean/descent step is isolated as an explicit theorem parameter. The weakest useful interface for that hard step is not the quartic residual itself, but the quadratic Eisenstein parameter statement

```lean
∃ a b : ℤ,
  a * b ≠ 0 ∧ Int.gcd a b = 1 ∧
  a * b = v ^ 2 ∧
  u ^ 2 = a ^ 2 - a * b + b ^ 2
```

because the remaining passage from `a*b = v^2` with `gcd(a,b)=1` to the degree-four residual is an independent coprime-square-product extraction.

The code below adds no axioms and no `sorry`. The hard arithmetic is represented by ordinary theorem parameters:

* `QuarticAParamBridge`: Pythagorean classification, parity split, gcd transfer, and sign-normalized production of the quadratic Eisenstein parameters.
* `CoprimeSquareProductExtraction`: the elementary but sometimes annoying integer extraction from a coprime product equal to a square.

## Lean wrapper code

This is written as a standalone checking file. To paste directly into `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, remove the `import` line and keep the namespace block contents.

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-- Final Ljunggren/Eisenstein quartic residual wanted for `QuarticA`. -/
def EisensteinQuarticResidual : Prop :=
  ∃ m n c : ℤ,
    m * n ≠ 0 ∧ Int.gcd m n = 1 ∧
    c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4

/--
Signed square factors.  This is deliberately sign-tolerant: if `a*b` is a
positive square and `gcd(a,b)=1`, then `a,b` may both be positive squares or
both be negative squares, and either sign gives the same Eisenstein quartic.
-/
def SameSignSquareFactors (a b : ℤ) : Prop :=
  ∃ m n : ℤ,
    m * n ≠ 0 ∧
    Int.gcd m n = 1 ∧
      ((a = m ^ 2 ∧ b = n ^ 2) ∨
       (a = -(m ^ 2) ∧ b = -(n ^ 2)))

/-- The weakest useful residual interface produced by the `QuarticA` descent. -/
def QuarticAEisensteinParam (u v : ℤ) : Prop :=
  ∃ a b : ℤ,
    a * b ≠ 0 ∧
    Int.gcd a b = 1 ∧
    a * b = v ^ 2 ∧
    u ^ 2 = a ^ 2 - a * b + b ^ 2

/--
Pure algebra/sign wrapper: once the quadratic Eisenstein parameter is known and
its coprime square product has been extracted, the quartic residual follows.
-/
theorem eisensteinQuarticResidual_of_param_of_signedSquares
    {u a b : ℤ}
    (hu : u ^ 2 = a ^ 2 - a * b + b ^ 2)
    (hsq : SameSignSquareFactors a b) :
    EisensteinQuarticResidual := by
  rcases hsq with ⟨m, n, hmn0, hmn_coprime, hsign⟩
  refine ⟨m, n, u, hmn0, hmn_coprime, ?_⟩
  rcases hsign with hpos | hneg
  · rcases hpos with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        subst a
        subst b
        ring
  · rcases hneg with ⟨ha, hb⟩
    calc
      u ^ 2 = a ^ 2 - a * b + b ^ 2 := hu
      _ = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
        subst a
        subst b
        ring

/--
The extraction obligation needed after the Pythagorean/descent bridge.  This is
not an axiom here; wrappers take it as a theorem parameter.
-/
def CoprimeSquareProductExtraction : Prop :=
  ∀ {v a b : ℤ},
    a * b ≠ 0 →
    Int.gcd a b = 1 →
    a * b = v ^ 2 →
    SameSignSquareFactors a b

/--
Turn the weakest quadratic Eisenstein interface into the requested quartic
residual, using an explicit coprime-square-product extraction theorem.
-/
theorem eisensteinQuarticResidual_of_eisensteinParam
    {u v : ℤ}
    (hParam : QuarticAEisensteinParam u v)
    (hExtract :
      ∀ {a b : ℤ},
        a * b ≠ 0 →
        Int.gcd a b = 1 →
        a * b = v ^ 2 →
        SameSignSquareFactors a b) :
    EisensteinQuarticResidual := by
  rcases hParam with ⟨a, b, hab0, hab_coprime, hab_square, hu⟩
  exact eisensteinQuarticResidual_of_param_of_signedSquares
    hu (hExtract hab0 hab_coprime hab_square)

/--
Ring-only wrapper for the opposite-parity/even-leg Pythagorean classification
output.  In this branch, classification of
`PythagoreanTriple Z (2 * v^2) (u^2 + v^2)` should supply `r*s = v^2` and
`r^2+s^2 = u^2+v^2`.
-/
theorem quarticA_eisensteinParam_from_evenLegParams
    {u v r s : ℤ}
    (hrs0 : r * s ≠ 0)
    (hrs_coprime : Int.gcd r s = 1)
    (hprod : r * s = v ^ 2)
    (hhyp : r ^ 2 + s ^ 2 = u ^ 2 + v ^ 2) :
    QuarticAEisensteinParam u v := by
  refine ⟨r, s, hrs0, hrs_coprime, hprod, ?_⟩
  calc
    u ^ 2 = (u ^ 2 + v ^ 2) - v ^ 2 := by ring
    _ = (r ^ 2 + s ^ 2) - v ^ 2 := by rw [← hhyp]
    _ = r ^ 2 - r * s + s ^ 2 := by
      rw [← hprod]
      ring

/--
Ring-only wrapper for the odd-odd branch.  Here the original Pythagorean triple
is imprimitive by a factor of `2`; after classifying the divided primitive
triple, the odd leg `v^2` should be `(r+s)*(r-s)` and the doubled hypotenuse
identity should be `2*(r^2+s^2)=u^2+v^2`.
-/
theorem quarticA_eisensteinParam_from_oddLegParams
    {u v r s : ℤ}
    (hab0 : (r + s) * (r - s) ≠ 0)
    (hab_coprime : Int.gcd (r + s) (r - s) = 1)
    (hprod : (r + s) * (r - s) = v ^ 2)
    (hhyp : 2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2) :
    QuarticAEisensteinParam u v := by
  refine ⟨r + s, r - s, hab0, hab_coprime, hprod, ?_⟩
  calc
    u ^ 2 = (u ^ 2 + v ^ 2) - v ^ 2 := by ring
    _ = 2 * (r ^ 2 + s ^ 2) - v ^ 2 := by rw [← hhyp]
    _ = (r + s) ^ 2 - (r + s) * (r - s) + (r - s) ^ 2 := by
      rw [← hprod]
      ring

/--
The hard `QuarticA` bridge theorem as an explicit parameter.  This is the place
where Pythagorean classification, parity handling, and gcd transfer belong.
-/
def QuarticAParamBridge : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    QuarticA u v Z →
    QuarticAEisensteinParam u v

/-- Exact requested residual statement, conditional only on explicit theorem parameters. -/
theorem quarticA_to_eisensteinQuarticResidual_of_bridge
    (hBridge : QuarticAParamBridge)
    (hExtract : CoprimeSquareProductExtraction)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    EisensteinQuarticResidual := by
  exact eisensteinQuarticResidual_of_eisensteinParam
    (hBridge hcop huv0 hne hA)
    (fun {a b} hab0 hab_coprime hab_square =>
      hExtract hab0 hab_coprime hab_square)

/-- Same theorem with the existential expanded literally. -/
theorem quarticA_to_eisenstein_residual_statement_of_bridge
    (hBridge : QuarticAParamBridge)
    (hExtract : CoprimeSquareProductExtraction)
    {u v Z : ℤ}
    (hcop : Int.gcd u v = 1)
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    ∃ m n c : ℤ,
      m * n ≠ 0 ∧ Int.gcd m n = 1 ∧
      c ^ 2 = m ^ 4 - m ^ 2 * n ^ 2 + n ^ 4 := by
  exact quarticA_to_eisensteinQuarticResidual_of_bridge
    hBridge hExtract hcop huv0 hne hA

/-- Opposite-parity branch obligation. -/
def QuarticAOppParityParamBridge : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    ((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) →
    QuarticA u v Z →
    QuarticAEisensteinParam u v

/-- Odd-odd branch obligation. -/
def QuarticAOddOddParamBridge : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    u ^ 2 ≠ v ^ 2 →
    Odd u →
    Odd v →
    QuarticA u v Z →
    QuarticAEisensteinParam u v

/--
Parity split obligation for primitive inputs.  It rules out the even-even case;
the remaining cases are opposite parity or odd-odd.
-/
def QuarticAPrimitiveParitySplit : Prop :=
  ∀ {u v Z : ℤ},
    Int.gcd u v = 1 →
    u * v ≠ 0 →
    QuarticA u v Z →
    (((Odd u ∧ Even v) ∨ (Even u ∧ Odd v)) ∨ (Odd u ∧ Odd v))

/-- Compose the two parity branches into the single hard bridge parameter. -/
theorem quarticA_paramBridge_of_parity_cases
    (hParity : QuarticAPrimitiveParitySplit)
    (hOpp : QuarticAOppParityParamBridge)
    (hOddOdd : QuarticAOddOddParamBridge) :
    QuarticAParamBridge := by
  intro u v Z hcop huv0 hne hA
  rcases hParity hcop huv0 hA with hOp | hOo
  · exact hOpp hcop huv0 hne hOp hA
  · exact hOddOdd hcop huv0 hne hOo.1 hOo.2 hA

/--
With the existing positivity helpers, `u^2 ≠ v^2` and `v ≠ 0` imply `Z ≠ 0`.
The `huv0` hypothesis is a convenient way to obtain `v ≠ 0` in the primitive
non-axis wrapper.
-/
theorem quarticA_Z_ne_zero_of_nontrivial
    {u v Z : ℤ}
    (huv0 : u * v ≠ 0)
    (hne : u ^ 2 ≠ v ^ 2)
    (hA : QuarticA u v Z) :
    Z ≠ 0 := by
  have hv0 : v ≠ 0 := by
    intro hv
    exact huv0 (by simp [hv])
  have hleft : 0 < u ^ 2 - v ^ 2 :=
    quarticA_left_factor_pos (u := u) (v := v) (Z := Z) hv0 hne hA
  have hright : 0 < u ^ 2 + 3 * v ^ 2 :=
    quarticA_right_factor_pos (u := u) (v := v) hv0
  have hprod : 0 < (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) :=
    mul_pos hleft hright
  change Z ^ 2 = (u ^ 2 - v ^ 2) * (u ^ 2 + 3 * v ^ 2) at hA
  intro hZ
  exact (ne_of_gt hprod) (by
    simpa [hZ] using hA.symm)

end MazurProof.RationalPointsN12
```

## Proof obligations for `QuarticAParamBridge`

The bridge should prove `QuarticAEisensteinParam u v`.  It should **not** try to produce `pythagoreanQuarticRhs`.

The intended internal split is:

1. **Opposite parity**: classify the primitive triple
   ```lean
   PythagoreanTriple Z (2 * v ^ 2) (u ^ 2 + v ^ 2)
   ```
   from `quarticA_pythagoreanTriple`.  The classification output should be normalized to
   ```lean
   r * s = v ^ 2
   r ^ 2 + s ^ 2 = u ^ 2 + v ^ 2
   Int.gcd r s = 1
   r * s ≠ 0
   ```
   Then `quarticA_eisensteinParam_from_evenLegParams` supplies
   ```lean
   u ^ 2 = r ^ 2 - r * s + s ^ 2
   ```

2. **Odd-odd parity**: the original triple is imprimitive by a factor of `2`.  Prove `Even Z`, classify the divided primitive triple with odd leg `v^2`, and normalize the output to
   ```lean
   (r + s) * (r - s) = v ^ 2
   2 * (r ^ 2 + s ^ 2) = u ^ 2 + v ^ 2
   Int.gcd (r + s) (r - s) = 1
   (r + s) * (r - s) ≠ 0
   ```
   Then `quarticA_eisensteinParam_from_oddLegParams` supplies the same quadratic Eisenstein form.

3. **Coprime square-product extraction**: prove `CoprimeSquareProductExtraction`.  This is the gcd/sign transfer step:
   ```lean
   a * b ≠ 0 → Int.gcd a b = 1 → a * b = v ^ 2 →
   ∃ m n,
     m * n ≠ 0 ∧ Int.gcd m n = 1 ∧
       ((a = m ^ 2 ∧ b = n ^ 2) ∨
        (a = -(m ^ 2) ∧ b = -(n ^ 2)))
   ```
   If your Pythagorean classifier already returns positive parameters, this can be replaced locally by the simpler positive version `a = m^2 ∧ b = n^2`.

## Parity and nontriviality notes

* `u,v` do **not** need to be assumed opposite parity in the final residual interface.  Opposite parity is only the easiest branch, where the original Pythagorean triple is primitive and the even leg is `2*v^2`.
* If `u,v` are both odd, the original triple has a common factor `2`; this is not a reason to map to `pythagoreanQuarticRhs`.  It is the separate odd-leg branch above.
* If you want a smaller first patch, prove only `QuarticAOppParityParamBridge` and keep odd-odd as an explicit remaining obligation.  Do not silently assert opposite parity unless a 2-adic lemma has actually been proved.
* The residual needs a non-axis hypothesis.  Use either `u ^ 2 ≠ v ^ 2` or equivalently `Z ≠ 0` under `QuarticA`.  The wrapper above keeps `u ^ 2 ≠ v ^ 2` because the existing `quarticA_left_factor_pos` helper is already phrased that way.
* `u * v ≠ 0` is also needed: it excludes the axis cases and gives `v ≠ 0`, which is used for positivity and for the final `m*n ≠ 0` residual.
* With `u * v ≠ 0`, `u ^ 2 ≠ v ^ 2`, and `QuarticA u v Z`, the included theorem `quarticA_Z_ne_zero_of_nontrivial` proves `Z ≠ 0` using only the existing positivity helpers.
