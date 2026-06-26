# Q813 (dm1): the `Ψ₃ = 0` stratum and the even cofactor

## Recommendation

Do **not** try to get

```text
β² δ - α γ² ≠ 0
```

from the weak facts

```text
preΨ(j)(x) = 0 ↔ 3 ∣ j
```

and individual nonvanishing of `α, β, γ, δ`.  That is not enough: two nonzero monomials can still cancel.

Also, the plain Somos-style relation is not quite the right tool for Mathlib's **reduced** sequence `preΨ`.  The reduced sequence has parity-dependent `Ψ₂Sq²` factors in its recurrence.  The useful move is instead to specialize the whole reduced EDS recurrence to the `Ψ₃ = 0` stratum.  On that stratum there is an extra curve-specific identity:

```text
preΨ₄ = - Ψ₂Sq².
```

With that identity, the cofactor is not merely nonzero; it is an explicit monomial times `2`.

## The key polynomial identity

In `DivisionPolynomial/Basic.lean`, the relevant initial values are

```lean
preΨ' 1 = 1
preΨ' 2 = 1
preΨ' 3 = Ψ₃
preΨ' 4 = preΨ₄
```

and the reduced EDS parameter is `Ψ₂Sq²`.

The missing identity to prove is:

```lean
lemma preΨ₄_add_Ψ₂Sq_sq (W : WeierstrassCurve K) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 =
      (6 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, Ψ₃, b₂, b₄, b₆, b₈]
  ring1
```

The exact Lean syntax may need minor coercion polishing, for example `C (6 : K) * X ^ 2`, but mathematically the identity is exactly

```text
preΨ₄ + Ψ₂Sq² = (6X² + b₂X + b₄) Ψ₃.
```

So if `x` is on the `Ψ₃ = 0` stratum, and

```text
S := Ψ₂Sq(x),
B := S²,
D := preΨ₄(x),
```

then

```text
D = -B.
```

This is the fact that prevents cancellation in the cofactor.

## Specialized reduced EDS on the `Ψ₃ = 0` stratum

Let

```text
A_j := preΨ'(j)(x).
```

Using the map lemma for `preNormEDS'`, the specialization is

```text
A_j = preNormEDS' B 0 (-B) j,
```

where

```text
B = Ψ₂Sq(x)².
```

The specialized sequence has the following six-term pattern:

```text
A_{6t}     = 0
A_{6t+1}   =  B^(3t² + t)
A_{6t+2}   =  B^(3t² + 2t)
A_{6t+3}   = 0
A_{6t+4}   = -B^(3t² + 4t + 1)
A_{6t+5}   = -B^(3t² + 5t + 2)
```

Equivalently,

```text
A_{3q}   = 0,
A_{3q+1} = (-1)^q B^(q(q+1)/2 + floor(q²/4)),
A_{3q+2} = (-1)^q B^(q(q+1)/2 + floor((q+1)²/4)).
```

For Lean, the six-residue-class version is probably easier than the floor-division version.

This pattern follows directly from the two reduced EDS recurrences in Mathlib:

```lean
preΨ'_even :
  preΨ' (2 * (m + 3)) =
    preΨ' (m + 2)^2 * preΨ' (m + 3) * preΨ' (m + 5)
      - preΨ' (m + 1) * preΨ' (m + 3) * preΨ' (m + 4)^2

preΨ'_odd :
  preΨ' (2 * (m + 2) + 1) =
    preΨ' (m + 4) * preΨ' (m + 2)^3 * (if Even m then Ψ₂Sq² else 1)
      - preΨ' (m + 1) * preΨ' (m + 3)^3 * (if Even m then 1 else Ψ₂Sq²)
```

After evaluation at `x`, these become the recurrences for `preNormEDS' B 0 (-B)`.

## The cofactor computation

Your even case has

```text
n = 2 * (m + 3)
A_{m+3} = 0.
```

On the `Ψ₃ = 0` stratum, the divisibility/zero pattern gives

```text
3 ∣ m + 3.
```

Since `m : ℕ`, this means

```text
m = 3r
```

for some `r : ℕ`.  Then

```text
α = A_{m+1} = A_{3r+1}
β = A_{m+2} = A_{3r+2}
γ = A_{m+4} = A_{3r+4}
δ = A_{m+5} = A_{3r+5}.
```

Now split on the parity of `r`.

### Case 1: `r = 2t`

Using the six-term pattern:

```text
α =  B^(3t² + t)
β =  B^(3t² + 2t)
γ = -B^(3t² + 4t + 1)
δ = -B^(3t² + 5t + 2)
```

Therefore

```text
β²δ - αγ²
  = -B^(2(3t²+2t) + (3t²+5t+2))
    - B^((3t²+t) + 2(3t²+4t+1))
  = -2 * B^(9t² + 9t + 2).
```

### Case 2: `r = 2t + 1`

Then

```text
α = -B^(3t² + 4t + 1)
β = -B^(3t² + 5t + 2)
γ =  B^(3t² + 7t + 4)
δ =  B^(3t² + 8t + 5)
```

and hence

```text
β²δ - αγ²
  = B^(2(3t²+5t+2) + (3t²+8t+5))
    + B^((3t²+4t+1) + 2(3t²+7t+4))
  = 2 * B^(9t² + 18t + 9).
```

So in all cases the cofactor is

```text
β²δ - αγ² = ± 2 * B^N
```

for an explicit natural exponent `N`.  In the compact `q = (m+3)/3` notation:

```text
β²δ - αγ² = (-1)^q * 2 * B^floor(9q² / 4).
```

Here `B = Ψ₂Sq(x)²`.

## Nonvanishing hypotheses needed

The final nonvanishing is now immediate under the separability hypotheses you should already have:

```text
2 ≠ 0
Ψ₂Sq(x) ≠ 0
```

because then

```text
B = Ψ₂Sq(x)² ≠ 0,
B^N ≠ 0,
±2 * B^N ≠ 0.
```

In a field this is just `mul_ne_zero`, `pow_ne_zero`, and `neg_ne_zero`.

The hypothesis `Ψ₂Sq(x) ≠ 0` is geometrically: a `3`-torsion point is not also `2`-torsion.  Algebraically, it is the statement that `Ψ₃` and `Ψ₂Sq` have no common root on a nonsingular curve, under the characteristic assumptions in the separability theorem.  If your global assumptions include `Nat.Prime p`, `p ∤ n`, or `NeZero (n : K)`, then in this even branch with `3 ∣ m+3` and `n = 2(m+3)`, you should in particular have `2 ≠ 0`; usually you also exclude the bad common-root case by the nonsingularity/discriminant hypothesis.

## Why the simple Somos argument is insufficient

The relation you wrote is too weak for this goal.  Even if some Somos relation gives a product equality among neighboring nonzero terms, it does not by itself rule out cancellation in

```text
β²δ - αγ².
```

For example, in the abstract specialized recurrence with only `A₃ = 0`, if one treats

```text
B = Ψ₂Sq(x)²,
D = preΨ₄(x)
```

as unrelated nonzero parameters, then already for `m = 0`:

```text
α = A₁ = 1,
β = A₂ = 1,
γ = A₄ = D,
δ = A₅ = B D,
```

so

```text
β²δ - αγ² = B D - D² = D(B - D),
```

which can vanish with all four of `α, β, γ, δ` nonzero.

The actual division-polynomial stratum avoids this because `D = -B`, not because the zero pattern alone is strong enough.  With `D = -B`, the same base case becomes

```text
β²δ - αγ² = -2B².
```

That is the whole mechanism.

## Lean implementation route

I would close this sub-sorry with three small local lemmas.

### 1. The stratum identity

```lean
lemma preΨ₄_add_Ψ₂Sq_sq (W : WeierstrassCurve K) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 =
      (6 * X ^ 2 + C W.b₂ * X + C W.b₄) * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, Ψ₃, b₂, b₄, b₆, b₈]
  ring1
```

Then derive, after evaluation at `x`:

```lean
have hD : W.preΨ₄.eval x = - (W.Ψ₂Sq.eval x)^2 := by
  have h := congrArg (fun f : K[X] => f.eval x) (preΨ₄_add_Ψ₂Sq_sq W)
  -- simp [Polynomial.eval_mul, Polynomial.eval_add, hΨ₃] at h
  -- exact rearranged h
```

### 2. The specialized sequence formula

Define locally:

```lean
def A (B : K) (j : ℕ) : K :=
  preNormEDS' B 0 (-B) j
```

Prove the six residue formulas:

```lean
A B (6*t)     = 0
A B (6*t+1)   =  B^(3*t^2 + t)
A B (6*t+2)   =  B^(3*t^2 + 2*t)
A B (6*t+3)   = 0
A B (6*t+4)   = -B^(3*t^2 + 4*t + 1)
A B (6*t+5)   = -B^(3*t^2 + 5*t + 2)
```

Use `normEDSRec'` or strong induction over the recurrences.  Each recurrence branch is just `simp [preNormEDS'_even, preNormEDS'_odd]` followed by parity splitting and `ring_nf`/`ring1` for exponents.

This is more Lean-friendly than using `floor(9q²/4)`.

### 3. The cofactor lemma

State the exact nonzero lemma in the form that matches your branch:

```lean
lemma cofactor_ne_zero_three_stratum
    {B : K} (hB : B ≠ 0) (h2 : (2 : K) ≠ 0) (r : ℕ) :
    let A := fun j => preNormEDS' B 0 (-B) j
    A (3*r + 2)^2 * A (3*r + 5)
      - A (3*r + 1) * A (3*r + 4)^2 ≠ 0 := by
  -- split `r` as `2*t` or `2*t+1`
  -- rewrite the six residue formulas
  -- case r = 2*t: expression is `-2 * B^(9*t^2 + 9*t + 2)`
  -- case r = 2*t+1: expression is `2 * B^(9*t^2 + 18*t + 9)`
  -- finish by `mul_ne_zero h2 (pow_ne_zero _ hB)` and sign handling
```

Then connect your actual terms to this lemma using

```lean
B = (W.Ψ₂Sq.eval x)^2,
preΨ'(j)(x) = preNormEDS' B 0 (-B) j,
m = 3*r.
```

That should close exactly the `Ψ₃(x)=0` even-cofactor subcase.
