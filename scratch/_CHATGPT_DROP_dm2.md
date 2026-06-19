# ChatGPT Drop File (dm2)

## Task

Prove `zphi_descent_step_even_core` for the positive denominator quartic

```text
t² = p⁴ + p²q² - q⁴,
q ≥ 2,
2 ∣ q,
gcd(p,q)=1.
```

The proposed shortcut was:

```text
q = 2r.
Apply the general descent step to get a smaller q'.
If q' is still even, repeat. Eventually q' becomes odd.
```

## Key correction

That shortcut is valid only **after** the general descent theorem has already been proved.  It cannot be used as a sublemma in the proof of the general descent theorem, because it is circular.

There are two separate issues.

### 1. Replacing `q` by `r` does not preserve the equation

If `q = 2r`, then the equation is

```text
t² = p⁴ + p²(2r)² - (2r)⁴
   = p⁴ + 4p²r² - 16r⁴.
```

This is **not** the same as

```text
t² = p⁴ + p²r² - r⁴.
```

So one cannot simply call the odd theorem, or the induction hypothesis, on `(p,r,t)`.

### 2. Calling `zphi_descent_step` on `(p,q,t)` is circular

The statement of `zphi_descent_step` is already:

```text
from a solution with denominator q, produce a solution with smaller denominator q'.
```

So an even-core proof of the form

```lean
exact zphi_descent_step p q t hq hcop h
```

is only a wrapper around the already-proved theorem.  It cannot be one of the ingredients used to prove that theorem.

## What is the valid short Lean proof?

If the general theorem is already available, then the even-core theorem is indeed short.  The evenness hypothesis is unused.

```lean
import Mathlib

namespace DenominatorQuartic

/-- The positive denominator quartic. -/
def PosQuartic (p q t : ℤ) : Prop :=
  t ^ 2 = p ^ 4 + p ^ 2 * q ^ 2 - q ^ 4

/-- The smaller-solution output used by descent. -/
def SmallerSolution (p q t p' q' t' : ℤ) : Prop :=
  2 ≤ q' ∧
  Int.gcd p' q' = 1 ∧
  PosQuartic p' q' t' ∧
  q'.natAbs < q.natAbs

/--
The already-proved general descent step.

This is intentionally an axiom here only to show the exact dependency of the
short even-core wrapper.  In the real development this should be the theorem
proved from the odd and even Pellian factor-split arguments.
-/
axiom zphi_descent_step (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : PosQuartic p q t) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t'

/--
Even denominator wrapper.

This theorem is valid only downstream of the general descent step.  It is not a
valid upstream proof of the even branch, because it calls the theorem it would be
used to prove.
-/
theorem zphi_descent_step_even_core (p q t : ℤ)
    (hq : 2 ≤ q)
    (_hq_even : (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : PosQuartic p q t) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  exact zphi_descent_step p q t hq hcop h

end DenominatorQuartic
```

## What is needed for a non-circular even-core proof?

A genuine even-core proof must construct a smaller denominator solution **before** invoking induction.  The correct theorem boundary is therefore not

```text
q = 2r, then call the general descent step.
```

It must be something like:

```lean
theorem even_pellian_factor_split_and_descent (p q t : ℤ)
    (hq : 2 ≤ q)
    (hq_even : (2 : ℤ) ∣ q)
    (hcop : Int.gcd p q = 1)
    (h : PosQuartic p q t) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  -- Must actually construct `(p',q',t')` from the even Pellian factorization.
  -- This is the non-circular hard part.
  sorry
```

Then the general descent step can split on parity:

```lean
theorem zphi_descent_step_from_cores
    (odd_core : ∀ p q t : ℤ,
      2 ≤ q → ¬ (2 : ℤ) ∣ q → Int.gcd p q = 1 → PosQuartic p q t →
      ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t')
    (even_core : ∀ p q t : ℤ,
      2 ≤ q → (2 : ℤ) ∣ q → Int.gcd p q = 1 → PosQuartic p q t →
      ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t')
    (p q t : ℤ)
    (hq : 2 ≤ q)
    (hcop : Int.gcd p q = 1)
    (h : PosQuartic p q t) :
    ∃ p' q' t' : ℤ, SmallerSolution p q t p' q' t' := by
  by_cases hq_even : (2 : ℤ) ∣ q
  · exact even_core p q t hq hq_even hcop h
  · exact odd_core p q t hq hq_even hcop h
```

## Bottom line

The short proof

```lean
exact zphi_descent_step p q t hq hcop h
```

is a correct Lean wrapper **only if** `zphi_descent_step` is already available.  It is not a proof of the even branch for use inside `zphi_descent_step`.

To prove the general theorem by strong induction, the even branch still needs its own non-circular construction of a smaller solution from the even Pellian factorization.  Factoring `q = 2r` alone does not provide such a solution, because the quartic equation is not preserved when replacing `q` by `r`.
