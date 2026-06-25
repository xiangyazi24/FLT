# Q342 (dm4): `Polynomial.discriminant` / discriminant shortcut investigation

## Short answer

For current Mathlib, the practical answer is: **do not plan on closing `preΨ'ₙ` separability through a built-in `Polynomial.discriminant` one-liner.**  The polynomial separability API exposed in Mathlib is centered on

```lean
Polynomial.Separable f  ↔  IsCoprime f f.derivative
```

not on a general discriminant shortcut.

The robust Lean route for a concrete polynomial is therefore a **Bezout/resultant/coprimality certificate**:

```lean
rw [Polynomial.separable_def']
exact ⟨A, B, by ring⟩
```

or equivalently prove `IsCoprime p p.derivative` directly.  This is usually much easier and more reliable than trying to formalize and evaluate a symbolic quartic discriminant.

## Answers to the concrete questions

### (a) Does Mathlib have `Polynomial.discriminant`?

I do not find a current, general-purpose API of the form

```lean
Polynomial.discriminant : R[X] → R
```

that is wired into the separability API.  In particular, I would not write downstream code expecting

```lean
(p.discriminant)
Polynomial.discriminant p
```

to be available and usable for `p.Separable`.

Mathlib certainly has a polynomial separability definition and theorem API.  The relevant definition is:

```lean
Polynomial.Separable f
```

and it is definitionally / theorem-wise equivalent to coprimality with the derivative:

```lean
Polynomial.separable_def  : f.Separable ↔ IsCoprime f f.derivative
Polynomial.separable_def' : f.Separable ↔ ∃ a b, a * f + b * f.derivative = 1
```

Use those for concrete proofs.

### (b) Does Mathlib have `Polynomial.separable_of_discriminant_ne_zero` or `separable_iff_discriminant_ne_zero`?

I would not rely on such a lemma; the exposed separability API is the coprime/Bezout API.  The actual stable route is:

```lean
by
  rw [Polynomial.separable_def']
  exact ⟨A, B, by ring⟩
```

where `A` and `B` are CAS-generated cofactors satisfying

```lean
A * p + B * p.derivative = 1.
```

If your CAS certificate gives a nonzero scalar instead,

```lean
A * p + B * p.derivative = C
```

with `C ≠ 0` over a field, divide through by `C`:

```lean
by
  rw [Polynomial.separable_def']
  refine ⟨C⁻¹ • A, C⁻¹ • B, ?_⟩
  -- or use `C⁻¹ * A` / `C⁻¹ * B` depending on the coefficient type and simp-normal form.
  -- Rewrite the certificate and use `field_simp [hC]` / `ring`.
```

### (c) Does Mathlib have `Polynomial.discriminant_eq_resultant`?

Do not bank on a discriminant theorem.  If you want a resultant route, search/use the `Polynomial.resultant` API directly, but the separability endpoint still wants coprimality:

```lean
Polynomial.Separable p = IsCoprime p p.derivative
```

A resultant nonzero theorem, when available, is only useful as a way to produce the same coprimality statement.  In a proof generated from CAS, the Bezout certificate is usually more direct than a resultant determinant/discriminant equality.

### (d) Can `norm_num` compute the discriminant of `Ψ₃ = 3X⁴+b₂X³+3b₄X²+3b₆X+b₈`?

No, not in the sense you need.

* `norm_num` computes numeric expressions; it does not symbolically compute the discriminant of a quartic with symbolic coefficients `b₂,b₄,b₆,b₈`.
* `ring` can verify a fully expanded symbolic polynomial identity **after** you state the identity explicitly.
* If you define your own quartic-discriminant expression and specialize it to `Ψ₃`, `ring`/`ring_nf` can verify algebraic rearrangements, but it will not discover the discriminant formula.

For `Ψ₃`, the better Lean tactic route is:

```lean
rw [Polynomial.separable_def']
exact ⟨A, B, by
  -- A and B are explicit polynomial cofactors from CAS.
  -- Then close by `ring` / `ring_nf` after unfolding `Ψ₃`.
  ring⟩
```

or, if the goal is only nonzero rather than separability, use the existing degree/nonzero lemmas for division polynomials.

## Buildable skeleton: concrete separability from a Bezout certificate

```lean
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

open Polynomial
open scoped Polynomial

namespace PolynomialConcreteSeparable

variable {K : Type*} [Field K]

/-- Concrete separability from an explicit Bezout identity. -/
theorem separable_of_bezout_certificate
    (p A B : K[X])
    (hbez : A * p + B * p.derivative = 1) :
    p.Separable := by
  rw [Polynomial.separable_def']
  exact ⟨A, B, hbez⟩

/-- Same, with the certificate closed by `ring`. -/
example (p A B : K[X])
    (hbez : A * p + B * p.derivative = 1) :
    p.Separable := by
  exact separable_of_bezout_certificate p A B hbez

/-- If the CAS gives a nonzero scalar certificate, normalize it to a Bezout identity. -/
theorem separable_of_scalar_bezout_certificate
    (p A B : K[X]) {c : K} (hc : c ≠ 0)
    (hbez : A * p + B * p.derivative = C c) :
    p.Separable := by
  rw [Polynomial.separable_def']
  refine ⟨C c⁻¹ * A, C c⁻¹ * B, ?_⟩
  calc
    (C c⁻¹ * A) * p + (C c⁻¹ * B) * p.derivative
        = C c⁻¹ * (A * p + B * p.derivative) := by ring
    _ = C c⁻¹ * C c := by rw [hbez]
    _ = 1 := by
      ext m
      fin_cases m <;> simp [hc]

end PolynomialConcreteSeparable
```

If the last `ext/fin_cases` is brittle in your Mathlib version, replace the final line by:

```lean
      simpa [Polynomial.C_mul, hc]
```

or simply:

```lean
      simp [hc]
```

depending on how `C c⁻¹ * C c` normalizes locally.

## What this means for `preΨ'ₙ`

A discriminant formula like

```text
Disc(preΨ'ₙ) = ± n^a · Δ^b
```

would be mathematically excellent, but in Lean it only helps if you also have a formal discriminant API connecting nonzero discriminant to `Polynomial.Separable`.  Since the stable Mathlib endpoint is coprimality with the derivative, the immediately actionable version of such a formula is a **resultant/Bezout certificate** for

```lean
IsCoprime (W.preΨ' n) (W.preΨ' n).derivative
```

or an explicit identity

```lean
A * W.preΨ' n + B * (W.preΨ' n).derivative = 1
```

after specializing and normalizing the curve parameters.

For the general `n` theorem, a closed-form discriminant in Lean would be a major formalization project.  For small fixed `n` like `n = 3`, a CAS-generated Bezout identity is the fastest path.
