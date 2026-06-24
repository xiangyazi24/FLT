# Q87 (dm3): Planning separability of division polynomials by concrete resultants

Goal brick:

```lean
IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n))
```

under `(n : k) ≠ 0`, with the existing wrapper to `.Separable` already known.

This plan follows the same “keystone” style that worked for the small
coprimality certs: compute an integer Bezout certificate by CAS, import the
cofactors as explicit polynomials, and close in Lean by `linear_combination` or a
specialized sparse certificate checker.  No axioms, no analytic geometry.

---

## 1. What the resultant should be

For the usual x-division polynomial convention

```text
f_n(X) = preΨ'_n(X)
```

where for even `n` this is the univariate factor with the `ψ₂`/`y` factor removed,
the degree is

```text
d(n) = (n^2 - 1)/2   if n is odd,
d(n) = (n^2 - 4)/2   if n is even.
```

This is the standard degree formula for the x-division polynomial.  In short
Weierstrass normalization, `preΨ'_n` has leading coefficient `n` for odd `n` and
`n/2` for even `n`; some papers normalize the even polynomial by an extra factor
`2`, giving leading coefficient `n`.  This changes only the integer constant in
the discriminant/resultant, not the exponent of `Δ`.

The discriminant/resultant is expected to have the form

```text
Disc_X(f_n) = C_n · Δ^e(n)
Res_X(f_n, f_n') = ± lc(f_n) · C_n · Δ^e(n)
```

where `C_n ∈ ℤ \ {0}` is supported only at primes dividing `n`, hence becomes a
unit over a field once `(n : k) ≠ 0`.  The exponent is forced by weighted
homogeneity and agrees with the classical elliptic discriminant formula:

```text
e(n) = d(n) * (d(n) - 1) / 6.
```

Equivalently,

```text
n odd:   e(n) = (n^2 - 1)(n^2 - 3) / 24,
n even:  e(n) = (n^2 - 4)(n^2 - 6) / 24.
```

For odd `n`, with the standard short-Weierstrass normalization, the more precise
classical formula is

```text
Disc_X(ψ_n) = (-1)^((n-1)/2) · n^((n^2-3)/2)
              · Δ^((n^2-1)(n^2-3)/24).
```

Examples:

```text
n = 3:  Disc(ψ₃) = -3^3 · Δ^2.
n = 5:  Disc(ψ₅) =  5^11 · Δ^22.
n = 7:  Disc(ψ₇) = -7^23 · Δ^92.
```

For even `n`, I would not hard-code a closed-form `C_n` into Lean.  The exponent
is the important invariant; the exact integer constant should be read from the
same CAS computation that emits the Bezout certificate.  For Mathlib’s
`preΨ'_n = ψ_n / ψ₂`-style normalization on a short model, small constants are:

```text
n = 4:  Disc(preΨ'_4) = -2^8 · Δ^5,
n = 6:  Disc(preΨ'_6) =  2^16 · 3^12 · Δ^40,
n = 8:  Disc(preΨ'_8) = -2^82 · Δ^145.
```

These examples are exactly what the plan needs: the non-`Δ` factor is a unit
under `(n : k) ≠ 0`.

Reference trail for the planning document: Silverman, *Arithmetic of Elliptic
Curves*, Exercise III.3.7 for division polynomials; de Jong, “One half log
discriminant and division polynomials,” for the x-division-polynomial degree
statement and its relation to the discriminant/intersection formula; the precise
odd discriminant identity is usually cited as the elliptic discriminant formula
for division polynomials.  For the Lean project, the CAS certificate itself is the
source of truth, so no theorem from the literature needs to be trusted inside
Lean.

---

## 2. Why this proves `IsCoprime`

For each fixed `n`, generate a certificate over the universal integer coefficient
ring, preferably in invariant variables rather than raw `aᵢ` variables:

```text
A_n(X) · preΨ'_n(X) + B_n(X) · derivative(preΨ'_n)(X)
  = C_n · Δ^e(n).
```

After specializing to a field `k`, `[W.IsElliptic]` gives `W.Δ ≠ 0`, hence
`(W.Δ)^e(n) ≠ 0`.  The hypothesis `(n : k) ≠ 0` makes the integer `C_n` nonzero
because all prime divisors of `C_n` divide `n`.  Therefore the right-hand side is
a nonzero constant polynomial, hence a unit in `k[X]`; scaling the identity by
that unit inverse gives a Bezout identity with right-hand side `1`.

Lean skeleton:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace WeierstrassCurve

open Polynomial

variable {k : Type*} [Field k]

/-- Metadata for one fixed certificate.  In practice this is generated, not hand-written. -/
structure PrePsiSepCertData where
  n : ℕ
  e : ℕ
  C : ℤ
  A : Polynomial UniversalWeierstrassInvariantRing
  B : Polynomial UniversalWeierstrassInvariantRing

/-- Universal certificate shape for one fixed `n`. -/
theorem preΨ'_derivative_resultant_cert_7_universal :
    certA_7 * universal_preΨ' 7
      + certB_7 * derivative (universal_preΨ' 7)
        = Polynomial.C (certC_7 * universal_Δ ^ certE_7) := by
  -- Generated proof: `native_decide` over normalized sparse maps, or
  -- `linear_combination` if the generated expression is still small enough.
  native_decide

/-- Specialized certificate over an arbitrary field. -/
theorem preΨ'_derivative_resultant_cert_7
    (W : WeierstrassCurve k) :
    A_7 W * W.preΨ' 7 + B_7 W * derivative (W.preΨ' 7)
      = Polynomial.C ((certC_7 : k) * W.Δ ^ certE_7) := by
  -- Map the universal identity along the coefficient specialization.
  simpa using map_preΨ'_derivative_resultant_cert_7_universal (W := W)

/-- One fixed `n` separability brick from the certificate. -/
theorem isCoprime_preΨ'_derivative_7
    (W : WeierstrassCurve k) [W.IsElliptic]
    (h7 : (7 : k) ≠ 0) :
    IsCoprime (W.preΨ' 7) (derivative (W.preΨ' 7)) := by
  have hΔ : W.Δ ≠ 0 := by
    simpa [WeierstrassCurve.IsElliptic] using W.discr_ne_zero

  have hC : (certC_7 : k) ≠ 0 := by
    -- Generated from the factorization of `certC_7`, e.g. `± 7^a`.
    -- The final proof is a tiny `norm_num`/`field_simp` lemma using `h7`.
    exact certC_7_ne_zero_of_natCast_ne_zero h7

  have hunit_scalar : IsUnit ((certC_7 : k) * W.Δ ^ certE_7) := by
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero hC (pow_ne_zero _ hΔ))

  rcases hunit_scalar with ⟨u, hu⟩

  have hcert := preΨ'_derivative_resultant_cert_7 (W := W)

  -- Convert `A*f+B*f' = C(unit)` into `A'*f+B'*f' = 1`.
  refine ⟨Polynomial.C ↑u⁻¹ * A_7 W, Polynomial.C ↑u⁻¹ * B_7 W, ?_⟩
  calc
    Polynomial.C ↑u⁻¹ * A_7 W * W.preΨ' 7
        + Polynomial.C ↑u⁻¹ * B_7 W * derivative (W.preΨ' 7)
        = Polynomial.C ↑u⁻¹ *
            (A_7 W * W.preΨ' 7 + B_7 W * derivative (W.preΨ' 7)) := by ring
    _ = Polynomial.C ↑u⁻¹ * Polynomial.C ((certC_7 : k) * W.Δ ^ certE_7) := by
          rw [hcert]
    _ = 1 := by
          -- `hu` identifies the scalar with `u`; this is just field/unit arithmetic.
          simpa [hu]

/-- Finite capstone wrapper for the torsion-bound range. -/
theorem isCoprime_preΨ'_derivative_of_natCast_ne_zero_le_16
    (W : WeierstrassCurve k) [W.IsElliptic]
    {n : ℕ} (hn0 : (n : k) ≠ 0) (hnle : n ≤ 16) :
    IsCoprime (W.preΨ' n) (derivative (W.preΨ' n)) := by
  interval_cases n <;>
    first
    | simpa using isCoprime_preΨ'_derivative_1 (W := W)
    | simpa using isCoprime_preΨ'_derivative_2 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_3 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_4 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_5 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_6 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_7 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_8 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_9 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_10 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_11 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_12 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_13 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_14 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_15 (W := W) hn0
    | simpa using isCoprime_preΨ'_derivative_16 (W := W) hn0

end WeierstrassCurve
```

The names in the skeleton are intentionally schematic.  I would generate one
file per `n`, for example

```text
scratch/KeystoneSepCert03.lean
scratch/KeystoneSepCert04.lean
...
scratch/KeystoneSepCert16.lean
```

and a small capstone file importing them.

---

## 3. Boundedness for `n = 1..16`

The degree/resultant sizes are:

| n | degree d(n) | exponent e(n) | Sylvester size 2d-1 |
|---:|---:|---:|---:|
| 1 | 0 | 0 | trivial |
| 2 | 0 | 0 | trivial |
| 3 | 4 | 2 | 7 |
| 4 | 6 | 5 | 11 |
| 5 | 12 | 22 | 23 |
| 6 | 16 | 40 | 31 |
| 7 | 24 | 92 | 47 |
| 8 | 30 | 145 | 59 |
| 9 | 40 | 260 | 79 |
| 10 | 48 | 376 | 95 |
| 11 | 60 | 590 | 119 |
| 12 | 70 | 805 | 139 |
| 13 | 84 | 1162 | 167 |
| 14 | 96 | 1520 | 191 |
| 15 | 112 | 2072 | 223 |
| 16 | 126 | 2625 | 251 |

Raw Sylvester determinants in the universal coefficient ring are not the right
way to do all sixteen.  They are useful as a conceptual guarantee, but the actual
pipeline should use fraction-free subresultants, modular images, and sparse
reconstruction.

For small `n`, this is very viable:

```text
n = 3,4: tiny; comparable to or easier than the existing keystone certs.
n = 5: moderate; likely hundreds to a few thousand cofactor terms.
n = 6: moderate-to-large; likely several thousand terms.
n = 7: large; likely 10^4 to 10^5 terms depending on variables/normalization.
```

So up to `n≈7`, expect “same technique, larger certs.”  It is not just another
250-term keystone cert by `n=7`; it is probably one to two orders of magnitude
larger, but still within a reasonable generated-certificate workflow.

For `n = 8..16`, a naive full universal Bezout certificate is the risky part.
The polynomial degrees are still finite and not astronomical, but the universal
cofactor coefficients can become enormous.  The matrix size `251` at `n=16` is
not itself fatal; the issue is expression swell in the five/invariant coefficient
variables.

Recommended mitigation:

1. Work in invariant coordinates (`b₂,b₄,b₆,b₈` or the smallest existing Mathlib
   coefficient basis), not raw expanded `a₁,a₂,a₃,a₄,a₆`, until the final map to
   `W`.
2. Generate certificates with a sparse polynomial dictionary, not pretty-printed
   ring expressions.
3. Verify certificates by a custom Horner/sparse evaluator plus `native_decide`,
   not by asking `ring` to rediscover a 100k-term identity.
4. Use modular computation and Chinese remainder reconstruction for the cofactors.
5. Record the factorization of `C_n` separately, so the Lean unit proof from
   `(n : k) ≠ 0` is tiny.
6. Pilot `n=5,6,7` before committing to all sixteen; the term-count curve at
   `n=7` will predict whether `n=16` is acceptable.

---

## 4. Per-`n` versus variable-`n`

A single variable-`n` proof is mathematically cleaner but not the pragmatic route
for this project right now.

There are two possible variable-`n` routes:

1. **Group-scheme route.**  Prove multiplication-by-`n` is finite étale on an
   elliptic curve when `(n : k) ≠ 0`; identify the x-division divisor cut out by
   `preΨ'_n`; prove the quotient by `±1` has reduced x-coordinate polynomial.
   This is conceptually the right theorem, but it requires substantial algebraic
   geometry and a tight bridge from Mathlib’s division-polynomial recursion to
   the finite étale torsion scheme.

2. **Symbolic recurrence route.**  Prove the discriminant formula for all `n` by
   induction on division-polynomial recurrences.  This avoids schemes but still
   requires a serious theory of resultants/discriminants under the nonlinear Ward
   recurrences.  It is probably more work than the group-scheme route and less
   reusable.

For the torsion-bound range `n ≤ 16`, per-`n` certificates are the pragmatic path.
They match the project’s successful keystone methodology and produce small Lean
proof obligations after generation.  The only caveat is certificate size for
`n ≥ 8`.

---

## 5. Verdict

Yes: the resultant/discriminant is a nonzero integer constant times a power of
`Δ`, and the exponent is

```text
e(n) = d(n)(d(n)-1)/6
```

with `d(n)` as above.  Over a field, `[W.IsElliptic]` makes the `Δ` factor a unit,
and `(n : k) ≠ 0` makes the integer constant a unit.  This gives exactly the
Bezout identity needed for

```lean
IsCoprime (W.preΨ' n) (Polynomial.derivative (W.preΨ' n)).
```

The practical recommendation is:

```text
Phase A: generate and integrate certs for n = 1..7.
Phase B: measure certificate size at n = 7 and n = 8.
Phase C: if growth is acceptable, finish n = 9..16 per-n.
Phase D: if n ≥ 10 explodes, switch to a hybrid proof: per-prime or group-scheme
         separability for the large indices, keeping the small resultant certs as
         local keystone bricks.
```

Cofactor-size risk is low for `n≤5`, moderate for `n=6,7`, and high for raw
universal certificates beyond that.  The plan remains viable if the generator is
built as a sparse modular certificate pipeline rather than as literal expanded
`ring` terms.
