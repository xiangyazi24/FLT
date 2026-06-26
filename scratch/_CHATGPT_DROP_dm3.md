# Q819 (dm3): odd `preΨ' n` separability for `n ≥ 5`

## Bottom line

Do **not** try to prove the odd case by reducing it to a nearby even case, and do **not** expect the odd EDS recurrence to give a clean product-rule descent.

For odd `n`, the correct short route is the same one used in the classical proof: use the tangent/differential identity for multiplication-by-`n`.  In Mathlib-compatible notation, for odd `n` the reduced identity is

```text
ψ₂ · Φₙ · (preΨ'_n)' + n · Ωₙ ≡ 0      mod preΨ'_n,
```

or, if avoiding `Ωₙ` and using the quotient `Qₙ = ψ₂ₙ / ψₙ`,

```text
2 · ψ₂ · Φₙ · (preΨ'_n)' + n · Qₙ ≡ 0  mod preΨ'_n.
```

The quotient form is enough when `2` is invertible.  In characteristic `2`, it loses the y-coordinate information, so for odd `n` in characteristic `2` one still needs the genuine `Ωₙ`/`ωₙ` or a formal-group argument that bypasses `Qₙ`.

The EDS odd recurrence is useful for defining `preΨ'`, degrees, and adjacent coprimality, but it is not the right separability induction principle.

---

## Why nearby even cases do not imply the odd case

A root of `preΨ'(2m+1)` corresponds to the `x`-coordinate of a nonzero `(2m+1)`-torsion point.  It is not forced to be a root of either `preΨ'(2m)` or `preΨ'(2m+2)`.  In fact, the adjacent-coprimality statements you need elsewhere say the opposite: generically there should be no common root between adjacent division polynomials.

So even if separability is known for all even indices, that does not rule out a multiple root of an odd-index polynomial.  Separability is not monotone in the index and does not propagate from `n+1` to `n`.

The same issue affects the proposed `n = 5, 7` base-case strategy.  Proving `5` and `7` by Bézout certificates is useful for computations, but it does not supply an induction step for arbitrary odd `n`, because the odd recurrence is a difference of two products, not a smaller factor times a cofactor.

---

## Why the odd recurrence is a trap for squarefreeness

The recurrence has the shape

```text
preΨ(2m+1)
  = preΨ(m+2) · preΨ(m)^3 · F₁
    - preΨ(m-1) · preΨ(m+1)^3 · F₂,
```

where the `Fᵢ` are `1` or powers of `Ψ₂Sq`, depending on parity.

At a point `x` with

```text
preΨ(2m+1)(x) = 0,
```

you only get an equality of two products:

```text
preΨ(m+2)(x) · preΨ(m)(x)^3 · F₁(x)
  = preΨ(m-1)(x) · preΨ(m+1)(x)^3 · F₂(x).
```

If one of the visible factors is zero, then adjacent/strong coprimality can sometimes descend to a smaller index.  But the hard case is exactly the generic case where all these factors are nonzero.  Then the zero of `preΨ(2m+1)` comes from cancellation between two nonzero products.

Differentiating the recurrence gives a log-derivative equality in the residue field:

```text
(A'B - AB') evaluated at x = 0,
```

or, after cancellation of nonzero factors, a relation between logarithmic derivatives of the smaller `preΨ`s and the `Ψ₂Sq` factors.  That relation is not a descent statement.  To rule it out, you need extra structure: precisely the invariant differential / multiplication-by-`n` tangent identity.

So a recurrence-only proof will end up reproving the differential identity in a much less usable form.

---

## The clean odd-case argument

Let

```text
pₙ := preΨ'_n.
```

Assume `n` is odd, `n ≥ 5`, and `(n : K) ≠ 0`, over a field `K` and a nonsingular Weierstrass curve.  Suppose for contradiction that `α` is a double root:

```text
pₙ(α) = 0,
pₙ'(α) = 0.
```

Choose a point `P = (α, β)` on the affine curve above `α`, after passing to an algebraic closure if needed.

For odd `n`, Mathlib’s reduced/full denominator relation has no extra `ψ₂` factor:

```text
Ψₙ = C(pₙ).
```

The invariant differential identity reduces to

```text
ψ₂(P) · Φₙ(α) · pₙ'(α) + n · Ωₙ(P) = 0.
```

Since `pₙ'(α) = 0`, this gives

```text
n · Ωₙ(P) = 0.
```

If `(n : K) ≠ 0`, then

```text
Ωₙ(P) = 0.
```

Now use the cleared curve equation for the image `[n]P`:

```text
Ωₙ² + a₁ Φₙ Ωₙ Ψₙ + a₃ Ωₙ Ψₙ³
  = Φₙ³ + a₂ Φₙ² Ψₙ² + a₄ Φₙ Ψₙ⁴ + a₆ Ψₙ⁶.
```

At a root of `pₙ`, we have `Ψₙ(P) = 0`, so this reduces to

```text
Ωₙ(P)^2 = Φₙ(α)^3.
```

Since `Ωₙ(P) = 0`, it follows that

```text
Φₙ(α) = 0.
```

But for odd `n`, Mathlib’s definition of `Φ` gives, modulo `pₙ`,

```text
Φₙ ≡ - preΨ'_{n+1} · preΨ'_{n-1} · Ψ₂Sq     mod pₙ.
```

Thus `Φₙ(α) ≠ 0` follows from the three coprimality facts

```text
gcd(pₙ, preΨ'_{n+1}) = 1,
gcd(pₙ, preΨ'_{n-1}) = 1,
gcd(pₙ, Ψ₂Sq) = 1        -- because n is odd: no odd n-torsion point is 2-torsion.
```

Contradiction.  Hence `pₙ` has no double root.

This proof does not use `n ≥ 5` in an essential way except to avoid small-index edge cases and to ensure the standard adjacent-coprimality package is being used outside the degenerate definitions `preΨ'_1 = 1`, `preΨ'_2 = 1`, `preΨ'_3 = Ψ₃`.

---

## Lean target for the odd differential identity

If `Ωₙ` is available, the odd reduced theorem should be stated directly as an affine-coordinate-ring ideal membership.

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

/-- Placeholder: Mathlib does not yet define the y-coordinate numerator. -/
protected noncomputable def Ω (_n : ℤ) : K[X][Y] :=
  sorry

private abbrev coeffBiv (r : K) : K[X][Y] :=
  C (C r)

/-- Ideal generated by the reduced denominator `preΨ'_n` in the affine coordinate ring. -/
def reducedPsiIdeal (n : ℕ) : Ideal W.toAffine.CoordinateRing :=
  Ideal.span
    ({Affine.CoordinateRing.mk W (C (W.preΨ' n))} : Set W.toAffine.CoordinateRing)

/-- The exact odd-index reduced differential identity.

For odd `n`, there is no extra parity factor because
`W.Ψ (n : ℤ) = C (W.preΨ' n)`. -/
theorem odd_reduced_Ω_differential_congruence
    (n : ℕ) (hn : Odd n) :
    Affine.CoordinateRing.mk W
      (W.ψ₂ * C (W.Φ (n : ℤ) * (W.preΨ' n).derivative)
        + coeffBiv (n : K) * W.Ω (n : ℤ))
      ∈ W.reducedPsiIdeal n := by
  sorry

end WeierstrassCurve
```

If using the quotient `Qₙ = ψ₂ₙ / ψₙ` instead of `Ωₙ`, use the division-by-2-free theorem:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve K)

private abbrev coeffBiv (r : K) : K[X][Y] :=
  C (C r)

/-- Quotient `Qₙ = ψ₂ₙ / ψₙ`, available from Mathlib's EDS complement sequence. -/
protected noncomputable def divisionQuot (n : ℤ) : K[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

theorem ψ_mul_divisionQuot (n : ℤ) :
    W.ψ n * W.divisionQuot n = W.ψ (2 * n) := by
  simpa [WeierstrassCurve.ψ, WeierstrassCurve.divisionQuot] using
    (normEDS_mul_complEDS₂
      (b := W.ψ₂)
      (c := C W.Ψ₃)
      (d := C W.preΨ₄)
      n)

def reducedPsiIdeal (n : ℕ) : Ideal W.toAffine.CoordinateRing :=
  Ideal.span
    ({Affine.CoordinateRing.mk W (C (W.preΨ' n))} : Set W.toAffine.CoordinateRing)

/-- Odd reduced differential identity without defining `Ωₙ`.

This is enough for separability when `2` is invertible. -/
theorem odd_reduced_divisionQuot_differential_congruence
    (n : ℕ) (hn : Odd n) :
    Affine.CoordinateRing.mk W
      (coeffBiv (2 : K) *
          (W.ψ₂ * C (W.Φ (n : ℤ) * (W.preΨ' n).derivative))
        + coeffBiv (n : K) * W.divisionQuot (n : ℤ))
      ∈ W.reducedPsiIdeal n := by
  sorry

end WeierstrassCurve
```

This quotient theorem is the one I would formalize first, because `divisionQuot` is directly available from `complEDS₂` and does not require building the universal `Ωₙ` construction.

---

## The odd `Φₙ` nonvanishing lemma

For the contradiction, isolate the following lemma.  It is the exact place where oddness matters.

```lean
-- schematic statement
lemma odd_eval_Φ_ne_zero_of_eval_preΨ_eq_zero
    {K : Type*} [Field K]
    (W : WeierstrassCurve K)
    (n : ℕ) (hn_odd : Odd n) (hn_ge : 3 ≤ n)
    (α : K)
    (hroot : (W.preΨ' n).eval α = 0)
    -- coprimality hypotheses packaged separately:
    (hcop_next : IsCoprime (W.preΨ' n) (W.preΨ' (n+1)))
    (hcop_prev : IsCoprime (W.preΨ' n) (W.preΨ' (n-1)))
    (hcop_two : IsCoprime (W.preΨ' n) W.Ψ₂Sq) :
    (W.Φ (n : ℤ)).eval α ≠ 0 := by
  sorry
```

The proof is by rewriting `Φ` modulo `preΨ'_n`.  For odd `n`, Mathlib’s definition gives

```text
Φₙ = X · pₙ² - pₙ₊₁ · pₙ₋₁ · Ψ₂Sq.
```

Therefore at a root of `pₙ`,

```text
Φₙ(α) = -pₙ₊₁(α) · pₙ₋₁(α) · Ψ₂Sq(α).
```

Each factor is nonzero by the corresponding coprimality hypothesis.

In Lean, this lemma is much easier if you prove three small evaluation consequences of coprimality first:

```lean
lemma eval_ne_zero_of_isCoprime_of_eval_eq_zero
    {K : Type*} [Field K] {p q : K[X]} {α : K}
    (hcop : IsCoprime p q) (hp : p.eval α = 0) :
    q.eval α ≠ 0 := by
  intro hq
  -- evaluate a Bézout identity `a*p + b*q = 1` at α
  -- contradiction: `0 = 1`
  sorry
```

Then `odd_eval_Φ_ne_zero_of_eval_preΨ_eq_zero` is mostly `rw [Φ_ofNat]`, parity simplification, evaluation, and `mul_ne_zero`.

---

## What to use as the induction theorem instead

If you still want an induction-based proof, the induction invariant should not be plain squarefreeness of `preΨ'_n`.  A workable invariant is the differential congruence itself:

```text
D(Ψₙ) controls the tangent of `[n]`.
```

For odd `n`, after reduction this says:

```text
ψ₂ · Φₙ · pₙ' + n · Ωₙ ≡ 0 mod pₙ.
```

For all `n`, with the parity factor `ηₙ = if Even n then ψ₂ else 1`, it says:

```text
ηₙ · ψ₂ · Φₙ · pₙ' + n · Ωₙ ≡ 0 mod pₙ.
```

Or with `Qₙ`:

```text
2 · ηₙ · ψ₂ · Φₙ · pₙ' + n · Qₙ ≡ 0 mod pₙ.
```

That invariant is stable under addition formulas because it is really `[n]^*ω = nω`.  Plain squarefreeness is not stable under the odd EDS recurrence in any direct way.

---

## Small `n` Bézout certificates

Bézout/resultant certificates for `n = 5` and `n = 7` are useful as tests, but they should not be the main proof architecture.

A good use of them:

```text
example : IsCoprime (W.preΨ' 5) (W.preΨ' 5).derivative := by
  -- generated certificate, probably after specializing hypotheses and normalizing coefficients
  ...

example : IsCoprime (W.preΨ' 7) (W.preΨ' 7).derivative := by
  ...
```

A bad use:

```text
prove n = 5, 7, then hope the odd recurrence descends squarefreeness.
```

There is no such clean descent because odd-index roots can arise from cancellation between nonzero products.

For arbitrary `n`, a resultant formula for division polynomials would also work in principle, but formalizing that universal resultant/discriminant identity is likely harder than proving the invariant differential identity.

---

## Recommended Lean plan

1. **Keep the EDS recurrence for definitions and coprimality.**
   Use it to prove or import:

   ```text
   gcd(preΨ'_n, preΨ'_{n+1}) = 1,
   gcd(preΨ'_n, preΨ'_{n-1}) = 1,
   if Odd n then gcd(preΨ'_n, Ψ₂Sq) = 1.
   ```

2. **Define `divisionQuot`.**
   This is immediate from `complEDS₂`:

   ```lean
   W.divisionQuot n := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n
   ```

   with

   ```lean
   W.ψ n * W.divisionQuot n = W.ψ (2*n)
   ```

3. **Prove the quotient differential congruence.**
   For odd `n`:

   ```text
   2ψ₂Φₙpₙ' + nQₙ ≡ 0 mod pₙ.
   ```

4. **If `2` is invertible, finish using `Qₙ`.**
   At a double root, get `Qₙ(P)=0`, hence `ωₙ(P)=0`, hence `Φₙ(P)=0`, contradiction.

5. **If characteristic `2` is in scope, do not use `Qₙ` as the final y-coordinate substitute.**
   You need either the genuine universal `Ωₙ` or a formal-group proof of the tangent identity that gives `Ωₙ(P)=0` directly.

---

## Final answer to the proposed idea

The nearby-even reduction is not viable, and `n = 5, 7` base cases do not produce an odd induction.  The simpler route is to stop trying to make the odd recurrence factor.  Prove the odd differential identity instead:

```text
ψ₂ · Φₙ · (preΨ'_n)' + n · Ωₙ ≡ 0      mod preΨ'_n
```

or, in the division-by-2-free quotient form,

```text
2 · ψ₂ · Φₙ · (preΨ'_n)' + n · Qₙ ≡ 0  mod preΨ'_n.
```

Then the odd case is straightforward: a double root forces `Ωₙ = 0` (or, when `2` is invertible, `Qₙ = 0` and hence `Ωₙ = 0`), while the curve equation and adjacent coprimality force `Ωₙ ≠ 0`.  This is the mathematically natural proof and the Lean-friendly proof, because it turns the difficult cancellation in the odd recurrence into a single reusable tangent-transport lemma.
