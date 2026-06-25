# Q339 (dm1): strategic assessment — general discriminant/resultant route for `preΨ'_n` separability

## Executive decision

For fixed `n`, the discriminant/resultant route is excellent.  For general `n`, I would **not** pivot from the formal/projective bridge to a pure EDS-discriminant induction unless a precise published formula and proof strategy are already in hand.

The reason is structural: a general discriminant formula for `preΨ'_n` is essentially the same theorem as separability of `[n]` in a more global packaging.  Proving it uniformly in `n` by EDS recurrences is not just “the fixed-`n` resultant certificate with a parameter.”  It requires controlling resultants among all neighboring division polynomials appearing in the recurrences, and those coprimality/resultant controls are exactly the torsion/formal-group content reappearing algebraically.

So the route ranking remains:

```text
fixed small n:      CAS Bezout/resultant certificates
all n:              formal/projective bridge, or a geometric theorem that [n] is étale
pure EDS Disc_n:    possible in principle, but likely larger and more circular-risky
```

The discriminant route is useful as a **diagnostic** and for fixed cases; I do not think it is the shortest axiom-removal path for the general theorem.

---

## 1. First normalization warning

The candidate formula must be stated very carefully.  With Mathlib’s reduced `preΨ'_n`, the even cases do not have the same scalar power as the odd cases.

From the previous CAS data:

```text
n = 3:
  Res(preΨ'_3, (preΨ'_3)') = -3^4 * Δ^2
  lc(preΨ'_3) = 3
  Disc(preΨ'_3) = -3^3 * Δ^2

n = 4:
  Res(preΨ'_4, (preΨ'_4)') = 2^9 * Δ^5
  lc(preΨ'_4) = 2
  Disc(preΨ'_4) = ±2^8 * Δ^5

n = 6:
  Res(preΨ'_6, (preΨ'_6)') = 2^16 * 3^13 * Δ^40
  lc(preΨ'_6) = 3
  Disc(preΨ'_6) = ±2^16 * 3^12 * Δ^40

n = 8:
  Res(preΨ'_8, (preΨ'_8)') = 2^84 * Δ^145
  lc(preΨ'_8) = 4
  Disc(preΨ'_8) = ±2^82 * Δ^145
```

The exponent of `Δ` matches

```text
d * (d - 1) / 6
```

where

```text
d = deg(preΨ'_n).
```

But the scalar factor depends on the normalization and parity.  For odd `n`, the pattern `± n^(d-1) * Δ^(d(d-1)/6)` matches the examples.  For even reduced `preΨ'_n`, the leading coefficient is `n/2`, and the scalar is not simply `n^(d-1)`.

Therefore the safe general theorem for Lean should first be the weaker but sufficient statement:

```lean
∃ u : K, IsUnit u ∧
  resultant (W.preΨ' n) (derivative (W.preΨ' n)) = C(u) * W.Δ ^ e(n)
```

or simply:

```lean
resultant (W.preΨ' n) (derivative (W.preΨ' n)) ≠ 0
```

under `[W.IsElliptic]` and `(n : K) ≠ 0`.

Trying to prove the exact closed scalar formula first is extra work and a possible normalization trap.

---

## 2. Why an EDS discriminant induction is not straightforward

The tempting plan is:

```text
Disc(f*g) = Disc(f)*Disc(g)*Res(f,g)^2
```

and the division-polynomial recurrences look product-like.  But the key odd recurrence is not a product:

```text
ψ_{2m+1} = ψ_{m+2} * ψ_m^3 - ψ_{m-1} * ψ_{m+1}^3.
```

The discriminant of a **difference of products** does not factor into discriminants and resultants of the factors.  To compute

```text
Disc(ψ_{2m+1}) = Res(ψ_{2m+1}, (ψ_{2m+1})') / lc(ψ_{2m+1}),
```

you must control the derivative of that difference.  This immediately introduces common-root exclusions and resultants between neighboring division-polynomial factors and their derivatives.

In other words, the induction would need lemmas like:

```lean
IsCoprime (W.preΨ' m) (W.preΨ' (m+1))
IsCoprime (W.preΨ' m) (W.preΨ' (m-1))
IsCoprime (W.preΨ' m) W.Ψ₂Sq
IsCoprime (W.preΨ' m) (derivative (W.preΨ' m))
resultant formulas for many neighboring pairs
```

The last line includes the target theorem for smaller indices, and the neighboring-pair resultants encode rank-of-apparition / torsion structure.  This is not impossible, but it is a large structural theory, not a short recurrence induction.

The even recurrence has a quotient/complement flavor, which also forces control of the `ψ₂` factor and the reduced/full normalization.  Again, this is manageable for fixed `n`, but general `n` becomes a web of resultant identities.

---

## 3. Does a closed-form formula exist in the literature?

There are classical product formulas for division polynomials and their discriminants/resultants, and there is literature studying division polynomials and discriminants.  But the proofs I know are geometric/arithmetic: they use the fact that the roots of `ψ_n` are torsion `x`-coordinates, the multiplication-by-`n` map, or intersection theory.

That is exactly the content we are trying to formalize.

I do **not** know a Lean-ready theorem of the form

```text
Disc(preΨ'_n) = unit(n) * Δ^e(n)
```

with a proof that uses only the Ward/EDS recurrences and no torsion geometry, no formal group, and no separability of `[n]`.

Even if such a formula is written somewhere, porting it to Lean would likely require:

```text
1. exact normalization translation to Mathlib's `preΨ'`,
2. parity handling for reduced even polynomials,
3. many auxiliary resultant identities,
4. proof that all scalar factors are units under `(n : K) ≠ 0`,
5. a discriminant/resultant API bridge to `Polynomial.Separable`.
```

That is very likely comparable to, or larger than, the formal/projective bridge.

---

## 4. What a Lean discriminant route would actually need

A full Lean route would look like this:

```lean
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

open Polynomial

namespace WeierstrassCurve

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.IsElliptic]

/-- Scalar factor in the discriminant/resultant formula, with correct parity normalization. -/
noncomputable def preΨ'ResultantUnitScalar (n : ℕ) : K :=
  -- exact formula TBD; must distinguish odd/even reduced normalization
  1

/-- Exponent of the discriminant in the resultant/discriminant formula. -/
def preΨ'DeltaExponent (n : ℕ) : ℕ :=
  let d := if Even n then (n^2 - 4) / 2 else (n^2 - 1) / 2
  d * (d - 1) / 6

/-- The hard structural theorem. -/
theorem resultant_preΨ'_derivative_formula
    {n : ℕ} (hn : n ≠ 0) :
    Polynomial.resultant (W.preΨ' n) (derivative (W.preΨ' n)) =
      C (preΨ'ResultantUnitScalar W n) * C (W.Δ ^ preΨ'DeltaExponent n) := by
  -- This is the whole project, not a small wrapper.
  sorry

/-- Resultant nonzero gives separability. -/
theorem preΨ'_separable_of_resultant_formula
    {n : ℕ} (hn : (n : K) ≠ 0)
    (hres : Polynomial.resultant (W.preΨ' n) (derivative (W.preΨ' n)) ≠ 0) :
    (W.preΨ' n).Separable := by
  -- Use the polynomial API relating nonzero resultant to coprimality over a field,
  -- or prove a Bezout identity from the resultant/Sylvester construction.
  -- `Polynomial.Separable` is definitionally `IsCoprime f f'`.
  sorry

end

end WeierstrassCurve
```

The hard theorem is `resultant_preΨ'_derivative_formula`.  If you can prove it, the rest is easy.  But proving it is at least as hard as proving the separability theorem itself.

---

## 5. Why the formal/projective route is still better

The formal/projective route isolates the one geometric input that is actually needed:

```text
d[n]|_O = n
```

and then connects it to division polynomials through the projective formula.  Your current A-path atoms are local and compositional:

```text
ω_n normalization
projective representative [φ_n : ω_n : ψ_n]
local parameter t = -X*Z/Y
nonzero φ_n and ω_n at ψ_n-roots
TangentO.nsmul₁ = n
```

Each atom has a clear role in the final contradiction.  By contrast, a general discriminant proof compresses all of this into one global resultant formula.  That can look shorter on paper, but in Lean it hides many of the same lemmas inside a harder-to-debug algebraic theorem.

For fixed `n`, global compression is good: a CAS certificate is a finite artifact.  For variable `n`, global compression is bad: the proof has to rediscover the structure uniformly.

---

## 6. Possible compromise

Use discriminants/resultants only for small base cases and sanity checks:

```text
n = 3,4,5,7 fixed separability certificates
small resultant certificates for Ψ₂Sq, Ψ₃, preΨ₄
spot-checks of predicted scalar powers
```

But keep the general theorem on the A-path.

A useful theorem to prove from the A-path later is the resultant/discriminant formula as a **corollary**.  Once separability and torsion/root descriptions are available, the discriminant formula becomes much more natural: roots are torsion `x`-coordinates, and products of differences can be computed using division-polynomial values/intersections.

---

## Final recommendation

Do not pivot the general proof to discriminants.

The discriminant formula is a good validation target and a good fixed-`n` certificate generator.  But as a general Lean proof strategy, it is likely larger than the projective/formal bridge and risks circularity through hidden adjacent-coprimality and torsion-root facts.

The current A-path remains the better architecture:

```text
build ω_n + projective formula + local parameter bridge
```

If the goal is to close `preΨ'_separable_of_natCast_ne_zero` for all `n`, the most honest bottleneck is still the structural theorem behind `[n]` on first-order tangent directions, not a missing symbolic discriminant identity.
