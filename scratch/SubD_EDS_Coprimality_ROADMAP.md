[ask-gpt dm2 tid=1be80bd1 +0s] dispatched, waiting for answer
[ask-gpt dm2 tid=1be80bd1 +90s] waiting (status=processing)
[ask-gpt dm2 tid=1be80bd1 +180s] waiting (status=processing)
[ask-gpt dm2 tid=1be80bd1 +270s] waiting (status=processing)
[ask-gpt dm2 tid=1be80bd1 +360s] waiting (status=processing)
[ask-gpt dm2 tid=1be80bd1 +450s] waiting (status=processing)
[ask-gpt dm2 tid=1be80bd1 +540s] waiting (status=processing)
[ask-gpt dm2 tid=1be80bd1 +574s] terminal: status=completed
## Honest answer

The **non-circular** proof should be polynomial/EDS-level. The shortest route is **not** a full resultant formula. It is:

```text
evaluate the auxiliary EDS `preΨ'_n` at a root of `Ψ₂Sq`;
at such a root the EDS parameter `Ψ₂Sq²` becomes `0`;
then prove the specialized EDS never vanishes when `(n : k) ≠ 0`.
```

But there is no existing Mathlib theorem that already says this. The genuinely missing sublemma is a **generic EDS specialization theorem** for

```lean
preNormEDS' 0 c d n
```

under the relation

```lean
d ^ 2 = -4 * c ^ 3
```

and `c ≠ 0`.

That is still a grind, but it is much smaller and more local than a global resultant/discriminant identity.

Mathlib’s division-polynomial file confirms the relevant normalization: `preΨ' n` is defined as

```lean
preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n
```

and has recurrences

```lean
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd
```

coming from `preNormEDS'_even` and `preNormEDS'_odd`. fileciteturn69file0L1-L4 The source comments also state exactly the split

```text
ΨSqₙ := preΨₙ² · Ψ₂Sq  if n even,
ΨSqₙ := preΨₙ²        if n odd.
```

fileciteturn69file0L1-L4

## The key evaluation formula

Let

```lean
F := W.Ψ₂Sq
C := W.Ψ₃
D := W.preΨ₄
```

and let `x : k` satisfy

```lean
hF : F.eval x = 0.
```

Then

```lean
(W.preΨ' n).eval x
=
preNormEDS' (0 : k) (C.eval x) (D.eval x) n.
```

At such an `x`, the initial values satisfy the crucial identities:

```lean
C.eval x ≠ 0
(D.eval x) ^ 2 = -4 * (C.eval x) ^ 3
```

The second identity is a direct polynomial identity modulo `Ψ₂Sq`:

```lean
(W.preΨ₄ ^ 2 + 4 * W.Ψ₃ ^ 3) % W.Ψ₂Sq = 0
```

or equivalently

```lean
W.Ψ₂Sq ∣ W.preΨ₄ ^ 2 + 4 * W.Ψ₃ ^ 3.
```

The first is the “no singular 2-torsion root” statement: `Ψ₂Sq` and `Ψ₃` have no common root on an elliptic curve. This is still polynomial-level, not the root-realization seam. It can be proved by a small resultant/gcd identity for the cubic `Ψ₂Sq` and the quartic `Ψ₃`, using `W.IsElliptic` / nonzero discriminant. Mathlib exposes `Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly`, and the Weierstrass file documents `twoTorsionPolynomial_discr` as the link between the two-torsion cubic discriminant and the curve discriminant. fileciteturn69file0L1-L4 fileciteturn73file0L1-L4

## Closed form of the specialized EDS

Set

```lean
u n := preNormEDS' (0 : k) c d n
```

with

```lean
hc : c ≠ 0
hd : d ^ 2 = -4 * c ^ 3.
```

Then the closed forms are:

```lean
u (2*s + 1)
  = (-1 : k) ^ (s * (s - 1) / 2) * c ^ (s * (s + 1) / 2)

u (4*s + 2)
  = ((2*s + 1 : ℕ) : k) * c ^ (2 * s * (s + 1))

u (4*(s + 1))
  = ((s + 1 : ℕ) : k) * c ^ (2 * s * (s + 2)) * d
```

These match the classical behavior at a 2-torsion point: odd multiples return the 2-torsion point, even multiples go to `O`, but after dividing off the `ψ₂` factor the auxiliary polynomial is still nonzero. The coefficient is essentially `n` in the odd/even quotient normalization.

From these formulas:

```lean
(n : k) ≠ 0 → u n ≠ 0.
```

For odd `n`, only powers of `c` and `±1` occur.  
For `n = 4*s + 2`, the scalar coefficient is `(2*s+1 : k)`, and it is nonzero because `(n : k) = 2 * (2*s+1)` is nonzero.  
For `n = 4*(s+1)`, the scalar coefficient is `(s+1 : k)`, and it is nonzero because `(n : k) = 4 * (s+1)` is nonzero. Also `d ≠ 0` follows from `d² = -4c³`, `c ≠ 0`, and `(2 : k) ≠ 0`, which follows from `(n : k) ≠ 0` in the even cases.

## The minimal non-circular theorem chain

Here is the exact architecture I recommend.

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

/--
Evaluation of `preΨ'` commutes with the auxiliary EDS definition.

This is a pure recursion lemma for `preNormEDS'`; prove it once by induction from
`preNormEDS'_even` / `preNormEDS'_odd`.
-/
theorem eval_preΨ'_eq_preNormEDS'_eval
    (n : ℕ) (x : k) :
    (W.preΨ' n).eval x =
      preNormEDS' ((W.Ψ₂Sq.eval x) ^ 2) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
  -- Pure EDS/map recursion lemma.
  -- This is not currently a one-line Mathlib theorem.
  -- Prove by induction on the defining recursion of `preNormEDS'`.
  sorry

/--
At a root of `Ψ₂Sq`, the initial values `Ψ₃` and `preΨ₄` satisfy
`preΨ₄² = -4 Ψ₃³`.

This is a direct polynomial identity modulo `Ψ₂Sq`.
-/
theorem preΨ₄_eval_sq_eq_neg_four_Ψ₃_eval_cube_of_Ψ₂Sq_eval_eq_zero
    {x : k} (hx : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ₄.eval x) ^ 2 = -4 * (W.Ψ₃.eval x) ^ 3 := by
  -- Prove the polynomial divisibility
  --   W.Ψ₂Sq ∣ W.preΨ₄ ^ 2 + 4 * W.Ψ₃ ^ 3
  -- by expanding `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, and using `W.b_relation`.
  --
  -- Then evaluate at `x` and use `hx`.
  sorry

/--
`Ψ₃` is nonzero at a root of `Ψ₂Sq` on an elliptic curve.

This is the polynomial-level nonsingularity of the two-torsion cubic; it should be
proved from `Ψ₂Sq_eq`, `twoTorsionPolynomial_discr`, and `W.IsElliptic`.
-/
theorem Ψ₃_eval_ne_zero_of_Ψ₂Sq_eval_eq_zero
    {x : k} (hx : W.Ψ₂Sq.eval x = 0) :
    W.Ψ₃.eval x ≠ 0 := by
  -- Polynomial-level proof:
  -- show `W.Ψ₂Sq` and `W.Ψ₃` are coprime, or show common root would force
  -- discriminant zero.
  --
  -- Use:
  --   W.Ψ₂Sq_eq
  --   W.twoTorsionPolynomial_discr
  --   W.isUnit_Δ / ellipticity
  sorry

end WeierstrassCurve
```

The remaining pure EDS theorem is the actual smallest isolated grind:

```lean
import Mathlib

noncomputable section

open Polynomial

/--
Specialized EDS nonvanishing at the 2-torsion parameter.

This is the core non-circular arithmetic lemma. It is independent of elliptic curves.
-/
theorem preNormEDS'_zero_param_ne_zero
    {k : Type*} [Field k] {c d : k} {n : ℕ}
    (hc : c ≠ 0)
    (hd : d ^ 2 = -4 * c ^ 3)
    (hn : (n : k) ≠ 0) :
    preNormEDS' (0 : k) c d n ≠ 0 := by
  -- Prove using the three closed forms:
  --
  --   preNormEDS' 0 c d (2*s + 1)
  --     = (-1)^(s*(s-1)/2) * c^(s*(s+1)/2)
  --
  --   preNormEDS' 0 c d (4*s + 2)
  --     = (2*s + 1 : k) * c^(2*s*(s+1))
  --
  --   preNormEDS' 0 c d (4*(s+1))
  --     = (s+1 : k) * c^(2*s*(s+2)) * d
  --
  -- The formulas are proved by induction using:
  --   preNormEDS'_zero
  --   preNormEDS'_one
  --   preNormEDS'_two
  --   preNormEDS'_three
  --   preNormEDS'_four
  --   preNormEDS'_even
  --   preNormEDS'_odd
  sorry
```

Once those four sublemmas exist, the final coprimality/no-common-root theorem is genuinely short and non-circular:

```lean
import Mathlib
import FLT.EllipticCurve.Torsion

noncomputable section

open Polynomial
open WeierstrassCurve

namespace WeierstrassCurve

universe u

variable {k : Type u} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic]

theorem preΨ'_eval_ne_zero_of_Ψ₂Sq_eval_eq_zero
    {n : ℕ} {x : k}
    (hn : (n : k) ≠ 0)
    (hx : W.Ψ₂Sq.eval x = 0) :
    (W.preΨ' n).eval x ≠ 0 := by
  have hc : W.Ψ₃.eval x ≠ 0 :=
    W.Ψ₃_eval_ne_zero_of_Ψ₂Sq_eval_eq_zero hx

  have hd :
      (W.preΨ₄.eval x) ^ 2 =
        -4 * (W.Ψ₃.eval x) ^ 3 :=
    W.preΨ₄_eval_sq_eq_neg_four_Ψ₃_eval_cube_of_Ψ₂Sq_eval_eq_zero hx

  have hpre :
      (W.preΨ' n).eval x =
        preNormEDS' (0 : k) (W.Ψ₃.eval x) (W.preΨ₄.eval x) n := by
    rw [W.eval_preΨ'_eq_preNormEDS'_eval n x, hx]
    simp

  rw [hpre]
  exact preNormEDS'_zero_param_ne_zero hc hd hn

/--
No common root form.
-/
theorem preΨ'_root_not_Ψ₂Sq_root
    {n : ℕ} {x : k}
    (hn : (n : k) ≠ 0)
    (hpre : (W.preΨ' n).eval x = 0) :
    W.Ψ₂Sq.eval x ≠ 0 := by
  intro hx
  exact W.preΨ'_eval_ne_zero_of_Ψ₂Sq_eval_eq_zero hn hx hpre

end WeierstrassCurve
```

This is the proof you want downstream: it does not use point realization, does not use `2 • P = 0 ↔ Ψ₂Sq(x)=0`, and therefore is not circular.

## Why the resultant route is longer

The resultant route would aim for:

```lean
theorem resultant_preΨ'_Ψ₂Sq_ne_zero
    {n : ℕ} (hn : (n : k) ≠ 0) :
    (W.preΨ' n).resultant W.Ψ₂Sq ≠ 0
```

Then use Mathlib:

```lean
Polynomial.resultant_eq_zero_iff
Polynomial.isUnit_resultant_iff_isCoprime
```

to get coprimality/no common root. Mathlib has the generic API; `Polynomial.resultant` is defined in `Mathlib.RingTheory.Polynomial.Resultant.Basic`, with lemmas such as `resultant_eq_zero_iff`, `resultant_eq_prod_eval`, `resultant_comm`, and `isUnit_resultant_iff_isCoprime`. The resultant file’s docs confirm these declarations. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Polynomial/Resultant/Basic.html))

But to prove the resultant nonzero, you still need essentially the same evaluation formula at every root of `Ψ₂Sq`:

```text
resultant(preΨ'_n, Ψ₂Sq)
= leadingCoeff(preΨ'_n)^3 * ∏_{Ψ₂Sq(α)=0} preΨ'_n(α).
```

So you still need:

```lean
preNormEDS'_zero_param_ne_zero
```

plus the polynomial identities for `Ψ₃` and `preΨ₄` at `Ψ₂Sq` roots, and then extra resultant/root-product bookkeeping. It is strictly more infrastructure for the same mathematical content.

## Smallest sublemma to start

Start here, in `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` or a local FLT helper file:

```lean
theorem preNormEDS'_zero_param_ne_zero
    {k : Type*} [Field k] {c d : k} {n : ℕ}
    (hc : c ≠ 0)
    (hd : d ^ 2 = -4 * c ^ 3)
    (hn : (n : k) ≠ 0) :
    preNormEDS' (0 : k) c d n ≠ 0
```

The closed-form supporting lemmas should be:

```lean
theorem preNormEDS'_zero_param_two_mul_add_one
    {k : Type*} [CommRing k] {c d : k}
    (hd : d ^ 2 = -4 * c ^ 3) (s : ℕ) :
    preNormEDS' (0 : k) c d (2 * s + 1)
      =
    (-1 : k) ^ (s * (s - 1) / 2) *
      c ^ (s * (s + 1) / 2)

theorem preNormEDS'_zero_param_four_mul_add_two
    {k : Type*} [CommRing k] {c d : k}
    (hd : d ^ 2 = -4 * c ^ 3) (s : ℕ) :
    preNormEDS' (0 : k) c d (4 * s + 2)
      =
    ((2 * s + 1 : ℕ) : k) * c ^ (2 * s * (s + 1))

theorem preNormEDS'_zero_param_four_mul_succ
    {k : Type*} [CommRing k] {c d : k}
    (hd : d ^ 2 = -4 * c ^ 3) (s : ℕ) :
    preNormEDS' (0 : k) c d (4 * (s + 1))
      =
    ((s + 1 : ℕ) : k) * c ^ (2 * s * (s + 2)) * d
```

This is the smallest honest non-circular kernel. Everything else reduces to `ring_nf` identities for `Ψ₂Sq`, `Ψ₃`, and `preΨ₄`.

## Named API summary

Use:

```lean
-- Division polynomial definitions/recurrences
WeierstrassCurve.Ψ₂Sq
WeierstrassCurve.Ψ₂Sq_eq
WeierstrassCurve.Ψ₃
WeierstrassCurve.preΨ₄
WeierstrassCurve.preΨ'
WeierstrassCurve.preΨ'_even
WeierstrassCurve.preΨ'_odd

-- EDS recurrences
preNormEDS'
preNormEDS'_zero
preNormEDS'_one
preNormEDS'_two
preNormEDS'_three
preNormEDS'_four
preNormEDS'_even
preNormEDS'_odd

-- Weierstrass discriminant/two-torsion cubic
WeierstrassCurve.twoTorsionPolynomial
WeierstrassCurve.twoTorsionPolynomial_discr
WeierstrassCurve.Ψ₂Sq_eq
WeierstrassCurve.IsElliptic
WeierstrassCurve.isUnit_Δ

-- If you later choose resultants
Polynomial.resultant
Polynomial.resultant_eq_zero_iff
Polynomial.isUnit_resultant_iff_isCoprime
Polynomial.resultant_eq_prod_eval
Polynomial.resultant_comm
```

The direct EDS-evaluation proof is the shorter and more robust route. The resultant route is useful only after this same EDS specialization has already been proved, so it should not be the first target.
