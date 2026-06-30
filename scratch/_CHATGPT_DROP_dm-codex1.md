# Q2642 (dm-codex1): `DoubleLegCoverDegenerate` non-circular route

Repo path mentioned by requester: `/Users/huangx/repos/flt-ai`  
Lean project: `FLT`  
Main file context: N=12 Mazur proof

This note separates the true mathematical reduction from Lean import/wiring suggestions.  The short conclusion is:

* The double-leg obstruction is **not** a direct four-rational-squares-in-AP obstruction.
* A short denominator-clearing use of Mathlib FLT4 / `not_fermat_42` is also **not** the natural target.
* The natural obstruction is the Eisenstein quartic

  ```text
  s^2 = t^4 - t^2 + 1.
  ```

* To avoid circularity, prove that quartic classification in a small independent file, not via the current E24/E1 finite-point theorem.

## 1. AP alone: no direct four-square AP substitution

Given

```lean
hh : h ^ 2 = x ^ 2 + y ^ 2
hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2
```

we have

```text
h^2 = y^2 + x^2,
k^2 = y^2 + 4*x^2.
```

So the visible square values

```text
y^2, h^2, k^2
```

sit at positions

```text
y^2,
y^2 + x^2,
y^2 + 4*x^2,
```

whose gaps are `x^2` and `3*x^2`, not a common AP gap.  The missing values for a four-term AP with gap `x^2` would be

```text
y^2 + 2*x^2,
y^2 + 3*x^2,
```

and the two double-leg equations do not assert that either is a square.

The usual Pythagorean-triangle-to-three-squares construction gives only two **three-term** APs with different gaps:

```text
((x - y) / 2)^2,      (h / 2)^2, ((x + y) / 2)^2       gap = x*y/2
((2*x - y) / 2)^2,    (k / 2)^2, ((2*x + y) / 2)^2     gap = x*y
```

They do not glue into one four-term AP over `ℚ`.  Extending the first three-term AP would require the fourth square

```text
((x + y) / 2)^2 + x*y/2 = (x^2 + 4*x*y + y^2) / 4,
```

whereas the second double-leg equation gives the unrelated square

```text
k^2 / 4 = (4*x^2 + y^2) / 4.
```

So the tempting AP route is false in the direct sense needed for a clean Lean proof.  `FourRatSquaresAPConst` closes the nondegenerate cover residuals, but it does not directly supply `DoubleLegCoverDegenerate`.

I would not add a theorem claiming

```lean
FourRatSquaresAPConst → DoubleLegCoverDegenerate
```

unless you first prove a genuinely new bridge from the double-leg equations to a nonconstant four-square AP.  The elementary algebra above is strong evidence that this is the wrong bridge: the natural reduction is to an Eisenstein quartic, not to a four-square AP.

## 2. The corrected obstruction: Eisenstein quartic

Assume `x ≠ 0` and `y ≠ 0`; otherwise `DoubleLegCoverDegenerate` is already proved.  Use the second right-triangle equation

```lean
hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2
```

to parametrize the rational point on the conic.  Define

```text
t   = (k - y) / (2*x),
lam = x / t,
s   = h / lam = h*t/x.
```

Then, from `(k - y) * (k + y) = (2*x)^2`, one obtains

```text
2*x = 2*t*lam,
y   = (1 - t^2)*lam,
k   = (1 + t^2)*lam.
```

Now substitute these into the first equation:

```text
h^2 = x^2 + y^2
    = (t*lam)^2 + ((1 - t^2)*lam)^2
    = lam^2 * (t^4 - t^2 + 1).
```

Thus

```text
s^2 = t^4 - t^2 + 1.
```

Moreover:

* `t = 0` would force `k = y`, hence `(2*x)^2 = 0`, hence `x = 0`.
* `t^2 = 1` gives `y = (1 - t^2)*lam = 0`.

Therefore a theorem saying that all rational points on the Eisenstein quartic have `t = 0` or `t^2 = 1` immediately proves `DoubleLegCoverDegenerate`.

The clean interface is:

```lean
import FLT.Assumptions.MazurProof.N12E1CoverResiduals
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Independent rational Eisenstein-quartic obstruction. -/
def RatQuarticEisensteinDegenerate : Prop :=
  ∀ {t s : ℚ},
    s ^ 2 = t ^ 4 - t ^ 2 + 1 →
    t = 0 ∨ t ^ 2 = 1

/-- The double-leg residual follows from the independent Eisenstein-quartic obstruction. -/
theorem doubleLegCoverDegenerate_of_ratQuarticEisensteinDegenerate
    (hEis : RatQuarticEisensteinDegenerate) :
    DoubleLegCoverDegenerate := by
  -- Proof DAG:
  -- intro x y h k hh hk
  -- by_cases hx : x = 0; exact Or.inl hx
  -- by_cases hy : y = 0; exact Or.inr hy
  -- set t : ℚ := (k - y) / (2*x)
  -- set lam : ℚ := x / t
  -- set s : ℚ := h / lam
  -- prove ht0 : t ≠ 0 from hx and hk
  -- prove hlam0 : lam ≠ 0 from hx and ht0
  -- prove hparam_x : x = t*lam
  -- prove hparam_y : y = (1 - t^2)*lam
  -- prove hquartic : s^2 = t^4 - t^2 + 1 by substituting into hh and field_simp [hlam0]
  -- rcases hEis hquartic with ht | ht2
  -- · exact False.elim (ht0 ht) |> Or.elim?  -- choose Or.inl only in impossible branch
  -- · have : y = 0 := by simpa [hparam_y, ht2]
  --   exact Or.inr this
  -- The actual implementation should avoid the impossible-branch comment above and simply
  -- use `exfalso` or contradiction before returning the desired disjunction.
  admit

end MazurProof.RationalPointsN12
```

The code block above is a proof DAG, not paste-ready code; do not commit it with `admit`.  The important point is the theorem shape and the parameter definitions.

A more implementation-friendly helper is to split out the nonzero reduction:

```lean
import FLT.Assumptions.MazurProof.N12E1CoverResiduals
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Nonzero double-leg data produce a nontrivial rational point on the Eisenstein quartic. -/
theorem ratQuarticEisenstein_of_double_leg_nonzero
    {x y h k : ℚ}
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2) :
    ∃ t s : ℚ,
      t ≠ 0 ∧ t ^ 2 ≠ 1 ∧
      s ^ 2 = t ^ 4 - t ^ 2 + 1 := by
  -- Use t=(k-y)/(2*x), lam=x/t, s=h/lam.
  -- The proof is rational field algebra plus the two nonzero hypotheses.
  admit

/-- Linear wrapper from the quartic obstruction to the cover residual. -/
theorem doubleLegCoverDegenerate_of_ratQuarticEisensteinDegenerate'
    (hEis : RatQuarticEisensteinDegenerate) :
    DoubleLegCoverDegenerate := by
  -- intro x y h k hh hk
  -- by_cases hx : x = 0; exact Or.inl hx
  -- by_cases hy : y = 0; exact Or.inr hy
  -- rcases ratQuarticEisenstein_of_double_leg_nonzero hx hy hh hk with
  --   ⟨t, s, ht0, htne1, hquartic⟩
  -- rcases hEis hquartic with ht | ht2
  -- · exact False.elim (ht0 ht)
  -- · exact False.elim (htne1 ht2)
  admit

end MazurProof.RationalPointsN12
```

Again: theorem shapes only; remove `admit` in real code.

## 3. FLT4 / `not_fermat_42` is not a short denominator-clearing route

A short denominator-clearing route from `not_fermat_42` would need the double-leg equations to produce an integer equation of the form forbidden by FLT4, such as

```text
A^4 + B^4 = C^2
```

or an integer/rational right triangle with square area.  The actual denominator-cleared target is different.

From the Eisenstein quartic, choose a common denominator `N` so that

```text
t = A / N,
s = S / N^2.
```

Clearing denominators gives

```text
S^2 = A^4 - A^2*N^2 + N^4.
```

So the needed integer theorem is the homogeneous Eisenstein quartic obstruction:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Integer homogeneous Eisenstein-quartic obstruction. -/
def IntQuarticEisensteinDegenerate : Prop :=
  ∀ {A N S : ℤ},
    N ≠ 0 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    A = 0 ∨ A ^ 2 = N ^ 2

/-- Rational denominator clearing from the homogeneous integer theorem. -/
theorem ratQuarticEisensteinDegenerate_of_int
    (hZ : IntQuarticEisensteinDegenerate) :
    RatQuarticEisensteinDegenerate := by
  -- Proof DAG:
  -- intro t s hquartic
  -- choose a common nonzero integer denominator N with t=A/N and s=S/N^2
  -- clear denominators to get S^2 = A^4 - A^2*N^2 + N^4
  -- apply hZ
  -- translate A=0 to t=0 and A^2=N^2 to t^2=1
  admit

end MazurProof.RationalPointsN12
```

That theorem is not `not_fermat_42`.  It is an Eisenstein / `j = 0` quartic, while the four-square-AP / square-area / FLT4 obstruction is the `j = 1728` Fermat-right-triangle obstruction.

So the answer to “is it derivable from Mathlib FLT4 with a short rational-denominator clearing argument?” is **no**.  If somebody proves

```lean
theorem intQuarticEisensteinDegenerate_of_not_fermat_42 :
    IntQuarticEisensteinDegenerate := ...
```

that proof would be a real additional descent or elliptic-curve argument, not just denominator clearing.  I would not make `not_fermat_42` the planned dependency unless you already have that bridge checked.

## 4. The Eisenstein-quartic route and circularity boundary

The current theorem described as

```lean
doubleLeg_of_ratQuarticEisenstein
```

in `RationalPointsN12.lean` is not safe as an upstream input if it uses

```lean
RatQuarticEisensteinXClassification
```

and that classification is routed through the E24/E1 finite-point theorem that the full-cover proof is trying to establish.  That is a real circularity.

The non-circular boundary is:

```text
N12E1CoverResiduals
  defines DoubleLegCoverDegenerate and conditional cover residuals
        ▲
        │
N12DoubleLegDegenerate
  proves DoubleLegCoverDegenerate from an independent Eisenstein-quartic theorem
        ▲
        │
N12QuarticEisensteinElementary
  proves RatQuarticEisensteinDegenerate or IntQuarticEisensteinDegenerate
  without importing E24/E1 finite-point, full cover, or RationalPointsN12 terminal theorems
```

Forbidden route:

```text
DoubleLegCoverDegenerate
  ← RatQuarticEisensteinXClassification
  ← E24/E1 finite-point theorem
  ← full-cover residuals
  ← DoubleLegCoverDegenerate
```

The Eisenstein theorem can be a strictly smaller independent theorem if proved by elementary descent in the Eisenstein integers, or by a standalone classification of

```text
s^2 = t^4 - t^2 + 1
```

that does not mention the E1 finite-point theorem.  But if the proof imports the same E1 finite-point theorem, it is circular and should stay terminal/downstream only.

## 5. Recommended Lean import placement

### Keep `N12E1CoverResiduals.lean` conditional

Do not import `N12FourSquaresAP.lean`, `N12CheckedDescentBridge.lean`, `RationalPointsN12.lean`, or any E1 full-cover theorem into `N12E1CoverResiduals.lean`.

```lean
-- N12E1CoverResiduals.lean

namespace MazurProof.RationalPointsN12

def DoubleLegCoverDegenerate : Prop :=
  ∀ {x y h k : ℚ},
    h ^ 2 = x ^ 2 + y ^ 2 →
    k ^ 2 = (2 * x) ^ 2 + y ^ 2 →
    x = 0 ∨ y = 0

-- Degenerate residuals should keep taking
--   (hDL : DoubleLegCoverDegenerate)
-- explicitly.

end MazurProof.RationalPointsN12
```

### Add a small non-circular bridge file

```lean
-- FLT/Assumptions/MazurProof/N12DoubleLegDegenerate.lean

import FLT.Assumptions.MazurProof.N12E1CoverResiduals
import FLT.Assumptions.MazurProof.N12QuarticEisensteinElementary
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Convert nonzero double-leg data to a nontrivial Eisenstein-quartic point. -/
theorem ratQuarticEisenstein_of_double_leg_nonzero
    {x y h k : ℚ}
    (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hh : h ^ 2 = x ^ 2 + y ^ 2)
    (hk : k ^ 2 = (2 * x) ^ 2 + y ^ 2) :
    ∃ t s : ℚ,
      t ≠ 0 ∧ t ^ 2 ≠ 1 ∧
      s ^ 2 = t ^ 4 - t ^ 2 + 1 := by
  -- Implement with t=(k-y)/(2*x), lam=x/t, s=h/lam.
  admit

/-- Checked, non-circular double-leg residual. -/
theorem doubleLegCoverDegenerate_checked : DoubleLegCoverDegenerate := by
  -- Use `ratQuarticEisenstein_of_double_leg_nonzero` and
  -- `ratQuarticEisensteinDegenerate_checked` from the independent file.
  admit

end MazurProof.RationalPointsN12
```

Do not commit those `admit`s; they mark the proof DAG only.

### Independent quartic file

```lean
-- FLT/Assumptions/MazurProof/N12QuarticEisensteinElementary.lean

import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

def RatQuarticEisensteinDegenerate : Prop :=
  ∀ {t s : ℚ},
    s ^ 2 = t ^ 4 - t ^ 2 + 1 →
    t = 0 ∨ t ^ 2 = 1

def IntQuarticEisensteinDegenerate : Prop :=
  ∀ {A N S : ℤ},
    N ≠ 0 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    A = 0 ∨ A ^ 2 = N ^ 2

/-- Prove this independently, e.g. by Eisenstein-integer descent. -/
theorem intQuarticEisensteinDegenerate_checked :
    IntQuarticEisensteinDegenerate := by
  -- Independent proof only.  Do not import E1 finite-point or full-cover modules.
  admit

/-- Rational consequence by common-denominator clearing. -/
theorem ratQuarticEisensteinDegenerate_checked :
    RatQuarticEisensteinDegenerate := by
  -- Apply `intQuarticEisensteinDegenerate_checked` after homogeneous clearing.
  admit

end MazurProof.RationalPointsN12
```

Again, no `admit` in real code; these are theorem-shape placeholders.

## 6. Concrete helper lemmas to implement

I would implement these in this order.

```lean
import FLT.Assumptions.MazurProof.N12E1CoverResiduals
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

-- Algebra from the second double-leg equation.
-- Proves `(k-y)*(k+y) = (2*x)^2`.
-- This is just `nlinarith`/`ring_nf` from `hk`.
-- theorem double_leg_factor ...

-- Nonzero parameter `t=(k-y)/(2*x)`.
-- theorem double_leg_t_ne_zero ...

-- Parameter identities:
-- theorem double_leg_param_x : x = t*lam
-- theorem double_leg_param_y : y = (1 - t^2)*lam
-- theorem double_leg_param_k : k = (1 + t^2)*lam

-- Quartic identity after substituting into `h^2=x^2+y^2`.
-- theorem eisenstein_quartic_from_param :
--   s^2 = t^4 - t^2 + 1

-- Nontriviality transfer:
-- theorem y_ne_zero_of_t_sq_ne_one contrapositive, or directly:
--   y ≠ 0 → t^2 ≠ 1

end MazurProof.RationalPointsN12
```

For denominator clearing, prefer homogeneous common-denominator clearing over reduced fractions.  It avoids proving that the denominator of `s` divides the square of the denominator of `t`.

Use a lemma with this shape:

```lean
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- Common denominator representation for a pair `(t,s)` as `(A/N, S/N^2)`. -/
theorem rat_pair_as_num_over_common_square_den
    (t s : ℚ) :
    ∃ A N S : ℤ,
      N ≠ 0 ∧
      t = (A : ℚ) / N ∧
      s = (S : ℚ) / (N ^ 2 : ℤ) := by
  -- Take any denominator `n₁` for `t` and `n₂` for `s`, then set `N=n₁*n₂`.
  -- If t=a/n₁ and s=b/n₂, then
  --   t = (a*n₂)/(n₁*n₂)
  --   s = (b*n₁^2*n₂)/(n₁^2*n₂^2) = S/N^2.
  admit

end MazurProof.RationalPointsN12
```

Then clearing `s^2 = t^4 - t^2 + 1` is just `field_simp` plus `ring`.

## 7. Final recommendation

Do not try to use `FourRatSquaresAPConst` for `DoubleLegCoverDegenerate`.  It does not give the missing fourth AP square from the two double-leg equations.

Do not rely on the current `doubleLeg_of_ratQuarticEisenstein` if it imports or depends on the E24/E1 finite-point theorem.  That is circular for the full-cover proof.

The clean non-circular route is:

```text
independent Eisenstein quartic theorem
  RatQuarticEisensteinDegenerate
        ↓
doubleLegCoverDegenerate_of_ratQuarticEisensteinDegenerate
        ↓
DoubleLegCoverDegenerate
        ↓
degenerate cover residuals
```

If you do not yet want to formalize the independent Eisenstein descent, keep `DoubleLegCoverDegenerate` as an explicit residual.  Do not hide it behind `FourRatSquaresAPConst`, `not_fermat_42`, or the finite-point theorem.
