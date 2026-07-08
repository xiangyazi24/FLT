ANSWER Q3862 d87fdfaf

# Feasibility notes for cyclic torsion exclusions in Tate normal form

## Executive answer

The raw division-polynomial route is less frightening for `n = 11` and `n = 13` than it first looks, **provided you evaluate at the Tate origin `(0,0)` early and remove the obvious Tate degeneracy factor `b^k`**.  The specialized conditions are small:

* `ψ₁₁(0,0) = b^40 * F11(b,c)`, where `F11` has **11 monomials**, `b`-degree `5`, `c`-degree `7`, and total degree `8`.
* `ψ₁₃(0,0) = - b^56 * F13(b,c)`, where `F13` has **20 monomials**, `b`-degree `7`, `c`-degree `10`, and total degree `11`.

So the next Lean layer should **not** expand general `ψₙ(x)` and then specialize.  Define a tiny specialized recurrence for `ψₙ(P)` at the Tate origin and prove the displayed factorizations by `ring_nf`/`ring`.

For composite exclusions, do not use a single giant `ψₙ` unless `n` is a prime power.  For `n = ab` with `(a,b)=1`, use elementary group theory: a point of order `ab` is equivalent to simultaneous rational points of orders `a` and `b`.  That is the right Lean shape for `14,15,18,20,21,24`.

There is **no elementary uniform tail** from just Weil pairing, `|E(ℝ)[n]| ≤ 2n`, the rank-two torsion decomposition with `m₁ ≤ 2`, and group theory.  Those facts are compatible with cyclic torsion `ℤ/Nℤ` for arbitrarily large `N`.  A tail needs extra arithmetic input: modular curves, reduction/Hasse plus good-prime arguments, isogeny theorems, or a known uniform boundedness theorem.

## Normal-form algebra to prove first

For the Tate normal form

```text
E(b,c) : y^2 + (1-c)xy - b y = x^3 - b x^2,
P = (0,0),
a1 = 1-c,
a2 = -b,
a3 = -b,
a4 = 0,
a6 = 0,
```

the standard `bᵢ` invariants become

```text
b2 = (1-c)^2 - 4*b
b4 = b*(c-1)
b6 = b^2
b8 = -b^3
```

Use these as rewrite lemmas.  Then the first specialized division-polynomial values at `P` are:

```text
ψ₂(P) = -b
ψ₃(P) = -b^3
ψ₄(P) = b^5*c
ψ₅(P) = b^8*(b-c)
ψ₆(P) = b^12*(b-c-c^2)
ψ₇(P) = b^16*(c^3 - b^2 + b*c)
ψ₈(P) = -b^21*c*(2*b^2 - 3*b*c - b*c^2 + c^2)
ψ₉(P) = b^27*((b-c)^3 + c^3*(b-c-c^2))
```

These formulas are more useful than full `ψₙ(x)` polynomials.  They also give the allowed-family relations:

```text
order 4 at P:   c = 0                         (with b ≠ 0)
order 5 at P:   b - c = 0                     (with b ≠ 0)
order 6 at P:   b - c - c^2 = 0               (with b ≠ 0)
order 7 at P:   c^3 - b^2 + b*c = 0           (with b ≠ 0)
order 8 at P:   2*b^2 - 3*b*c - b*c^2 + c^2=0 (with b ≠ 0 and c ≠ 0)
order 9 at P:   (b-c)^3 + c^3*(b-c-c^2)=0     (with b ≠ 0)
```

For Lean, define the small factors, not the expanded forms, as canonical.

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur.TateNF

variable {K : Type*} [Field K]

/-- `ψ₅(0,0) / b^8`. -/
def F5 (b c : K) : K := b - c

/-- `ψ₆(0,0) / b^12`. -/
def F6 (b c : K) : K := b - c - c^2

/-- `ψ₇(0,0) / b^16`. -/
def F7 (b c : K) : K := c^3 - b^2 + b*c

/-- The non-`b`, non-`c` factor of `ψ₈(0,0)`. -/
def F8 (b c : K) : K := 2*b^2 - 3*b*c - b*c^2 + c^2

/-- `ψ₉(0,0) / b^27`. -/
def F9 (b c : K) : K := (b-c)^3 + c^3*(b-c-c^2)

/-- The compact form of `ψ₁₁(0,0) / b^40`. -/
def F11 (b c : K) : K :=
  (c^3 - b*(b-c))*(b-c)^3 - b*c*(b-c-c^2)^3

/-- The compact form of `-ψ₁₃(0,0) / b^56`. -/
def F13 (b c : K) : K :=
  (b-c)*(c^3 - b*(b-c))^3 +
    b*c*(2*b^2 - 3*b*c - b*c^2 + c^2)*(b-c-c^2)^3

/-- The compact form of `ψ₁₅(0,0) / b^75`, useful for cyclic `15`
if one decides to attack `X₁(15)` from the Tate origin directly. -/
def F15 (b c : K) : K :=
  F9 b c * (F7 b c)^3 + (b-c-c^2)*c^3*(F8 b c)^3

end FLT.Mazur.TateNF
```

Then add the concrete rational-field evaluation lemmas.  The right-hand sides below are the ones to make theorems; their proofs should be `ring_nf` after unfolding the specialized recurrence.

```lean
import Mathlib

noncomputable section

namespace FLT.Mazur.TateNF

-- Placeholder for your already-defined generalized division polynomial specialized at `P=(0,0)`.
-- In the implementation this should be your actual definition, not an axiom.
def psiOrigin (n : ℕ) (b c : ℚ) : ℚ := 0

-- In real code, delete the placeholder definition above and prove the following from the recurrence.

theorem psi5_origin_factor (b c : ℚ) :
    psiOrigin 5 b c = b^8 * F5 b c := by
  -- unfold psiOrigin F5; ring_nf
  sorry

theorem psi7_origin_factor (b c : ℚ) :
    psiOrigin 7 b c = b^16 * F7 b c := by
  -- unfold psiOrigin F7; ring_nf
  sorry

theorem psi8_origin_factor (b c : ℚ) :
    psiOrigin 8 b c = - b^21 * c * F8 b c := by
  -- unfold psiOrigin F8; ring_nf
  sorry

theorem psi9_origin_factor (b c : ℚ) :
    psiOrigin 9 b c = b^27 * F9 b c := by
  -- unfold psiOrigin F9; ring_nf
  sorry

theorem psi11_origin_factor (b c : ℚ) :
    psiOrigin 11 b c = b^40 * F11 b c := by
  -- unfold psiOrigin F11; ring_nf
  sorry

theorem psi13_origin_factor (b c : ℚ) :
    psiOrigin 13 b c = - b^56 * F13 b c := by
  -- unfold psiOrigin F13; ring_nf
  sorry

end FLT.Mazur.TateNF
```

The `sorry`s above are only skeleton markers for the file plan.  The intended checked proof is the recurrence plus `ring_nf`; no axiom is needed.

## Q1. Division-polynomial sizes

### `n = 11`

Use

```text
F11(b,c) = (c^3 - b*(b-c))*(b-c)^3 - b*c*(b-c-c^2)^3.
```

Expanded:

```text
F11 =
  - b^5
  + 3*b^4*c
  - 3*b^3*c^2
  + b^2*c^3
  + 4*b^3*c^3
  - 9*b^2*c^4
  + 6*b*c^5
  - c^6
  - 3*b^2*c^5
  + 3*b*c^6
  + b*c^7.
```

So after removing `b^40`, it is **11 terms**, not degree `20-30` in each variable.  The maximal `b` exponent is `5`, maximal `c` exponent is `7`, and maximal total degree is `8`.

Lean implementation advice: keep the compact product form as `def F11`; prove a separate optional expanded-normal-form lemma only if a later `ring_nf` proof needs it.

### `n = 13`

Use

```text
F13(b,c) =
  (b-c)*(c^3 - b*(b-c))^3
  + b*c*(2*b^2 - 3*b*c - b*c^2 + c^2)*(b-c-c^2)^3.
```

One expanded normalization has **20 monomials**:

```text
F13 =
  - b^7
  + 6*b^6*c
  - 15*b^5*c^2
  - 4*b^5*c^3
  + 20*b^4*c^3
  + 15*b^4*c^4
  + 9*b^4*c^5
  - 15*b^3*c^4
  - 21*b^3*c^5
  - 24*b^3*c^6
  - 5*b^3*c^7
  + 6*b^2*c^5
  + 13*b^2*c^6
  + 21*b^2*c^7
  + 6*b^2*c^8
  + b^2*c^9
  - b*c^6
  - 3*b*c^7
  - 6*b*c^8
  - c^10.
```

Here `ψ₁₃(0,0) = -b^56 * F13(b,c)`.  After removing `b^56`, the maximal `b` exponent is `7`, maximal `c` exponent is `10`, and maximal total degree is `11`.

Again, keep the compact form canonical.

### `n = 14 = 2*7`

There are two possible encodings.  The Lean-friendly one is **not** “`ψ₇(P)=0` and `ψ₂(P)=0` at the same Tate-origin point `P`.”  If the Tate origin itself has order `14`, then `ψ₁₄(P)=0` and `ψ₇(P) ≠ 0`.

The better composite encoding is:

* put an order-`7` point at the Tate origin, so `F7(b,c)=0`;
* ask for an independent rational point of order `2`, i.e. a rational root of the 2-division cubic.

The 2-division `x`-polynomial for `E(b,c)` is

```text
T2(b,c,X) =
  4*X^3 + ((1-c)^2 - 4*b)*X^2 + 2*b*(c-1)*X + b^2.
```

So the system is

```text
F7(b,c) = 0,
∃ X : ℚ, T2(b,c,X) = 0,
b ≠ 0,
disc(E(b,c)) ≠ 0.
```

Using the reverse parametrization of `F7=0`, for example

```text
b = u^2*(u-1),
c = u*(u-1),
```

the existence of rational 2-torsion reduces to the elliptic obstruction curve

```text
C14 : z^2 = 4*u^3 + u^2 - 2*u + 1.
```

The only rational `u` on this curve should be the degenerate/cusp values `u ∈ {-1,0,1}` in the chosen parametrization.  This is a small rank-zero elliptic-curve computation and is the right formal target for `14`.

### `n = 25 = 5^2`

The prompt’s proposed condition has the direction reversed.  If the Tate origin `P=(0,0)` has exact order `25`, then

```text
[25]P = 0  and  [5]P ≠ 0.
```

Equivalently, in division-polynomial language over characteristic zero,

```text
ψ₂₅(P) = 0  and  ψ₅(P) ≠ 0.
```

Since `ψ₅(P)=b^8*(b-c)`, exact order `25` requires `b-c ≠ 0` after the nondegeneracy hypothesis `b ≠ 0`.  The condition `ψ₅(P)=0` would make `[5]P=0`, i.e. order dividing `5`, not order `25`.

For Lean, the group-theory lemma should be independent of elliptic curves:

```lean
import Mathlib

namespace FLT.Mazur.GroupTheory

variable {G : Type*} [AddGroup G]

/-- Exact order `25` in additive notation. -/
theorem addOrderOf_eq_25_iff (P : G) :
    addOrderOf P = 25 ↔ (25 : ℕ) • P = 0 ∧ (5 : ℕ) • P ≠ 0 := by
  -- Suggested proof:
  -- * use `addOrderOf_dvd_iff_nsmul_eq_zero` in both directions;
  -- * divisors of 25 are 1,5,25;
  -- * exclude 1 and 5 using `5 • P ≠ 0`.
  sorry

end FLT.Mazur.GroupTheory
```

Mathematically, `X₁(25)` is a much harder curve than `11,13,14,15,16`; I would not put it in the first computational batch unless you already have a modular-curve rational-points proof available.  If you attack it by Tate normal form, use `ψ₂₅(P)=0 ∧ ψ₅(P)≠0`, not `ψ₅(P)=0`.

## Q2. Diophantine solvability

### `n = 11`

The equation `F11(b,c)=0` is one equation in two variables, i.e. a curve.  There is no meaningful single univariate resultant that proves impossibility by “no rational roots”: the projective closure has rational cusp/degenerate points.  The right statement is:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- Nondegenerate Tate-normal-form point of exact order 11 gives a rational point
on the `X₁(11)` obstruction curve. -/
theorem exactOrder11_to_C11
    {b c : ℚ}
    (hb : b ≠ 0)
    (hdisc : True) -- replace by the actual nonsingularity/discriminant predicate
    (h11 : F11 b c = 0) :
    True := by
  -- construct the rational point on the chosen model of X₁(11)
  trivial

/-- The only rational points on the chosen `X₁(11)` model are cusps. -/
theorem C11_rational_points_are_cusps : True := by
  -- rank-zero elliptic curve computation, no axiom
  trivial

/-- No nonsingular Tate normal form has the origin of exact order 11. -/
theorem no_tate_origin_exact_order_11
    {b c : ℚ} (hb : b ≠ 0) (hdisc : True) :
    F11 b c ≠ 0 := by
  -- combine `exactOrder11_to_C11` with `C11_rational_points_are_cusps`
  sorry

end FLT.Mazur.TateNF
```

In implementation terms, prove a birational map from the plane curve `F11=0` to a rank-zero elliptic model of `X₁(11)`, then enumerate rational points and show they are exactly the degeneracies.  Do not try to make “irreducibility of a univariate resultant” carry the argument.

### `n = 13`

The same warning is stronger.  `F13=0` is a genus-2 obstruction, not a univariate no-root problem.  The practical path is:

1. prove `ψ₁₃(0,0) = -b^56 * F13(b,c)`;
2. prove a birational map from the nondegenerate locus of `F13=0` to a standard hyperelliptic model of `X₁(13)`;
3. prove rational points on that model are cusps/degenerate points only.

A common hyperelliptic target for `X₁(13)` should be fixed once in the codebase.  Do not rely on the exact displayed model until its birational map from your `F13` convention is checked by `ring`; different Kubert/Tate parameter conventions change signs and Möbius transformations.

Skeleton:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- Nondegenerate `F13=0` gives a rational point on the chosen genus-2 model of `X₁(13)`. -/
theorem exactOrder13_to_C13
    {b c : ℚ}
    (hb : b ≠ 0)
    (hdisc : True) -- replace by actual nonsingularity
    (h13 : F13 b c = 0) :
    True := by
  trivial

/-- Rational points on the chosen `X₁(13)` model are only cusps. -/
theorem C13_rational_points_are_cusps : True := by
  -- This is the real arithmetic theorem: usually a genus-2 rational-points computation.
  trivial

/-- No nonsingular Tate normal form has the origin of exact order 13. -/
theorem no_tate_origin_exact_order_13
    {b c : ℚ} (hb : b ≠ 0) (hdisc : True) :
    F13 b c ≠ 0 := by
  sorry

end FLT.Mazur.TateNF
```

### `n = 14, 15, 16`

The obstruction-curve approach is standard in spirit, but the details differ.

#### `14`

Use the order-`7` family plus rational 2-torsion.  The explicit obstruction curve is

```text
C14 : z^2 = 4*u^3 + u^2 - 2*u + 1.
```

Lean theorem shape:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

def T2 (b c X : ℚ) : ℚ :=
  4*X^3 + ((1-c)^2 - 4*b)*X^2 + 2*b*(c-1)*X + b^2

def C14 (u z : ℚ) : Prop :=
  z^2 = 4*u^3 + u^2 - 2*u + 1

theorem order7_and_order2_to_C14
    {b c X : ℚ}
    (h7 : F7 b c = 0)
    (h2 : T2 b c X = 0)
    (hb : b ≠ 0) :
    ∃ u z : ℚ, C14 u z := by
  -- reverse-parametrize `F7=0`, then transform the root of `T2` to `z`
  sorry

theorem C14_rational_points_degenerate
    {u z : ℚ} (h : C14 u z) :
    u = -1 ∨ u = 0 ∨ u = 1 := by
  -- rank-zero elliptic curve / finite rational-point computation
  sorry

end FLT.Mazur.TateNF
```

#### `15`

Two viable routes:

* direct odd-order route: put a hypothetical order-`15` point at the Tate origin and use `F15(b,c)=0` with exactness conditions `F3≠0` and `F5≠0`;
* simultaneous route: order `3` point plus order `5` point, because `gcd(3,5)=1`.

The direct route is algebraically compact because the specialized recurrence gives

```text
ψ₁₅(0,0) = b^75 * F15(b,c),
F15 = F9*F7^3 + (b-c-c^2)*c^3*F8^3.
```

Exact order `15` at the origin requires

```text
F15(b,c)=0,
b ≠ 0,
b-c ≠ 0,
disc(E(b,c)) ≠ 0.
```

The obstruction curve is the genus-one curve `X₁(15)` obtained from this plane model after removing cusp components.  I recommend making the plane model `F15=0` the first checked object, then adding a separately checked birational map to the chosen elliptic model of `X₁(15)`.  Avoid hard-coding an external model unless you also prove the map from your `b,c` convention by `ring`.

Skeleton:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

theorem psi15_origin_factor (b c : ℚ) :
    psiOrigin 15 b c = b^75 * F15 b c := by
  -- recurrence + ring_nf
  sorry

/-- Exact-order-15 Tate origin gives a point on the chosen `X₁(15)` obstruction model. -/
theorem exactOrder15_to_C15
    {b c : ℚ}
    (hb : b ≠ 0)
    (hnot5 : b - c ≠ 0)
    (hdisc : True)
    (h15 : F15 b c = 0) :
    True := by
  sorry

theorem C15_rational_points_are_cusps : True := by
  -- rank-zero genus-one computation for the chosen X₁(15) model
  trivial

end FLT.Mazur.TateNF
```

#### `16`

`16` is not a coprime-composite problem.  It is a 2-primary divisibility problem: an order-`16` point is an order-`8` point that is rationally 2-divisible in the right way.

Use a standard genus-2 model of `X₁(16)` as the obstruction target, for example a hyperelliptic model of the shape

```text
C16 : Y^2 = X*(X^2 + 1)*(X^2 + 2*X - 1),
```

but, as with `13`, fix the exact model only together with a checked birational map from your Tate-normal-form convention.  The Tate-origin exact-order condition is

```text
ψ₁₆(P)=0,
ψ₈(P)≠0,
```

not just the order-`8` relation `F8=0`.  If you want to build from the order-`8` family, express the extra condition as “the order-`8` point is rationally 2-divisible”; do not replace it by existence of a rational 2-torsion point.

Lean shape:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- The chosen hyperelliptic obstruction model for `X₁(16)`. -/
def C16 (X Y : ℚ) : Prop :=
  Y^2 = X * (X^2 + 1) * (X^2 + 2*X - 1)

/-- A hypothetical exact-order-16 Tate origin maps to `C16`. -/
theorem exactOrder16_to_C16
    {b c : ℚ}
    (hb : b ≠ 0)
    (hdisc : True)
    (h16 : psiOrigin 16 b c = 0)
    (hnot8 : psiOrigin 8 b c ≠ 0) :
    ∃ X Y : ℚ, C16 X Y := by
  -- prove using the checked birational map from the exact Tate convention
  sorry

/-- Rational points on the selected `X₁(16)` model are cusps only. -/
theorem C16_rational_points_are_cusps
    {X Y : ℚ} (h : C16 X Y) : True := by
  -- genus-2 rational-points computation
  trivial

end FLT.Mazur.TateNF
```

## Q3. No elementary uniform tail from the listed ingredients

The answer is **no**.

The listed ingredients imply, at most, that rational torsion has abstract form

```text
ℤ/m₁ℤ × ℤ/m₂ℤ,  with m₁ | m₂ and m₁ ≤ 2,
```

or equivalently that full `n`-torsion is very restricted over `ℚ`.  They do **not** bound the cyclic factor `m₂`.  The cyclic group `ℤ/Nℤ` is compatible with all of those group-theoretic constraints for arbitrary `N`:

* `m₁ = 1 ≤ 2`;
* there is no full `n × n` torsion, so the Weil-pairing obstruction does not fire;
* the real-torsion size bound is also compatible with a cyclic `N`-torsion subgroup, since cyclic `n`-torsion has at most `n` elements, hence certainly at most `2n`.

A formal “countermodel to the method” can be stated purely in group theory:

```lean
import Mathlib

namespace FLT.Mazur.GroupTheory

/-- The proposed elementary constraints do not rule out arbitrarily large cyclic torsion groups.
This is not an elliptic-curve existence statement; it is a formal obstruction to proving a
uniform tail from those constraints alone. -/
theorem cyclic_groups_satisfy_elementary_constraints (N : ℕ) (hN : 0 < N) :
    ∃ G : Type, ∃ _ : AddCommGroup G, ∃ g : G,
      addOrderOf g = N := by
  refine ⟨ZMod N, inferInstance, (1 : ZMod N), ?_⟩
  -- There is a mathlib lemma for `addOrderOf (1 : ZMod N)`; use it here.
  sorry

end FLT.Mazur.GroupTheory
```

Therefore a proof of “all `n > B` are impossible” needs extra arithmetic.  In a Mazur formalization this extra arithmetic is exactly the hard part: modular curves, isogeny results, reduction plus good-prime control, or a uniform boundedness theorem.  The four listed elementary facts alone cannot produce a finite `B`.

## Q4. Composite orders `18,20,21,24`

For coprime factors, use this group-theory lemma first.

```lean
import Mathlib

namespace FLT.Mazur.GroupTheory

variable {G : Type*} [AddCommGroup G]

/-- If `m` and `n` are coprime, points of orders `m` and `n` add to a point of
order `m*n`.  This is the forward construction used for simultaneous torsion. -/
theorem addOrderOf_add_of_coprime
    {P Q : G} {m n : ℕ}
    (hP : addOrderOf P = m) (hQ : addOrderOf Q = n)
    (hcop : Nat.Coprime m n) :
    addOrderOf (P + Q) = m * n := by
  -- Mathlib likely has this for commuting elements/order; otherwise prove from
  -- divisibility and Bezout.
  sorry

/-- A point of order `m*n` gives points of orders `m` and `n` by multiplication,
when `m` and `n` are coprime. -/
theorem exact_order_mul_to_factors
    {R : G} {m n : ℕ}
    (hcop : Nat.Coprime m n) (hR : addOrderOf R = m*n) :
    (addOrderOf (n • R) = m) ∧ (addOrderOf (m • R) = n) := by
  -- Use `addOrderOf_nsmul`.
  sorry

end FLT.Mazur.GroupTheory
```

Then the cyclic exclusions reduce as follows:

```text
18 = 2 * 9   : order 18 ↔ simultaneous order 2 and order 9.
20 = 4 * 5   : order 20 ↔ simultaneous order 4 and order 5.
21 = 3 * 7   : order 21 ↔ simultaneous order 3 and order 7.
24 = 3 * 8   : order 24 ↔ simultaneous order 3 and order 8.
```

### Explicit Tate-normal-form conditions

Use these helper predicates.

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- Affine curve equation for Tate normal form. -/
def TateEq (b c X Y : ℚ) : Prop :=
  Y^2 + (1-c)*X*Y - b*Y = X^3 - b*X^2

/-- 2-division x-polynomial. -/
def TwoDivX (b c X : ℚ) : ℚ :=
  4*X^3 + ((1-c)^2 - 4*b)*X^2 + 2*b*(c-1)*X + b^2

/-- 3-division x-polynomial on `E(b,c)`.  A rational order-3 point also needs a
rational `Y` satisfying the curve equation. -/
def ThreeDivX (b c X : ℚ) : ℚ :=
  3*X^4 + ((1-c)^2 - 4*b)*X^3 +
    3*(b*(c-1))*X^2 + 3*b^2*X - b^3

/-- Placeholder for the full 5-division x-condition at an arbitrary point.
Use the actual generalized division polynomial in the implementation. -/
def FiveDivX (b c X : ℚ) : ℚ := 0

/-- There is a rational point of order 2. -/
def HasPointOrder2_Tate (b c : ℚ) : Prop :=
  ∃ X : ℚ, TwoDivX b c X = 0

/-- There is a rational point of order 3. -/
def HasPointOrder3_Tate (b c : ℚ) : Prop :=
  ∃ X Y : ℚ, TateEq b c X Y ∧ ThreeDivX b c X = 0

/-- There is a rational point of order 5.  In real code add exactness/nonzero
conditions or derive them from the division polynomial and nonsingularity. -/
def HasPointOrder5_Tate (b c : ℚ) : Prop :=
  ∃ X Y : ℚ, TateEq b c X Y ∧ FiveDivX b c X = 0

end FLT.Mazur.TateNF
```

Then state the composite obstruction predicates like this.

#### `18`

Put the order-`9` point at the Tate origin and ask for rational 2-torsion:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- Candidate system for cyclic order 18. -/
def Obstruction18 (b c : ℚ) : Prop :=
  F9 b c = 0 ∧ HasPointOrder2_Tate b c

/-- A cyclic point of order 18 gives the `Obstruction18` system after Tate normalization. -/
theorem order18_to_obstruction18 : True := by
  -- Normalize a point of order 9, then use the order-2 multiple of the original point.
  trivial

end FLT.Mazur.TateNF
```

Concretely:

```text
F9(b,c) = (b-c)^3 + c^3*(b-c-c^2) = 0,
∃X, 4X^3 + ((1-c)^2 - 4b)X^2 + 2b(c-1)X + b^2 = 0.
```

#### `20`

Use order `4` plus order `5`:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- Candidate system for cyclic order 20: origin has order 4, and some rational
point has order 5. -/
def Obstruction20 (b c : ℚ) : Prop :=
  c = 0 ∧ b ≠ 0 ∧ HasPointOrder5_Tate b c

end FLT.Mazur.TateNF
```

The concrete first relation is just `c=0`; the order-`5` point should be imposed by the 5-division polynomial at an arbitrary rational point, not by setting the Tate origin to order `5` simultaneously.

#### `21`

Use order `7` plus order `3`:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- Candidate system for cyclic order 21: origin has order 7, and some rational
point has order 3. -/
def Obstruction21 (b c : ℚ) : Prop :=
  F7 b c = 0 ∧ b ≠ 0 ∧ HasPointOrder3_Tate b c

end FLT.Mazur.TateNF
```

Concretely:

```text
c^3 - b^2 + b*c = 0,
∃X,Y, TateEq(b,c,X,Y) ∧ ThreeDivX(b,c,X)=0.
```

#### `24`

Use order `8` plus order `3`:

```lean
import Mathlib

namespace FLT.Mazur.TateNF

/-- Candidate system for cyclic order 24: origin has order 8, and some rational
point has order 3. -/
def Obstruction24 (b c : ℚ) : Prop :=
  F8 b c = 0 ∧ c ≠ 0 ∧ b ≠ 0 ∧ HasPointOrder3_Tate b c

end FLT.Mazur.TateNF
```

Concretely:

```text
2*b^2 - 3*b*c - b*c^2 + c^2 = 0,
c ≠ 0,
∃X,Y, TateEq(b,c,X,Y) ∧ ThreeDivX(b,c,X)=0.
```

## Recommended implementation order

1. Add `TateNF.BasicInvariants`: `b2,b4,b6,b8` for `E(b,c)` and the 2-division polynomial `T2`.
2. Add `TateNF.DivisionAtOrigin`: specialized recurrence for `ψₙ(0,0)` and prove the factors through `ψ₁₃`, plus `ψ₁₅` if desired.
3. Add `TateNF.ExactOrderSmall`: exact-order criteria for the Tate origin for `4,5,6,7,8,9,11,13,15,25`.
4. Add `GroupTheory.CoprimeOrders`: the coprime simultaneous-torsion lemmas.
5. Add `TateNF.CompositeSystems`: `Obstruction14`, `Obstruction18`, `Obstruction20`, `Obstruction21`, `Obstruction24`.
6. Prove `14` first.  It is the cleanest composite obstruction: `F7=0` plus the rational 2-division cubic reduces to `z^2 = 4u^3+u^2-2u+1`.
7. Then prove `11`, because `F11` is small and the obstruction is genus 1.
8. Then prove `15`, preferably from `F15=0` to a genus-one obstruction.
9. Then `13` and `16`, which need genus-2 rational point computations or checked imports of such computations.
10. Keep `25` out of the first batch unless the project already has a rational-points proof for `X₁(25)`.

## Pitfalls

* Do not confuse `ψ₅(P)=0` with exact order `25`; it proves the opposite direction, order dividing `5`.
* For `14`, if the Tate origin is order `7`, then the extra condition is a separate rational 2-torsion point.  If the Tate origin is order `14`, use `ψ₁₄(P)=0 ∧ ψ₇(P)≠0` instead.
* For `16`, existence of rational 2-torsion is not enough.  The issue is rational 2-divisibility of an order-`8` point.
* A rational root of an odd division `x`-polynomial is not always enough to produce a rational torsion point; keep the affine curve equation and the rational `Y` coordinate in the predicate unless a previous lemma proves the `Y` recovery.
* Avoid global resultants as proof engines.  The objects are modular curves with rational cusps, not univariate polynomials with no rational roots.
* Use compact polynomial definitions (`F11`, `F13`, `F15`) and prove expanded normal forms only as `[simp]` or `ring_nf` helper lemmas.  This keeps term explosion out of theorem statements.
