# Q2801 (dm-codex1): attack plan for E1 full-cover extraction residuals

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Local file from prompt: `FLT/Assumptions/MazurProof/N12E1FullCoverExtraction.lean`  
Namespace: `MazurProof.RationalPointsN12`

Connector note: `FLT/Assumptions/MazurProof/N12E1FullCoverExtraction.lean` is not visible through the GitHub connector on `scratch`, so the plan below is based on the exact definitions in the prompt. The theorem names and statement shapes are chosen to be pasted into the local WIP and adjusted only for local accessor names.

## Executive route

There are three residuals:

```lean
def E1FactorEvenPadicOutside23Statement : Prop :=
  ∀ {X Y : ℚ}, E1FullCoverCurve X Y → Y ≠ 0 →
    EvenPadicOutside23 X ∧ EvenPadicOutside23 (X - 1) ∧ EvenPadicOutside23 (X + 3)

def SquareclassSupportedOn23OfEvenPadicOutside23Statement : Prop :=
  ∀ {q : ℚ}, EvenPadicOutside23 q → SquareclassSupportedOn23 q

def E1FullCoverIntDataOfFactorSquareclassesStatement : Prop :=
  ∀ {X Y : ℚ}, E1FullCoverCurve X Y → Y ≠ 0 →
    SquareclassSupportedOn23 X → SquareclassSupportedOn23 (X - 1) → SquareclassSupportedOn23 (X + 3) →
    E1FullCoverIntData X Y
```

The right implementation order is:

1. Prove the valuation parity residual `E1FactorEvenPadicOutside23Statement` using only additivity of `padicValRat` away from `2,3` and pairwise coprimality of the three factors `X`, `X-1`, `X+3` away from `2,3`.
2. Prove `SquareclassSupportedOn23OfEvenPadicOutside23Statement` by a rational squareclass normalization theorem for rationals whose valuations outside `{2,3}` are even. This is the genuinely number-theoretic/Mathlib-API hard residual.
3. Prove `E1FullCoverIntDataOfFactorSquareclassesStatement` by clearing denominators from three squareclass equations. This is mostly mechanical but has several sign/nonzero pitfalls.

The two genuinely hard points are:

* a clean `padicValRat` API for additivity and for `q = d*r^2` squareclass extraction;
* a robust denominator-clearing lemma producing a primitive integer quadruple without making false claims about a shared denominator being primitive.

Everything else should be small algebra.

## 1. Factor parity outside `{2,3}`

For `p ≠ 2,3`, the three rational factors

```lean
X, X - 1, X + 3
```

are pairwise coprime at `p`, because their differences are

```text
X - (X-1) = 1,
(X+3) - X = 3,
(X+3) - (X-1) = 4.
```

Thus for `p ≠ 2,3`, no two of the three can have positive `p`-adic valuation. Since

```lean
Y^2 = X * (X - 1) * (X + 3)
```

has even valuation, each individual factor must have even valuation.

### Suggested local valuation API targets

Do not try to prove the final statement directly. Isolate the generic local-prime lemma:

```lean
import FLT.Assumptions.MazurProof.N12E1FullCoverExtraction
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Rat.Defs

namespace MazurProof.RationalPointsN12

/-- If two rationals differ by a rational whose `p`-valuation is zero, they
cannot both have positive `p`-valuation. This is the basic ultrametric
coprimality lemma needed for the E1 factors. -/
theorem rat_padicVal_pos_not_pos_of_sub_val_zero
    {p : ℕ} [Fact p.Prime] {a b c : ℚ}
    (hsub : a - b = c)
    (hc : padicValRat p c = 0) :
    ¬ (0 < padicValRat p a ∧ 0 < padicValRat p b) := by
  -- Route:
  -- use `padicValRat.sub` / ultrametric inequality in the form
  -- `min (v a) (v b) < v (a-b)` if valuations unequal, or at least
  -- `min (v a) (v b) ≤ v (a-b)`.
  -- If both are positive, then `0 < v(a-b)`, contradicting `hc`.
  sorry

/-- For primes outside `{2,3}`, the constants `1`, `3`, and `4` have valuation
zero. -/
theorem padicValRat_one_three_four_outside23
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    padicValRat p (1 : ℚ) = 0 ∧
    padicValRat p (3 : ℚ) = 0 ∧
    padicValRat p (4 : ℚ) = 0 := by
  -- Usually `norm_num [padicValRat, hp2, hp3]` or valuation-of-nat API.
  -- For `4`, use `4 = 2^2` and hp2.
  sorry

/-- For `p ≠ 2,3`, the three E1 factors are pairwise not simultaneously
positive in `p`-adic valuation. -/
theorem e1_factors_pairwise_not_both_pos_outside23
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (X : ℚ) :
    ¬ (0 < padicValRat p X ∧ 0 < padicValRat p (X - 1)) ∧
    ¬ (0 < padicValRat p X ∧ 0 < padicValRat p (X + 3)) ∧
    ¬ (0 < padicValRat p (X - 1) ∧ 0 < padicValRat p (X + 3)) := by
  -- Use differences `1`, `-3`, `-4` and the previous constant-valuation lemma.
  sorry
```

The parity conclusion can be formulated without naming minimum valuations:

```lean
/-- If three integers/valuation values sum to an even number and no two of the
corresponding rational factors have positive valuation, then each is even.
This statement is intentionally valuation-agnostic. -/
theorem even_each_of_sum_even_and_pairwise_not_two_pos
    {a b c : ℤ}
    (hsum : Even (a + b + c))
    (hab : ¬ (0 < a ∧ 0 < b))
    (hac : ¬ (0 < a ∧ 0 < c))
    (hbc : ¬ (0 < b ∧ 0 < c))
    -- Optional: in the actual valuation situation, at most one can be nonzero;
    -- if negative values are possible, use pairwise nonzero/coprime valuations
    -- rather than just positive. See warning below.
    : Even a ∧ Even b ∧ Even c := by
  -- This exact statement is NOT sufficient if two valuations can both be negative.
  -- Use the refined lemma below in production.
  sorry
```

### Important correction: handle negative valuations

For rationals, valuations can be negative. Pairwise `not both positive` is not enough. What is actually true for `p ≠ 2,3` is that **at most one of the three valuations is nonzero**. This follows because if `v(a) ≠ 0` and `v(b) ≠ 0`, then both `a` and `b` are divisible by `p` after clearing denominators, and their difference has nonzero valuation; but their difference is a `p`-adic unit.

Use this stronger theorem:

```lean
/-- For `p ≠ 2,3`, at most one of the three E1 factor valuations is nonzero. -/
theorem e1_factor_padicVal_pairwise_zero_outside23
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (X : ℚ) :
    (padicValRat p X ≠ 0 → padicValRat p (X - 1) = 0 ∧ padicValRat p (X + 3) = 0) ∧
    (padicValRat p (X - 1) ≠ 0 → padicValRat p X = 0 ∧ padicValRat p (X + 3) = 0) ∧
    (padicValRat p (X + 3) ≠ 0 → padicValRat p X = 0 ∧ padicValRat p (X - 1) = 0) := by
  -- Best proof route: use `padicValRat` on normalized numerator/denominator,
  -- or use the p-adic unit criterion for differences. Avoid a statement only
  -- about positive valuations.
  sorry

/-- The actual factor parity lemma. -/
theorem e1_factor_even_padicVal_outside23
    {X Y : ℚ} (hcurve : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    Even (padicValRat p X) ∧
    Even (padicValRat p (X - 1)) ∧
    Even (padicValRat p (X + 3)) := by
  -- 1. From `Y ≠ 0` and the curve equation, prove all three factors are nonzero.
  -- 2. Apply valuation additivity to
  --      Y^2 = X*(X-1)*(X+3)
  --    to get
  --      2*v(Y) = v(X)+v(X-1)+v(X+3).
  -- 3. Use `e1_factor_padicVal_pairwise_zero_outside23`.
  --    Since at most one of the three valuations is nonzero, the sum being even
  --    forces that one nonzero valuation to be even; the zero valuations are even.
  sorry
```

Then the residual itself is just packaging:

```lean
theorem e1FactorEvenPadicOutside23_checked :
    E1FactorEvenPadicOutside23Statement := by
  intro X Y hcurve hY
  have hnonzeroX : X ≠ 0 := by
    intro hX
    -- curve gives Y^2=0
    have : Y ^ 2 = 0 := by simpa [E1FullCoverCurve, hX] using hcurve
    exact hY (sq_eq_zero_iff.mp this)
  have hnonzeroXm1 : X - 1 ≠ 0 := by
    intro h
    have : Y ^ 2 = 0 := by
      -- use hcurve and `h : X-1=0`
      nlinarith [hcurve]
    exact hY (sq_eq_zero_iff.mp this)
  have hnonzeroXp3 : X + 3 ≠ 0 := by
    intro h
    have : Y ^ 2 = 0 := by
      nlinarith [hcurve]
    exact hY (sq_eq_zero_iff.mp this)
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨hnonzeroX, fun p hp hp2 hp3 => (e1_factor_even_padicVal_outside23 hcurve hY hp2 hp3).1⟩
  · exact ⟨hnonzeroXm1, fun p hp hp2 hp3 => (e1_factor_even_padicVal_outside23 hcurve hY hp2 hp3).2.1⟩
  · exact ⟨hnonzeroXp3, fun p hp hp2 hp3 => (e1_factor_even_padicVal_outside23 hcurve hY hp2 hp3).2.2⟩
```

If `nlinarith` over rationals and powers struggles, rewrite with the curve equation first and use `ring_nf`.

## 2. Squareclass support from even valuations outside `{2,3}`

This is the cleanest reusable number-theory theorem:

```lean
/-- Rational squareclass normalization supported on `{2,3}`. -/
theorem rat_squareclass_supported_on_23_of_even_outside23
    {q : ℚ}
    (hq0 : q ≠ 0)
    (hval : ∀ p : ℕ, Fact p.Prime → p ≠ 2 → p ≠ 3 → Even (padicValRat p q)) :
    ∃ d : ℤ, InS23 d ∧ ∃ r : ℚ, r ≠ 0 ∧ q = (d : ℚ) * r ^ 2 := by
  -- Genuinely hard/API-heavy theorem.
  -- Recommended implementation route is via numerator/denominator factorization:
  --   q = sign(q) * ∏ p p^(v_p q)
  -- Even outside {2,3} means the nonsquare part only uses sign, 2, 3.
  -- Hence d ∈ {±1,±2,±3,±6}.
  sorry

theorem squareclassSupportedOn23OfEvenPadicOutside23_checked :
    SquareclassSupportedOn23OfEvenPadicOutside23Statement := by
  intro q hq
  rcases hq with ⟨hq0, hval⟩
  exact ⟨hq0, rat_squareclass_supported_on_23_of_even_outside23 hq0 hval⟩
```

### More implementable decomposition using `Rat.num`/`Rat.den`

If `padicValRat` factorization APIs are thin, implement the theorem in two mechanical layers:

```lean
/-- Integer squarefree kernel after removing squares, supported outside `{2,3}`.
This is the integer core of the rational theorem. -/
theorem int_squarefree_kernel_supported23_of_even_prime_exponents
    {z : ℤ} (hz : z ≠ 0)
    (h : ∀ p : ℕ, Fact p.Prime → p ≠ 2 → p ≠ 3 → Even (padicValInt p z)) :
    ∃ d : ℤ, InS23 d ∧ ∃ a : ℤ, a ≠ 0 ∧ z = d * a ^ 2 := by
  -- Use integer unique factorization / normalized factors.
  sorry

/-- Rational version from numerator and denominator. -/
theorem rat_squareclass_supported_on_23_num_den
    {q : ℚ} (hq : q ≠ 0)
    (hval : ∀ p : ℕ, Fact p.Prime → p ≠ 2 → p ≠ 3 → Even (padicValRat p q)) :
    ∃ d : ℤ, InS23 d ∧ SquareclassBy q d := by
  -- Use `q.num` and `q.den`.
  -- Since q is reduced, `v_p(q) = v_p(num) - v_p(den)`.
  -- Evenness of the difference plus coprimality of num/den implies each odd/outside
  -- prime exponent in num and den has even parity individually.
  -- Extract square kernels for num and den, combine denominators into a rational square.
  sorry
```

This is the part most likely to take time. It is not algebraically hard, but it depends heavily on exact Mathlib names for `Rat.num`, `Rat.den`, `padicValRat`, and UFD/factorization lemmas.

### Pitfalls

* Do not claim `q = d*r^2` without `q ≠ 0`. Your `SquareclassBy` requires `r ≠ 0`; if `q=0`, no such representation exists with `r≠0` and nonzero `d`.
* Sign matters. Negative rationals use `d < 0` and positive square `r^2`.
* Do not forget that the denominator squareclass contributes too. Since denominators are positive, it only changes the square factor after reducing to `d ∈ S23`.

## 3. Full-cover integer data from factor squareclasses

Assume

```lean
SquareclassSupportedOn23 X
SquareclassSupportedOn23 (X - 1)
SquareclassSupportedOn23 (X + 3)
```

Unpack:

```lean
X     = d0 * r0^2
X - 1 = d1 * r1^2
X + 3 = d3 * r3^2
```

with `d0,d1,d3 ∈ S23` and nonzero `r0,r1,r3`.

Then the three cover equations over `ℚ` are immediate:

```text
d0*r0^2 - d1*r1^2 = 1
d3*r3^2 - d0*r0^2 = 3
```

The product squareclass condition comes from the curve:

```text
Y^2 = X*(X-1)*(X+3)
    = (d0*d1*d3) * (r0*r1*r3)^2.
```

So `d0*d1*d3` is a rational square, with witness

```text
r = Y / (r0*r1*r3)
```

which is nonzero because `Y≠0` and all `ri≠0`.

### Rational cover data interface

First introduce a rational intermediate. This avoids mixing squareclass unpacking with integer clearing.

```lean
def E1FullCoverRatData (X Y : ℚ) : Prop :=
  ∃ d0 d1 d3 : ℤ,
  ∃ r0 r1 r3 : ℚ,
    InS23 d0 ∧ InS23 d1 ∧ InS23 d3 ∧
    r0 ≠ 0 ∧ r1 ≠ 0 ∧ r3 ≠ 0 ∧
    X = (d0 : ℚ) * r0 ^ 2 ∧
    X - 1 = (d1 : ℚ) * r1 ^ 2 ∧
    X + 3 = (d3 : ℚ) * r3 ^ 2 ∧
    ProductSquareclassCondition d0 d1 d3 ∧
    ((d0 : ℚ) * r0 ^ 2 - (d1 : ℚ) * r1 ^ 2 = 1) ∧
    ((d3 : ℚ) * r3 ^ 2 - (d0 : ℚ) * r0 ^ 2 = 3)

theorem e1FullCoverRatData_of_factor_squareclasses
    {X Y : ℚ} (hcurve : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    (hX : SquareclassSupportedOn23 X)
    (hXm1 : SquareclassSupportedOn23 (X - 1))
    (hXp3 : SquareclassSupportedOn23 (X + 3)) :
    E1FullCoverRatData X Y := by
  rcases hX with ⟨hX0, d0, hd0, r0, hr0, hXsq⟩
  rcases hXm1 with ⟨hXm10, d1, hd1, r1, hr1, hXm1sq⟩
  rcases hXp3 with ⟨hXp30, d3, hd3, r3, hr3, hXp3sq⟩
  refine ⟨d0, d1, d3, r0, r1, r3, hd0, hd1, hd3, hr0, hr1, hr3, hXsq, hXm1sq, hXp3sq, ?_, ?_, ?_⟩
  · -- product squareclass condition
    refine ⟨Y / (r0 * r1 * r3), ?_, ?_⟩
    · field_simp [hY, hr0, hr1, hr3]
    · -- use curve and the three squareclass equations
      field_simp [hY, hr0, hr1, hr3]
      -- after clearing denominators, `ring` closes
      rw [E1FullCoverCurve] at hcurve
      nlinarith [hcurve, hXsq, hXm1sq, hXp3sq]
  · -- first cover equation
    calc
      (d0 : ℚ) * r0 ^ 2 - (d1 : ℚ) * r1 ^ 2
          = X - (X - 1) := by rw [← hXsq, ← hXm1sq]
      _ = 1 := by ring
  · -- second cover equation
    calc
      (d3 : ℚ) * r3 ^ 2 - (d0 : ℚ) * r0 ^ 2
          = (X + 3) - X := by rw [← hXp3sq, ← hXsq]
      _ = 3 := by ring
```

The `rcases` pattern may need adjustment because `SquareclassSupportedOn23 q` is `q ≠ 0 ∧ ∃ d, InS23 d ∧ SquareclassBy q d`, and `SquareclassBy` is `∃ r, r≠0 ∧ q = d*r^2`. A safer unpacking is:

```lean
rcases hX with ⟨hX0, d0, hd0, r0, hr0, hXsq⟩
```

if Lean unfolds the nested exists; otherwise unfold `SquareclassSupportedOn23 SquareclassBy` first.

### Denominator clearing: rational cover to integer data

This is mechanical but should be separated.

The least painful route is to choose one common positive denominator `D` for `r0,r1,r3` and set

```text
A = numerator of D*r0
B = numerator of D*r1
C = numerator of D*r3
T = D
```

Then

```text
d0*A^2 - d1*B^2 = T^2
d3*C^2 - d0*A^2 = 3*T^2
```

because the rational equations have RHS `1` and `3`.

However, `PrimitiveInt4 A B C T` is not automatic. The safe route is:

1. Build an integer quadruple `(A,B,C,T)` with `T>0` and equations.
2. Divide by the common gcd `g = gcd4(A,B,C,T)` to obtain a primitive quadruple.
3. Because the equations are homogeneous of degree 2, the equations survive division by `g^2`.

Do **not** claim the first denominator-cleared quadruple is primitive.

Suggested interfaces:

```lean
/-- A non-primitive integer cover package obtained by clearing denominators. -/
def E1FullCoverIntDataRaw (X Y : ℚ) : Prop :=
  ∃ d0 d1 d3 A B C T : ℤ,
    InS23 d0 ∧ InS23 d1 ∧ InS23 d3 ∧
    ProductSquareclassCondition d0 d1 d3 ∧
    T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
    d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
    d3 * C ^ 2 - d0 * A ^ 2 = 3 * T ^ 2

theorem e1FullCoverIntDataRaw_of_ratData
    {X Y : ℚ} (h : E1FullCoverRatData X Y) :
    E1FullCoverIntDataRaw X Y := by
  -- Choose a common denominator D for r0,r1,r3.
  -- Easiest concrete choice:
  --   D = r0.den * r1.den * r3.den
  --   A = r0.num * r1.den * r3.den
  --   B = r1.num * r0.den * r3.den
  --   C = r3.num * r0.den * r1.den
  --   T = D
  -- Then `r0 = A/T`, etc. Use `Rat.num_div_den`/normalization APIs.
  sorry

/-- Primitive reduction of a homogeneous degree-two cover quadruple. -/
theorem primitiveInt4_cover_of_raw_cover
    {d0 d1 d3 A B C T : ℤ}
    (hT : T ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (h1 : d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2)
    (h2 : d3 * C ^ 2 - d0 * A ^ 2 = 3 * T ^ 2) :
    ∃ A' B' C' T' : ℤ,
      T' ≠ 0 ∧ A' ≠ 0 ∧ B' ≠ 0 ∧ C' ≠ 0 ∧
      PrimitiveInt4 A' B' C' T' ∧
      d0 * A' ^ 2 - d1 * B' ^ 2 = T' ^ 2 ∧
      d3 * C' ^ 2 - d0 * A' ^ 2 = 3 * T' ^ 2 := by
  -- Let g be a positive gcd of the four coordinates.
  -- Set A'=A/g, ...; prove g divides all four and equations descend by g^2.
  -- This is mechanical but gcd-API heavy. If `PrimitiveInt4` is Bezout-style,
  -- choose g as `Int.gcd A (Int.gcd B (Int.gcd C T))` or the local Nat gcd4.
  sorry

theorem e1FullCoverIntData_of_ratData
    {X Y : ℚ} (h : E1FullCoverRatData X Y) :
    E1FullCoverIntData X Y := by
  rcases e1FullCoverIntDataRaw_of_ratData h with
    ⟨d0,d1,d3,A,B,C,T,hd0,hd1,hd3,hprod,hT,hA,hB,hC,h1,h2⟩
  rcases primitiveInt4_cover_of_raw_cover hT hA hB hC h1 h2 with
    ⟨A',B',C',T',hT',hA',hB',hC',hprim,h1',h2'⟩
  -- Package according to the local `E1FullCoverIntData` definition.
  -- This is likely just a nested exists with the fields above.
  exact ⟨d0,d1,d3,A',B',C',T',hd0,hd1,hd3,hprod,hT',hA',hB',hC',hprim,⟨h1',h2'⟩⟩
```

Then the residual is clean:

```lean
theorem e1FullCoverIntDataOfFactorSquareclasses_checked :
    E1FullCoverIntDataOfFactorSquareclassesStatement := by
  intro X Y hcurve hY hX hXm1 hXp3
  exact e1FullCoverIntData_of_ratData
    (e1FullCoverRatData_of_factor_squareclasses hcurve hY hX hXm1 hXp3)
```

## 4. A more direct denominator-clearing interface

If proving primitive reduction is too much immediately, introduce this exact residual as the next mechanical target:

```lean
def RationalCoverEquations (d0 d1 d3 : ℤ) (r0 r1 r3 : ℚ) : Prop :=
  r0 ≠ 0 ∧ r1 ≠ 0 ∧ r3 ≠ 0 ∧
  (d0 : ℚ) * r0 ^ 2 - (d1 : ℚ) * r1 ^ 2 = 1 ∧
  (d3 : ℚ) * r3 ^ 2 - (d0 : ℚ) * r0 ^ 2 = 3

def IntCoverEquations (d0 d1 d3 A B C T : ℤ) : Prop :=
  T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
  PrimitiveInt4 A B C T ∧
  d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
  d3 * C ^ 2 - d0 * A ^ 2 = 3 * T ^ 2

theorem intCoverEquations_of_ratCoverEquations
    {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ}
    (h : RationalCoverEquations d0 d1 d3 r0 r1 r3) :
    ∃ A B C T : ℤ, IntCoverEquations d0 d1 d3 A B C T := by
  -- This theorem is independent of E1 and squareclasses.
  -- It is the right isolated denominator-clearing target.
  sorry
```

This is likely the best next local file to attack because failures will be pure `Rat.num/den` and gcd normalization failures, not mixed with E1 geometry.

## 5. Product squareclass bridge detail

When constructing `ProductSquareclassCondition`, avoid the false zero witness pitfall:

```lean
theorem productSquareclass_of_curve_and_squareclasses
    {X Y : ℚ} (hcurve : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ}
    (hr0 : r0 ≠ 0) (hr1 : r1 ≠ 0) (hr3 : r3 ≠ 0)
    (hX : X = (d0 : ℚ) * r0 ^ 2)
    (hXm1 : X - 1 = (d1 : ℚ) * r1 ^ 2)
    (hXp3 : X + 3 = (d3 : ℚ) * r3 ^ 2) :
    ProductSquareclassCondition d0 d1 d3 := by
  refine ⟨Y / (r0 * r1 * r3), ?_, ?_⟩
  · field_simp [hY, hr0, hr1, hr3]
  · have hprod : Y ^ 2 = ((d0 * d1 * d3 : ℤ) : ℚ) * (r0 * r1 * r3) ^ 2 := by
      rw [E1FullCoverCurve] at hcurve
      rw [hcurve, hX, hXm1, hXp3]
      norm_num
      ring
    field_simp [hY, hr0, hr1, hr3]
    -- Equivalent to rearranging `hprod`.
    nlinarith [hprod]
```

If `nlinarith` cannot handle the division square, use `field_simp` and `ring_nf` after multiplying by `(r0*r1*r3)^2`.

## 6. Pitfalls checklist

* `Y ≠ 0` is needed twice: to show factors are nonzero in `EvenPadicOutside23`, and to build a nonzero product-squareclass witness `Y/(r0*r1*r3)`.
* Never try to represent `q=0` as `d*r^2` with `r≠0`; this is explicitly impossible for nonzero `d∈S23`.
* For the factor parity theorem, negative rational valuations matter. Use “at most one factor has nonzero valuation,” not just “not two positive valuations.”
* Do not claim a common denominator-cleared quadruple is primitive. Build raw integer data first, then primitive-reduce using a gcd of all four coordinates.
* Do not introduce a shared-denominator primitiveness claim such as `gcd(A,B,C,T)=1` from reduced rational `r_i`; it is generally false.
* Product squareclass support on `{2,3}` is the hardest residual if Mathlib lacks a ready `Rat.isSquare_intCast_iff`/valuation squareclass theorem. Keep it isolated.

## Recommended next commits locally

1. Add `E1FullCoverRatData` and prove `e1FullCoverRatData_of_factor_squareclasses`. This is mostly algebra and validates the squareclass unpacking.
2. Add `RationalCoverEquations`, `IntCoverEquations`, and attack `intCoverEquations_of_ratCoverEquations` independently.
3. Add the generic `rat_squareclass_supported_on_23_of_even_outside23` theorem as a standalone number-theory file/section.
4. Add the local-prime factor parity theorem `e1_factor_even_padicVal_outside23` last, because it depends most on exact `padicValRat` APIs.

This order gets the denominator-clearing and packaging residual checked before the heavier valuation-squareclass normalization.
