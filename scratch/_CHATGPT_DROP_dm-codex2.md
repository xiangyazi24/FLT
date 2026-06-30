# Q2394 (dm-codex2): four rational squares in arithmetic progression residual

## Mathlib audit

I would not assume Mathlib already has the exact theorem

```lean
∀ {w x y z : ℚ},
  x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 →
  y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2 →
  w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2
```

under a memorable direct name.  The likely local searches are:

```bash
# Direct phrases; likely no direct hit except docs/overview material.
grep -R "four.*squares" .lake/packages/mathlib/Mathlib/NumberTheory .lake/packages/mathlib/Mathlib/Algebra
grep -R "arithmetic.*progress" .lake/packages/mathlib/Mathlib/NumberTheory .lake/packages/mathlib/Mathlib/Algebra
grep -R "ArithmeticProgression" .lake/packages/mathlib/Mathlib
grep -R "squares.*progress" .lake/packages/mathlib/Mathlib

# Relevant existing descent machinery.
grep -R "def Fermat42\|theorem not_fermat_42\|PythagoreanTriple" \
  .lake/packages/mathlib/Mathlib/NumberTheory
```

The important existing file to check is:

```lean
import Mathlib.NumberTheory.FLT.Four

#check Fermat42
#check Fermat42.exists_minimal
#check Fermat42.not_minimal
#check not_fermat_42
```

In current Mathlib, `Mathlib.NumberTheory.FLT.Four` proves the exponent-4 descent theorem in the form

```lean
theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 2
```

This is close in spirit and useful as a reference/model, but it is not syntactically the four-squares-in-AP theorem.  I would introduce the AP statement as a named residual unless a local `#check`/grep finds an exact theorem in your pinned Mathlib.

## Lean-facing residual interface

The smallest downstream-facing residual is the rational theorem, because the cover wrappers already live over `ℚ`.  For a future proof, keep the integer theorem separate and prove the rational wrapper by clearing denominators.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Four integer squares in arithmetic progression are constant.  This is the
classical Fermat four-squares-in-AP theorem in the integer form. -/
def FourIntSquaresAPConst : Prop :=
  ∀ {w x y z : ℤ},
    x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 →
    y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2 →
    w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2

/-- Four rational squares in arithmetic progression are constant.  This is the
residual shape most convenient for the N=12 cover wrappers. -/
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 →
    y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2 →
    w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2

/-- Common-denominator lemma for four rationals.  This is algebraic plumbing,
not number theory.  It can be proved with `Rat.num`, `Rat.den`, and a product
of denominators, or with any existing common-denominator helper. -/
def RatCommonDenom4 : Prop :=
  ∀ w x y z : ℚ,
    ∃ W X Y Z D : ℤ,
      D ≠ 0 ∧
      w = (W : ℚ) / (D : ℚ) ∧
      x = (X : ℚ) / (D : ℚ) ∧
      y = (Y : ℚ) / (D : ℚ) ∧
      z = (Z : ℚ) / (D : ℚ)

/-- Rational denominator wrapper.  This should be proved now once the common
ominator lemma is available: multiply the two AP equations by `D^2`, apply the
integer theorem to `W,X,Y,Z`, then divide back by `D^2`. -/
def FourRatSquaresAPConst_of_int_statement : Prop :=
  RatCommonDenom4 → FourIntSquaresAPConst → FourRatSquaresAPConst

/-- The two rational cover equations from the full-cover route. -/
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  (d0 : ℚ) * A ^ 2 - (d1 : ℚ) * B ^ 2 = T ^ 2 ∧
    (d3 : ℚ) * C ^ 2 - (d0 : ℚ) * A ^ 2 = (3 : ℚ) * T ^ 2

/-- The surviving positive-sign cover triple `(3,2,6)` gives the AP
`T^2, C^2, A^2, B^2`. -/
theorem coverQ_3_2_6_AP_const
    (hAP : FourRatSquaresAPConst) {A B C T : ℚ}
    (hcov : CoverQ (3 : ℤ) (2 : ℤ) (6 : ℤ) A B C T) :
    T ^ 2 = C ^ 2 ∧ C ^ 2 = A ^ 2 ∧ A ^ 2 = B ^ 2 := by
  rcases hcov with ⟨h1, h2⟩
  have hAP1 : C ^ 2 - T ^ 2 = A ^ 2 - C ^ 2 := by
    nlinarith
  have hAP2 : A ^ 2 - C ^ 2 = B ^ 2 - A ^ 2 := by
    nlinarith
  exact hAP hAP1 hAP2

/-- The surviving negative-sign cover triple `(-1,-2,2)` gives the AP
`A^2, B^2, T^2, C^2`. -/
theorem coverQ_neg1_neg2_2_AP_const
    (hAP : FourRatSquaresAPConst) {A B C T : ℚ}
    (hcov : CoverQ (-1 : ℤ) (-2 : ℤ) (2 : ℤ) A B C T) :
    A ^ 2 = B ^ 2 ∧ B ^ 2 = T ^ 2 ∧ T ^ 2 = C ^ 2 := by
  rcases hcov with ⟨h1, h2⟩
  have hAP1 : B ^ 2 - A ^ 2 = T ^ 2 - B ^ 2 := by
    nlinarith
  have hAP2 : T ^ 2 - B ^ 2 = C ^ 2 - T ^ 2 := by
    nlinarith
  exact hAP hAP1 hAP2

/-- Downstream consequence for the `(3,2,6)` wrapper: once `T ≠ 0`, the cover
coordinate `X = 3*(A/T)^2` is forced to be `3`. -/
def CoverQ_3_2_6_forces_X_eq_three : Prop :=
  FourRatSquaresAPConst →
    ∀ {X A B C T : ℚ}, T ≠ 0 →
      X = (3 : ℚ) * (A / T) ^ 2 →
      CoverQ (3 : ℤ) (2 : ℤ) (6 : ℤ) A B C T →
      X = 3

/-- Downstream consequence for the `(-1,-2,2)` wrapper: once `T ≠ 0`, the cover
coordinate `X = -1*(A/T)^2` is forced to be `-1`. -/
def CoverQ_neg1_neg2_2_forces_X_eq_neg_one : Prop :=
  FourRatSquaresAPConst →
    ∀ {X A B C T : ℚ}, T ≠ 0 →
      X = (-1 : ℚ) * (A / T) ^ 2 →
      CoverQ (-1 : ℤ) (-2 : ℤ) (2 : ℤ) A B C T →
      X = -1

end MazurProof.RationalPointsN12
```

The two `coverQ_*_AP_const` theorems are deliberately small and should be kept as proved plumbing.  The final two `CoverQ_*_forces_X_eq_*` statements can also be proved immediately from them with one tiny field step: extract `A^2 = T^2`, rewrite `(A/T)^2 = A^2/T^2`, and use `T^2 ≠ 0`.

## Integer-to-rational denominator wrapper

A concrete wrapper proof should use this shape:

```lean
-- Suggested theorem, not a residual once `RatCommonDenom4` is available.
theorem fourRatSquaresAPConst_of_fourIntSquaresAPConst
    (hden : RatCommonDenom4)
    (hInt : FourIntSquaresAPConst) :
    FourRatSquaresAPConst := by
  intro w x y z h1 h2
  -- obtain ⟨W, X, Y, Z, D, hD, hw, hx, hy, hz⟩ := hden w x y z
  -- Substitute.  Each square is `(W^2 : ℚ) / D^2`, etc.
  -- Multiply both AP equations by `D^2` using `mul_right_cancel₀` or `field_simp [hD]`.
  -- Apply `hInt` to `W X Y Z`.
  -- Divide the resulting integer square equalities by `D^2` and rewrite back.
  -- This is pure algebra; no descent belongs here.
  exact by
    -- keep this theorem as a target skeleton; implement after choosing the
    -- local common-denominator helper.
    admit
```

Do not commit the `admit`; the point is that this theorem should not be the named hard residual.  The hard residual is `FourIntSquaresAPConst`, or even just `FourRatSquaresAPConst` if you want the smallest possible N=12 interface.

## Classical infinite-descent theorem DAG, non-circular

Do **not** prove this by invoking the E1 point classification, because that would be circular for the N=12 route.  The descent should be a standalone Fermat descent, parallel to the structure of `Mathlib.NumberTheory.FLT.Four`.

Recommended DAG:

```lean
/-- A nonconstant integer AP of four squares. -/
def FourIntSquaresAPNonconstant (w x y z : ℤ) : Prop :=
  x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 ∧
  y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2 ∧
  ¬ (w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2)

/-- Primitive version used for descent. -/
def PrimitiveFourIntSquaresAP (w x y z : ℤ) : Prop :=
  FourIntSquaresAPNonconstant w x y z ∧
    Int.gcd (Int.gcd (Int.gcd w x) y) z = 1

/-- Every nonconstant AP can be scaled down to a primitive one. -/
def FourIntSquaresAPNonconstant.exists_primitive : Prop :=
  ∀ {w x y z : ℤ}, FourIntSquaresAPNonconstant w x y z →
    ∃ w' x' y' z' : ℤ, PrimitiveFourIntSquaresAP w' x' y' z'

/-- Minimal primitive counterexample by positive height, e.g. max of absolute
values or the last square after orientation. -/
def PrimitiveFourIntSquaresAP.exists_minimal : Prop :=
  (∃ w x y z : ℤ, PrimitiveFourIntSquaresAP w x y z) →
    ∃ w x y z : ℤ, PrimitiveFourIntSquaresAP w x y z ∧
      ∀ a b c d : ℤ, PrimitiveFourIntSquaresAP a b c d →
        max (max (Int.natAbs w) (Int.natAbs x)) (max (Int.natAbs y) (Int.natAbs z)) ≤
          max (max (Int.natAbs a) (Int.natAbs b)) (max (Int.natAbs c) (Int.natAbs d))

/-- Congruence normalization: in a primitive nonconstant AP, all four variables
are odd and the common difference is divisible by `8`. -/
def PrimitiveFourIntSquaresAP.parity_normal_form : Prop :=
  ∀ {w x y z : ℤ}, PrimitiveFourIntSquaresAP w x y z →
    w % 2 = 1 ∧ x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 ∧
      8 ∣ (x ^ 2 - w ^ 2)

/-- Pythagorean-triple extraction from the two relations
`w^2 + y^2 = 2*x^2` and `x^2 + z^2 = 2*y^2`. -/
def PrimitiveFourIntSquaresAP.pythagorean_extraction : Prop :=
  ∀ {w x y z : ℤ}, PrimitiveFourIntSquaresAP w x y z →
    ∃ r s u v : ℤ,
      -- exact parametrization fields should be chosen to match
      -- `PythagoreanTriple.coprime_classification'`.
      True

/-- Descent step: a primitive nonconstant four-square AP produces a smaller one.
This is the real Fermat descent content.  It should be proved from the
Pythagorean-triple classification, not from E1. -/
def PrimitiveFourIntSquaresAP.descent_step : Prop :=
  ∀ {w x y z : ℤ}, PrimitiveFourIntSquaresAP w x y z →
    ∃ w' x' y' z' : ℤ,
      PrimitiveFourIntSquaresAP w' x' y' z' ∧
      max (max (Int.natAbs w') (Int.natAbs x')) (max (Int.natAbs y') (Int.natAbs z')) <
        max (max (Int.natAbs w) (Int.natAbs x)) (max (Int.natAbs y) (Int.natAbs z))

/-- Infinite descent contradiction. -/
def FourIntSquaresAPConst_from_descent : Prop :=
  PrimitiveFourIntSquaresAP.descent_step → FourIntSquaresAPConst
```

What should remain named residual:

```lean
def FourIntSquaresAPConst : Prop := ...
```

or, if you want to mirror the descent proof explicitly:

```lean
def PrimitiveFourIntSquaresAP.descent_step : Prop := ...
```

Everything else in the DAG is much more algebraic and can be implemented incrementally.

## Using the residual in the two surviving cover wrappers

### Triple `(3,2,6)`

The cover equations are:

```text
3*A^2 - 2*B^2 = T^2,
6*C^2 - 3*A^2 = 3*T^2.
```

The second equation is equivalent to:

```text
2*C^2 = A^2 + T^2.
```

So:

```text
C^2 - T^2 = A^2 - C^2.
```

The first equation is equivalent to:

```text
2*B^2 = 3*A^2 - T^2,
```

and, using `2*C^2 = A^2 + T^2`, gives:

```text
A^2 - C^2 = B^2 - A^2.
```

Thus

```text
T^2, C^2, A^2, B^2
```

are four rational squares in AP.  The residual gives

```text
T^2 = C^2 = A^2 = B^2.
```

Since `T ≠ 0`, `(A/T)^2 = 1`, hence the associated E1 coordinate

```text
X = 3*(A/T)^2
```

is forced to be

```text
X = 3.
```

This is the non-torsion point branch `X=3`, `Y=±6`, not a contradiction.

### Triple `(-1,-2,2)`

The cover equations are:

```text
-A^2 + 2*B^2 = T^2,
2*C^2 + A^2 = 3*T^2.
```

The first gives:

```text
B^2 - A^2 = T^2 - B^2.
```

The second, together with the first, gives:

```text
T^2 - B^2 = C^2 - T^2.
```

Thus

```text
A^2, B^2, T^2, C^2
```

are four rational squares in AP.  The residual gives

```text
A^2 = B^2 = T^2 = C^2.
```

Since `T ≠ 0`, `(A/T)^2 = 1`, hence the associated E1 coordinate

```text
X = -1*(A/T)^2
```

is forced to be

```text
X = -1.
```

This is the non-torsion point branch `X=-1`, `Y=±2`, not a contradiction.

## Finite/congruence quick reductions

These are useful plumbing lemmas but do not replace Fermat descent.

1. For integer squares modulo `4`, a four-term AP must have common difference divisible by `4`.  If the common difference is `1`, `2`, or `3 mod 4`, one of the four residues is not in `{0,1}`.

2. In a primitive integer AP of four squares, if one variable is even then all four square residues are `0 or 4 mod 8`, forcing all four variables even after checking the AP pattern.  Therefore a primitive nonconstant counterexample can be normalized to all variables odd.

3. With all variables odd, all four squares are `1 mod 8`, so the common difference is divisible by `8`.

4. These congruences are enough to simplify the parity branch of the descent and to reject many malformed integer-cover special cases, but they do not kill the two real cover triples `(3,2,6)` and `(-1,-2,2)`: those triples collapse to constant square APs and yield the actual E1 points `X=3` and `X=-1`.

## Conservative recommendation

Use this residual in the N=12 route:

```lean
def FourRatSquaresAPConst : Prop :=
  ∀ {w x y z : ℚ},
    x ^ 2 - w ^ 2 = y ^ 2 - x ^ 2 →
    y ^ 2 - x ^ 2 = z ^ 2 - y ^ 2 →
    w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2
```

Then prove the two cover wrappers now using the `coverQ_*_AP_const` algebra above.  Separately, either later prove `FourRatSquaresAPConst` from the integer theorem by denominator clearing, or replace it with a direct import if a pinned-Mathlib search finds an exact AP theorem.
