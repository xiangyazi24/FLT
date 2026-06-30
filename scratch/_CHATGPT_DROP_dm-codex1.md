# Q2449-RETRY AP-to-FLT4 bridge proof route

## Executive answer

The proposed residual

```lean
def FourSquaresAPToFermat42Bridge : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ (w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2) →
    ∃ a b c : ℤ,
      a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2
```

is not the right Lean frontier.  Since the antecedent is expected to be impossible, the statement is classically true only vacuously after proving the four-square-AP theorem itself.  I do not know a direct algebraic construction of such `a,b,c` from an arbitrary nonconstant four-square AP.  The standard AP algebra gives a Pythagorean triangle with one **square** leg, not an equation `a^4 + b^4 = c^2`.

The corrected route is:

```lean
arbitrary integer AP
  → primitive positive/centered four-square AP
  → Pythagorean triple identity
  → Pythagorean parameterization and gcd splitting
  → descent to a smaller primitive centered AP
  → contradiction by well-founded descent
```

So the useful residual should be a primitive-centered descent theorem, not `FourSquaresAPToFermat42Bridge`.

---

## 0. Base definitions

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

def IntFourSqAP (w x y z : ℤ) : Prop :=
  x^2 - w^2 = y^2 - x^2 ∧ y^2 - x^2 = z^2 - y^2

def FourSqAPConst (w x y z : ℤ) : Prop :=
  w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2
```

The final integer theorem should be shaped as:

```lean
def FourIntSquaresAPConst : Prop :=
  ∀ {w x y z : ℤ}, IntFourSqAP w x y z → FourSqAPConst w x y z
```

---

## 1. Edge cases and AP algebra

### 1.1 Adjacent repeat closes immediately

```lean
theorem intFourSqAP_const_of_adjacent_eq
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z)
    (hzero : w^2 = x^2 ∨ x^2 = y^2 ∨ y^2 = z^2) :
    FourSqAPConst w x y z := by
  unfold IntFourSqAP FourSqAPConst at *
  rcases hAP with ⟨h1, h2⟩
  rcases hzero with h | h | h <;> nlinarith
```

This is pure `nlinarith`.

### 1.2 Reversal handles negative common difference

```lean
theorem intFourSqAP_reverse
    {w x y z : ℤ}
    (hAP : IntFourSqAP w x y z) :
    IntFourSqAP z y x w := by
  unfold IntFourSqAP at *
  rcases hAP with ⟨h1, h2⟩
  constructor <;> nlinarith
```

Also pure `nlinarith`.

### 1.3 Centering convention

For a positive common difference divisible by `4`, set the four square terms as

```text
p^2 = X - 6*N
q^2 = X - 2*N
r^2 = X + 2*N
s^2 = X + 6*N
```

so their common difference is `4*N`.

The centering equations are all `ring`/`nlinarith`; the only nontrivial work is proving that a nonconstant primitive AP can be normalized so the common difference is positive and divisible by `4`.

---

## 2. Correct primitive positive statement

Use this as the honest normalized object:

```lean
structure PrimitiveCenteredFourSqAP where
  X : ℤ
  N : ℤ
  hNpos : 0 < N
  p : ℤ
  q : ℤ
  r : ℤ
  s : ℤ
  hp : p^2 = X - 6*N
  hq : q^2 = X - 2*N
  hr : r^2 = X + 2*N
  hs : s^2 = X + 6*N
  hp0 : p ≠ 0
  hq0 : q ≠ 0
  hr0 : r ≠ 0
  hs0 : s ≠ 0
  -- primitive normalization: pairwise coprime roots
  hpq : Int.gcd p q = 1
  hpr : Int.gcd p r = 1
  hps : Int.gcd p s = 1
  hqr : Int.gcd q r = 1
  hqs : Int.gcd q s = 1
  hrs : Int.gcd r s = 1
  -- parity normalization in the primitive nonconstant case
  hp_odd : p % 2 = 1
  hq_odd : q % 2 = 1
  hr_odd : r % 2 = 1
  hs_odd : s % 2 = 1
```

Reduction from arbitrary AP:

```lean
def ArbitraryAP_to_primitive_centered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    Nonempty PrimitiveCenteredFourSqAP
```

This reduction is not `ring`; it is normalization bookkeeping:

1. Define `δ = x^2 - w^2`.
2. If `δ = 0`, close by `intFourSqAP_const_of_adjacent_eq`.
3. If `δ < 0`, reverse the quadruple using `intFourSqAP_reverse`.
4. Divide the roots by their common gcd.  The AP difference divides by `g^2`.
5. In the primitive nonconstant case, prove all roots are odd and the common difference is divisible by `4`.  This is a parity/mod-8 and gcd argument.
6. Write the positive common difference as `4*N` and define the centered `X` by the average convention above.

The only hard pieces in this reduction are gcd/divisibility normalization and the primitive parity lemma.  The centering equalities are `ring`/`nlinarith`.

---

## 3. Exact AP-to-Pythagorean equations

For a primitive centered AP, define

```lean
Y = p*q*r*s
E = 16*N^2
H = X^2 - 20*N^2
```

The central product identity is:

```lean
theorem centered_product_identity
    {X N p q r s : ℤ}
    (hp : p^2 = X - 6*N)
    (hq : q^2 = X - 2*N)
    (hr : r^2 = X + 2*N)
    (hs : s^2 = X + 6*N) :
    (p*q*r*s)^2 = (X^2 - 36*N^2) * (X^2 - 4*N^2) := by
  nlinarith [hp, hq, hr, hs]
```

If `nlinarith` is slow, split into two `ring` identities:

```lean
have hps : (p*s)^2 = X^2 - 36*N^2 := by nlinarith [hp, hs]
have hqr : (q*r)^2 = X^2 - 4*N^2 := by nlinarith [hq, hr]
-- then normalize `(p*q*r*s)^2 = (p*s)^2 * (q*r)^2` by `ring`.
```

The exact Pythagorean identity is:

```lean
theorem centered_pythagorean_identity
    {X N Y : ℤ}
    (hY : Y^2 = (X^2 - 36*N^2) * (X^2 - 4*N^2)) :
    Y^2 + (16*N^2)^2 = (X^2 - 20*N^2)^2 := by
  rw [hY]
  ring
```

Thus:

```lean
def CenteredAP_to_pythagorean_triple : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    PythagoreanTriple (S.p*S.q*S.r*S.s) (16*S.N^2) (S.X^2 - 20*S.N^2)
```

Proof is `centered_product_identity`, `centered_pythagorean_identity`, then unfold `PythagoreanTriple` and `ring`.

---

## 4. Why this is not yet `a^4 + b^4 = c^2`

The exact equation from the AP is

```text
(p*q*r*s)^2 + (16*N^2)^2 = (X^2 - 20*N^2)^2.
```

Equivalently,

```text
(p*q*r*s)^2 + (4*N)^4 = (X^2 - 20*N^2)^2.
```

Only the second leg is visibly a fourth power.  The first leg is the square of `p*q*r*s`; it is not generally a fourth power.  The primitive normalization gives the roots `p,q,r,s` pairwise coprime and odd; it does **not** imply that each of `p,q,r,s` is itself a square.  Therefore the AP algebra does not produce a direct instance of

```lean
a ^ 4 + b ^ 4 = c ^ 2
```

by `ring`.

So the proposed `FourSquaresAPToFermat42Bridge` should not be used as the next local theorem unless you are willing to prove it by first proving the four-square-AP theorem, making it vacuous.

---

## 5. Correct descent theorem DAG

### 5.1 Primitive centered descent residual

```lean
def PrimitiveCenteredFourSqAPDescent : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ T : PrimitiveCenteredFourSqAP, T.N.natAbs < S.N.natAbs
```

This is the genuine hard mathematical frontier.

### 5.2 No primitive AP from descent

```lean
theorem no_primitive_centered_from_descent
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    ¬ Nonempty PrimitiveCenteredFourSqAP := by
  intro hne
  classical
  let Sset : Set ℕ := {n | ∃ S : PrimitiveCenteredFourSqAP, n = S.N.natAbs}
  have hS : Sset.Nonempty := by
    rcases hne with ⟨S⟩
    exact ⟨S.N.natAbs, ⟨S, rfl⟩⟩
  let m := Nat.find hS
  have hm : m ∈ Sset := Nat.find_spec hS
  rcases hm with ⟨S, hmS⟩
  rcases hdesc S with ⟨T, hlt⟩
  have hTmem : T.N.natAbs ∈ Sset := ⟨T, rfl⟩
  have hmin : m ≤ T.N.natAbs := Nat.find_min' hS hTmem
  rw [hmS] at hmin
  exact not_lt_of_ge hmin hlt
```

This is compile-oriented and contains no mathematical hard work.

### 5.3 Integer AP theorem from normalization and descent

```lean
theorem fourIntSquaresAPConst_of_descent
    (hnorm : ArbitraryAP_to_primitive_centered)
    (hdesc : PrimitiveCenteredFourSqAPDescent) :
    FourIntSquaresAPConst := by
  intro w x y z hAP
  by_contra hnot
  have hno := no_primitive_centered_from_descent hdesc
  exact hno (hnorm hAP hnot)
```

Here `FourIntSquaresAPConst` is:

```lean
def FourIntSquaresAPConst : Prop :=
  ∀ {w x y z : ℤ}, IntFourSqAP w x y z → FourSqAPConst w x y z
```

---

## 6. Sub-DAG for the descent step

The descent theorem should be decomposed into these exact targets.

### D1. Primitive Pythagorean triple classification

```lean
def CenteredAP_pythagorean_classification : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ m n : ℤ,
      S.p*S.q*S.r*S.s = m^2 - n^2 ∧
      16*S.N^2 = 2*m*n ∧
      S.X^2 - 20*S.N^2 = m^2 + n^2 ∧
      Int.gcd m n = 1 ∧
      ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) ∧
      0 ≤ m
```

This uses:

```lean
PythagoreanTriple.coprime_classification'
```

Required supporting lemmas:

```lean
def CenteredAP_pythagorean_coprime : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    Int.gcd (S.p*S.q*S.r*S.s) (16*S.N^2) = 1

def CenteredAP_pythagorean_odd : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    (S.p*S.q*S.r*S.s) % 2 = 1

def CenteredAP_pythagorean_hyp_pos : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    0 < S.X^2 - 20*S.N^2
```

`CenteredAP_pythagorean_odd` is parity simplification from `hp_odd hq_odd hr_odd hs_odd`.  The coprime lemma is gcd bookkeeping using pairwise coprimality and the fact any prime dividing `N` also divides differences among the square terms.  Hypotenuse positivity follows from the Pythagorean identity and nonzero legs.

### D2. Square even-leg split

From

```lean
16*N^2 = 2*m*n
Int.gcd m n = 1
opposite parity of m,n
```

one obtains a square-factor split of the coprime factors.  State it independently:

```lean
def SquareEvenLegSplit : Prop :=
  ∀ {N m n : ℤ},
    0 < N →
    16*N^2 = 2*m*n →
    Int.gcd m n = 1 →
    ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) →
    ∃ A D : ℤ,
      A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧
      -- exact orientation can be swapped depending on which of m,n is even
      ((m = 8*A^2 ∧ n = D^2) ∨ (n = 8*A^2 ∧ m = D^2)) ∧
      N.natAbs = (A*D).natAbs
```

This is gcd/factorization work, not `ring`.  It is a standard “coprime factors of a square are squares” lemma plus parity bookkeeping.

### D3. Square-pair extraction

After substituting the split back into

```lean
S.p*S.q*S.r*S.s = m^2 - n^2
S.X^2 - 20*S.N^2 = m^2 + n^2
```

extract the pair of square witnesses:

```lean
def CenteredAP_to_square_pair : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ A D R T : ℤ,
      A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧
      S.N.natAbs = (A*D).natAbs ∧
      R^2 = 4*A^2 + D^2 ∧
      T^2 = 16*A^2 + D^2
```

This contains ring algebra plus the square-factor split above.  It is the clean interface to the classical descent.

### D4. Square-pair descent

```lean
def SquarePairDescent : Prop :=
  ∀ {A D R T : ℤ},
    A ≠ 0 → D ≠ 0 → Odd D →
    R^2 = 4*A^2 + D^2 →
    T^2 = 16*A^2 + D^2 →
    ∃ A' D' R' T' : ℤ,
      A' ≠ 0 ∧ D' ≠ 0 ∧ Odd D' ∧
      R'^2 = 4*A'^2 + D'^2 ∧
      T'^2 = 16*A'^2 + D'^2 ∧
      (A'*D').natAbs < (A*D).natAbs
```

This is the real descent core.  It is not `ring`; it requires Pythagorean parametrization, two coprime factorization refinements, and an inequality decrease.

### D5. Rebuild a smaller primitive AP

```lean
def SquarePair_to_primitive_centered_AP : Prop :=
  ∀ {A D R T : ℤ},
    A ≠ 0 → D ≠ 0 → Odd D →
    R^2 = 4*A^2 + D^2 →
    T^2 = 16*A^2 + D^2 →
    ∃ S : PrimitiveCenteredFourSqAP,
      S.N.natAbs = (A*D).natAbs
```

Most equations here are `ring`; primitive normalization may need gcd cleanup.

Then:

```lean
def PrimitiveCenteredFourSqAPDescent_from_square_pair : Prop :=
  CenteredAP_to_square_pair →
  SquarePairDescent →
  SquarePair_to_primitive_centered_AP →
  PrimitiveCenteredFourSqAPDescent
```

---

## 7. Edge cases checklist

1. **Signs.**  Replace roots by `natAbs` or choose sign-normalized integer roots during primitive normalization.  AP depends only on squares.
2. **Negative common difference.**  Reverse `(w,x,y,z)` to `(z,y,x,w)`.
3. **Zero common difference / repeated adjacent squares.**  Close by `intFourSqAP_const_of_adjacent_eq` with `nlinarith`.
4. **Zero root in a primitive nonconstant AP.**  Excluded by the primitive parity lemma: primitive nonconstant roots are odd, hence nonzero.
5. **Nonprimitive scaling.**  Divide all four roots by their common gcd; the common square difference divides by `g^2`; constantness lifts back after multiplying by `g^2`.
6. **Pairwise coprimality.**  After primitive normalization, if an odd prime divides two roots, it divides their square difference and then all four roots; contradiction.  Prime `2` is excluded by oddness.

---

## 8. If insisting on `not_fermat_42`

The exact AP equation you get is

```lean
(p*q*r*s)^2 + (16*N^2)^2 = (X^2 - 20*N^2)^2
```

or

```text
(p*q*r*s)^2 + (4*N)^4 = (X^2 - 20*N^2)^2.
```

This is **not** an instance of

```lean
a^4 + b^4 = c^2
```

unless one can also prove `p*q*r*s` is a square.  Primitive AP hypotheses do not give that.  Therefore there is no short direct `not_fermat_42` call from the four-square AP algebra.  The correct proof target is the primitive descent DAG above.
