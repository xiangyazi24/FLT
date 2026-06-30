# Q2449 AP-to-FLT4 bridge proof route

## Verdict

The proposed residual

```lean
def FourSquaresAPToFermat42Bridge : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ (w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2) →
    ∃ a b c : ℤ,
      a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2
```

is not the right Lean frontier.  I do not know an honest direct algebraic construction of such `a,b,c` from an arbitrary nonconstant four-square AP.  The first canonical algebraic construction gives a Pythagorean triple

```text
Y^2 + (16*N^2)^2 = (X^2 - 20*N^2)^2,
```

so only one leg is a fourth power: `(16*N^2)^2 = (4*N)^4`.  The other leg is `Y = p*q*r*s`; it is not generally a square, so this does **not** feed directly into `not_fermat_42`, whose input must have the shape

```lean
a^4 + b^4 = c^2.
```

Thus `FourSquaresAPToFermat42Bridge` is classically true only after the four-square-AP theorem itself is already proved, at which point it can be proved vacuously by `False.elim`.  That makes it useless as a reduction to `not_fermat_42`.

The corrected Lean frontier should be a primitive positive AP descent theorem, or a square-pair descent theorem reached from the primitive AP.  This is the route whose algebra is Lean-feasible.

---

## Basic definitions

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.Tactic

def IntFourSqAP (w x y z : ℤ) : Prop :=
  x^2 - w^2 = y^2 - x^2 ∧ y^2 - x^2 = z^2 - y^2

def FourSqAPConst (w x y z : ℤ) : Prop :=
  w ^ 2 = x ^ 2 ∧ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2
```

Useful immediate edge-case lemma:

```lean
-- proof: unfold `IntFourSqAP`, then `nlinarith`.
def IntFourSqAP.adjacent_eq_forces_const_target : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    (w^2 = x^2 ∨ x^2 = y^2 ∨ y^2 = z^2) →
    FourSqAPConst w x y z
```

This is a pure `nlinarith` lemma: if one adjacent difference is zero, the common difference is zero, hence all three adjacent differences are zero.

---

## Correct primitive positive AP statement

Use a centered four-square AP with positive common difference `4*N`:

```lean
structure PrimitiveCenteredFourSqAP where
  X : ℤ
  N : ℤ
  hNpos : 0 < N
  p q r s : ℤ
  hp : p^2 = X - 6*N
  hq : q^2 = X - 2*N
  hr : r^2 = X + 2*N
  hs : s^2 = X + 6*N
  -- primitive/pairwise root conditions; this is stronger than merely gcd of all roots = 1
  hpq : Int.gcd p q = 1
  hpr : Int.gcd p r = 1
  hps : Int.gcd p s = 1
  hqr : Int.gcd q r = 1
  hqs : Int.gcd q s = 1
  hrs : Int.gcd r s = 1
  -- parity after primitive normalization: all roots are odd
  hp_odd : p % 2 = 1
  hq_odd : q % 2 = 1
  hr_odd : r % 2 = 1
  hs_odd : s % 2 = 1
```

The reduction from arbitrary AP should be isolated as:

```lean
def ArbitraryAP_to_primitive_centered : Prop :=
  ∀ {w x y z : ℤ},
    IntFourSqAP w x y z →
    ¬ FourSqAPConst w x y z →
    Nonempty PrimitiveCenteredFourSqAP
```

Proof route for this reduction:

1. Let the common difference be `δ = x^2 - w^2`.
2. If `δ = 0`, close by `IntFourSqAP.adjacent_eq_forces_const_target`.
3. If `δ < 0`, reverse the AP: `(z,y,x,w)` has common difference `-δ > 0`.
4. Divide all roots by their common gcd.  The square AP divides by `g^2`.
5. In the primitive AP, the roots are all odd:
   * square residues mod `8` are `0,1,4`;
   * a primitive nonconstant length-four AP cannot have an odd common difference because the residues would force a non-square residue at the third term;
   * if the even common difference made all roots even, primitiveness is contradicted;
   * hence all square residues are `1 mod 8`, so the difference is divisible by `8`, in particular by `4`.
6. Write the positive common difference as `4*N` and center the four terms as

```lean
p^2 = X - 6*N,
q^2 = X - 2*N,
r^2 = X + 2*N,
s^2 = X + 6*N.
```

The centering algebra is all `ring`/`nlinarith`; the primitive parity/gcd normalization is the only number-theoretic bookkeeping.

---

## The key AP algebra: the Pythagorean triple

From a primitive centered AP, define

```lean
Y := p*q*r*s.
C := X^2 - 20*N^2.
```

The exact identities are:

```lean
lemma centered_AP_product_identity
    (S : PrimitiveCenteredFourSqAP) :
    (S.p*S.q*S.r*S.s)^2 =
      (S.X^2 - 36*S.N^2) * (S.X^2 - 4*S.N^2)
```

Proof: rewrite

```text
(p*s)^2 = (X - 6N)(X + 6N) = X^2 - 36N^2,
(q*r)^2 = (X - 2N)(X + 2N) = X^2 - 4N^2,
```

then `ring`.

The key identity is:

```lean
lemma centered_AP_pythagorean_identity
    (X N Y : ℤ)
    (hY : Y^2 = (X^2 - 36*N^2) * (X^2 - 4*N^2)) :
    Y^2 + (16*N^2)^2 = (X^2 - 20*N^2)^2 := by
  nlinarith [hY]
-- or just `rw [hY]; ring`
```

So the centered AP gives:

```lean
def CenteredAP_to_pythagorean_triple_target : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    PythagoreanTriple (S.p*S.q*S.r*S.s) (16*S.N^2) (S.X^2 - 20*S.N^2)
```

This is pure algebra after `centered_AP_product_identity`.

The gcd and positivity lemmas needed to call Mathlib's classification are:

```lean
def CenteredAP_pythagorean_primitive_target : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    Int.gcd (S.p*S.q*S.r*S.s) (16*S.N^2) = 1

def CenteredAP_pythagorean_odd_leg_target : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    (S.p*S.q*S.r*S.s) % 2 = 1

def CenteredAP_pythagorean_hyp_pos_target : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    0 < S.X^2 - 20*S.N^2
```

Classification target:

```lean
def CenteredAP_pythagorean_param_target : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ m n : ℤ,
      S.p*S.q*S.r*S.s = m^2 - n^2 ∧
      16*S.N^2 = 2*m*n ∧
      S.X^2 - 20*S.N^2 = m^2 + n^2 ∧
      Int.gcd m n = 1 ∧
      ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) ∧
      0 ≤ m
```

Proof: exact application of

```lean
PythagoreanTriple.coprime_classification'
```

to the triple above.

---

## Why this does not directly give `not_fermat_42`

The obtained equation is

```text
(p*q*r*s)^2 + (4*N)^4 = (X^2 - 20*N^2)^2.
```

To use `not_fermat_42`, we would need `(p*q*r*s)^2` to be a fourth power, equivalently `p*q*r*s` to be a square up to sign.  That is not a formal consequence of the primitive AP hypotheses.  The primitive hypotheses give pairwise coprime odd roots, not that their product is a square.  In fact, making that product a square would require each root to be a square up to sign, which is not available: the roots are the square roots of the AP terms, not themselves known squares.

Therefore there is no short equation of the form

```lean
a^4 + b^4 = c^2
```

coming from the centered AP by `ring` alone.

---

## Correct descent frontier

The correct hard theorem is a descent step on primitive centered APs:

```lean
def PrimitiveCenteredFourSqAPDescent : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ T : PrimitiveCenteredFourSqAP, T.N.natAbs < S.N.natAbs
```

Then:

```lean
def NoPrimitiveCenteredFourSqAP_from_descent : Prop :=
  PrimitiveCenteredFourSqAPDescent → ¬ Nonempty PrimitiveCenteredFourSqAP
```

This wrapper is standard well-founded descent on `S.N.natAbs` using `Nat.find` or `WellFounded.fix`; it is not mathematically hard.

Then the integer AP theorem is:

```lean
def FourIntSquaresAPConst_from_descent : Prop :=
  ArbitraryAP_to_primitive_centered →
  PrimitiveCenteredFourSqAPDescent →
  ∀ {w x y z : ℤ}, IntFourSqAP w x y z → FourSqAPConst w x y z
```

This is the honest replacement for `FourSquaresAPToFermat42Bridge`.

---

## Descent step DAG after the Pythagorean triple

The descent step from `S` should be split as follows.

### D1. Parameterize the Pythagorean triple

Use the target `CenteredAP_pythagorean_param_target` above.

### D2. Split the square even leg

From

```lean
16*S.N^2 = 2*m*n
Int.gcd m n = 1
one of m,n is even and the other odd
```

normalize the even parameter as `2*u` and the odd parameter as `v`, obtaining

```lean
def SplitEvenSquareLeg_target : Prop :=
  ∀ {N m n : ℤ},
    0 < N →
    16*N^2 = 2*m*n →
    Int.gcd m n = 1 →
    ((m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0)) →
    ∃ u v : ℤ,
      4*u*v = 16*N^2 ∧
      Int.gcd (2*u) v = 1 ∧
      Odd v
```

This is mostly parity normalization and `ring`.

### D3. Coprime product of a square gives square factors

From

```lean
4*u*v = 16*N^2
Int.gcd (2*u) v = 1
Odd v
```

prove the square-factor split:

```lean
def CoprimeSquareLegFactor_target : Prop :=
  ∀ {N u v : ℤ},
    0 < N →
    4*u*v = 16*N^2 →
    Int.gcd (2*u) v = 1 →
    Odd v →
    ∃ A D : ℤ,
      A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧
      u = 4*A^2 ∧ v = D^2 ∧
      N.natAbs = (A*D).natAbs
```

This is gcd/factorization work, not `ring`.  Use the existing “coprime product square implies square factors” lemmas if already developed; otherwise prove it over `Nat` using prime valuations or `Nat.Coprime` divisibility APIs.

### D4. Obtain the two square witnesses

The previous steps imply there are `A,D` such that both

```lean
4*A^2 + D^2
16*A^2 + D^2
```

are squares.  State this as:

```lean
def CenteredAP_to_square_pair_target : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ A D R T : ℤ,
      A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧
      S.N.natAbs = (A*D).natAbs ∧
      R^2 = 4*A^2 + D^2 ∧
      T^2 = 16*A^2 + D^2
```

This is the algebraic core after Pythagorean classification.  The identities connecting `R,T` to the centered AP parameters are `ring` once the normalized parameter equations are in hand; the square-factor split is the only hard arithmetic part.

### D5. Square-pair descent back to a smaller centered AP

From the two square witnesses, prove a smaller pair and then reconstruct a smaller primitive centered AP.  The theorem shape should be:

```lean
def SquarePairDescent_target : Prop :=
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

Then reconstruct a centered AP from `A',D'` by the reversible algebra from the square-pair construction.  This final reconstruction is again `ring` plus normalization; the strict decrease is an inequality/gcd lemma.

This is the proof route sketched by the classical four-square AP descent: primitive AP → Pythagorean triple → square pair → smaller square pair → smaller primitive AP.

---

## Edge cases checklist

1. **Signs of roots.**  Irrelevant to AP equations because only squares occur.  In normalization, replace roots by `natAbs` or choose signs convenient for Pythagorean classification.

2. **Negative common difference.**  Reverse the quadruple `(w,x,y,z)` to `(z,y,x,w)`.

3. **Zero common difference.**  Immediate constant AP.  Close by `nlinarith`.

4. **Repeated adjacent square.**  Same as zero common difference; if one adjacent difference is zero, all are zero.

5. **Zero root in a nonconstant primitive AP.**  Excluded during primitive parity normalization: primitive nonconstant length-four square AP must have all roots odd.  A zero root is even.

6. **Nonprimitive scaling.**  Divide all roots by their common gcd `g`; AP differences divide by `g^2`.  Constantness of squares is preserved upward by multiplying by `g^2`.

7. **Pairwise coprimality.**  After primitive normalization and oddness, pairwise coprimality follows: if an odd prime divides two roots, it divides the common difference and then all four roots; contradiction.  The prime `2` is excluded by oddness.

---

## Bottom line

There is no useful short AP-to-`not_fermat_42` bridge with explicit `a,b,c`.  The exact algebra from a primitive centered AP gives

```text
(p*q*r*s)^2 + (4*N)^4 = (X^2 - 20*N^2)^2,
```

not `a^4 + b^4 = c^2`.

So the corrected implementation plan is:

```lean
ArbitraryAP_to_primitive_centered
PrimitiveCenteredFourSqAPDescent
FourIntSquaresAPConst_from_descent
```

Use `Mathlib.NumberTheory.FLT.Four` only if another independently proved local bridge really produces `a^4 + b^4 = c^2`; the primitive AP algebra above does not do so by itself.
