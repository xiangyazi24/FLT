# Q2653 (dm-codex1): independent `RatQuarticEisensteinDegenerate` route

Repo path mentioned by requester: `/Users/huangx/repos/flt-ai`  
GitHub repo/branch: `xiangyazi24/FLT`, branch `scratch`

Target already reduced in the project:

```lean
def RatQuarticEisensteinDegenerate : Prop :=
  ∀ {t s : ℚ}, s ^ 2 = t ^ 4 - t ^ 2 + 1 → t = 0 ∨ t ^ 2 = 1
```

Constraint respected by this plan: do not use `RationalPointsN12`, the E24/E1 finite-point theorem, or full-cover residual theorems.  The only recommended Mathlib reuse is elementary arithmetic, rational denominator APIs, Pythagorean triples, and possibly existing cyclotomic/PID infrastructure if choosing the algebraic-number-theory route.

## 1. Classical equivalence and exact integer theorem

`x^4 - x^2 + 1` is `Φ₁₂(x)`.  Homogenizing at `t = A/N` gives

```text
N^4 * (t^4 - t^2 + 1) = A^4 - A^2*N^2 + N^4.
```

This is the Eisenstein norm form

```text
A^4 - A^2*N^2 + N^4 = Norm(A^2 + N^2*ω),   ω^2 + ω + 1 = 0,
```

because `Norm(a + bω) = a^2 - a*b + b^2`.  I would call the Lean target the primitive homogeneous Eisenstein quartic.  It is adjacent to, but not literally the usual Ljunggren equation `Y^2 = X^4 + X^2 + 1` unless an additional proved transformation is supplied.  Do not target the plus-sign Ljunggren theorem as a black box.

The exact integer theorem to target is:

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

namespace MazurProof.RationalPointsN12

/-- Primitive cleared Eisenstein quartic datum. -/
def PrimitiveEisensteinQuarticDatum (A N S : ℤ) : Prop :=
  N ≠ 0 ∧
  Int.gcd A N = 1 ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Main independent integer theorem. -/
def PrimitiveEisensteinQuarticTheorem : Prop :=
  ∀ {A N S : ℤ},
    PrimitiveEisensteinQuarticDatum A N S →
    A = 0 ∨ A ^ 2 = N ^ 2

/-- Normalized positive bad solution used for descent. -/
def NormalizedEisensteinBad (A N S : ℤ) : Prop :=
  0 < A ∧ A < N ∧
  Int.gcd A N = 1 ∧
  0 < S ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Bounded descent theorem sufficient to prove the primitive theorem. -/
def NormalizedEisensteinDescent : Prop :=
  ∀ {A N S : ℤ},
    NormalizedEisensteinBad A N S →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧
      Int.natAbs A' + Int.natAbs N' < Int.natAbs A + Int.natAbs N

end MazurProof.RationalPointsN12
```

Then prove `PrimitiveEisensteinQuarticTheorem` by: primitive bad solution → sign/swap normalization → minimal normalized bad solution by measure `Int.natAbs A + Int.natAbs N` → contradict `NormalizedEisensteinDescent`.

## 2. Why `not_fermat_42` is not a direct solution

Mathlib has:

```lean
-- Mathlib.NumberTheory.FLT.Four
-- theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
--   a ^ 4 + b ^ 4 ≠ c ^ 2
```

The cleared target is not of that shape.  It rewrites as both

```text
S^2 = A^4 - A^2*N^2 + N^4
S^2 = (A^2 - N^2)^2 + (A*N)^2
(A^2 + N^2)^2 = S^2 + 3*(A*N)^2
```

The Pythagorean form has one square leg, `A^2 - N^2`, but the other leg is only `A*N`, not a square or fourth power.  `not_fermat_42` would apply only after proving additional splitting that is essentially the missing descent.  Therefore:

* Do **not** use `not_fermat_42` as the main dependency.
* It is fine to imitate the proof architecture of `Mathlib/NumberTheory/FLT/Four.lean`.
* Reuse underlying tools such as `PythagoreanTriple.coprime_classification`, `PythagoreanTriple.coprime_classification'`, `Int.sq_of_gcd_eq_one`, `Int.sq_of_isCoprime`, `Nat.find`, and `linear_combination`.

## 3. Rational denominator clearing and primitive reduction

Use `A = t.num`, `N = (t.den : ℤ)`.  The denominator is positive, and `Rat.reduced` gives coprimality of numerator and denominator.

Best denominator-clearing lemma:

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- If an integer is a rational square, then it is an integer square. -/
def IntSquareOfRatSquareInt : Prop :=
  ∀ {q : ℚ} {m : ℤ},
    q ^ 2 = (m : ℚ) → ∃ z : ℤ, z ^ 2 = m

/-- Denominator-cleared primitive integer point from a rational quartic point. -/
def RatQuarticToPrimitiveInt : Prop :=
  ∀ {t s : ℚ},
    s ^ 2 = t ^ 4 - t ^ 2 + 1 →
    ∃ A N S : ℤ,
      Int.gcd A N = 1 ∧
      N ≠ 0 ∧
      t = (A : ℚ) / (N : ℚ) ∧
      S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Integer theorem supplies the required rational theorem. -/
def RatQuarticFromPrimitiveInt : Prop :=
  PrimitiveEisensteinQuarticTheorem →
  RatQuarticEisensteinDegenerate

end MazurProof.RationalPointsN12
```

Proof notes:

1. For `IntSquareOfRatSquareInt`, use `Rat.isSquare_intCast_iff` from `Mathlib.Data.Rat.Lemmas`.  From `q^2 = (m : ℚ)`, obtain `IsSquare (m : ℚ)`, then `IsSquare m`.
2. For `RatQuarticToPrimitiveInt`, set `A := t.num`, `N := (t.den : ℤ)`, `P := A^4 - A^2*N^2 + N^4`.
3. Rewrite `t = A/N` using `Rat.num_divInt_den`/`Rat.num_div_den` APIs.
4. From the quartic equation prove in `ℚ`:

   ```lean
   (s * (N : ℚ) ^ 2) ^ 2 = (P : ℚ)
   ```

   using `field_simp` with `Rat.den_nz`, then `ring`.
5. Apply `IntSquareOfRatSquareInt` to get `S^2 = P` in `ℤ`.
6. Apply `PrimitiveEisensteinQuarticTheorem`; translate `A = 0` to `t = 0`, and `A^2 = N^2` to `t^2 = 1` by clearing `N ≠ 0`.

The reverse implication is also easy and useful for tests: from primitive `A,N,S`, set `t = (A:ℚ)/(N:ℚ)`, `s = (S:ℚ)/(N:ℚ)^2`.

## 4. Concrete independent descent DAG

Define the integer Eisenstein-triple conic locally:

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

namespace MazurProof.RationalPointsN12

/-- `Z^2 = X^2 - X*Y + Y^2`, the Eisenstein norm conic. -/
def EisensteinTriple (X Y Z : ℤ) : Prop :=
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2

/-- One positive primitive parametrization, up to swapping `X` and `Y`. -/
def EisensteinParam (X Y Z m n : ℤ) : Prop :=
  Z = m ^ 2 - m * n + n ^ 2 ∧
  ((X = m ^ 2 - n ^ 2 ∧ Y = 2 * m * n - n ^ 2) ∨
   (Y = m ^ 2 - n ^ 2 ∧ X = 2 * m * n - n ^ 2))

/-- Positive primitive classification of Eisenstein triples. -/
def EisensteinTripleClassification : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    Int.gcd X Y = 1 →
    EisensteinTriple X Y Z →
    ∃ m n : ℤ,
      0 < n ∧ n < m ∧
      Int.gcd m n = 1 ∧
      ¬ (3 : ℤ) ∣ m + n ∧
      EisensteinParam X Y Z m n

/-- Classification plus square-side splitting gives a smaller bad solution. -/
def EisensteinSquareSidesDescentCore : Prop :=
  ∀ {A N S m n : ℤ},
    0 < A → A < N → Int.gcd A N = 1 →
    0 < n → n < m → Int.gcd m n = 1 → ¬ (3 : ℤ) ∣ m + n →
    EisensteinParam (A ^ 2) (N ^ 2) S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧
      Int.natAbs A' + Int.natAbs N' < Int.natAbs A + Int.natAbs N

end MazurProof.RationalPointsN12
```

DAG to prove `NormalizedEisensteinDescent`:

1. From `NormalizedEisensteinBad A N S`, get

   ```lean
   EisensteinTriple (A ^ 2) (N ^ 2) S
   Int.gcd (A ^ 2) (N ^ 2) = 1
   0 < A ^ 2
   0 < N ^ 2
   0 < S
   ```

   The triple equation is just `ring`; coprimality follows from `Int.gcd A N = 1` and `.pow`/prime-divisor arguments.

2. Apply `EisensteinTripleClassification` to obtain `m,n` and `EisensteinParam (A^2) (N^2) S m n`.

3. Prove the finite square-factor splitting lemmas needed by `EisensteinSquareSidesDescentCore`:

   ```lean
   -- factors from A^2 = m^2 - n^2 = (m-n)*(m+n)
   -- factors from N^2 = n*(2*m-n)
   -- gcd controls: gcd(m-n,m+n) ∣ 2, gcd n (2*m-n) ∣ 2, and 3 ∤ m+n
   -- conclusion: each factor is a square or twice a square, by parity cases.
   ```

   Use `Int.sq_of_gcd_eq_one` / `Int.sq_of_isCoprime` after dividing out the controlled factor `2`.  This is the same kind of casework as `Fermat42.not_minimal`, but for the Eisenstein parametrization.

4. The algebraic core should be isolated as `EisensteinSquareSidesDescentCore`.  It is the only genuinely hard local theorem.  Its output is another primitive solution with a strictly smaller measure, so no elliptic-curve finite-point theorem enters.

5. Close the descent with a minimal-counterexample wrapper copied structurally from `Fermat42.exists_minimal`:

   ```lean
   -- def badMeasure (A N : ℤ) : ℕ := Int.natAbs A + Int.natAbs N
   -- use Nat.find on {m | ∃ A N S, NormalizedEisensteinBad A N S ∧ m = badMeasure A N}
   -- apply NormalizedEisensteinDescent to contradict minimality
   ```

## 5. Alternative Route A: use Eisenstein PID infrastructure

This is still independent of E1/E24 rational-point theorems, but heavier.  Mathlib’s FLT3 development imports the third-cyclotomic PID machinery:

```lean
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
```

Possible theorem shape:

```lean
/-- In `ℤ[ω]`, primitive `α` with square norm is associated to a square. -/
def EisensteinNormSquareAssociatedSquare : Prop :=
  ∀ {A N S : ℤ},
    Int.gcd A N = 1 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    -- α = A^2 + N^2*ω, expanded in the chosen Mathlib cyclotomic-integer representation
    True
```

Concrete Route A steps:

1. Work in `𝓞 K`, `[NumberField K]`, `[IsCyclotomicExtension {3} ℚ K]`, with `ω = ζ₃`.
2. Define `α = A^2 + N^2 * ω`; prove `norm α = A^4 - A^2*N^2 + N^4`.
3. Prove `IsCoprime α (star α)` from `Int.gcd A N = 1`; the only delicate common prime is above `3`.
4. Use the existing UFD/PID associated-power lemma behind `Int.sq_of_gcd_eq_one`, e.g. grep `exists_associated_pow_of_mul_eq_pow`.
5. Reduce units using `IsCyclotomicExtension.Rat.Three.Units.mem` and related unit congruence lemmas.
6. Expanding `α = unit * β^2` gives the same square-side splitting/descent as Route B.

I would try Route B first unless the project already imports cyclotomic number fields elsewhere; Route A may spend more effort on typeclass and representation issues than on the actual quartic descent.

## 6. Mathlib files/API to grep first

Project pin from `lakefile.toml`: Mathlib rev `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.

```text
Mathlib/Data/Rat/Lemmas.lean
  Rat.isSquare_iff
  Rat.isSquare_intCast_iff
  Rat.mul_self_num
  Rat.mul_self_den
  Rat.num_den_mk
  Rat.num_divInt_den

Mathlib/NumberTheory/PythagoreanTriples.lean
  PythagoreanTriple.coprime_classification
  PythagoreanTriple.coprime_classification'
  PythagoreanTriple.classification
  PythagoreanTriple.even_odd_of_coprime

Mathlib/RingTheory/Int/Basic.lean
  Int.sq_of_gcd_eq_one
  Int.sq_of_isCoprime
  Int.eq_pow_of_mul_eq_pow_odd
  Int.Prime.dvd_mul'
  Int.Prime.dvd_pow'

Mathlib/NumberTheory/FLT/Four.lean
  Fermat42.exists_minimal
  Fermat42.coprime_of_minimal
  Fermat42.not_minimal
  not_fermat_42       -- proof pattern only; not the desired dependency

Mathlib/NumberTheory/FLT/Three.lean
Mathlib/NumberTheory/NumberField/Cyclotomic/PID.lean
Mathlib/NumberTheory/NumberField/Cyclotomic/Three.lean
  IsCyclotomicExtension.Rat.three_pid
  IsCyclotomicExtension.Rat.Three.Units.mem
  IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
  IsCyclotomicExtension.Rat.Three.eta_sq
  IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one

Mathlib/NumberTheory/Zsqrtd/Basic.lean
Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean
  useful norm examples, but no ready `EisensteinInt` classifier found
```

Search notes from this pass:

```text
Ljunggren                    -- no ready Mathlib classifier found
Eisenstein quartic           -- no ready Mathlib classifier found
RatQuartic                   -- no ready Mathlib classifier found
x^4 - x^2*y^2 + y^4          -- no ready Mathlib classifier found
not_fermat_42                -- exists in FLT/Four; wrong final shape
EisensteinInt                -- no obvious dedicated Mathlib type found
```

## 7. Recommended implementation seam

Add a new file independent of the N12 finite-point route, for example:

```lean
-- FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.LinearCombination

-- no imports of:
--   FLT.Assumptions.MazurProof.RationalPointsN12
--   E24/E1 finite-point terminal theorem files
--   full-cover residual theorem files
```

First milestones to check:

```lean
-- 1. integer-square extraction from rational square
-- theorem intSquare_of_ratSquare_int : IntSquareOfRatSquareInt

-- 2. denominator clearing
-- theorem ratQuartic_to_primitive_int : RatQuarticToPrimitiveInt

-- 3. wrapper from integer theorem to project theorem
-- theorem ratQuarticEisensteinDegenerate_of_primitive
--     (hZ : PrimitiveEisensteinQuarticTheorem) :
--     RatQuarticEisensteinDegenerate

-- 4. hard independent theorem
-- theorem primitiveEisensteinQuartic : PrimitiveEisensteinQuarticTheorem
```

Once milestones 1–3 compile, the project has a clean hard seam: all remaining work is the standalone primitive integer descent, with no dependency on E1 finite-point classification.
