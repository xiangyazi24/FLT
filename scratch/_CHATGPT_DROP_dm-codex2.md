# Q2408 (dm-codex2): Lean-realistic plan for E1 nonzero-Y squareclass extraction

## Audit summary

For the target

```lean
E1FullCoverSquareclassExtractionIntStatement :
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y
```

the cleanest route is **not** to start with quotient squareclasses.  Use ordinary rational representatives and split the work into three layers:

1. **Valuation parity layer**: from `E1 X Y` and `Y ≠ 0`, prove that each of `X`, `X-1`, `X+3` has even `p`-adic valuation for every prime `p ≠ 2,3`.
2. **Squareclass support layer**: convert “all outside valuations even” into a representative `d ∈ {±1,±2,±3,±6}` and a rational square factor.
3. **Algebra/denominator layer**: choose a common integer denominator for the three rational square factors and clear denominators to get the two integer cover equations, then primitive-normalize `(A,B,C,T)`.

The smallest genuinely hard residual is layer 1 plus, depending on how much UFD infrastructure you want to write, possibly layer 2.  Layer 3 is algebraic plumbing and should be proved now.

## Mathlib APIs to check/use locally

Search/check these names first:

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.Squarefree.Basic

#check Rat.num
#check Rat.den
#check Rat.den_nz
#check Rat.den_ne_zero
#check Rat.num_ne_zero
#check Rat.num_divInt_den
#check Rat.num_den_mk
#check Rat.add_num_den
#check Rat.sub_intCast_den
#check Rat.add_intCast_den
#check Rat.pow_eq_divInt

#check padicValRat
#check padicValRat.defn
#check padicValRat.mul
#check padicValRat.div
#check padicValRat.pow
#check padicValRat.of_int_multiplicity
#check multiplicity
#check multiplicity_mul
#check FiniteMultiplicity
#check Nat.prime_iff_prime_int
```

Important API facts visible in current Mathlib:

- `Rat.num_divInt_den : q.num /. q.den = q` is the reduced rational representation.
- `Rat.den_nz`, `Rat.den_ne_zero`, and `Rat.den_pos` discharge nonzero/positive denominator goals.
- `Rat.num_ne_zero : q.num ≠ 0 ↔ q ≠ 0` bridges nonzero rational and nonzero numerator.
- `Rat.sub_intCast_den` and `Rat.add_intCast_den` show that subtracting/adding an integer does not change a rational denominator.  Thus for `X = N/D`, the factors are represented by `(N-D)/D` and `(N+3D)/D` with the same `D`.
- `padicValRat : ℕ → ℚ → ℤ` is defined as `padicValInt p q.num - padicValNat p q.den`.
- `padicValRat.pow` gives `padicValRat p (q^k) = k * padicValRat p q`.
- `padicValRat.mul` and `padicValRat.div` require `[Fact p.Prime]` and nonzero hypotheses.
- `padicValRat.defn` rewrites a rational presented as `n /. d` into integer multiplicities.

## Lean-facing definitions

These are quotient-free and should be stable.

```lean
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Algebra.Squarefree.Basic

namespace MazurProof.RationalPointsN12

/-- The shifted curve `E1 : Y^2 = X(X-1)(X+3)`. -/
def E1 (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 1) * (X + 3)

/-- Squareclass representatives supported only at primes `2` and `3`, including sign. -/
def S23 : List ℤ := [1, -1, 2, -2, 3, -3, 6, -6]

def InS23 (d : ℤ) : Prop := d ∈ S23

/-- `q = d*r^2`, with the square factor nonzero. -/
def SquareclassBy (q : ℚ) (d : ℤ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ q = (d : ℚ) * r ^ 2

/-- Valuation parity outside `{2,3}`.  This is the p-adic form of “squareclass
supported on 2 and 3”. -/
def EvenPadicOutside23 (q : ℚ) : Prop :=
  q ≠ 0 ∧
    ∀ p : ℕ, Fact p.Prime → p ≠ 2 → p ≠ 3 → Even (padicValRat p q)

/-- Representative form of the same squareclass support. -/
def SquareclassSupportedOn23 (q : ℚ) : Prop :=
  q ≠ 0 ∧ ∃ d : ℤ, InS23 d ∧ SquareclassBy q d

/-- Product-square condition, avoiding quotient groups. -/
def ProductSquareclassCondition (d0 d1 d3 : ℤ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ ((d0 * d1 * d3 : ℤ) : ℚ) = r ^ 2

/-- Rational cover equations before integer denominator clearing. -/
def CoverQ (d0 d1 d3 : ℤ) (A B C T : ℚ) : Prop :=
  (d0 : ℚ) * A ^ 2 - (d1 : ℚ) * B ^ 2 = T ^ 2 ∧
    (d3 : ℚ) * C ^ 2 - (d0 : ℚ) * A ^ 2 = (3 : ℚ) * T ^ 2

/-- Integer cover equations after clearing a common denominator. -/
def CoverInt (d0 d1 d3 A B C T : ℤ) : Prop :=
  d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
    d3 * C ^ 2 - d0 * A ^ 2 = (3 : ℤ) * T ^ 2

/-- Primitive projective condition over integers. -/
def PrimitiveInt4 (A B C T : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ¬ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ B ∧ (p : ℤ) ∣ C ∧ (p : ℤ) ∣ T)

/-- Final integer full-cover data consumed by the local obstruction table. -/
def E1FullCoverIntData (X Y : ℚ) : Prop :=
  ∃ d0 d1 d3 : ℤ,
    InS23 d0 ∧ InS23 d1 ∧ InS23 d3 ∧
    ProductSquareclassCondition d0 d1 d3 ∧
    ∃ A B C T : ℤ,
      T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
      PrimitiveInt4 A B C T ∧
      X = (d0 : ℚ) * (((A : ℚ) / (T : ℚ)) ^ 2) ∧
      X - 1 = (d1 : ℚ) * (((B : ℚ) / (T : ℚ)) ^ 2) ∧
      X + 3 = (d3 : ℚ) * (((C : ℚ) / (T : ℚ)) ^ 2) ∧
      CoverInt d0 d1 d3 A B C T

end MazurProof.RationalPointsN12
```

## Recommended residual split

Use these as named residuals instead of one opaque theorem.  This keeps the genuinely hard arithmetic visible.

```lean
namespace MazurProof.RationalPointsN12

/-- Hard p-adic/gcd layer: the three E1 factors have even valuation outside
`2,3`. -/
def E1FactorEvenPadicOutside23Statement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    EvenPadicOutside23 X ∧
      EvenPadicOutside23 (X - 1) ∧
        EvenPadicOutside23 (X + 3)

/-- UFD/squarefree extraction layer: even outside valuations imply one of the
8 representatives `{±1,±2,±3,±6}` times a rational square. -/
def SquareclassSupportedOn23_of_evenPadicOutside23_statement : Prop :=
  ∀ {q : ℚ}, EvenPadicOutside23 q → SquareclassSupportedOn23 q

/-- Algebraic denominator-clearing layer: three supported squareclasses coming
from an E1 point give primitive integer full-cover data. -/
def E1FullCoverIntData_of_factor_squareclasses_statement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 →
    SquareclassSupportedOn23 X →
    SquareclassSupportedOn23 (X - 1) →
    SquareclassSupportedOn23 (X + 3) →
    E1FullCoverIntData X Y

/-- Final target assembled from the three smaller residuals. -/
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y

/-- This wrapper is real proof plumbing, not a residual. -/
theorem e1_full_cover_extraction_from_split_residuals
    (hval : E1FactorEvenPadicOutside23Statement)
    (hsq : SquareclassSupportedOn23_of_evenPadicOutside23_statement)
    (hclear : E1FullCoverIntData_of_factor_squareclasses_statement) :
    E1FullCoverSquareclassExtractionIntStatement := by
  intro X Y hE hY
  rcases hval hE hY with ⟨hX, hXm1, hXp3⟩
  exact hclear hE hY (hsq hX) (hsq hXm1) (hsq hXp3)

end MazurProof.RationalPointsN12
```

This theorem should compile once the definitions are in scope; it contains no number theory.

## Layer 1 plan: valuation parity from `E1`

Normalize `X` with Mathlib's reduced rational representation:

```lean
let N : ℤ := X.num
let D : ℕ := X.den
have hXrep : (X.num /. X.den) = X := X.num_divInt_den
have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast X.den_ne_zero
have hN0 : N ≠ 0 := Rat.num_ne_zero.2 hX_nonzero
```

For the shifted factors, use denominator stability:

```lean
#check Rat.sub_intCast_den   -- (X - n).den = X.den
#check Rat.add_intCast_den   -- (X + n).den = X.den
```

The numerators should be related to `N - D` and `N + 3*D` either by direct `Rat.num_den_mk` or by `padicValRat.defn` on explicit presentations:

```lean
have hXm1_rep : X - 1 = (N - (D : ℤ)) /. (D : ℤ) := by
  -- derive from `X.num_divInt_den`; `ring_nf` or `norm_num [Rat.sub_def]` may help.
  -- This is algebraic.
  ...

have hXp3_rep : X + 3 = (N + 3 * (D : ℤ)) /. (D : ℤ) := by
  -- same pattern.
  ...
```

Then for each prime `p` with `[Fact p.Prime]`, `p ≠ 2`, `p ≠ 3`, prove:

```lean
Even (padicValRat p X)
Even (padicValRat p (X - 1))
Even (padicValRat p (X + 3))
```

Use:

```lean
padicValRat.pow Y        -- valuation of Y^2 is even
padicValRat.mul          -- valuation of product of nonzero factors
padicValRat.defn p hq h_rep
```

The exact arithmetic argument is:

1. From `Y^2 = X*(X-1)*(X+3)` and nonzero factors,
   ```text
   2*v(Y) = v(X) + v(X-1) + v(X+3).
   ```
2. With `X=N/D`, the three numerators are `N`, `N-D`, `N+3D`, common denominator `D`.
3. GCD facts:
   ```text
   gcd(N,D)=1
   gcd(N-D,D)=1
   gcd(N+3D,D)=1
   gcd(N,N-D)=1
   gcd(N,N+3D) ∣ 3
   gcd(N-D,N+3D) ∣ 4
   ```
4. Therefore for `p ≠ 2,3`, the numerator valuations of `N`, `N-D`, `N+3D` are pairwise disjoint.  Also if `p ∣ D`, then it divides none of the three numerators.
5. If `p ∤ D`, at most one factor valuation can be nonzero, and the product valuation is even, so that factor valuation is even.
6. If `p ∣ D`, all three factor valuations are `-v_p(D)`.  Their sum is `-3*v_p(D)`, even, so `v_p(D)` is even, hence each factor valuation is even.

This layer is the best single “hard” residual if time is limited:

```lean
def E1FactorEvenPadicOutside23Statement : Prop := ...
```

## Layer 2 plan: from even valuations to `S23` representative

There are two Lean-realistic routes.

### Route A: `Rat.num`/`Rat.den` and integer squarefree kernels

For `q ≠ 0`, use `q.num` and `q.den`:

```lean
q = q.num /. q.den
```

The support statement says every prime outside `2,3` has even exponent in both numerator and denominator after cancellation.  Build the representative by parity of signs and the parities of `v₂(q)` and `v₃(q)`:

```text
d = sign(q) * 2^(v₂(q) mod 2) * 3^(v₃(q) mod 2)
```

Then prove `d ∈ S23` by finite case split and prove `q/d` is a rational square using UFD/multiplicity parity.

Likely APIs:

```lean
multiplicity
FiniteMultiplicity
multiplicity_mul
Int.finiteMultiplicity_iff
Nat.prime_iff_prime_int
Squarefree
Associated
UniqueFactorizationMonoid
```

This is a medium residual if not already in the project.

### Route B: make squareclass extraction itself the residual

Use the narrow statement:

```lean
def SquareclassSupportedOn23_of_evenPadicOutside23_statement : Prop :=
  ∀ {q : ℚ}, EvenPadicOutside23 q → SquareclassSupportedOn23 q
```

This is clean, non-circular, and independent of E1.

## Layer 3 plan: algebraic clearing to primitive integer cover data

Assume:

```text
X     = d0*r0^2
X - 1 = d1*r1^2
X + 3 = d3*r3^2
```

with `r0,r1,r3 ≠ 0` and `d0,d1,d3 ∈ S23`.

Product-square condition is immediate from E1:

```text
Y^2 = d0*d1*d3*(r0*r1*r3)^2
```

so

```text
d0*d1*d3 = (Y/(r0*r1*r3))^2.
```

Choose common denominator

```text
T0 = r0.den * r1.den * r3.den
A0 = r0.num * (T0 / r0.den)
B0 = r1.num * (T0 / r1.den)
C0 = r3.num * (T0 / r3.den)
```

or use a lcm version.  Product is simpler to prove because `rᵢ.den ∣ T0` is immediate.  Then:

```text
r0 = A0/T0, r1 = B0/T0, r3 = C0/T0.
```

Subtract identities and clear `T0^2`:

```text
d0*A0^2 - d1*B0^2 = T0^2
d3*C0^2 - d0*A0^2 = 3*T0^2
```

Finally primitive-normalize.  Let `g = gcd4(A0,B0,C0,T0)` and divide all four by `g`.  Since both cover equations are homogeneous degree 2, the equations survive.  Use a positive `Nat` gcd converted to `ℤ`, or an `Int.gcd` chain:

```lean
def gcd4 (A B C T : ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (Nat.gcd A.natAbs B.natAbs) C.natAbs) T.natAbs
```

The nonzero fields survive because `A0,B0,C0,T0` are nonzero and division is by a nonzero common divisor.  This is algebraic but a little lengthy; it should not be bundled with the valuation residual.

Recommended local residual boundary if primitive normalization becomes long:

```lean
def CommonDenomSquareclassRepsToPrimitiveCoverIntStatement : Prop :=
  ∀ {X Y : ℚ} {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ},
    E1 X Y → Y ≠ 0 →
    InS23 d0 → InS23 d1 → InS23 d3 →
    r0 ≠ 0 → r1 ≠ 0 → r3 ≠ 0 →
    X = (d0 : ℚ) * r0 ^ 2 →
    X - 1 = (d1 : ℚ) * r1 ^ 2 →
    X + 3 = (d3 : ℚ) * r3 ^ 2 →
    E1FullCoverIntData X Y
```

But I would try proving this one now; it is denominator algebra, not new mathematics.

## Minimal honest residual recommendation

For the N=12 route, the most honest split is:

```lean
E1FactorEvenPadicOutside23Statement
SquareclassSupportedOn23_of_evenPadicOutside23_statement
E1FullCoverIntData_of_factor_squareclasses_statement
```

The first is the genuinely E1-specific arithmetic/gcd proof.  The second is generic rational squareclass extraction and may be reusable elsewhere.  The third is cover-equation plumbing and should eventually be eliminated first.

If you need a single residual to unblock downstream finite obstruction assembly, use only:

```lean
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1 X Y → Y ≠ 0 → E1FullCoverIntData X Y
```

but keep the three-way split above in comments or adjacent declarations, so it is clear which part is hard and which part is algebraic.
