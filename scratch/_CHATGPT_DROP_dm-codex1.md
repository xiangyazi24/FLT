# Q2663 (dm-codex1): primitive quartic → non-unit Eisenstein parametrization interface

Repo/branch requested: `xiangyazi24/FLT@scratch`  
Target Lean area: `FLT/Assumptions/MazurProof/N12QuarticEisenstein.lean`  
Namespace assumed from prompt: `MazurProof.RationalPointsN12`

## Verdict

The unit branch of the primitive Eisenstein triple parametrization is safe: for the quartic use

```text
X = A^2,  Y = N^2,  Z = |S|,
Z^2 = X^2 - X*Y + Y^2.
```

The exceptional primitive triple `(X,Y,Z) = (1,1,1)` implies `A^2 = N^2`, exactly the degenerate conclusion, so a primitive bad quartic solution always enters the **non-unit** parametrization branch.

The non-unit parametrization gives very concrete square-side factor equations, but I do **not** know a verified closed-form smaller quartic triple `(A',N',S')` that follows immediately from those equations. The tempting step “each factor is a square, therefore descend” is false without parity/gcd splitting; after the split one obtains simultaneous Pythagorean/Pell-type constraints, not an automatic new quartic solution. The honest Lean boundary should isolate this remaining descent as a small integer-algebra theorem, not hide it in the parametrization theorem.

---

## 1. Normalized bad solution

Use signs and symmetry to reduce every bad solution to positive ordered coordinates.

```lean
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import FLT.Assumptions.MazurProof.N12QuarticEisenstein

namespace MazurProof.RationalPointsN12

/-- Positive ordered primitive non-degenerate quartic counterexample. -/
def NormalizedEisensteinQuarticBad (A N S : ℤ) : Prop :=
  0 < A ∧ 0 < N ∧ A < N ∧ 0 < S ∧
  IsCoprime A N ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

end MazurProof.RationalPointsN12
```

Recommended wrappers:

```lean
namespace MazurProof.RationalPointsN12

/-- Absolute values and, if necessary, swapping `A,N` normalize a bad solution. -/
theorem normalized_bad_of_bad {A N S : ℤ}
    (h : EisensteinQuarticBad A N S) :
    ∃ A0 N0 S0 : ℤ, NormalizedEisensteinQuarticBad A0 N0 S0 := by
  -- Implementation plan:
  -- * set a = |A|, n = |N|, z = |S|;
  -- * use equation invariance under signs;
  -- * bad gives a ≠ 0, n ≠ 0, a^2 ≠ n^2, hence a ≠ n;
  -- * if a < n keep `(a,n,z)`, otherwise use symmetry and take `(n,a,z)`;
  -- * `z > 0` follows from
  --   `A^4 - A^2*N^2 + N^4 = (A^2 - N^2)^2 + A^2*N^2 > 0`.
  sorry

/-- It suffices to rule out normalized bad solutions. -/
theorem no_bad_of_no_normalized_bad
    (hNo : ∀ {A N S : ℤ}, NormalizedEisensteinQuarticBad A N S → False) :
    ∀ {A N S : ℤ}, EisensteinQuarticBad A N S → False := by
  intro A N S hbad
  rcases normalized_bad_of_bad hbad with ⟨A0, N0, S0, hnorm⟩
  exact hNo hnorm

/-- Final primitive theorem from absence of bad solutions. -/
theorem intQuarticEisensteinPrimitive_of_no_bad
    (hNo : ∀ {A N S : ℤ}, EisensteinQuarticBad A N S → False) :
    IntQuarticEisensteinPrimitive := by
  intro A N S hcop hN hEq
  by_cases hA : A = 0
  · exact Or.inl hA
  by_cases hdeg : A ^ 2 = N ^ 2
  · exact Or.inr hdeg
  exfalso
  exact hNo ⟨hcop, hA, hN, hdeg, hEq⟩

end MazurProof.RationalPointsN12
```

The two `sorry`s above are intended theorem skeletons. The actual proof of `normalized_bad_of_bad` is local algebra/order over `ℤ`; it does not need any elliptic curve or full-cover result.

### Parity and mod-3 facts to prove immediately

For normalized bad `(A,N,S)`:

```lean
namespace MazurProof.RationalPointsN12

/-- Quartic as an Eisenstein-conic equation for square sides. -/
theorem quartic_as_eisenstein_conic {A N S : ℤ}
    (h : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
    S ^ 2 = (A ^ 2) ^ 2 - (A ^ 2) * (N ^ 2) + (N ^ 2) ^ 2 := by
  -- `ring_nf` after rewriting `h`.
  sorry

/-- Quartic as a primitive Pythagorean triple. Useful for parity checks. -/
theorem quartic_as_pythagorean {A N S : ℤ}
    (h : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
    S ^ 2 = (A ^ 2 - N ^ 2) ^ 2 + (A * N) ^ 2 := by
  -- `ring_nf` after rewriting `h`.
  sorry

/-- `S` is odd in every primitive solution. -/
theorem normalized_bad_odd_S {A N S : ℤ}
    (h : NormalizedEisensteinQuarticBad A N S) : Odd S := by
  -- Since `IsCoprime A N`, not both `A,N` are even.
  -- Mod 2: `A^4 - A^2*N^2 + N^4 ≡ 1` in all allowed parity cases.
  sorry

/-- If exactly one of `A,N` is even, the even one is divisible by 4. -/
theorem normalized_bad_even_coord_divisible_by_four {A N S : ℤ}
    (h : NormalizedEisensteinQuarticBad A N S) :
    (Even A ∧ Odd N → (4 : ℤ) ∣ A) ∧
    (Odd A ∧ Even N → (4 : ℤ) ∣ N) := by
  -- Mod 16: if the even coordinate is `2 mod 4`, then
  -- RHS is `13 mod 16`, not a square.
  sorry

/-- The ramified prime over 3 is absent for primitive square sides. -/
theorem normalized_bad_not_three_dvd_S {A N S : ℤ}
    (h : NormalizedEisensteinQuarticBad A N S) : ¬ (3 : ℤ) ∣ S := by
  -- Squares mod 3 are 0 or 1; `IsCoprime A N` prevents both 0.
  -- Hence `A^4 - A^2*N^2 + N^4 ≡ 1 mod 3`.
  sorry

/-- Also `3 ∤ A^2 + N^2`; useful for the Eisenstein gcd/conjugate step. -/
theorem normalized_bad_not_three_dvd_square_sum {A N S : ℤ}
    (h : NormalizedEisensteinQuarticBad A N S) :
    ¬ (3 : ℤ) ∣ A ^ 2 + N ^ 2 := by
  -- Squares mod 3 and coprimality: possible pairs are `(1,0)`, `(0,1)`, `(1,1)`,
  -- giving sums `1,1,2`, never `0`.
  sorry

end MazurProof.RationalPointsN12
```

---

## 2. Positive primitive Eisenstein triple and unit branch

Define a minimal triple predicate. This is just the conic, not the hard theorem.

```lean
namespace MazurProof.RationalPointsN12

/-- Positive primitive integral solution of `Z^2 = X^2 - X*Y + Y^2`. -/
def PositivePrimitiveEisensteinTriple (X Y Z : ℤ) : Prop :=
  0 < X ∧ 0 < Y ∧ 0 < Z ∧ IsCoprime X Y ∧
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2

/-- A normalized quartic bad solution gives a positive primitive Eisenstein triple. -/
theorem eisensteinTriple_of_normalized_bad {A N S : ℤ}
    (h : NormalizedEisensteinQuarticBad A N S) :
    PositivePrimitiveEisensteinTriple (A ^ 2) (N ^ 2) S := by
  -- Positivity: from `0 < A`, `0 < N`, `0 < S`.
  -- Primitive: `IsCoprime A N` implies `IsCoprime (A^2) (N^2)`.
  -- Equation: `quartic_as_eisenstein_conic h.eq`.
  sorry

/-- The parametrization's unit exception is exactly degenerate for square sides. -/
theorem unit_branch_degenerate_for_square_sides {A N S : ℤ}
    (hX : A ^ 2 = 1) (hY : N ^ 2 = 1) :
    A ^ 2 = N ^ 2 := by
  exact hX.trans hY.symm

/-- Therefore a normalized bad solution cannot be in the unit branch `(1,1,1)`. -/
theorem normalized_bad_not_unit_branch {A N S : ℤ}
    (h : NormalizedEisensteinQuarticBad A N S) :
    ¬ (A ^ 2 = 1 ∧ N ^ 2 = 1 ∧ S = 1) := by
  intro hu
  have hdeg : A ^ 2 = N ^ 2 := unit_branch_degenerate_for_square_sides hu.1 hu.2.1
  have hlt : A ^ 2 < N ^ 2 := by
    -- from `0 < A`, `A < N`.
    sorry
  exact (ne_of_lt hlt) hdeg

end MazurProof.RationalPointsN12
```

The only nontrivial local lemma above is monotonicity of square on positive integers.

---

## 3. Corrected non-unit Eisenstein parametrization and square-side equations

A Lean-friendly parametrization should **not** silently choose one unit associate. Use a unit branch plus three positive non-unit branches.

For `q = m^2 - n^2`, `r = 2*m*n - n^2`, `z = m^2 - m*n + n^2`, the square in `ℤ[ω]` gives `(q,r,z)`. Multiplication by units yields the positive associate branches:

```lean
namespace MazurProof.RationalPointsN12

/-- First positive associate of an Eisenstein square. -/
def EisensteinParamBranch0 (X Y Z m n : ℤ) : Prop :=
  IsCoprime m n ∧
  X = m ^ 2 - n ^ 2 ∧
  Y = 2 * m * n - n ^ 2 ∧
  Z = m ^ 2 - m * n + n ^ 2

/-- Second positive associate. -/
def EisensteinParamBranch1 (X Y Z m n : ℤ) : Prop :=
  IsCoprime m n ∧
  X = 2 * m * n - n ^ 2 ∧
  Y = 2 * m * n - m ^ 2 ∧
  Z = m ^ 2 - m * n + n ^ 2

/-- Third positive associate. -/
def EisensteinParamBranch2 (X Y Z m n : ℤ) : Prop :=
  IsCoprime m n ∧
  X = m ^ 2 - 2 * m * n ∧
  Y = m ^ 2 - n ^ 2 ∧
  Z = m ^ 2 - m * n + n ^ 2

/-- Non-unit parametrization branch for a positive primitive Eisenstein triple. -/
def NonunitEisensteinParam (X Y Z m n : ℤ) : Prop :=
  EisensteinParamBranch0 X Y Z m n ∨
  EisensteinParamBranch1 X Y Z m n ∨
  EisensteinParamBranch2 X Y Z m n

/-- Shape of the corrected parametrization theorem: unit branch or non-unit branch. -/
def EisensteinTripleParamTheorem : Prop :=
  ∀ {X Y Z : ℤ},
    PositivePrimitiveEisensteinTriple X Y Z →
    (X = 1 ∧ Y = 1 ∧ Z = 1) ∨
      ∃ m n : ℤ, NonunitEisensteinParam X Y Z m n

end MazurProof.RationalPointsN12
```

Given `X=A^2`, `Y=N^2`, `Z=S`, the branch equations are:

### Branch 0

```text
A^2 = m^2 - n^2 = (m-n)(m+n)
N^2 = 2mn - n^2 = n(2m-n)
S   = m^2 - mn + n^2
```

### Branch 1

```text
A^2 = 2mn - n^2 = n(2m-n)
N^2 = 2mn - m^2 = m(2n-m)
S   = m^2 - mn + n^2
```

### Branch 2

```text
A^2 = m^2 - 2mn = m(m-2n)
N^2 = m^2 - n^2 = (m-n)(m+n)
S   = m^2 - mn + n^2
```

Lean wrappers:

```lean
namespace MazurProof.RationalPointsN12

theorem branch0_square_side_factors {A N S m n : ℤ}
    (hp : EisensteinParamBranch0 (A ^ 2) (N ^ 2) S m n) :
    A ^ 2 = (m - n) * (m + n) ∧
    N ^ 2 = n * (2 * m - n) ∧
    S = m ^ 2 - m * n + n ^ 2 := by
  -- `rcases hp with ⟨hcop, hX, hY, hZ⟩`; `ring_nf`.
  sorry

theorem branch1_square_side_factors {A N S m n : ℤ}
    (hp : EisensteinParamBranch1 (A ^ 2) (N ^ 2) S m n) :
    A ^ 2 = n * (2 * m - n) ∧
    N ^ 2 = m * (2 * n - m) ∧
    S = m ^ 2 - m * n + n ^ 2 := by
  sorry

theorem branch2_square_side_factors {A N S m n : ℤ}
    (hp : EisensteinParamBranch2 (A ^ 2) (N ^ 2) S m n) :
    A ^ 2 = m * (m - 2 * n) ∧
    N ^ 2 = (m - n) * (m + n) ∧
    S = m ^ 2 - m * n + n ^ 2 := by
  sorry

end MazurProof.RationalPointsN12
```

### GCD facts needed for factor extraction

For `IsCoprime m n`:

```text
gcd(m-n, m+n) ∣ 2
gcd(n, 2m-n) = gcd(n, 2)
gcd(m, 2n-m) = gcd(m, 2)
gcd(m, m-2n) = gcd(m, 2)
```

Lean theorem shapes:

```lean
namespace MazurProof.RationalPointsN12

theorem gcd_sub_add_dvd_two {m n : ℤ} (hcop : IsCoprime m n) :
    ∀ d : ℤ, d ∣ m - n → d ∣ m + n → d ∣ (2 : ℤ) := by
  -- `d ∣ (m+n)+(m-n)=2m` and `d ∣ (m+n)-(m-n)=2n`;
  -- combine with `IsCoprime m n`.
  sorry

theorem gcd_n_two_mul_sub_dvd_two {m n : ℤ} (hcop : IsCoprime m n) :
    ∀ d : ℤ, d ∣ n → d ∣ 2 * m - n → d ∣ (2 : ℤ) := by
  -- `d ∣ 2*m`; coprimality with `n` leaves only factor `2`.
  sorry

theorem gcd_m_two_mul_sub_dvd_two {m n : ℤ} (hcop : IsCoprime m n) :
    ∀ d : ℤ, d ∣ m → d ∣ 2 * n - m → d ∣ (2 : ℤ) := by
  sorry

theorem gcd_m_sub_two_mul_dvd_two {m n : ℤ} (hcop : IsCoprime m n) :
    ∀ d : ℤ, d ∣ m → d ∣ m - 2 * n → d ∣ (2 : ℤ) := by
  sorry

end MazurProof.RationalPointsN12
```

### Square-up-to-2 extraction lemmas

These are reusable and independent of Eisenstein integers.

```lean
namespace MazurProof.RationalPointsN12

/-- Coprime positive factors whose product is a square are squares. -/
theorem coprime_factors_of_square {u v a : ℤ}
    (hu : 0 < u) (hv : 0 < v)
    (hcop : IsCoprime u v)
    (hmul : u * v = a ^ 2) :
    ∃ r s : ℤ, 0 ≤ r ∧ 0 ≤ s ∧ u = r ^ 2 ∧ v = s ^ 2 ∧ a ^ 2 = (r * s) ^ 2 := by
  -- Best proved via `Int.factorization`/unique factorization, or move to `ℕ`.
  sorry

/-- Even factors with only common divisor 2 whose product is a square are twice squares. -/
theorem two_coprime_factors_of_square {u v a : ℤ}
    (hu : 0 < u) (hv : 0 < v)
    (hu2 : (2 : ℤ) ∣ u) (hv2 : (2 : ℤ) ∣ v)
    (hcommon : ∀ d : ℤ, d ∣ u → d ∣ v → d ∣ (2 : ℤ))
    (hmul : u * v = a ^ 2) :
    ∃ r s : ℤ, 0 ≤ r ∧ 0 ≤ s ∧ u = 2 * r ^ 2 ∧ v = 2 * s ^ 2 ∧ a ^ 2 = (2 * r * s) ^ 2 := by
  -- Divide both factors by 2, prove the quotients are coprime, then use
  -- `coprime_factors_of_square` on `u/2 * v/2 = (a/2)^2`.
  sorry

end MazurProof.RationalPointsN12
```

### Parity split example: branch 0

Branch 0 already illustrates why there is no immediate one-line descent.

If `m,n` are both odd, then `(m-n)` and `(m+n)` are even with common divisor exactly `2`, while `n` and `2m-n` are odd and coprime. The square-side equations become

```text
m - n = 2*a^2
m + n = 2*b^2
n     = c^2
2m-n = d^2
A     = ± 2ab
N     = ± cd
```

Algebraically:

```text
m = a^2 + b^2
n = b^2 - a^2 = c^2
d^2 = 2m - n = 3a^2 + b^2
```

Equivalently, using `b^2 = a^2 + c^2`,

```text
b^2 = a^2 + c^2
d^2 = 4a^2 + c^2.
```

This is a simultaneous Pythagorean/Pell-type system. It is useful, but it is **not** yet a smaller quartic solution.

If `m` is odd and `n` is even, then `(m-n)` and `(m+n)` are odd and coprime, while `n` and `2m-n` are even with common divisor `2`. The equations become

```text
m - n = a^2
m + n = b^2
n     = 2*c^2
2m-n = 2*d^2
A     = ± ab
N     = ± 2cd
```

Then

```text
b^2 - a^2 = 4c^2
d^2 = a^2 + c^2.
```

If `m` is even and `n` is odd`, all four factors in branch 0 are odd. Then the equations would force

```text
m - n = a^2
m + n = b^2
n     = c^2
2m-n = d^2
```

and hence `b^2 - a^2 = 2c^2`. Here `a,b,c` are odd, so the left side is `0 mod 8` while the right side is `2 mod 8`; contradiction. This is a good Lean lemma.

Analogous tables should be generated for branches 1 and 2 by the same `gcd ∣ 2` lemmas.

### 3-divisibility after parametrization

Since `S = m^2 - mn + n^2` in every branch and normalized bad gives `3 ∤ S`, prove:

```lean
namespace MazurProof.RationalPointsN12

/-- For coprime `m,n`, the Eisenstein norm is divisible by 3 iff `m+n` is. -/
theorem three_dvd_eisenstein_norm_iff {m n : ℤ} (hcop : IsCoprime m n) :
    ((3 : ℤ) ∣ m ^ 2 - m * n + n ^ 2) ↔ (3 : ℤ) ∣ m + n := by
  -- Work modulo 3; coprimality excludes `m ≡ n ≡ 0`.
  sorry

/-- In a non-unit parametrization from a normalized bad solution, `3 ∤ m+n`. -/
theorem normalized_bad_param_not_three_dvd_m_add_n {A N S m n : ℤ}
    (hbad : NormalizedEisensteinQuarticBad A N S)
    (hp : NonunitEisensteinParam (A ^ 2) (N ^ 2) S m n) :
    ¬ (3 : ℤ) ∣ m + n := by
  -- Use `S = m^2 - mn + n^2` from any branch, then
  -- `normalized_bad_not_three_dvd_S` and `three_dvd_eisenstein_norm_iff`.
  sorry

end MazurProof.RationalPointsN12
```

---

## 4. Smaller quartic solution formulas: status and honest residual boundary

I do **not** have a verified formula

```text
(A,N,S,m,n) ↦ (A',N',S')
```

that can be safely committed as the classical descent step from the square-side equations above.

The concrete obstruction is that the corrected parametrization gives products such as

```text
A^2 = (m-n)(m+n),   N^2 = n(2m-n),
```

but the gcds are only controlled up to `2`, and unit associates move the products among three branches. After parity splitting, one gets systems like

```text
b^2 = a^2 + c^2,
d^2 = 4a^2 + c^2,
```

or

```text
b^2 - a^2 = 4c^2,
d^2 = a^2 + c^2,
```

not an immediate new solution of

```text
S'^2 = A'^4 - A'^2*N'^2 + N'^4.
```

Therefore the smallest honest residual theorem is the square-parametrization descent step:

```lean
namespace MazurProof.RationalPointsN12

/-- The remaining independent descent theorem.

It starts only after:
* quartic bad solution has been normalized;
* square sides have been converted to a positive primitive Eisenstein triple;
* the unit branch has been eliminated;
* a non-unit parametrization has been obtained.

This theorem must be proved by elementary integer algebra/number theory only.
It must not import `RationalPointsN12`, E1/E24 finite-point theorems, or full-cover residuals.
-/
def EisensteinSquareParamDescent : Prop :=
  ∀ {A N S m n : ℤ},
    NormalizedEisensteinQuarticBad A N S →
    NonunitEisensteinParam (A ^ 2) (N ^ 2) S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinQuarticBad A' N' S' ∧
      Int.natAbs N' < Int.natAbs N

/-- Less constructive but smaller boundary: no non-unit square-side parametrization exists. -/
def EisensteinParamSquaresImpossible : Prop :=
  ∀ {A N S m n : ℤ},
    NormalizedEisensteinQuarticBad A N S →
    NonunitEisensteinParam (A ^ 2) (N ^ 2) S m n → False

end MazurProof.RationalPointsN12
```

`EisensteinParamSquaresImpossible` is almost the original theorem after parametrization, so it is less illuminating. `EisensteinSquareParamDescent` is better because it gives a well-founded proof by descending on `N`.

---

## 5. Wrappers provable now, assuming only parametrization plus residual descent

```lean
namespace MazurProof.RationalPointsN12

/-- Parametrization plus unit elimination gives a non-unit parametrization. -/
theorem nonunit_param_of_normalized_bad
    (hParam : EisensteinTripleParamTheorem)
    {A N S : ℤ}
    (hbad : NormalizedEisensteinQuarticBad A N S) :
    ∃ m n : ℤ, NonunitEisensteinParam (A ^ 2) (N ^ 2) S m n := by
  have htri : PositivePrimitiveEisensteinTriple (A ^ 2) (N ^ 2) S :=
    eisensteinTriple_of_normalized_bad hbad
  rcases hParam htri with hunit | hnonunit
  · exfalso
    exact normalized_bad_not_unit_branch hbad hunit
  · exact hnonunit

/-- Descent eliminates normalized bad solutions. -/
theorem no_normalized_bad_of_param_descent
    (hParam : EisensteinTripleParamTheorem)
    (hDesc : EisensteinSquareParamDescent) :
    ∀ {A N S : ℤ}, NormalizedEisensteinQuarticBad A N S → False := by
  -- Use well-founded induction on `Int.natAbs N`.
  -- For a normalized bad `(A,N,S)`, get `m,n` from `nonunit_param_of_normalized_bad`.
  -- Apply `hDesc` to get normalized bad `(A',N',S')` with `natAbs N' < natAbs N`.
  -- Contradict the induction hypothesis.
  intro A N S hbad
  classical
  -- Suggested implementation shape:
  --   refine Nat.lt_wfRel.wf.induction (a := Int.natAbs N) ?step ?
  -- It may be cleaner to state an auxiliary theorem by induction on `k`:
  --   `∀ k, (∀ bad with natAbs N < k, False) → ...`
  sorry

/-- Final theorem from corrected Eisenstein parametrization and square-param descent. -/
theorem intQuarticEisensteinPrimitive_of_eisenstein_square_param_descent
    (hParam : EisensteinTripleParamTheorem)
    (hDesc : EisensteinSquareParamDescent) :
    IntQuarticEisensteinPrimitive := by
  apply intQuarticEisensteinPrimitive_of_no_bad
  apply no_bad_of_no_normalized_bad
  exact no_normalized_bad_of_param_descent hParam hDesc

/-- Alternative final theorem if the residual is the direct impossibility boundary. -/
theorem intQuarticEisensteinPrimitive_of_param_squares_impossible
    (hParam : EisensteinTripleParamTheorem)
    (hImpossible : EisensteinParamSquaresImpossible) :
    IntQuarticEisensteinPrimitive := by
  apply intQuarticEisensteinPrimitive_of_no_bad
  apply no_bad_of_no_normalized_bad
  intro A N S hbad
  rcases nonunit_param_of_normalized_bad hParam hbad with ⟨m, n, hp⟩
  exact hImpossible hbad hp

end MazurProof.RationalPointsN12
```

---

## Implementation priorities

1. Prove normalization and the `PositivePrimitiveEisensteinTriple` wrapper.
2. Implement or import the primitive Eisenstein triple parametrization with an explicit unit branch and three unit-associate non-unit branches.
3. Prove `normalized_bad_not_unit_branch`; this closes the Q2659 unit-exception issue.
4. Add the branch factor equations and the gcd/2/parity/3 lemmas.
5. Leave exactly one named residual boundary, preferably `EisensteinSquareParamDescent`, until the explicit smaller-solution formulas are verified.

## False steps to avoid

* Do not assume the parametrization has only one branch; unit associates matter.
* Do not treat the unit exception as a bad solution; for square sides it implies `A^2=N^2`.
* Do not conclude `(m-n)`, `(m+n)`, `n`, and `(2m-n)` are all squares without checking parity and common divisor `2`.
* Do not claim a smaller quartic solution from the systems `b^2=a^2+c^2`, `d^2=4a^2+c^2` unless the actual formulas for `(A',N',S')` and the strict measure decrease are written and algebraically checked.
* Do not use `RationalPointsN12`, E1/E24 finite-point theorems, or full-cover residuals in any file proving `EisensteinTripleParamTheorem`, the factor lemmas, or `EisensteinSquareParamDescent`.
