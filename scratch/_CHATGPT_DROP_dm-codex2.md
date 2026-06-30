# Q2418 (dm-codex2): EulerAux descent step DAG

## Core descent formula

Normalize first to positive data

```text
A0 = |A|,    D0 = |D|,    S0 = |S|,    R0 = |R|.
```

Then

```text
S0^2 = (2*A0)^2 + D0^2,
R0^2 = (4*A0)^2 + D0^2,
gcd(A0,D0)=1,
D0 odd,
A0 ≠ 0, D0 ≠ 0.
```

From `S0^2 = (2*A0)^2 + D0^2`, primitive Pythagorean classification gives coprime parameters `U,V` with

```text
U*V = A0,
U^2 - V^2 = ε*D0,     ε ∈ {1,-1},
U even, V odd.
```

The choice `U even, V odd` is deliberate.  If Mathlib returns the even parameter second, swap the names and absorb the sign into `ε`.

From `R0^2 = (4*A0)^2 + D0^2`, primitive classification gives coprime parameters `U',V'` with

```text
U'*V' = A0,
4*U'^2 - V'^2 = η*D0,     η ∈ {1,-1},
U' even, V' odd.
```

Here `2*U'` is the even Pythagorean parameter for the second triangle, because

```text
4*A0 = 2*(2*U')*V'.
```

This is the main place where an off-by-two error can enter.

Since both

```text
U^2 - V^2        ≡ -1 mod 4,
4*U'^2 - V'^2   ≡ -1 mod 4,
```

and `D0` is odd, the signs are equal: `ε = η`.  Then the two factorizations `U*V = U'*V' = A0`, with `U,U'` even and `V,V'` odd, refine to pairwise coprime integers `2a,b,c,d` such that

```text
U  = 2*a*b,     V  = c*d,
U' = 2*a*c,     V' = b*d,
A0 = 2*a*b*c*d,
```

with `a,b,c,d` nonzero and `b,c,d` odd.  Substituting gives

```text
ε*D0 = 4*a^2*b^2 - c^2*d^2
ε*D0 = 16*a^2*c^2 - b^2*d^2.
```

Subtracting yields

```text
b^2 * (4*a^2 + d^2) = c^2 * (16*a^2 + d^2).      (★)
```

The two factors

```text
M = 4*a^2 + d^2,
N = 16*a^2 + d^2
```

are positive and coprime.  Any common prime divisor divides `N-M = 12*a^2`; since it also divides `M`, it cannot divide `a`, hence it divides `12`.  It is not `2` because `d` is odd, and it is not `3` because `a^2+d^2` is not `0 mod 3` when `gcd(a,d)=1`.  Thus `gcd(M,N)=1`.

From `(★)` and `gcd(M,N)=1`, the prime exponents of `M` and `N` are even, so both are squares.  Equivalently, use a dedicated lemma `coprime_ratio_square_imp_squares`.  Therefore there are `s,r` with

```text
s^2 = 4*a^2 + d^2,
r^2 = 16*a^2 + d^2.
```

Hence `(a,d)` is a new `EulerAux` solution.  The descent is strict because

```text
A0 = 2*a*b*c*d,    D0 ≥ 1,    |b| ≥ 1,    |c| ≥ 1,
```

so

```text
|a*d| < |A*D| = A0*D0.
```

## Hidden flaw in `U=2ab, V=cd, U'=2ac, V'=bd`

The formula is correct **only** with the following convention:

```text
first triple:   D = U^2 - V^2,       2A = 2UV,
second triple:  D = 4U'^2 - V'^2,    4A = 4U'V'.
```

Thus `2U'` is the actual even parameter in the second Pythagorean triple.  If one writes the second odd leg as `U'^2 - V'^2`, the formula is off by a factor of `4`.  The sign also cannot be ignored: one must prove the two signs agree, best by the mod-4 argument above.

## Lean theorem DAG

Use `Prop` wrappers first, then replace them by theorems as they are proved.  This avoids fake `sorry` scaffolding.

```lean
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Data.Int.Parity

namespace MazurProof.RationalPointsN12

/-- Local auxiliary condition for Euler/van der Poorten descent. -/
def EulerAux (A D : ℤ) : Prop :=
  A ≠ 0 ∧ D ≠ 0 ∧ Odd D ∧ Nat.Coprime A.natAbs D.natAbs ∧
    ∃ S R : ℤ, S ^ 2 = 4 * A ^ 2 + D ^ 2 ∧
      R ^ 2 = 16 * A ^ 2 + D ^ 2

/-- Pairwise coprimality for four integer parameters, stated on `natAbs`. -/
def PairwiseCoprime4 (w x y z : ℤ) : Prop :=
  Nat.Coprime w.natAbs x.natAbs ∧
  Nat.Coprime w.natAbs y.natAbs ∧
  Nat.Coprime w.natAbs z.natAbs ∧
  Nat.Coprime x.natAbs y.natAbs ∧
  Nat.Coprime x.natAbs z.natAbs ∧
  Nat.Coprime y.natAbs z.natAbs

/-- Normalized positive form extracted from `EulerAux A D`. -/
def EulerAuxPositiveData (A0 D0 S0 R0 : ℤ) : Prop :=
  0 < A0 ∧ 0 < D0 ∧ 0 < S0 ∧ 0 < R0 ∧ Odd D0 ∧
  Nat.Coprime A0.natAbs D0.natAbs ∧
  S0 ^ 2 = 4 * A0 ^ 2 + D0 ^ 2 ∧
  R0 ^ 2 = 16 * A0 ^ 2 + D0 ^ 2

/-- Algebraic normalization by absolute values. -/
def EulerAux_abs_normalize_statement : Prop :=
  ∀ {A D : ℤ}, EulerAux A D →
    ∃ A0 D0 S0 R0 : ℤ,
      EulerAuxPositiveData A0 D0 S0 R0 ∧
      A0 = (A.natAbs : ℤ) ∧ D0 = (D.natAbs : ℤ)

/-- `A0` is even.  This is a mod-8 consequence of
`S0^2 = 4*A0^2 + D0^2` and `D0` odd. -/
def EulerAuxPositiveData_even_A_statement : Prop :=
  ∀ {A0 D0 S0 R0 : ℤ}, EulerAuxPositiveData A0 D0 S0 R0 → Even A0

/-- First primitive Pythagorean parametrization, with the even parameter named
`U`.  The sign `eps` records whether the even square is larger than the odd
square. -/
def Euler_first_params_statement : Prop :=
  ∀ {A0 D0 S0 R0 : ℤ}, EulerAuxPositiveData A0 D0 S0 R0 → Even A0 →
    ∃ eps U V : ℤ,
      (eps = 1 ∨ eps = -1) ∧
      U ≠ 0 ∧ V ≠ 0 ∧ Even U ∧ Odd V ∧
      Nat.Coprime U.natAbs V.natAbs ∧
      U * V = A0 ∧
      U ^ 2 - V ^ 2 = eps * D0

/-- Second primitive Pythagorean parametrization.  Here `2*Up` is the even
Pythagorean parameter, so the odd leg is `4*Up^2 - Vp^2`. -/
def Euler_second_params_statement : Prop :=
  ∀ {A0 D0 S0 R0 : ℤ}, EulerAuxPositiveData A0 D0 S0 R0 → Even A0 →
    ∃ eta Up Vp : ℤ,
      (eta = 1 ∨ eta = -1) ∧
      Up ≠ 0 ∧ Vp ≠ 0 ∧ Even Up ∧ Odd Vp ∧
      Nat.Coprime Up.natAbs Vp.natAbs ∧
      Up * Vp = A0 ∧
      4 * Up ^ 2 - Vp ^ 2 = eta * D0

/-- The two signs in the first and second parametrizations agree.  The proof is
by reducing both displayed odd-leg formulas modulo `4`. -/
def Euler_param_signs_agree_statement : Prop :=
  ∀ {D0 eps eta U V Up Vp : ℤ},
    Odd D0 →
    (eps = 1 ∨ eps = -1) → (eta = 1 ∨ eta = -1) →
    Even U → Odd V → Odd Vp →
    U ^ 2 - V ^ 2 = eps * D0 →
    4 * Up ^ 2 - Vp ^ 2 = eta * D0 →
      eps = eta

/-- Refinement of the two coprime factorizations of the same even integer.
This is the factor-splitting lemma behind
`U=2ab, V=cd, Up=2ac, Vp=bd`. -/
def Euler_factor_refinement_statement : Prop :=
  ∀ {A0 U V Up Vp : ℤ},
    0 < A0 →
    U * V = A0 → Up * Vp = A0 →
    U ≠ 0 → V ≠ 0 → Up ≠ 0 → Vp ≠ 0 →
    Even U → Even Up → Odd V → Odd Vp →
    Nat.Coprime U.natAbs V.natAbs →
    Nat.Coprime Up.natAbs Vp.natAbs →
      ∃ a b c d : ℤ,
        a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
        Odd b ∧ Odd c ∧ Odd d ∧
        PairwiseCoprime4 (2 * a) b c d ∧
        U = 2 * a * b ∧ V = c * d ∧
        Up = 2 * a * c ∧ Vp = b * d ∧
        A0 = 2 * a * b * c * d

/-- The refined parameters give the two signed formulas for `D0`. -/
def Euler_refined_D_formulas_statement : Prop :=
  ∀ {D0 eps U V Up Vp a b c d : ℤ},
    U = 2 * a * b → V = c * d →
    Up = 2 * a * c → Vp = b * d →
    U ^ 2 - V ^ 2 = eps * D0 →
    4 * Up ^ 2 - Vp ^ 2 = eps * D0 →
      eps * D0 = 4 * a ^ 2 * b ^ 2 - c ^ 2 * d ^ 2 ∧
      eps * D0 = 16 * a ^ 2 * c ^ 2 - b ^ 2 * d ^ 2

/-- Coprimality of the two new Euler factors. -/
def Euler_new_factors_coprime_statement : Prop :=
  ∀ {a d : ℤ},
    a ≠ 0 → d ≠ 0 → Odd d → Nat.Coprime a.natAbs d.natAbs →
      Nat.Coprime (4 * a ^ 2 + d ^ 2).natAbs
        (16 * a ^ 2 + d ^ 2).natAbs

/-- From `b^2*M = c^2*N` with coprime positive `M,N`, conclude `M,N` are
squares.  This is the most reusable number-theoretic sublemma; it can be
proved by prime multiplicities, or by adapting `Int.sq_of_gcd_eq_one`. -/
def coprime_ratio_square_imp_squares_statement : Prop :=
  ∀ {b c M N : ℤ},
    b ≠ 0 → c ≠ 0 → 0 < M → 0 < N →
    Nat.Coprime M.natAbs N.natAbs →
    b ^ 2 * M = c ^ 2 * N →
      ∃ s r : ℤ, s ^ 2 = M ∧ r ^ 2 = N

/-- The actual local construction of the smaller EulerAux pair from refined
parameters.  The smaller pair is exactly `(a,d)`. -/
def Euler_refined_params_to_smaller_statement : Prop :=
  ∀ {A0 D0 eps a b c d : ℤ},
    0 < A0 → 0 < D0 →
    (eps = 1 ∨ eps = -1) →
    a ≠ 0 → b ≠ 0 → c ≠ 0 → d ≠ 0 →
    Odd d → PairwiseCoprime4 (2 * a) b c d →
    A0 = 2 * a * b * c * d →
    eps * D0 = 4 * a ^ 2 * b ^ 2 - c ^ 2 * d ^ 2 →
    eps * D0 = 16 * a ^ 2 * c ^ 2 - b ^ 2 * d ^ 2 →
      EulerAux a d ∧ (a * d).natAbs < (A0 * D0).natAbs

/-- Final descent statement, composed from the above lemmas. -/
def EulerAux_descent_step_statement : Prop :=
  ∀ {A D : ℤ}, EulerAux A D →
    ∃ a d : ℤ, EulerAux a d ∧ (a * d).natAbs < (A * D).natAbs

end MazurProof.RationalPointsN12
```

## Proof plan for the hard theorem

### 1. Normalize signs by absolute values

Prove `EulerAux_abs_normalize_statement` directly.  Replace witnesses `S,R` by `S.natAbs`, `R.natAbs`; use `Int.natAbs_mul_self` or `sq_abs`-style lemmas plus `ring_nf`.  The final descent bound is stated in `natAbs`, so no sign information is lost.

### 2. Prove `A0` even

Use the first square equation modulo `8`:

```text
D0 odd → D0^2 ≡ 1 mod 8.
A0 odd → 4*A0^2 ≡ 4 mod 8.
```

Then `S0^2 ≡ 5 mod 8`, impossible because integer squares modulo `8` are `0,1,4`.  This is a small finite `ZMod 8` lemma.

Suggested helper:

```lean
def sq_mod8_mem_statement : Prop :=
  ∀ z : ZMod 8, z ^ 2 = 0 ∨ z ^ 2 = 1 ∨ z ^ 2 = 4
```

This can be proved by `fin_cases z <;> decide`.

### 3. Pythagorean parametrizations

Use Mathlib’s `PythagoreanTriple` API:

```lean
#check PythagoreanTriple
#check PythagoreanTriple.coprime_classification
#check PythagoreanTriple.coprime_classification'
```

For the first triangle, build

```lean
have htri1 : PythagoreanTriple D0 (2*A0) S0 := by
  unfold PythagoreanTriple
  nlinarith [hS]
```

Use `PythagoreanTriple.coprime_classification'` with:

```text
gcd(D0, 2*A0)=1,
D0 % 2 = 1,
0 < S0.
```

The gcd follows from `Nat.Coprime A0.natAbs D0.natAbs` and `D0` odd.  If the classification returns `D0 = m^2-n^2`, `2*A0 = 2*m*n`, choose the even one among `m,n` as `U` and the odd one as `V`; if this swaps order, record the sign `eps=-1`.

For the second triangle, build

```lean
have htri2 : PythagoreanTriple D0 (4*A0) R0 := by
  unfold PythagoreanTriple
  nlinarith [hR]
```

Again classify.  Since `4*A0 = 2*m*n`, the even parameter is divisible by `2`; write it as `2*Up`, with the odd parameter `Vp`.  Then

```text
Up*Vp = A0,
4*Up^2 - Vp^2 = eta*D0.
```

This is a common place for a Lean proof to become long: isolate divisibility of the even parameter by `2` as a separate lemma, using `A0` even and the product equation.

### 4. Prove sign agreement

This is short and should not be residual.  From `Even U`, `Odd V`, and `Odd Vp`:

```text
U^2 - V^2 ≡ -1 mod 4,
4*Up^2 - Vp^2 ≡ -1 mod 4.
```

Both equal a sign times `D0`.  Since `D0` is odd, multiplication by `D0` distinguishes `1` from `-1` modulo `4`.  Therefore `eps=eta`.

### 5. Factor refinement

This is one of the hardest Lean lemmas, but it is pure arithmetic.  Work with positive natural absolute values if possible.

Constructive formulas:

```text
a = gcd(U/2, Up/2),
b = (U/2)/a,
c = (Up/2)/a,
d = V/c = Vp/b.
```

Then prove:

```text
U  = 2ab,
V  = cd,
Up = 2ac,
Vp = bd.
```

The proof uses:

```lean
Nat.Coprime.dvd_of_dvd_mul_left
Nat.Coprime.dvd_of_dvd_mul_right
Nat.gcd_dvd_left
Nat.gcd_dvd_right
Nat.coprime_div_gcd_div_gcd
```

For sign-safety, first replace `U,V,Up,Vp` by positive parameters.  Since `U*V=A0>0` and `Up*Vp=A0>0`, the two factors in each pair have the same sign; flipping both signs preserves the square-difference formula and product.  State a normalization lemma if needed:

```lean
def normalize_factor_pair_sign_statement : Prop :=
  ∀ {U V A0 : ℤ}, 0 < A0 → U * V = A0 →
    ∃ U1 V1 : ℤ, 0 < U1 ∧ 0 < V1 ∧
      U1 * V1 = A0 ∧ U1 ^ 2 = U ^ 2 ∧ V1 ^ 2 = V ^ 2
```

### 6. Prove the new factors are coprime and square

From pairwise coprime `2a,b,c,d`, get:

```text
gcd(a,d)=1, d odd.
```

For

```text
M = 4a^2+d^2,
N = 16a^2+d^2,
```

prove `gcd(M,N)=1` as described above.  Then subtract the two `D0` formulas to get

```text
b^2*M = c^2*N.
```

Use `coprime_ratio_square_imp_squares_statement` to get `S,R` for the new `EulerAux a d`.

This `coprime_ratio_square_imp_squares_statement` is the second hardest standalone lemma.  It is very similar in spirit to Mathlib’s `Int.sq_of_gcd_eq_one`, used in `Mathlib.NumberTheory.FLT.Four`, and can probably be proved by adapting that lemma or by prime multiplicity parity.

### 7. Strict descent bound

Use

```text
A0 = 2*a*b*c*d,
D0 ≠ 0,
b ≠ 0,
c ≠ 0.
```

Then

```text
|A*D| = A0*D0 = 2*|a|*|b|*|c|*|d|*D0
```

and `|b|,|c|,D0 ≥ 1`, so

```text
|a*d| < |A*D|.
```

This part is easy `natAbs` arithmetic after the sign normalization.

## Hardest lemmas to isolate

1. `Euler_factor_refinement_statement`: splitting two coprime factorizations into `U=2ab`, `V=cd`, `Up=2ac`, `Vp=bd`.  This is pure gcd/divisibility but will be the longest Lean proof.
2. `coprime_ratio_square_imp_squares_statement`: from `b^2*M = c^2*N` and `gcd(M,N)=1`, prove `M,N` squares.  Use `Int.sq_of_gcd_eq_one` or multiplicity parity.
3. The Pythagorean parameter normalization for the second triangle: converting the even parameter to `2*Up` and proving `Up*Vp=A0` without losing signs.

Everything else is algebra, parity, or `natAbs` bookkeeping.

## Non-circularity

This descent uses only:

- primitive Pythagorean triple classification,
- gcd/factorization arithmetic,
- parity/modular square facts,
- infinite descent via the strict `natAbs` measure.

It does **not** use the elliptic curve finite-point theorem, the N=12 rational point theorem, or any E1 point classification.
