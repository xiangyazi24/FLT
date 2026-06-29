# Q2180 dm-codex2 — N=12 Kubert-cover residual audit

## Verdict

I do **not** believe there is an integer counterexample under

```text
m*n ≠ 0,  gcd(m,n)=1,  and m,n have opposite parity.
```

The eight residual cases are impossible, but the shortest proof is **not** a local modular contradiction on the displayed factor identities. The right next step is an infinite descent. The descent briefly leaves the residual interface and returns to the original square equation for a strictly smaller primitive pair; then the already-proved square-to-residual reduction is invoked again.

The key invariant is the four-way factorization forced by

```text
a*c = m*n
```

after proving `gcd(a,c)=1`. All eight signs and swaps fold to one normal case:

```text
NormalResidual(M,N,A,C):
  A*C = M*N,
  (M-N)(M+N) = (A-C)(3A-C),
  M*N ≠ 0,
  gcd(M,N)=1,
  M,N opposite parity.
```

From this normal case the descent is forced.

## A. Counterexample audit

No counterexample survives the normalization below. Small primitive opposite-parity pairs such as `(±2,±1)`, `(±1,±2)`, `(±3,±2)`, `(±4,±1)`, `(±5,±2)`, `(±5,±4)` already fail by direct factor-pair inspection, but that is not the proof. The proof below handles all signs and all sizes.

Two warnings from the audit:

1. If the opposite-parity hypothesis is dropped, trivial degeneracies appear, for example `m=n=a=c=1` gives a zero factor identity. So parity is genuinely used.
2. It is false that equality of products of two coprime factor pairs lets you identify the individual factors. For example `3*10 = 5*6` with both pairs coprime. A route that tries to prove `m-n = ±(a-c)` or `m+n = ±(3a-c)` is not sound.

## B. The proof route

Write

```text
H(m,n) = m^2 + 4mn - n^2
Q(m,n) = m^4 + 8m^3n + 2m^2n^2 - 8mn^3 + n^4.
```

Then

```text
Q(m,n) = H(m,n)^2 - 12*(m*n)^2.
```

### Step 1: fold the eight cases to one normal case

Use only these transformations:

```text
(a,c) ↦ (c,a)                 -- swaps the coefficient 3 side
c ↦ -c                        -- converts ac=-mn to ac=mn
(m,n,a,c) ↦ (n,-m,a,-c)       -- converts the negative H sign to positive H sign
```

More explicitly, each residual case maps to `NormalResidual(M,N,A,C)` as follows:

| residual case | `(M,N,A,C)` |
|---|---|
| P1 | `(m,n,a,c)` |
| P2 | `(n,-m,a,-c)` |
| P3 | `(m,n,c,a)` |
| P4 | `(n,-m,c,-a)` |
| N5 | `(m,n,a,-c)` |
| N6 | `(n,-m,a,c)` |
| N7 | `(m,n,-c,a)` |
| N8 | `(n,-m,c,a)` |

These transformations preserve `M*N ≠ 0`, primitivity, opposite parity, and `|M*N|=|m*n|`.

So downstream there is only one case:

```text
A*C = M*N,
M^2 - N^2 = (A-C)(3A-C).
```

Equivalently,

```text
H(M,N) = 3*A^2 + C^2.
```

This also reconstructs a square witness:

```text
Q(M,N) = (C^2 - 3*A^2)^2.
```

So the residual is not detached from the original square equation.

### Step 2: recover `gcd(A,C)=1`

Let `d | A` and `d | C`. Then `d | A*C = M*N`. Also both linear factors `(A-C)` and `(3A-C)` are divisible by `d`, hence `d | M^2-N^2`.

But `gcd(M,N)=1` implies

```text
gcd(M*N, M^2-N^2) = 1.
```

Therefore `d=±1`, so

```text
gcd(A,C)=1.
```

Since `M,N` have opposite parity, `M*N` is even. Thus `A*C` is even. Together with `gcd(A,C)=1`, this gives `A,C` opposite parity.

### Step 3: split `A*C=M*N` into four coprime corners

Because both `(M,N)` and `(A,C)` are primitive and `A*C=M*N`, there are nonzero pairwise coprime integers `x,y,z,w` such that

```text
M = x*y,
N = z*w,
A = x*z,
C = y*w.
```

This is the crucial invariant. Think of each prime of `M*N` being assigned independently to the `M/N` side and to the `A/C` side.

The normal identity becomes

```text
(x*y - z*w)(x*y + z*w) = (x*z - y*w)(3*x*z - y*w),
```

or, after expansion as a quadratic in `y`,

```text
(x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0.        (E)
```

Exactly one of `x,y,z,w` is even: opposite parity of `M,N` gives one even among `xy,zw`, and opposite parity of `A,C` gives one even among `xz,yw`; pairwise coprimality prevents two even variables.

A mod-8 check of the normal equation forces the even variable to be **z**.

| even variable | contradiction modulo 8? |
|---|---|
| `x` | left side is `7`, right side is `1` |
| `y` | left and right differ by `4` |
| `z` | possible |
| `w` | left side is `1`, right side is `3` |

Thus

```text
z is even, and x,y,w are odd.
```

### Step 4: the discriminant gives a square product independent of `y,z`

If `x^2=w^2`, then pairwise coprimality and oddness give `|x|=|w|=1`. Equation (E) reduces to

```text
z = x*w*y,
```

contradicting `z` even and `y` odd. Hence

```text
x^2 ≠ w^2.
```

Since (E) has the integer root `y`, its discriminant is a square:

```text
D = 4*z^2*(3*x^2 - w^2)*(x^2 + w^2).
```

Because `z ≠ 0`, this implies

```text
(3*x^2 - w^2)*(x^2 + w^2) is a square.                (1)
```

Now `x,w` are odd and coprime. Therefore

```text
gcd(3*x^2 - w^2, x^2 + w^2) = 2,
3*x^2 - w^2 ≡ 2 mod 8,
x^2 + w^2 ≡ 2 mod 8.
```

So the two half-factors are coprime odd squares. There exist odd coprime integers `u,v` with

```text
3*x^2 - w^2 = 2*u^2,                                  (2)
x^2 + w^2 = 2*v^2.                                    (3)
```

### Step 5: convert to a smaller square solution

Set

```text
R = (x+w)/2,
S = (x-w)/2.
```

Since `x,w` are odd, `R,S` are integers. Since `gcd(x,w)=1`, `gcd(R,S)=1`. Since `x^2≠w^2`, both `R` and `S` are nonzero. Equation (3) gives

```text
R^2 + S^2 = v^2.
```

Equation (2), using `x=R+S` and `w=R-S`, gives

```text
u^2 = R^2 + 4*R*S + S^2.                              (4)
```

The primitive Pythagorean parametrization of `R^2+S^2=v^2` gives coprime opposite-parity nonzero integers `p,q` such that, up to swapping the two legs and changing signs,

```text
R = p^2 - q^2,
S = 2*p*q.
```

The expression in (4) is invariant under the allowed swap, and sign changes are absorbed by replacing `q` by `-q`. Consequently

```text
u^2 = p^4 + 8*p^3*q + 2*p^2*q^2 - 8*p*q^3 + q^4
    = Q(p,q).                                         (5)
```

Moreover `p*q ≠ 0`, `gcd(p,q)=1`, and `p,q` have opposite parity.

Finally the measure drops. From the Pythagorean parametrization,

```text
2*|p*q| ≤ p^2+q^2 = |v|.
```

From (3),

```text
v^2 = (x^2+w^2)/2 < x^2*w^2
```

because `x,w` are nonzero odd and `x^2≠w^2`. Hence `|p*q| < |x*w|`. Since `z` is even and `y` is nonzero,

```text
|M*N| = |x*y*z*w| ≥ 2*|x*w|.
```

Therefore

```text
|p*q| < |M*N| = |m*n|.
```

So any residual solution gives a strictly smaller primitive opposite-parity solution of the original square equation `b^2 = Q(p,q)`.

### Step 6: close by minimal descent

The formal closure should be:

1. Define `SquareSol(m,n,b)` to mean

   ```text
   m*n ≠ 0,
   gcd(m,n)=1,
   m,n opposite parity,
   b^2 = Q(m,n).
   ```

2. Use the already-proved reduction:

   ```text
   SquareSol(m,n,b) -> ∃ a c, Residual(m,n,a,c).
   ```

3. Prove the new descent lemma:

   ```text
   Residual(m,n,a,c) plus primitive/parity side conditions
     -> ∃ p q b', SquareSol(p,q,b') ∧ |p*q| < |m*n|.
   ```

4. Take a minimal `SquareSol` by the natural-number measure `Int.natAbs (m*n)`. The reduction gives a residual; the descent gives a smaller square solution; contradiction.

This proves no square solution, and then the residual is impossible because every residual reconstructs a square witness for its `(m,n)`.

## C. Lean theorem package

The following is the interface I would formalize. I use `import Mathlib` deliberately here so the snippet is self-contained with all imports; in the project you can replace it by narrower imports after the statements stabilize.

```lean
import Mathlib

namespace FLT.Kubert12

/-- The linear form used in the N=12 obstruction. -/
def H (m n : ℤ) : ℤ :=
  m^2 + 4*m*n - n^2

/-- The quartic whose square-ness is being obstructed. -/
def Q (m n : ℤ) : ℤ :=
  m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4

/-- Use this rather than fighting over the exact Int coprime API. -/
def IntCoprime (x y : ℤ) : Prop :=
  Int.gcd x y = 1

/-- For integers, opposite parity is equivalent to the sum being odd. -/
def OppParity (x y : ℤ) : Prop :=
  Odd (x + y)

/-- Descent measure. -/
def meas (m n : ℤ) : ℕ :=
  (m*n).natAbs

lemma Q_eq_H_sq_sub (m n : ℤ) :
    Q m n = H m n ^ 2 - 12*(m*n)^2 := by
  unfold Q H
  ring

/-- One normalized residual case. All eight original cases fold to this. -/
def NormalResidual (m n a c : ℤ) : Prop :=
  m*n ≠ 0 ∧
  IntCoprime m n ∧
  OppParity m n ∧
  a*c = m*n ∧
  (m-n)*(m+n) = (a-c)*(3*a-c)

/-- The original eight residual cases, without repeating the common side conditions. -/
inductive Residual (m n a c : ℤ) : Prop where
| P1
    (hprod : a*c = m*n)
    (hfac  : (m-n)*(m+n) =  (a-c)*(3*a-c)) : Residual m n a c
| P2
    (hprod : a*c = m*n)
    (hfac  : (m-n)*(m+n) = -(a+c)*(3*a+c)) : Residual m n a c
| P3
    (hprod : a*c = m*n)
    (hfac  : (m-n)*(m+n) =  (a-c)*(a-3*c)) : Residual m n a c
| P4
    (hprod : a*c = m*n)
    (hfac  : (m-n)*(m+n) = -(a+c)*(a+3*c)) : Residual m n a c
| N5
    (hprod : a*c = -m*n)
    (hfac  : (m-n)*(m+n) =  (a+c)*(3*a+c)) : Residual m n a c
| N6
    (hprod : a*c = -m*n)
    (hfac  : (m-n)*(m+n) = -(a-c)*(3*a-c)) : Residual m n a c
| N7
    (hprod : a*c = -m*n)
    (hfac  : (m-n)*(m+n) =  (a+c)*(a+3*c)) : Residual m n a c
| N8
    (hprod : a*c = -m*n)
    (hfac  : (m-n)*(m+n) = -(a-c)*(a-3*c)) : Residual m n a c

/-- Normalization table for the eight residual cases. -/
theorem residual_normalizes
    {m n a c : ℤ}
    (hmn0 : m*n ≠ 0)
    (hcop : IntCoprime m n)
    (hpar : OppParity m n)
    (h : Residual m n a c) :
    ∃ M N A C : ℤ,
      NormalResidual M N A C ∧ meas M N = meas m n := by
  -- Eight constructor cases. Each is a `ring` verification using the table:
  -- P1 -> (m,n,a,c)
  -- P2 -> (n,-m,a,-c)
  -- P3 -> (m,n,c,a)
  -- P4 -> (n,-m,c,-a)
  -- N5 -> (m,n,a,-c)
  -- N6 -> (n,-m,a,c)
  -- N7 -> (m,n,-c,a)
  -- N8 -> (n,-m,c,a)
  sorry

/-- Any residual already gives a square witness for the original quartic. -/
theorem residual_to_square
    {m n a c : ℤ}
    (h : Residual m n a c) :
    ∃ b : ℤ, b^2 = Q m n := by
  -- Cases P1/N5 give `H = 3*a^2+c^2` and `b = c^2-3*a^2`.
  -- Cases P2/N6 give `H = -(3*a^2+c^2)` and the same `b`.
  -- Cases P3/N7 give `H = a^2+3*c^2` and `b = a^2-3*c^2`.
  -- Cases P4/N8 give `H = -(a^2+3*c^2)` and the same `b`.
  -- Then use `Q_eq_H_sq_sub` and `a*c = ±m*n`.
  sorry

/-- Pairwise coprimality for the four corner factors. -/
def PairwiseCoprime4 (x y z w : ℤ) : Prop :=
  IntCoprime x y ∧ IntCoprime x z ∧ IntCoprime x w ∧
  IntCoprime y z ∧ IntCoprime y w ∧ IntCoprime z w

/-- Recover `gcd(a,c)=1` from the normalized residual. -/
theorem normal_coprime_ac
    {m n a c : ℤ}
    (h : NormalResidual m n a c) :
    IntCoprime a c := by
  -- If `d | a,c`, then `d | a*c = m*n` and `d | m^2-n^2`.
  -- But `gcd(m*n, m^2-n^2)=1` follows from `gcd(m,n)=1`.
  sorry

/-- Four-corner factorization of `a*c=m*n` for two primitive pairs. -/
theorem cross_factorization
    {m n a c : ℤ}
    (hmn : IntCoprime m n)
    (hac : IntCoprime a c)
    (hprod : a*c = m*n) :
    ∃ x y z w : ℤ,
      m = x*y ∧ n = z*w ∧ a = x*z ∧ c = y*w ∧
      x*y*z*w ≠ 0 ∧ PairwiseCoprime4 x y z w := by
  -- Construct by assigning every prime of `m*n` to one of four boxes:
  --   divides m/a -> x, divides m/c -> y, divides n/a -> z, divides n/c -> w.
  -- A concrete Lean construction can use `x = gcd(m,a)` and divisibility.
  sorry

/-- In the normal residual, the unique even corner is `z`. -/
theorem normal_cross_even
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hpar : OppParity (x*y) (z*w))
    (heq : (x*y - z*w)*(x*y + z*w)
         = (x*z - y*w)*(3*(x*z) - y*w)) :
    Even z ∧ Odd x ∧ Odd y ∧ Odd w := by
  -- Pairwise coprimality plus `OppParity (xy) (zw)` gives exactly one even corner.
  -- Check the four possible even corners modulo 8.
  -- x even: LHS=7, RHS=1.
  -- y even: LHS and RHS differ by 4.
  -- w even: LHS=1, RHS=3.
  -- Therefore z is even.
  sorry

/-- The quadratic discriminant step. -/
theorem normal_cross_discriminant_square
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hz : Even z)
    (hx : Odd x) (hy : Odd y) (hw : Odd w)
    (heq : (x*y - z*w)*(x*y + z*w)
         = (x*z - y*w)*(3*(x*z) - y*w)) :
    x^2 ≠ w^2 ∧
    ∃ T : ℤ, T^2 = (3*x^2 - w^2)*(x^2 + w^2) := by
  -- Expanded equation:
  --   (x^2-w^2)y^2 + 4*x*z*w*y - z^2*(3*x^2+w^2)=0.
  -- If x^2=w^2, then |x|=|w|=1 and the equation gives z=x*w*y,
  -- contradicting z even and y odd.
  -- Otherwise the discriminant is a square:
  --   4*z^2*(3*x^2-w^2)*(x^2+w^2).
  -- Cancel the square factor `(2*z)^2`.
  sorry

/-- Split the square product into two square half-factors. -/
theorem quartic_square_split
    {x w T : ℤ}
    (hcop : IntCoprime x w)
    (hx : Odd x) (hw : Odd w)
    (hT : T^2 = (3*x^2 - w^2)*(x^2 + w^2)) :
    ∃ u v : ℤ,
      3*x^2 - w^2 = 2*u^2 ∧
      x^2 + w^2 = 2*v^2 := by
  -- The two factors have gcd exactly 2 and are both 2 mod 8.
  -- Therefore their halves are coprime odd factors whose product is a square.
  sorry

/-- The Pythagorean-to-quartic conversion. -/
theorem twisted_pythagorean_to_Q
    {R S u v : ℤ}
    (hRS : IntCoprime R S)
    (hpar : OppParity R S)
    (hR0 : R ≠ 0)
    (hS0 : S ≠ 0)
    (hv : R^2 + S^2 = v^2)
    (hu : u^2 = R^2 + 4*R*S + S^2) :
    ∃ p q : ℤ,
      p*q ≠ 0 ∧
      IntCoprime p q ∧
      OppParity p q ∧
      u^2 = Q p q := by
  -- Primitive Pythagorean parametrization gives, up to swap/sign,
  --   R = p^2-q^2, S = 2*p*q.
  -- In both orientations,
  --   R^2 + 4*R*S + S^2
  -- becomes `Q p q`, after possibly replacing q by -q.
  sorry

/-- Main new descent lemma from the normalized residual. -/
theorem normal_residual_descent_to_square
    {m n a c : ℤ}
    (h : NormalResidual m n a c) :
    ∃ p q b : ℤ,
      p*q ≠ 0 ∧
      IntCoprime p q ∧
      OppParity p q ∧
      b^2 = Q p q ∧
      meas p q < meas m n := by
  -- 1. `normal_coprime_ac`.
  -- 2. `cross_factorization` gives `m=xy,n=zw,a=xz,c=yw`.
  -- 3. `normal_cross_even` forces z even.
  -- 4. `normal_cross_discriminant_square` and `quartic_square_split` give u,v.
  -- 5. Let R=(x+w)/2 and S=(x-w)/2.
  -- 6. `twisted_pythagorean_to_Q` gives p,q,b=u.
  -- 7. The measure inequality is:
  --      2*|p*q| ≤ p^2+q^2 = |v|,
  --      v^2 = (x^2+w^2)/2 < x^2*w^2,
  --      and |m*n| = |x*y*z*w| ≥ 2*|x*w| because z is even.
  sorry

/-- Descent lemma for the original eight residual cases. -/
theorem residual_descent_to_square
    {m n a c : ℤ}
    (hmn0 : m*n ≠ 0)
    (hcop : IntCoprime m n)
    (hpar : OppParity m n)
    (h : Residual m n a c) :
    ∃ p q b : ℤ,
      p*q ≠ 0 ∧
      IntCoprime p q ∧
      OppParity p q ∧
      b^2 = Q p q ∧
      meas p q < meas m n := by
  rcases residual_normalizes hmn0 hcop hpar h with ⟨M,N,A,C,hN,hmeas⟩
  rcases normal_residual_descent_to_square hN with
    ⟨p,q,b,hpq0,hpqcop,hpqpar,hb,hlt⟩
  refine ⟨p,q,b,hpq0,hpqcop,hpqpar,hb,?_⟩
  simpa [hmeas] using hlt

/-- The square-solution record used for the final minimal descent. -/
def SquareSol (m n b : ℤ) : Prop :=
  m*n ≠ 0 ∧ IntCoprime m n ∧ OppParity m n ∧ b^2 = Q m n

/-- Final closure, parameterized by the already-proved square-to-residual reduction. -/
theorem no_square_of_reduction_and_descent
    (reduce : ∀ {m n b : ℤ}, SquareSol m n b -> ∃ a c : ℤ, Residual m n a c) :
    ¬ ∃ m n b : ℤ, SquareSol m n b := by
  -- Well-founded descent on `meas m n`.
  -- Pick a SquareSol with minimal measure using Nat.find / wellFounded_lt.
  -- Apply `reduce`, then `residual_descent_to_square`, contradicting minimality.
  sorry

/-- Consequently, the residual itself is impossible. -/
theorem no_residual_of_reduction_and_descent
    (reduce : ∀ {m n b : ℤ}, SquareSol m n b -> ∃ a c : ℤ, Residual m n a c) :
    ¬ ∃ m n a c : ℤ,
      m*n ≠ 0 ∧ IntCoprime m n ∧ OppParity m n ∧ Residual m n a c := by
  intro hres
  rcases hres with ⟨m,n,a,c,hmn0,hcop,hpar,hR⟩
  rcases residual_to_square hR with ⟨b,hb⟩
  exact no_square_of_reduction_and_descent reduce ⟨m,n,b,hmn0,hcop,hpar,hb⟩

end FLT.Kubert12
```

## D. Did the residual lose crucial structure?

Not fatally. The residual still contains enough structure to reconstruct a square witness and to start the descent. However, it is the wrong final interface if you try to prove `Residual -> False` by a local congruence-only argument.

What should be retained in the Lean interface:

1. Keep a theorem of the form

   ```text
   SquareSol(m,n,b) -> ∃ a c, Residual(m,n,a,c)
   ```

   The new descent returns a smaller `SquareSol`, not immediately a smaller displayed residual. You close the loop by invoking this reduction again.

2. It is worth carrying the derived facts

   ```text
   gcd(a,c)=1,
   a,c opposite parity,
   the relevant 3-side nondivisibility from gcd(r,s)=1
   ```

   even though the first two are recoverable from the residual. Carrying them will shorten the Lean proof.

3. Do not keep all eight cases alive downstream. Normalize once to `NormalResidual`; otherwise the proof becomes eight copies of the same descent with sign noise.

4. Keep `Q_eq_H_sq_sub` and `residual_to_square` near the residual definition. They are the bridge showing the residual did not lose the square witness.

The adversarial conclusion is: the residual is not false for a cheap reason. The breakthrough is the chain

```text
Residual
  -> normalized case
  -> four-corner factorization x,y,z,w
  -> mod 8 forces z even
  -> discriminant square in x,w
  -> two half-square equations
  -> primitive Pythagorean parametrization
  -> smaller Q-square solution.
```

That is the route I would formalize next.
