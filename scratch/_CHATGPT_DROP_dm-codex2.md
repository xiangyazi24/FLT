# Q: FLT N12 nonaxis factor-identity residual

## Source check

I tried to inspect the exact remote paths named in the prompt on branch `scratch`:

```text
FLT/Assumptions/MazurProof/RationalPointsN12.lean
FLT/Assumptions/MazurProof/KubertBridgeN12.lean
```

The GitHub connector returned `Not Found` for both. Code search also did not find `NonAxisFactorIdentityResidual` or `rationalCoverSignedResidual_factorIdentityResidual` in the GitHub-visible repository. So this audit is based on the mathematical interface in the prompt and on the wrapper names you report as already checked. If those files exist only in the local worktree `/Users/huangx/repos/flt-ai` or on an unpushed branch, the theorem names below should be adjusted to the local definitions, but the number-theory route should be unchanged.

## Executive answer

The residual should close by an **elementary infinite descent on the same N=12 quartic square equation**, not by matching the visible factors and not by a direct one-shot congruence in `m,n,a,c`.

The exact arithmetic content behind the factor identities is:

1. normalize all signed/swapped factor identities to one branch;
2. recover `gcd(a,c)=1` and opposite parity for `a,c`;
3. use `a*c = m*n` and two primitive pairs to force a four-corner decomposition

   ```text
   m = x*y,   n = z*w,   a = x*z,   c = y*w,
   ```

   with `x,y,z,w` pairwise coprime;
4. a finite mod-8 check forces the unique even corner to be `z`;
5. the factor identity becomes a quadratic in `y`, whose discriminant gives

   ```text
   (3*x^2 - w^2) * (x^2 + w^2) = square;
   ```

6. because both factors are `2 mod 8` and have gcd `2`, split to

   ```text
   3*x^2 - w^2 = 2*u^2,
   x^2 + w^2   = 2*v^2;
   ```

7. set

   ```text
   R = (x+w)/2,   S = (x-w)/2;
   ```

   then

   ```text
   R^2 + S^2 = v^2,
   R^2 + 4*R*S + S^2 = u^2;
   ```

8. primitive Pythagorean parametrization gives a smaller primitive opposite-parity solution of the original quartic square equation.

So the loop-closing theorem should use the already-checked wrapper of shape

```text
SquareSol12(m,n,b) -> ∃ a c, FactorIdentityResidual12(m,n,a,c)
```

rather than trying to prove `FactorIdentityResidual12 -> False` by a local congruence only.

## Normalized arithmetic form

Let

```text
H12(m,n) = m^2 + 4*m*n - n^2,
Q12(m,n) = m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4.
```

Then

```text
Q12(m,n) = H12(m,n)^2 - 12*(m*n)^2.
```

The representative normal branch is

```text
a*c = m*n,
(m - n)*(m + n) = (a - c)*(3*a - c).                (N)
```

Expanding `(N)` and using `a*c=m*n` gives

```text
m^2 - n^2 = 3*a^2 - 4*a*c + c^2,
H12(m,n) = 3*a^2 + c^2.
```

Therefore

```text
Q12(m,n)
  = (3*a^2 + c^2)^2 - 12*(a*c)^2
  = (c^2 - 3*a^2)^2.
```

This is the key bridge: a residual reconstructs a quartic square witness.

For the signed/swapped branches, the square witness is one of

```text
c^2 - 3*a^2,
a^2 - 3*c^2,
```

up to sign. The sign is irrelevant after squaring.

## Fold the eight cases once

Do not carry eight branches through the descent. Normalize first.

Define the normal residual as:

```text
NormalResidual12(M,N,A,C) : Prop :=
  M*N ≠ 0 ∧
  gcd(M,N)=1 ∧
  M,N have opposite parity ∧
  A*C = M*N ∧
  (M-N)*(M+N) = (A-C)*(3*A-C).
```

The eight displayed cases fold as follows. Each row preserves primitivity, opposite parity, and the descent measure `|m*n|`.

| case | hypothesis | normalized `(M,N,A,C)` |
|---|---|---|
| P1 | `a*c=m*n`, `(m-n)(m+n)=(a-c)(3a-c)` | `(m,n,a,c)` |
| P2 | `a*c=m*n`, `(m-n)(m+n)=-(a+c)(3a+c)` | `(n,-m,a,-c)` |
| P3 | `a*c=m*n`, `(m-n)(m+n)=(a-c)(a-3c)` | `(m,n,c,a)` |
| P4 | `a*c=m*n`, `(m-n)(m+n)=-(a+c)(a+3c)` | `(n,-m,c,-a)` |
| N5 | `a*c=-m*n`, `(m-n)(m+n)=(a+c)(3a+c)` | `(m,n,a,-c)` |
| N6 | `a*c=-m*n`, `(m-n)(m+n)=-(a-c)(3a-c)` | `(n,-m,a,c)` |
| N7 | `a*c=-m*n`, `(m-n)(m+n)=(a+c)(a+3c)` | `(m,n,-c,a)` |
| N8 | `a*c=-m*n`, `(m-n)(m+n)=-(a-c)(a-3c)` | `(n,-m,c,a)` |

All entries are `ring` checks. This normalization is the first theorem I would put above the residual closer.

## GCD and parity content

In the normal branch:

```text
a*c = m*n,
(m-n)*(m+n) = (a-c)*(3*a-c),
gcd(m,n)=1,
m,n opposite parity.
```

First recover:

```text
gcd(a,c)=1.                                          (ACcop)
```

Proof sketch: if `d | a` and `d | c`, then `d | a*c = m*n`. Also `d | a-c` and `d | 3*a-c`, so `d | (m-n)*(m+n) = m^2-n^2`. But primitive `m,n` imply

```text
gcd(m*n, m^2-n^2)=1.
```

Thus `d` is a unit.

Since `m,n` have opposite parity, `m*n` is even. Hence `a*c` is even. Together with `gcd(a,c)=1`, exactly one of `a,c` is even, so `a,c` also have opposite parity.

Useful linear gcds:

```text
gcd(m-n, m+n)=1,
gcd(a-c, 3*a-c)=1.
```

For the second, a common divisor divides

```text
(3*a-c) - (a-c) = 2*a,
3*(a-c) - (3*a-c) = -2*c.
```

The opposite parity makes both linear factors odd, so the possible factor `2` is excluded.

These gcd lemmas are real but not sufficient for factor matching.

## False tempting routes

### False route 1: matching the two coprime factor pairs

The implication

```text
gcd(u,v)=1, gcd(r,s)=1, u*v=r*s
  -> {u,v} = {±r,±s}
```

is false.

Counterexample:

```text
3*35 = 5*21,
gcd(3,35)=1,
gcd(5,21)=1.
```

It even fits the linear shapes without `a*c=m*n`. Take

```text
m-n = 3,   m+n = 35      -> m=19, n=16,
a-c = 5,   3*a-c = 21    -> a=8,  c=3.
```

Then

```text
(m-n)*(m+n) = (a-c)*(3*a-c) = 105,
gcd(19,16)=1,
19,16 have opposite parity,
gcd(8,3)=1,
8,3 have opposite parity,
```

but

```text
a*c = 24 ≠ 304 = m*n.
```

So `a*c=±m*n` is essential, and factor matching is not a valid route.

### False route 2: dropping opposite parity

Without opposite parity the residual is false. For example

```text
m=n=a=c=1
```

gives

```text
a*c=m*n=1,
(m-n)*(m+n)=0=(a-c)*(3*a-c).
```

So the theorem must retain the primitive non-axis parity hypotheses, or use wrappers proving them.

### False route 3: expecting a fixed congruence contradiction before decomposition

In the original variables, the obstruction is hidden by the reassignment of prime factors between `m,n` and `a,c`. A blind `mod 8` or `mod 16` search in `m,n,a,c` will likely fail. The finite congruence is decisive only after the four-corner decomposition.

## Descent core in detail

Now work in the normal branch and write variables as `m,n,a,c`.

### Four-corner decomposition

From primitive pairs `(m,n)` and `(a,c)` and the product identity `a*c=m*n`, obtain pairwise coprime nonzero integers `x,y,z,w` such that

```text
m = x*y,
n = z*w,
a = x*z,
c = y*w.                                            (C)
```

This is the central invariant. Each prime divisor of `m*n` is assigned to one of four boxes according to whether it lies on the `m/n` side and the `a/c` side.

Substitute `(C)` into the normal factor identity:

```text
(x*y - z*w)*(x*y + z*w)
  = (x*z - y*w)*(3*x*z - y*w).                       (F)
```

Expanded as a quadratic in `y`:

```text
(x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0. (E)
```

### Mod-8 corner check

Opposite parity of `m,n` gives opposite parity of `x*y` and `z*w`. Opposite parity of `a,c` gives opposite parity of `x*z` and `y*w`. Pairwise coprimality implies that at most one of `x,y,z,w` is even. Therefore exactly one corner is even.

Equation `(F)` determines which one. With exactly one even corner and all odd squares `1 mod 8`:

| even corner | LHS `(xy)^2-(zw)^2 mod 8` | RHS `3x^2z^2 - 4xyzw + y^2w^2 mod 8` | conclusion |
|---|---:|---:|---|
| `x` | `7` or `3` | `1` or `5` | impossible |
| `y` | `7` or `3` | `3` or `7`, opposite choice | impossible |
| `z` | `1` or `5` | `1` or `5`, same choice | possible |
| `w` | `1` or `5` | `3` or `7` | impossible |

Thus

```text
z is even, and x,y,w are odd.                         (P)
```

This is the finite congruence check to formalize.

### Discriminant square

First rule out `x^2=w^2`. Since `x,w` are coprime nonzero odd integers, `x^2=w^2` would force `x^2=w^2=1`. Then `(E)` reduces to

```text
4*x*z*w*y - 4*z^2 = 0,
```

so

```text
z = x*w*y,
```

contradicting `z` even and `x,w,y` odd.

So

```text
x^2 ≠ w^2.                                           (Aneq)
```

Treat `(E)` as a quadratic equation in `y`. Its discriminant is

```text
Δ = 4*z^2*(3*x^2 - w^2)*(x^2 + w^2).                 (D)
```

The formal square root is

```text
2*(x^2-w^2)*y + 4*x*z*w.
```

To divide by `(2*z)^2` in Lean, prove separately:

```text
z ∣ x^2 - w^2.                                       (Zdiv)
```

This follows from `(E)` modulo `z`:

```text
z ∣ (x^2-w^2)*y^2,
```

and `gcd(y,z)=1`.

Then there is an integer `T` with

```text
T^2 = (3*x^2 - w^2)*(x^2 + w^2).                     (Sprod)
```

### Split the product of two `2 mod 8` factors

For coprime odd `x,w`:

```text
3*x^2 - w^2 ≡ 2 mod 8,
x^2 + w^2   ≡ 2 mod 8,
gcd(3*x^2 - w^2, x^2 + w^2) = 2.
```

The gcd proof: any common divisor divides

```text
(3*x^2-w^2) + (x^2+w^2) = 4*x^2,
3*(x^2+w^2) - (3*x^2-w^2) = 4*w^2,
```

and `gcd(x,w)=1`; the congruences show the gcd is exactly `2`, not `1` or `4`.

Since the product is a square and `x^2+w^2>0`, the first factor is positive. Therefore the half-factors are coprime positive odd squares. There exist integers `u,v` such that

```text
3*x^2 - w^2 = 2*u^2,                                 (U)
x^2 + w^2   = 2*v^2.                                 (V)
```

### Pythagorean conversion

Set

```text
R = (x+w)/2,
S = (x-w)/2.
```

Because `x,w` are odd, `R,S` are integers. Because `gcd(x,w)=1`, `gcd(R,S)=1`. Because `x^2≠w^2`, both `R` and `S` are nonzero. They have opposite parity.

Using `x=R+S` and `w=R-S`, equation `(V)` gives

```text
R^2 + S^2 = v^2.                                     (Py)
```

Equation `(U)` gives

```text
u^2 = R^2 + 4*R*S + S^2.                             (Tw)
```

Primitive Pythagorean parametrization gives coprime opposite-parity nonzero integers `p,q` with signed legs

```text
{R,S} = {p^2 - q^2, 2*p*q}.
```

After swapping legs and absorbing signs by `q ↦ -q` or swapping `p,q`, `(Tw)` becomes

```text
u^2 = (p^2-q^2)^2 + 4*(p^2-q^2)*(2*p*q) + (2*p*q)^2
    = p^4 + 8*p^3*q + 2*p^2*q^2 - 8*p*q^3 + q^4
    = Q12(p,q).                                      (Qsmall)
```

Moreover

```text
p*q ≠ 0,
gcd(p,q)=1,
p,q have opposite parity.
```

### Measure drop

Use

```text
μ(m,n) = |m*n|.
```

From Pythagorean parametrization:

```text
2*|p*q| ≤ p^2 + q^2 = |v|.
```

From `(V)`:

```text
v^2 = (x^2+w^2)/2.
```

For nonzero odd `x,w` with `x^2≠w^2`:

```text
(x^2+w^2)/2 < x^2*w^2,
```

so

```text
|v| < |x*w|.
```

Finally, from the corner decomposition and `z` even nonzero:

```text
|m*n| = |x*y*z*w| ≥ 2*|x*w|.
```

Thus

```text
|p*q| < |m*n|.
```

A normal residual gives a strictly smaller primitive opposite-parity solution of the original quartic square equation. The already-checked square-to-residual wrapper then closes the infinite descent.

## Lean-oriented lemma DAG

The following sketches use `import Mathlib` for self-contained snippets. Replace imports with local project imports after the theorem shape stabilizes.

### Basic definitions and normalization

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- N=12 quadratic form used in the square split. -/
def H12 (m n : ℤ) : ℤ :=
  m^2 + 4*m*n - n^2

/-- Homogeneous quartic for the N=12 obstruction. -/
def Q12 (m n : ℤ) : ℤ :=
  m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4

/-- Opposite parity over integers. -/
def OppParity (m n : ℤ) : Prop :=
  Odd (m + n)

/-- Primitive non-axis pair. -/
def PrimOppNonAxis (m n : ℤ) : Prop :=
  m*n ≠ 0 ∧ Int.gcd m n = 1 ∧ OppParity m n

/-- Descent measure. -/
def n12Measure (m n : ℤ) : ℕ :=
  (m*n).natAbs

/-- Quartic square solution. -/
def SquareSol12 (m n b : ℤ) : Prop :=
  PrimOppNonAxis m n ∧ b^2 = Q12 m n

lemma Q12_eq_H12_sq_sub (m n : ℤ) :
    Q12 m n = H12 m n ^ 2 - 12*(m*n)^2 := by
  unfold Q12 H12
  ring

/-- The one normalized residual branch. -/
def NormalResidual12 (m n a c : ℤ) : Prop :=
  PrimOppNonAxis m n ∧
  a*c = m*n ∧
  (m-n)*(m+n) = (a-c)*(3*a-c)

/-- Stand-in for the project's existing eight-case residual. -/
inductive FactorIdentityResidual12 (m n a c : ℤ) : Prop where
| P1 (hprod : a*c = m*n)
     (hfac : (m-n)*(m+n) = (a-c)*(3*a-c))
| P2 (hprod : a*c = m*n)
     (hfac : (m-n)*(m+n) = -(a+c)*(3*a+c))
| P3 (hprod : a*c = m*n)
     (hfac : (m-n)*(m+n) = (a-c)*(a-3*c))
| P4 (hprod : a*c = m*n)
     (hfac : (m-n)*(m+n) = -(a+c)*(a+3*c))
| N5 (hprod : a*c = -m*n)
     (hfac : (m-n)*(m+n) = (a+c)*(3*a+c))
| N6 (hprod : a*c = -m*n)
     (hfac : (m-n)*(m+n) = -(a-c)*(3*a-c))
| N7 (hprod : a*c = -m*n)
     (hfac : (m-n)*(m+n) = (a+c)*(a+3*c))
| N8 (hprod : a*c = -m*n)
     (hfac : (m-n)*(m+n) = -(a-c)*(a-3*c))

/-- Normalize all signed/swapped residual branches to the single branch. -/
theorem residual12_normalizes
    {m n a c : ℤ}
    (hprim : PrimOppNonAxis m n)
    (h : FactorIdentityResidual12 m n a c) :
    ∃ M N A C : ℤ,
      NormalResidual12 M N A C ∧ n12Measure M N = n12Measure m n := by
  -- Eight constructor cases using the table in the markdown:
  -- P1 -> (m,n,a,c)
  -- P2 -> (n,-m,a,-c)
  -- P3 -> (m,n,c,a)
  -- P4 -> (n,-m,c,-a)
  -- N5 -> (m,n,a,-c)
  -- N6 -> (n,-m,a,c)
  -- N7 -> (m,n,-c,a)
  -- N8 -> (n,-m,c,a)
  -- Each branch is a `ring_nf` verification plus gcd/parity preservation
  -- for `(m,n) ↦ (n,-m)`.
  sorry

/-- Normal residual reconstructs the quartic square witness. -/
theorem normalResidual12_to_square
    {m n a c : ℤ}
    (h : NormalResidual12 m n a c) :
    (c^2 - 3*a^2)^2 = Q12 m n := by
  -- From the factor identity and `a*c=m*n`, prove
  -- `H12 m n = 3*a^2 + c^2`, then use `Q12_eq_H12_sq_sub`.
  sorry

end MazurProof.RationalPointsN12
```

### GCD and parity lemmas

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma gcd_mul_sq_sub_sq_eq_one
    {m n : ℤ} (hcop : Int.gcd m n = 1) :
    Int.gcd (m*n) (m^2 - n^2) = 1 := by
  -- Prime/divisibility proof. Any common prime divisor of `m*n` and
  -- `m^2-n^2` divides one of `m,n`, then the other.
  sorry

lemma gcd_sub_add_eq_one_of_prim_opp
    {m n : ℤ} (hcop : Int.gcd m n = 1) (hpar : OppParity m n) :
    Int.gcd (m-n) (m+n) = 1 := by
  -- Common divisor divides `2*m` and `2*n`; opposite parity rules out 2.
  sorry

lemma normalResidual12_gcd_ac_eq_one
    {m n a c : ℤ} (h : NormalResidual12 m n a c) :
    Int.gcd a c = 1 := by
  -- If d divides a and c, then d divides a*c=m*n and also the RHS factors,
  -- hence d divides m^2-n^2. Use `gcd_mul_sq_sub_sq_eq_one`.
  sorry

lemma normalResidual12_oppParity_ac
    {m n a c : ℤ} (h : NormalResidual12 m n a c) :
    OppParity a c := by
  -- `a*c=m*n`; `m*n` is even because `m,n` are opposite parity.
  -- With gcd(a,c)=1, exactly one of a,c is even.
  sorry

lemma gcd_a_sub_c_three_a_sub_c_eq_one
    {a c : ℤ} (hcop : Int.gcd a c = 1) (hpar : OppParity a c) :
    Int.gcd (a-c) (3*a-c) = 1 := by
  -- Common divisor divides `2*a` and `2*c`; parity excludes 2.
  sorry

end MazurProof.RationalPointsN12
```

### Four-corner decomposition

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

def PairwiseCoprime4 (x y z w : ℤ) : Prop :=
  Int.gcd x y = 1 ∧ Int.gcd x z = 1 ∧ Int.gcd x w = 1 ∧
  Int.gcd y z = 1 ∧ Int.gcd y w = 1 ∧ Int.gcd z w = 1

/-- Cross decomposition of `a*c=m*n` for two primitive pairs. -/
theorem cross_decomposition
    {m n a c : ℤ}
    (hmn0 : m*n ≠ 0)
    (hmn : Int.gcd m n = 1)
    (hac : Int.gcd a c = 1)
    (hprod : a*c = m*n) :
    ∃ x y z w : ℤ,
      m = x*y ∧ n = z*w ∧ a = x*z ∧ c = y*w ∧
      x*y*z*w ≠ 0 ∧ PairwiseCoprime4 x y z w := by
  -- Recommended construction:
  -- choose x as the signed gcd/common divisor of m and a;
  -- write m=x*y and a=x*z;
  -- use a*c=m*n and coprimality to prove z | n;
  -- write n=z*w, then prove c=y*w.
  -- The signs can be parked in x.
  sorry

lemma cross_identity_quadratic
    (x y z w : ℤ) :
    ((x*y - z*w)*(x*y + z*w)
      = (x*z - y*w)*(3*(x*z) - y*w)) ↔
    (x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0 := by
  constructor <;> intro h <;> nlinarith [h]

/-- After cross decomposition, the unique even corner is `z`. -/
theorem cross_even_corner_is_z
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hparMN : OppParity (x*y) (z*w))
    (hparAC : OppParity (x*z) (y*w))
    (heq : (x*y - z*w)*(x*y + z*w)
         = (x*z - y*w)*(3*(x*z) - y*w)) :
    Even z ∧ Odd x ∧ Odd y ∧ Odd w := by
  -- 1. Pairwise coprimality -> at most one of x,y,z,w is even.
  -- 2. The two opposite-parity hypotheses -> at least one is even.
  -- 3. Four mod-8 cases using the table in the markdown.
  sorry

end MazurProof.RationalPointsN12
```

If `nlinarith [h]` does not close `cross_identity_quadratic`, replace it with:

```lean
  constructor <;> intro h
  · nlinarith [h]
  · nlinarith [h]
```

or simply use `ring_nf at h ⊢` with a manual rearrangement. The statement is a pure polynomial identity.

### Discriminant and square splitting

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

lemma cross_z_dvd_xsq_sub_wsq
    {x y z w : ℤ}
    (hyz : Int.gcd y z = 1)
    (heqQ : (x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0) :
    z ∣ x^2 - w^2 := by
  -- Reduce `heqQ` modulo z:
  -- z | (x^2-w^2)*y^2. Since gcd(y,z)=1, cancel y^2.
  sorry

lemma cross_xsq_ne_wsq
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hz : Even z) (hx : Odd x) (hy : Odd y) (hw : Odd w)
    (heqQ : (x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0) :
    x^2 ≠ w^2 := by
  -- If equal, coprime nonzero odd x,w force x^2=w^2=1.
  -- Then equation gives z=x*w*y, contradiction to z even and x*w*y odd.
  sorry

lemma cross_discriminant_square
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hz : Even z) (hx : Odd x) (hy : Odd y) (hw : Odd w)
    (heq : (x*y - z*w)*(x*y + z*w)
         = (x*z - y*w)*(3*(x*z) - y*w)) :
    ∃ T : ℤ, T^2 = (3*x^2 - w^2)*(x^2 + w^2) := by
  -- Use `cross_identity_quadratic` to get the quadratic equation.
  -- Discriminant identity:
  --   (2*(x^2-w^2)*y + 4*x*z*w)^2
  --     = 4*z^2*(3*x^2-w^2)*(x^2+w^2).
  -- Use `cross_z_dvd_xsq_sub_wsq` to divide the square root by `2*z`.
  sorry

lemma gcd_two_quadratic_factors_eq_two
    {x w : ℤ}
    (hcop : Int.gcd x w = 1) (hx : Odd x) (hw : Odd w) :
    Int.gcd (3*x^2 - w^2) (x^2 + w^2) = 2 := by
  -- Common divisor divides 4*x^2 and 4*w^2; both factors are 2 mod 8.
  -- Depending on sign conventions for `Int.gcd`, it may be cleaner to state
  -- this with natAbs values.
  sorry

lemma square_product_split_2mod8
    {x w T : ℤ}
    (hcop : Int.gcd x w = 1) (hx : Odd x) (hw : Odd w)
    (hT : T^2 = (3*x^2 - w^2)*(x^2 + w^2)) :
    ∃ u v : ℤ,
      3*x^2 - w^2 = 2*u^2 ∧
      x^2 + w^2 = 2*v^2 := by
  -- The two factors are 2 mod 8 and have gcd 2.
  -- Their halves are coprime odd positive factors whose product is a square.
  sorry

end MazurProof.RationalPointsN12
```

### Pythagorean step and descent theorem

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Signed primitive Pythagorean parametrization in the exact form needed. -/
theorem primitive_pythagorean_to_Q12
    {R S u v : ℤ}
    (hRS0 : R*S ≠ 0)
    (hcop : Int.gcd R S = 1)
    (hpar : OppParity R S)
    (hv : R^2 + S^2 = v^2)
    (hu : u^2 = R^2 + 4*R*S + S^2) :
    ∃ p q : ℤ,
      p*q ≠ 0 ∧ Int.gcd p q = 1 ∧ OppParity p q ∧ u^2 = Q12 p q := by
  -- Apply primitive Pythagorean parametrization to R^2+S^2=v^2.
  -- Signed/swap cases are absorbed by swapping p,q or replacing q by -q.
  sorry

lemma pythagorean_measure_drop_aux
    {p q x y z w v : ℤ}
    (hpq0 : p*q ≠ 0)
    (hzEven : Even z) (hy0 : y ≠ 0) (hz0 : z ≠ 0)
    (hx0 : x ≠ 0) (hw0 : w ≠ 0)
    (hxw : x^2 ≠ w^2)
    (hv : v^2 = (x^2 + w^2) / 2)
    (hpqv : 2 * (p*q).natAbs ≤ v.natAbs) :
    (p*q).natAbs < (x*y*z*w).natAbs := by
  -- Prove |v| < |x*w| from v^2=(x^2+w^2)/2 and x,w nonzero odd, x^2≠w^2.
  -- Then |x*y*z*w| ≥ 2*|x*w| because z is even nonzero and y nonzero.
  sorry

/-- Main normalized descent. -/
theorem normalResidual12_descent_square
    {m n a c : ℤ}
    (h : NormalResidual12 m n a c) :
    ∃ p q b : ℤ,
      SquareSol12 p q b ∧ n12Measure p q < n12Measure m n := by
  -- 1. Derive gcd(a,c)=1 and opposite parity for a,c.
  -- 2. Cross-decompose m=xy, n=zw, a=xz, c=yw.
  -- 3. Use the mod-8 corner lemma to get z even and x,y,w odd.
  -- 4. Use the discriminant square and split into U,V.
  -- 5. Set R=(x+w)/2, S=(x-w)/2.
  -- 6. Apply primitive_pythagorean_to_Q12 with b=u.
  -- 7. Prove the measure drop.
  sorry

/-- Descent from the original signed/swapped residual. -/
theorem residual12_descent_square
    {m n a c : ℤ}
    (hprim : PrimOppNonAxis m n)
    (hres : FactorIdentityResidual12 m n a c) :
    ∃ p q b : ℤ,
      SquareSol12 p q b ∧ n12Measure p q < n12Measure m n := by
  rcases residual12_normalizes hprim hres with ⟨M,N,A,C,hN,hmeas⟩
  rcases normalResidual12_descent_square hN with ⟨p,q,b,hsol,hlt⟩
  exact ⟨p,q,b,hsol, by simpa [hmeas] using hlt⟩

end MazurProof.RationalPointsN12
```

### Final closure by well-founded descent

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Parameterized by the already-checked square-to-residual wrapper. -/
theorem no_squareSol12_of_square_to_residual
    (square_to_residual :
      ∀ {m n b : ℤ}, SquareSol12 m n b -> ∃ a c : ℤ, FactorIdentityResidual12 m n a c) :
    ¬ ∃ m n b : ℤ, SquareSol12 m n b := by
  -- Well-founded descent on `n12Measure m n`.
  -- Choose a solution of minimal measure; reduce it to a residual;
  -- apply `residual12_descent_square`; contradiction.
  sorry

/-- Residual impossibility, using the loop-closing square-to-residual wrapper. -/
theorem no_factorIdentityResidual12
    (square_to_residual :
      ∀ {m n b : ℤ}, SquareSol12 m n b -> ∃ a c : ℤ, FactorIdentityResidual12 m n a c) :
    ¬ ∃ m n a c : ℤ,
      PrimOppNonAxis m n ∧ FactorIdentityResidual12 m n a c := by
  intro h
  rcases h with ⟨m,n,a,c,hprim,hres⟩
  -- Prove this either directly by eight cases, or via normalization plus
  -- `normalResidual12_to_square` and `Q12 n (-m) = Q12 m n`.
  have hsquare : ∃ b : ℤ, b^2 = Q12 m n := by
    sorry
  rcases hsquare with ⟨b,hb⟩
  exact no_squareSol12_of_square_to_residual square_to_residual ⟨m,n,b,hprim,hb⟩

end MazurProof.RationalPointsN12
```

## Clean arithmetic boundary if the full descent is too much now

This is not Mazur-hard. It is a genus-one / 2-descent calculation attached to the N=12 obstruction quartic. But it is Lean-heavy because of signed gcd decompositions and Pythagorean parametrization.

If you want an arithmetic boundary, do **not** leave it as the eight-case factor identity residual. The cleaner boundary is the primitive quartic square theorem:

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

def H12 (m n : ℤ) : ℤ :=
  m^2 + 4*m*n - n^2

def Q12 (m n : ℤ) : ℤ :=
  m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4

def OppParity (m n : ℤ) : Prop :=
  Odd (m + n)

/-- Arithmetic boundary for the N=12 non-axis quartic. -/
axiom no_primitive_nonaxis_Q12_square :
  ¬ ∃ m n b : ℤ,
    m*n ≠ 0 ∧ Int.gcd m n = 1 ∧ OppParity m n ∧ b^2 = Q12 m n

end MazurProof.RationalPointsN12
```

This is cleaner because:

1. every residual reconstructs a square witness;
2. the descent naturally returns a smaller square witness;
3. it states the actual homogeneous-space obstruction behind the N=12 curve;
4. the eight signed factor identities are an implementation artifact of the square split.

If the project wants a rational-points boundary instead, use the affine quartic

```text
Y^2 = X^4 + 8*X^3 + 2*X^2 - 8*X + 1
```

with a statement that all rational points map to axis/degenerate Kubert cases. For the current integer Lean layer, the primitive `Q12` square theorem is the most convenient boundary.

## What structure must remain in the Lean interface

The residual has enough information, but only if the following facts are retained or derivable:

```text
m*n ≠ 0,
gcd(m,n)=1,
m,n opposite parity,
a*c = ±m*n,
one of the exact signed/swapped factor identities,
SquareSol12 -> residual wrapper for the smaller solution.
```

Derived facts worth caching as lemmas:

```text
gcd(a,c)=1,
a,c opposite parity,
gcd(m-n,m+n)=1,
gcd(a-c,3*a-c)=1 in the normalized branch,
residual_to_square: residual -> ∃ b, b^2 = Q12(m,n).
```

The original `r,s` split does not need to be carried through the descent once it has produced the residual, except as a convenient source of `gcd(a,c)` and parity facts. The indispensable loop-closing structure is the checked reduction from any smaller quartic square solution back to a factor-identity residual.

## Recommended formalization order

1. Add `NormalResidual12` and prove the eight-case normalization theorem.
2. Prove `Q12_eq_H12_sq_sub` and `normalResidual12_to_square`.
3. Prove `normalResidual12_gcd_ac_eq_one` and `normalResidual12_oppParity_ac`.
4. Prove the cross decomposition `m=xy, n=zw, a=xz, c=yw`.
5. Prove `cross_even_corner_is_z` by the mod-8 table.
6. Prove `cross_identity_quadratic` and `z ∣ x^2-w^2`.
7. Prove `cross_discriminant_square`.
8. Prove the `2 mod 8` square-product split.
9. Prove the signed primitive Pythagorean parametrization in exactly the needed form.
10. Prove the `natAbs` measure inequality.
11. Close by well-founded descent using `factorIdentityResidual_of_square_12`, `rationalCoverSignedResidual_factorIdentityResidual`, or `bridge_N12_factorIdentityResidual`, whichever has the exact square-to-residual shape locally.

The brittle Lean points will be:

```text
- signed `Int.gcd` cross decomposition;
- preserving signs through normalization;
- converting parity statements between `Odd (m+n)` and Even/Odd cases;
- dividing the discriminant square by `(2*z)^2` cleanly;
- signed primitive Pythagorean parametrization;
- final `Int.natAbs` inequalities.
```

The mathematical route is therefore clear: normalize, decompose, force the even corner, split the discriminant, parametrize Pythagoreanly, and descend.
