# Q2200 dm-codex2 — N=12 non-axis factor-identity residual audit

## Source note

I attempted to inspect the exact files named in the prompt through the GitHub connector:

```text
FLT/Assumptions/MazurProof/RationalPointsN12.lean
FLT/Assumptions/MazurProof/KubertBridgeN12.lean
```

The connector returned `Not Found` for those paths on the checked remote refs, and GitHub code search did not find `NonAxisFactorIdentityResidual`, `factorIdentityResidual`, or `RationalPointsN12`. The repository itself is accessible and writable, and `FLT.lean` / `FLT/Assumptions/Mazur.lean` are present on the remote. So this audit is based on the mathematical interface in the prompt and on the already-checked wrapper names you supplied, not on exact source-line inspection. If these files exist only in the local worktree `/Users/huangx/repos/flt-ai` or on an unindexed/unpushed branch, the route below is still the one I would formalize, but theorem names may need small adaptation.

## Executive verdict

The non-axis factor-identity residual is very likely **impossible** under the intended primitive non-axis hypotheses, but not for a cheap reason such as matching the two factors or a direct mod-3/mod-4 contradiction in the original variables.

The real content is a classical infinite descent on the same binary quartic square equation that produced the residual. The factor identity is useful because, together with

```text
a*c = ± m*n,
```

it gives a four-corner coprime decomposition. After one mod-8 check, a discriminant calculation produces two quadratic equations, one Pythagorean and one twisted Pythagorean. The primitive Pythagorean parametrization then gives a strictly smaller primitive solution of the original quartic square equation.

So the closure should be organized as:

```text
signed factor residual
  -> normalized residual
  -> four-corner coprime decomposition x,y,z,w
  -> mod 8: the unique even corner is z
  -> discriminant square in x,w
  -> split into 3*x^2 - w^2 = 2*u^2 and x^2 + w^2 = 2*v^2
  -> set R=(x+w)/2, S=(x-w)/2
  -> primitive Pythagorean parametrization
  -> smaller solution of the original N=12 quartic square equation
  -> well-founded descent using the already-proved square-to-residual wrapper
```

This means `NonAxisFactorIdentityResidual` can be closed, but the proof should probably depend on the already-checked reduction from the quartic square equation back to a factor-identity residual. Trying to prove every residual false by an isolated finite case split will probably stall.

## 1. Exact arithmetic content behind the identities

Let

```text
H(m,n)  = m^2 + 4*m*n - n^2,
Q12(m,n)= m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4.
```

Then

```text
Q12(m,n) = H(m,n)^2 - 12*(m*n)^2.
```

The representative normal factor identity is

```text
a*c = m*n,
(m - n)*(m + n) = (a - c)*(3*a - c).              (N)
```

Expanding the second equation and using `a*c = m*n` gives

```text
m^2 - n^2 = 3*a^2 - 4*a*c + c^2,
H(m,n) = m^2 + 4*m*n - n^2 = 3*a^2 + c^2.
```

Consequently

```text
Q12(m,n) = (3*a^2 + c^2)^2 - 12*(a*c)^2
          = (c^2 - 3*a^2)^2.
```

Thus each normalized residual is not just a random factor identity: it reconstructs a square witness for the N=12 quartic. In the signed/swapped residual cases the square witness is one of

```text
c^2 - 3*a^2,
a^2 - 3*c^2,
```

up to sign, and the sign does not matter after squaring.

Conceptually, the residual is the arithmetic of the genus-one quartic

```text
Y^2 = X^4 + 8*X^3 + 2*X^2 - 8*X + 1,
```

in homogeneous form. It is also the norm equation

```text
b^2 = H(m,n)^2 - 12*(m*n)^2
```

with a primitive signed split in the quadratic order attached to `√3`. The factor identities encode one branch of the split.

## 2. Fold all signed/swapped cases once

Do not keep eight cases alive downstream. Normalize first.

A good normal residual is:

```text
NormalResidual(M,N,A,C) : Prop :=
  M*N ≠ 0 ∧
  gcd(M,N)=1 ∧
  M,N have opposite parity ∧
  A*C = M*N ∧
  (M-N)*(M+N) = (A-C)*(3*A-C).
```

The eight cases fold by the following substitutions. In each row, `(M,N,A,C)` satisfies the normal residual and `|M*N| = |m*n|`.

| case | product | factor identity | normalized `(M,N,A,C)` |
|---|---:|---|---|
| P1 | `a*c=m*n` | `(a-c)*(3a-c)` | `(m,n,a,c)` |
| P2 | `a*c=m*n` | `-(a+c)*(3a+c)` | `(n,-m,a,-c)` |
| P3 | `a*c=m*n` | `(a-c)*(a-3c)` | `(m,n,c,a)` |
| P4 | `a*c=m*n` | `-(a+c)*(a+3c)` | `(n,-m,c,-a)` |
| N5 | `a*c=-m*n` | `(a+c)*(3a+c)` | `(m,n,a,-c)` |
| N6 | `a*c=-m*n` | `-(a-c)*(3a-c)` | `(n,-m,a,c)` |
| N7 | `a*c=-m*n` | `(a+c)*(a+3c)` | `(m,n,-c,a)` |
| N8 | `a*c=-m*n` | `-(a-c)*(a-3c)` | `(n,-m,c,a)` |

These substitutions preserve nonzero product, primitivity, opposite parity, and descent measure `Int.natAbs (m*n)`.

## 3. First gcd/parity facts

From the normal residual:

```text
A*C = M*N,
(M-N)*(M+N) = (A-C)*(3*A-C),
gcd(M,N)=1,
M,N opposite parity.
```

The first necessary lemma is

```text
gcd(A,C)=1.
```

Proof: if `d | A` and `d | C`, then `d | A*C = M*N`. Also `d | A-C` and `d | 3*A-C`, hence `d | (M-N)*(M+N) = M^2-N^2`. But

```text
gcd(M*N, M^2-N^2)=1
```

for primitive `M,N`. Therefore `d` is a unit.

Since `M,N` have opposite parity, `M*N` is even. Hence `A*C` is even. With `gcd(A,C)=1`, this implies `A,C` have opposite parity.

Two useful linear gcd lemmas are then true:

```text
gcd(M-N, M+N)=1,
gcd(A-C, 3*A-C)=1.
```

For the second, any common divisor divides

```text
(3*A-C) - (A-C) = 2*A,
3*(A-C) - (3*A-C) = -2*C.
```

Since `A,C` are coprime and opposite parity, both linear factors are odd, so the common divisor is a unit.

These gcds are useful, but they do **not** justify matching factors one by one. Equality of products of coprime pairs does not imply the pairs are equal up to units.

## 4. False tempting generalizations and counterexamples

### 4.1 Factor matching is false

The implication

```text
gcd(u,v)=1, gcd(r,s)=1, u*v=r*s
  -> u=±r and v=±s, up to swap
```

is false. For example,

```text
3*35 = 5*21,
gcd(3,35)=1,
gcd(5,21)=1.
```

This even fits the linear shapes without the product relation `a*c=m*n`:

```text
m-n = 3,   m+n = 35        -> m=19, n=16,
a-c = 5,   3*a-c = 21      -> a=8,  c=3.
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

So the `a*c=±m*n` equation is essential. Do not formalize a bogus factor-matching route.

### 4.2 Dropping opposite parity makes the residual false

Without opposite parity, there are immediate degeneracies. In the normal case,

```text
m=n=a=c=1
```

gives

```text
a*c=m*n=1,
(m-n)*(m+n)=0,
(a-c)*(3*a-c)=0.
```

Thus the theorem must retain opposite parity, or must retain the original non-axis hypotheses that imply it.

### 4.3 The displayed factor identity alone has many primitive solutions

The identity

```text
(m-n)*(m+n) = (a-c)*(3*a-c)
```

is not the hard theorem. It has many primitive opposite-parity solutions if `a*c=m*n` is omitted. The example above, `(m,n,a,c)=(19,16,8,3)`, is already one.

### 4.4 Do not expect a direct fixed-modulus obstruction in `m,n,a,c`

The structural congruence obstruction appears only after the four-corner decomposition below. In the original variables, the signed cases and the factor reassignment hide the obstruction. A direct `omega`/`norm_num` search over `m,n,a,c mod 8` is unlikely to close the residual unless it first encodes the coprime corner decomposition.

## 5. The descent in detail

Work in the normalized case and rename variables back to `m,n,a,c` for readability:

```text
a*c = m*n,
(m-n)*(m+n) = (a-c)*(3*a-c),
m*n ≠ 0,
gcd(m,n)=1,
m,n opposite parity.
```

### 5.1 Four-corner decomposition

Because both pairs `(m,n)` and `(a,c)` are primitive and `a*c=m*n`, there are nonzero pairwise coprime integers `x,y,z,w` such that

```text
m = x*y,
n = z*w,
a = x*z,
c = y*w.                                            (C)
```

This is the key invariant. Each prime divisor of `m*n` is assigned independently to one of four boxes according to whether it lies in the `m/n` side and in the `a/c` side.

Substituting (C) into the normal factor identity gives

```text
(x*y - z*w)*(x*y + z*w)
  = (x*z - y*w)*(3*x*z - y*w).                       (F)
```

Expanded as a quadratic equation in `y`, this is

```text
(x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0. (E)
```

### 5.2 Unique even corner and the mod-8 check

The opposite parity of `m,n` says `x*y` and `z*w` have opposite parity. The opposite parity of `a,c` says `x*z` and `y*w` have opposite parity. Pairwise coprimality implies that at most one of `x,y,z,w` is even. Therefore exactly one corner is even.

The factor equation (F) decides which corner it is. With exactly one even variable, all odd squares are `1 mod 8`. The finite check is:

| even corner | LHS `(xy)^2-(zw)^2 mod 8` | RHS `(xz-yw)*(3xz-yw) mod 8` | result |
|---|---:|---:|---|
| `x` | `7` or `3` | `1` or `5` | impossible |
| `y` | `7` or `3` | `3` or `7` with opposite choice | impossible |
| `z` | `1` or `5` | `1` or `5` with same choice | possible |
| `w` | `1` or `5` | `3` or `7` | impossible |

So the normal case forces

```text
z is even,
x,y,w are odd.                                      (P)
```

This is the finite congruence check to formalize next.

### 5.3 Discriminant square

First rule out `x^2=w^2`. Since `x,w` are coprime odd integers, `x^2=w^2` would imply `|x|=|w|=1`. Equation (E) would reduce to

```text
4*x*z*w*y = 4*z^2,
```

hence

```text
z = x*w*y,
```

contradicting `z` even and `x,w,y` odd. Thus

```text
x^2 ≠ w^2.                                           (Aneq)
```

Now view (E) as a quadratic in `y`. Its discriminant is

```text
Δ = 4*z^2*(3*x^2 - w^2)*(x^2 + w^2).                (D)
```

Because `y` is an integer root,

```text
Δ = (2*(x^2-w^2)*y + 4*x*z*w)^2.
```

To divide by `(2*z)^2` in Lean, first prove the useful invariant

```text
z ∣ x^2 - w^2.                                      (Zdiv)
```

This follows from (E) modulo `z`:

```text
(x^2-w^2)*y^2 ≡ 0 mod z,
```

and `gcd(y,z)=1`. Hence the square root of `Δ` is divisible by `2*z`, and there is an integer `T` such that

```text
T^2 = (3*x^2 - w^2)*(x^2 + w^2).                   (Sprod)
```

### 5.4 Split the square product

Since `x,w` are coprime odd integers,

```text
3*x^2 - w^2 ≡ 2 mod 8,
x^2 + w^2   ≡ 2 mod 8.
```

Also

```text
gcd(3*x^2 - w^2, x^2 + w^2) = 2.
```

Indeed any common divisor divides

```text
(3*x^2-w^2) + (x^2+w^2) = 4*x^2,
3*(x^2+w^2) - (3*x^2-w^2) = 4*w^2,
```

and `gcd(x,w)=1`; the two factors are exactly `2 mod 8`, so the gcd is exactly `2`.

Therefore their halves are coprime odd integers whose product is a square. Since `x^2+w^2>0`, equation (Sprod) also forces `3*x^2-w^2>0`. Hence there are odd coprime integers `u,v` such that

```text
3*x^2 - w^2 = 2*u^2,                                (U)
x^2 + w^2   = 2*v^2.                                (V)
```

### 5.5 Pythagorean conversion

Set

```text
R = (x+w)/2,
S = (x-w)/2.
```

Because `x,w` are odd, `R,S` are integers. Because `gcd(x,w)=1`,

```text
gcd(R,S)=1.
```

Because `x,w` are odd, `R,S` have opposite parity. Because `x^2≠w^2`, both are nonzero.

Equation (V) gives

```text
R^2 + S^2 = v^2.                                    (Py)
```

Equation (U), using `x=R+S` and `w=R-S`, gives

```text
u^2 = R^2 + 4*R*S + S^2.                            (Tw)
```

The primitive Pythagorean parametrization gives coprime opposite-parity nonzero integers `p,q` such that, after swapping the legs and choosing signs,

```text
{R,S} = {p^2 - q^2, 2*p*q}
```

as signed legs. The expression `R^2 + 4*R*S + S^2` is symmetric in `R,S`; the remaining sign is absorbed by replacing `q` by `-q`. Therefore

```text
u^2 = (p^2-q^2)^2 + 4*(p^2-q^2)*(2*p*q) + (2*p*q)^2
    = p^4 + 8*p^3*q + 2*p^2*q^2 - 8*p*q^3 + q^4
    = Q12(p,q).                                     (Qsmall)
```

Moreover

```text
p*q ≠ 0,
gcd(p,q)=1,
p,q have opposite parity.
```

### 5.6 Strict descent measure

Use the measure

```text
μ(m,n) = Int.natAbs (m*n).
```

From the Pythagorean parametrization,

```text
2*|p*q| ≤ p^2 + q^2 = |v|.
```

From (V),

```text
v^2 = (x^2+w^2)/2.
```

Since `x,w` are nonzero odd and `x^2≠w^2`,

```text
(x^2+w^2)/2 < x^2*w^2,
```

so

```text
|v| < |x*w|.
```

Finally, from the corner decomposition,

```text
|m*n| = |x*y*z*w|.
```

Here `z` is even and nonzero, and `y` is nonzero, hence

```text
|m*n| ≥ 2*|x*w|.
```

Thus

```text
|p*q| < |m*n|.
```

So one normalized residual gives a strictly smaller primitive opposite-parity solution of the original quartic square equation.

## 6. Lean-oriented lemma DAG

Below is the theorem package I would aim for. The exact namespace can be changed to match the project. The statements are intentionally integer-only and isolate API-heavy facts.

```lean
import Mathlib

namespace FLT.Kubert.N12

/-- The quadratic form appearing in the N=12 split. -/
def H12 (m n : ℤ) : ℤ :=
  m^2 + 4*m*n - n^2

/-- The homogeneous quartic square equation. -/
def Q12 (m n : ℤ) : ℤ :=
  m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4

/-- Opposite parity, phrased in a way that is convenient over `ℤ`. -/
def OppParity (x y : ℤ) : Prop :=
  Odd (x + y)

/-- Primitive non-axis input pair. -/
def PrimOppNonAxis (m n : ℤ) : Prop :=
  m*n ≠ 0 ∧ IsCoprime m n ∧ OppParity m n

/-- Descent measure. -/
def n12Measure (m n : ℤ) : ℕ :=
  (m*n).natAbs

/-- The original quartic square solution. -/
def SquareSol12 (m n b : ℤ) : Prop :=
  PrimOppNonAxis m n ∧ b^2 = Q12 m n

lemma Q12_eq_H12_sq_sub (m n : ℤ) :
    Q12 m n = H12 m n ^ 2 - 12*(m*n)^2 := by
  unfold Q12 H12
  ring

/-- The single normal residual after signs/swaps have been removed. -/
def NormalResidual12 (m n a c : ℤ) : Prop :=
  PrimOppNonAxis m n ∧
  a*c = m*n ∧
  (m-n)*(m+n) = (a-c)*(3*a-c)

/-- Replace this with the project's existing residual/disjunction if it already exists. -/
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

/-- Normalize the eight residual cases to one case, preserving the measure. -/
theorem residual12_normalizes
    {m n a c : ℤ}
    (hprim : PrimOppNonAxis m n)
    (h : FactorIdentityResidual12 m n a c) :
    ∃ M N A C : ℤ,
      NormalResidual12 M N A C ∧ n12Measure M N = n12Measure m n := by
  -- Constructor split; the substitution table is in the markdown audit.
  -- Each branch is `refine ⟨..., ..., ..., ..., ?_, ?_⟩` followed by `ring_nf`.
  sorry

/-- In the normal case, the residual reconstructs a square of `Q12`. -/
theorem normalResidual12_to_square
    {m n a c : ℤ}
    (h : NormalResidual12 m n a c) :
    (c^2 - 3*a^2)^2 = Q12 m n := by
  -- From `(m-n)*(m+n)=(a-c)*(3*a-c)` and `a*c=m*n`, derive
  -- `H12 m n = 3*a^2+c^2`; then use `Q12_eq_H12_sq_sub`.
  sorry

/-- The eight-case residual also reconstructs a square witness. -/
theorem residual12_to_square
    {m n a c : ℤ}
    (hprim : PrimOppNonAxis m n)
    (h : FactorIdentityResidual12 m n a c) :
    ∃ b : ℤ, b^2 = Q12 m n := by
  rcases residual12_normalizes hprim h with ⟨M,N,A,C,hN,hmeas⟩
  -- If `M,N` is `(m,n)` this is direct. If it is `(n,-m)`, use
  -- the separate ring lemma `Q12 n (-m) = Q12 m n`.
  -- Alternatively prove the square reconstruction by an eight-case `ring_nf` split.
  sorry

end FLT.Kubert.N12
```

### 6.1 Small gcd/parity lemmas first

```lean
import Mathlib

namespace FLT.Kubert.N12

lemma coprime_mul_sq_sub_sq
    {m n : ℤ} (hcop : IsCoprime m n) :
    IsCoprime (m*n) (m^2 - n^2) := by
  -- Prime/divisibility proof: a common divisor of `m*n` and `m^2-n^2`
  -- divides both `m` and `n` locally.
  sorry

lemma coprime_sub_add_of_prim_opp
    {m n : ℤ} (hcop : IsCoprime m n) (hpar : OppParity m n) :
    IsCoprime (m-n) (m+n) := by
  -- Common divisor divides `2*m` and `2*n`; parity makes both factors odd.
  sorry

lemma normalResidual12_coprime_ac
    {m n a c : ℤ} (h : NormalResidual12 m n a c) :
    IsCoprime a c := by
  -- If `d | a,c`, then `d | a*c=m*n` and `d | m^2-n^2`.
  -- Use `coprime_mul_sq_sub_sq`.
  sorry

lemma normalResidual12_oppParity_ac
    {m n a c : ℤ} (h : NormalResidual12 m n a c) :
    OppParity a c := by
  -- `a*c=m*n` is even because `m,n` have opposite parity; combine with
  -- `normalResidual12_coprime_ac`.
  sorry

lemma coprime_a_sub_c_three_a_sub_c
    {a c : ℤ} (hcop : IsCoprime a c) (hpar : OppParity a c) :
    IsCoprime (a-c) (3*a-c) := by
  -- Common divisor divides `2*a` and `2*c`; parity makes both factors odd.
  sorry

end FLT.Kubert.N12
```

### 6.2 Four-corner decomposition lemmas

```lean
import Mathlib

namespace FLT.Kubert.N12

def PairwiseCoprime4 (x y z w : ℤ) : Prop :=
  IsCoprime x y ∧ IsCoprime x z ∧ IsCoprime x w ∧
  IsCoprime y z ∧ IsCoprime y w ∧ IsCoprime z w

/-- Cross decomposition of `a*c=m*n` for two primitive pairs. -/
theorem cross_decomposition
    {m n a c : ℤ}
    (hmn0 : m*n ≠ 0)
    (hmn : IsCoprime m n)
    (hac : IsCoprime a c)
    (hprod : a*c = m*n) :
    ∃ x y z w : ℤ,
      m = x*y ∧ n = z*w ∧ a = x*z ∧ c = y*w ∧
      x*y*z*w ≠ 0 ∧ PairwiseCoprime4 x y z w := by
  -- Concrete construction: take `x` to be the signed gcd/common divisor of `m` and `a`,
  -- write `m=x*y`, `a=x*z`, then use `a*c=m*n` and `IsCoprime y z` to prove
  -- `z | n`; write `n=z*w`; then prove `c=y*w`.
  sorry

lemma cross_identity_quadratic
    (x y z w : ℤ) :
    ((x*y - z*w)*(x*y + z*w)
      = (x*z - y*w)*(3*(x*z) - y*w)) ↔
    (x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0 := by
  constructor <;> intro h <;> nlinarith [h]

/-- The parity hypotheses imply exactly one even corner; the equation forces it to be `z`. -/
theorem cross_even_corner_is_z
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hparMN : OppParity (x*y) (z*w))
    (hparAC : OppParity (x*z) (y*w))
    (heq : (x*y - z*w)*(x*y + z*w)
         = (x*z - y*w)*(3*(x*z) - y*w)) :
    Even z ∧ Odd x ∧ Odd y ∧ Odd w := by
  -- First prove exactly one of `x,y,z,w` is even.
  -- Then four cases modulo 8 using the table in the audit.
  sorry

end FLT.Kubert.N12
```

Note: the `nlinarith [h]` in `cross_identity_quadratic` may need to be replaced by `ring_nf at h ⊢` depending on the local simplifier state. The lemma itself is a pure `ring` fact.

### 6.3 Discriminant and square-splitting lemmas

```lean
import Mathlib

namespace FLT.Kubert.N12

lemma cross_z_dvd_xsq_sub_wsq
    {x y z w : ℤ}
    (hyz : IsCoprime y z)
    (heqQ : (x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0) :
    z ∣ x^2 - w^2 := by
  -- Reduce `heqQ` modulo/divisibility by `z`:
  -- `z | (x^2-w^2)*y^2`, then cancel `y^2` using `IsCoprime y z`.
  sorry

lemma cross_xsq_ne_wsq
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hz : Even z) (hx : Odd x) (hy : Odd y) (hw : Odd w)
    (heqQ : (x^2 - w^2)*y^2 + 4*x*z*w*y - z^2*(3*x^2 + w^2) = 0) :
    x^2 ≠ w^2 := by
  -- If equal, coprime nonzero `x,w` force `x^2=w^2=1`.
  -- Then `heqQ` gives `z=x*w*y`, contradicting z even and x,w,y odd.
  sorry

lemma cross_discriminant_square
    {x y z w : ℤ}
    (hnz : x*y*z*w ≠ 0)
    (hpair : PairwiseCoprime4 x y z w)
    (hz : Even z) (hx : Odd x) (hy : Odd y) (hw : Odd w)
    (heq : (x*y - z*w)*(x*y + z*w)
         = (x*z - y*w)*(3*(x*z) - y*w)) :
    ∃ T : ℤ, T^2 = (3*x^2 - w^2)*(x^2 + w^2) := by
  -- Use `cross_identity_quadratic` to get `heqQ`.
  -- Discriminant identity:
  -- `(2*(x^2-w^2)*y + 4*x*z*w)^2
  --    = 4*z^2*(3*x^2 - w^2)*(x^2 + w^2)`.
  -- Use `cross_z_dvd_xsq_sub_wsq` to divide the square root by `2*z`.
  sorry

lemma gcd_two_quadratic_factors
    {x w : ℤ} (hcop : IsCoprime x w) (hx : Odd x) (hw : Odd w) :
    Nat.gcd ((3*x^2 - w^2).natAbs) ((x^2 + w^2).natAbs) = 2 := by
  -- Common divisor divides `4*x^2` and `4*w^2`; both factors are `2 mod 8`.
  sorry

lemma square_product_split_2mod8
    {x w T : ℤ}
    (hcop : IsCoprime x w) (hx : Odd x) (hw : Odd w)
    (hT : T^2 = (3*x^2 - w^2)*(x^2 + w^2)) :
    ∃ u v : ℤ,
      3*x^2 - w^2 = 2*u^2 ∧
      x^2 + w^2 = 2*v^2 := by
  -- Halves are coprime odd integers and their product is a square.
  -- Positivity of `3*x^2-w^2` follows from `hT` and `x^2+w^2>0`.
  sorry

end FLT.Kubert.N12
```

### 6.4 Pythagorean parametrization and descent

```lean
import Mathlib

namespace FLT.Kubert.N12

lemma half_sum_diff_coprime
    {x w R S : ℤ}
    (hR : R = (x+w)/2) (hS : S = (x-w)/2)
    (hx : Odd x) (hw : Odd w) (hcop : IsCoprime x w) :
    IsCoprime R S := by
  -- Better in Lean: introduce `R,S` by equations `x=R+S`, `w=R-S`
  -- instead of using integer division heavily.
  sorry

/-- Signed primitive Pythagorean parametrization in the exact form needed here. -/
theorem primitive_pythagorean_to_Q12
    {R S u v : ℤ}
    (hRS0 : R*S ≠ 0)
    (hcop : IsCoprime R S)
    (hpar : OppParity R S)
    (hv : R^2 + S^2 = v^2)
    (hu : u^2 = R^2 + 4*R*S + S^2) :
    ∃ p q : ℤ,
      p*q ≠ 0 ∧ IsCoprime p q ∧ OppParity p q ∧ u^2 = Q12 p q := by
  -- Apply primitive Pythagorean parametrization to `R^2+S^2=v^2`.
  -- The two signed legs are `p^2-q^2` and `2*p*q`, up to swap/sign.
  -- Swap is harmless because `R^2+4RS+S^2` is symmetric; sign is absorbed by `q ↦ -q`.
  sorry

lemma pythagorean_measure_bound
    {p q v x w : ℤ}
    (hpq : p*q ≠ 0)
    (hv : v^2 = (x^2 + w^2)/2)
    (hvw : (p^2 + q^2)^2 = v^2)
    (hx0 : x ≠ 0) (hw0 : w ≠ 0) (hne : x^2 ≠ w^2) :
    2*(p*q).natAbs < (x*w).natAbs := by
  -- Equivalent integer absolute-value proof:
  -- `2*|p*q| ≤ p^2+q^2 = |v|`, and `|v| < |x*w|`.
  sorry

/-- Main descent from the normalized residual to a smaller quartic square solution. -/
theorem normalResidual12_descent_square
    {m n a c : ℤ}
    (h : NormalResidual12 m n a c) :
    ∃ p q b : ℤ,
      SquareSol12 p q b ∧ n12Measure p q < n12Measure m n := by
  -- 1. `normalResidual12_coprime_ac` and `normalResidual12_oppParity_ac`.
  -- 2. `cross_decomposition` gives `m=xy,n=zw,a=xz,c=yw`.
  -- 3. `cross_even_corner_is_z` gives `z` even and `x,y,w` odd.
  -- 4. `cross_discriminant_square` gives square product in `x,w`.
  -- 5. `square_product_split_2mod8` gives `u,v`.
  -- 6. Define `R,S` by `x=R+S`, `w=R-S`.
  -- 7. `primitive_pythagorean_to_Q12` gives `p,q,b=u`.
  -- 8. Measure inequality: `|p*q| < |m*n|`.
  sorry

/-- Descent from the original eight-case residual. -/
theorem residual12_descent_square
    {m n a c : ℤ}
    (hprim : PrimOppNonAxis m n)
    (h : FactorIdentityResidual12 m n a c) :
    ∃ p q b : ℤ,
      SquareSol12 p q b ∧ n12Measure p q < n12Measure m n := by
  rcases residual12_normalizes hprim h with ⟨M,N,A,C,hN,hmeas⟩
  rcases normalResidual12_descent_square hN with ⟨p,q,b,hsol,hlt⟩
  refine ⟨p,q,b,hsol,?_⟩
  simpa [hmeas] using hlt

end FLT.Kubert.N12
```

### 6.5 Final well-founded closure

The descent returns a smaller **quartic square solution**, not immediately a smaller displayed residual. Therefore the final closure should use the already-checked reduction wrapper from square solutions to residuals.

```lean
import Mathlib

namespace FLT.Kubert.N12

/-- Clean final theorem parameterized by the already-proved reduction. -/
theorem no_squareSol12_of_square_to_residual
    (square_to_residual :
      ∀ {m n b : ℤ}, SquareSol12 m n b -> ∃ a c : ℤ, FactorIdentityResidual12 m n a c) :
    ¬ ∃ m n b : ℤ, SquareSol12 m n b := by
  -- Well-founded descent on `n12Measure m n`.
  -- Pick a solution of minimal measure.
  -- Apply `square_to_residual`, then `residual12_descent_square`, contradiction.
  sorry

/-- Residual impossibility, using the square-to-residual reduction. -/
theorem no_factorIdentityResidual12
    (square_to_residual :
      ∀ {m n b : ℤ}, SquareSol12 m n b -> ∃ a c : ℤ, FactorIdentityResidual12 m n a c) :
    ¬ ∃ m n a c : ℤ,
      PrimOppNonAxis m n ∧ FactorIdentityResidual12 m n a c := by
  intro h
  rcases h with ⟨m,n,a,c,hprim,hres⟩
  rcases residual12_to_square hprim hres with ⟨b,hb⟩
  exact no_squareSol12_of_square_to_residual square_to_residual ⟨m,n,b,hprim,hb⟩

end FLT.Kubert.N12
```

In the project, `square_to_residual` should be instantiated by the already-checked chain around

```text
factorIdentityResidual_of_square_12
rationalCoverSignedResidual_factorIdentityResidual
bridge_N12_factorIdentityResidual
```

depending on which one has the exact `SquareSol12 -> FactorIdentityResidual12` shape.

## 7. If this should remain an arithmetic boundary

If the project does not want to formalize the full descent right now, the cleanest boundary is **not** the eight-case factor residual. The cleanest boundary is the quartic square theorem:

```lean
import Mathlib

namespace FLT.Kubert.N12

def H12 (m n : ℤ) : ℤ :=
  m^2 + 4*m*n - n^2

def Q12 (m n : ℤ) : ℤ :=
  m^4 + 8*m^3*n + 2*m^2*n^2 - 8*m*n^3 + n^4

def OppParity (x y : ℤ) : Prop :=
  Odd (x + y)

/-- Arithmetic boundary for the N=12 non-axis quartic. -/
axiom no_primitive_nonaxis_Q12_square :
  ¬ ∃ m n b : ℤ,
    m*n ≠ 0 ∧ IsCoprime m n ∧ OppParity m n ∧ b^2 = Q12 m n

end FLT.Kubert.N12
```

This boundary is mathematically cleaner because:

1. every residual reconstructs a square witness;
2. the descent naturally produces a smaller square witness;
3. the statement is the genus-one/quartic rational-points assertion behind the N=12 cover;
4. the eight signed factor identities are an implementation artifact of the split, not the natural arithmetic endpoint.

If you prefer a rational-points boundary, use the affine quartic:

```text
Y^2 = X^4 + 8*X^3 + 2*X^2 - 8*X + 1,
```

with the assertion that all rational points correspond to axis/degenerate cases after the Kubert map. But for Lean integration with the current integer residual, the primitive integer square theorem above is probably easier.

I would not describe this as Mazur-hard. It is a genus-one descent, and the descent above is elementary. The hard part in Lean is not the theorem's mathematical depth; it is organizing the coprime decomposition and signed Pythagorean parametrization without drowning in integer-unit bookkeeping.

## 8. What structure must be retained in the Lean interface

The residual has not lost fatal structure, but the interface should retain or quickly derive these facts:

```text
m*n ≠ 0,
gcd(m,n)=1,
m,n opposite parity,
a*c = ±m*n,
the exact signed factor identity,
square_to_residual reduction for the smaller quartic solution.
```

Helpful derived facts worth caching as fields or lemmas:

```text
gcd(a,c)=1,
a,c opposite parity,
gcd(m-n,m+n)=1,
gcd(a-c,3*a-c)=1       -- in the normalized branch
residual_to_square       -- reconstructs b^2 = Q12(m,n)
```

The original `r,s` split does not need to remain in the final descent once it has produced the residual, except that it may already contain `gcd(a,c)=1` and parity facts. Keeping those as explicit hypotheses can save proof work, but they are recoverable from the residual plus primitive hypotheses.

The one thing that **must** remain available is the loop-closing theorem:

```text
SquareSol12(m,n,b) -> ∃ a c, FactorIdentityResidual12(m,n,a,c).
```

Without that theorem, the descent from a residual only gives a smaller square solution, not a contradiction to the residual statement itself.

## 9. Recommended immediate formalization order

1. Define `NormalResidual12` and prove the eight-case normalization table by `ring`.
2. Prove `Q12_eq_H12_sq_sub` and `normalResidual12_to_square`.
3. Prove `normalResidual12_coprime_ac` and `normalResidual12_oppParity_ac`.
4. Prove the four-corner decomposition from `a*c=m*n` with primitive pairs.
5. Prove the mod-8 corner lemma `cross_even_corner_is_z`.
6. Prove the quadratic expansion and `z ∣ x^2-w^2`.
7. Prove the discriminant square product.
8. Prove the `2 mod 8` square-product split.
9. Prove the signed primitive Pythagorean parametrization in exactly the needed form.
10. Prove the measure inequality.
11. Close by well-founded descent using `factorIdentityResidual_of_square_12` or whichever checked wrapper has the square-to-residual shape.

The most error-prone Lean points will be:

```text
- signed gcd/cross decomposition over ℤ;
- cancelling `z^2` from the discriminant square, which is why `z ∣ x^2-w^2` should be a separate lemma;
- signed primitive Pythagorean parametrization;
- absolute-value/natAbs inequalities for the descent measure.
```

The core mathematical route is sound only if all primitive/parity/non-axis hypotheses are present. If the current `NonAxisFactorIdentityResidual` theorem statement omits any of them, add them or prove a wrapper theorem that supplies them from the signed-cover context before attempting the descent.
