# N13 at two: the ramified first jet, not a 16-class table

Design audit, 2026-07-27.

## Verdict

The useful part of the seven PARI ray characters in
`N13_DIRECT_LOCAL_REPORT.md` has a small intrinsic description.

Put

```text
i  = zeta,
pi = 1-i,
F  = Q_2(i),
K  = F(theta).
```

Then

```text
pi^2 = -2i,                 v_pi(2)=2,
g(T) = T^3+2T^2-T-1-2iT(T+1),
g(theta)=0.
```

The reduction of `g` is `T^3+T+1`, so `K/F` is the unramified cubic
extension and its residue field is

```text
k = F_8 = F_2[alpha]/(alpha^3+alpha+1).
```

The decisive quotient is only the first ramified jet

```text
O_K / pi^2  =  k[epsilon]/(epsilon^2),
i            |-> 1+epsilon,
theta        |-> alpha.
```

If a unit maps to `r+epsilon*c`, define

```text
kappa(r+epsilon*c) = c/r in k.
```

It is a logarithmic character:

```text
kappa(uv) = kappa(u)+kappa(v),
kappa(u^2)=0,
kappa(q)=0 for q in Q_2^*.
```

Thus it descends to the fake local square-class target.  Its three
`F_2` coordinates are exactly the first three PARI characters, up to the
displayed change of basis below.  One equation in `F_8` replaces three
binary equations and reduces the sixteen global representatives to the two
classes `1` and `e2*a*q`.  The already-proved exact identity

```text
(e2*a*q) * (zeta*e1*a)^2 = 13
```

makes these two classes equal in the fake target.

The fourth observed character is real but is not needed for this reduction.
It is the trace of the next surviving principal-unit coefficient.  Its
restriction to the four global candidate generators duplicates one of the
three coordinates of `kappa`.

## 1. Corrections to the existing report

The calculations in `N13_DIRECT_LOCAL_REPORT.md` are consistent, but their
interpretation can be sharpened.

1. The first four rows of the candidate matrix have rank **three**, not
   four: rows three and four are equal on
   `zeta,e1,e2,a*q`.  This is why four vanishing ray coordinates leave two
   global classes rather than one.

2. The GP function

   ```text
   z / 2^(v_P(z)/2)
   ```

   silently presupposes even `P`-valuation.  That holds for the sixteen
   candidates and for `x-theta`: an integral `x` gives a unit, while a
   nonintegral `x` has
   `v_P(x-theta)=v_P(x)=2 v_2(x)`.  It should be a hypothesis of any formal
   statement, not part of a total definition.

3. Sampling integral `x mod 2^10` is unnecessary.  In fact
   `f(x)=1 mod 8` for every `x in Z_2`, so every integral `x` has a curve
   lift.  More importantly, the first-jet containment below holds for every
   `x in Q_2`, whether or not `f(x)` is a square.

4. The modulus `P^5` is the correct stabilization depth because
   `v_P(2)=2` and

   ```text
   u in 1+P^5  =>  u is a square.
   ```

   This last implication is a strong Hensel statement.  PARI's
   `idealstar` computation does not itself formalize it.

5. The power basis has index divisible by two, but the Gaussian cubic
   presentation avoids that obstruction.  Over `Q_2(i)`, `g` has separable
   irreducible reduction `T^3+T+1`; hence its power basis is the natural
   unramified local basis.

## 2. Exact Gaussian identities

The sextic is

```text
f = A^2+B^2,
A = T^3+2T^2-T-1,
B = 2T(T+1).
```

In the chosen sextic algebra the order-four unit satisfies `i=zeta` and

```text
A(theta)-i B(theta)=0.
```

Exact reduction from the degree-six power basis to
`1,theta,theta^2` over `Q(i)` gives

```text
zeta = i,

e1 = 1 - theta^2 + (i-1) theta,

e2 = 1 + i theta^2 + (1+2i) theta,

a  = 1 - i theta^2 - (1+i) theta,

q  = 2 - 3i.
```

These were rechecked by exact polynomial remainder modulo `g`, not by
floating-point recognition.  They are much smaller Lean certificates than
the original degree-five expressions.

## 3. The first-jet character

Let `D=k[epsilon]/epsilon^2`, implemented by
`TrivSqZeroExt k k`.  For a dual unit `z`, set

```lean
def firstJet (z : D) (hz : z.fst != 0) : k :=
  z.snd / z.fst
```

The multiplication law in a square-zero extension gives

```text
(r+epsilon*c)(s+epsilon*d)
  = rs + epsilon(rd+cs),
```

and therefore

```text
firstJet (z*w) = firstJet z + firstJet w.
```

In characteristic two,

```text
(r+epsilon*c)^2 = r^2,
```

so squares have zero first jet.  Scalars from `Q_2` reduce through
`F_2 -> F_8` with zero epsilon coefficient and also have zero first jet.

No completeness, valuation classification, local norm, or Hensel theorem is
needed for these facts.

### Exact values on the global generators

Write `alpha^3+alpha+1=0`.  Reducing the Gaussian identities above under

```text
i     |-> 1+epsilon,
theta |-> alpha
```

gives

```text
kappa(zeta) = 1,
kappa(e1)   = alpha^2,
kappa(e2)   = alpha+alpha^2.
```

For the last two generators,

```text
kappa(a) = 1+alpha+alpha^2,
kappa(q) = 1,
kappa(a*q) = alpha+alpha^2.
```

For

```text
z(i,j,k,s)=zeta^i e1^j e2^k (a*q)^s
```

with binary exponents,

```text
kappa(z(i,j,k,s))
  = i + j alpha^2 + (k+s)(alpha+alpha^2).
```

The three elements

```text
1, alpha^2, alpha+alpha^2
```

are `F_2`-linearly independent.  Hence

```text
kappa(z(i,j,k,s))=0
  iff
i=0, j=0, k=s.
```

This is the non-enumerative `16 -> 2` argument.

### Relation with the PARI basis

The additional exact GP audit used the three first-layer elements

```text
1+pi, 1+pi*theta, 1+pi*theta^2.
```

Their first three ray coordinates are respectively

```text
(0,0,1), (1,0,1), (1,1,0).
```

This matrix is invertible over `F_2`.  If
`b=b0+b1*alpha+b2*alpha^2`, the PARI coordinates are

```text
chi1=b1+b2,
chi2=b2,
chi3=b0+b1.
```

Thus the first three printed ray characters are exactly a choice of basis
for `kappa`; their simultaneous vanishing is canonical even though the
individual PARI coordinates are not.

## 4. The two valuation regimes

The local statement should be formulated for the fake class of
`delta=x-theta`, with the rational scalar removed in the nonintegral case.

### Regime I: integral `x`

Assume `v_2(x)>=0`.  Then `x` belongs to `Z_2` and reduces to
`xbar in F_2`.  Since `alpha` is neither zero nor one,

```text
xbar-alpha != 0.
```

In the first-jet quotient,

```text
x-theta |-> (xbar-alpha) + epsilon*0.
```

Consequently

```text
kappa(x-theta)=0.
```

The same residue observation proves that `x-theta` is a local unit.  This is
the complete integral-regime proof; the equation `y^2=f(x)` is not used.

A Lean-facing statement is:

```lean
theorem firstJet_x_sub_theta_of_integral
    (xbar : ZMod 2) :
    fst (scalar xbar - alphaDual) != 0 /\
    firstJet (scalar xbar - alphaDual) = 0
```

where `alphaDual=inl alpha`.

### Regime II: nonintegral `x`

Assume `v_2(x)<0`.  Then `x!=0` and

```text
t=x^-1 belongs to 2 Z_2.
```

Factor

```text
x-theta = x (1-t theta).
```

The first factor is a rational scalar and vanishes in the fake target.
Since `t=0` in `O_K/pi^2` (the ideals `(2)` and `(pi^2)` agree),

```text
1-t theta |-> 1,
```

and hence

```text
kappa(1-t theta)=0.
```

For the direct, non-fake target, `v_P(x)=2v_2(x)` is even; after the standard
valuation normalization the same first-jet conclusion holds.

A Lean-facing semantic statement is:

```lean
theorem firstJet_one_sub_t_theta
    (tbar : ZMod 2) (ht : tbar = 0) :
    firstJet (1 - scalar tbar * alphaDual) = 0
```

The actual `Q_2` adapter only has to prove that `v_2(t)>0` implies
`tbar=0`.

## 5. The fourth character

The seven unit squareclasses have the structural filtration

```text
O_K^*/O_K^{*2}
  ~= k              -- coefficient at pi
      + k            -- coefficient at pi^3
      + F_2.         -- Artin--Schreier cokernel at pi^4
```

The dimensions are `3+3+1=7`.

Successive squaring explains the missing levels:

```text
(1+pi*r)^2
  = 1 + pi^2 r^2 + pi^3 r - pi^4 r       mod pi^5,

(1+pi^2*s)^2
  = 1 + pi^4(s^2+s)                      mod pi^5.
```

After `kappa=0`, multiply by a square to put the class in `U_3`.
For

```text
u = 1+pi^3*b mod pi^4,
```

the fourth intrinsic character is

```text
lambda(u)=Tr_{F_8/F_2}(b).
```

It is also detected by the relative norm:

```text
N_{K/F}(u)
  = 1+pi^3 Tr(b) mod pi^4.
```

The GP coordinates of

```text
1+pi^3, 1+pi^3 theta, 1+pi^3 theta^2
```

have fourth entries `1,0,0`, exactly

```text
Tr(1)=1, Tr(alpha)=0, Tr(alpha^2)=0.
```

Thus the four observed vanishings are intrinsically

```text
kappa=0 in F_8                         -- three binary conditions
lambda=0 in F_2.                       -- one binary condition
```

### Structural proof of `lambda=0`

The relative norm of `x-theta` is

```text
N_{K/F}(x-theta)=g(x).
```

It is a rational scalar modulo squares in both regimes.

For integral `x`, write

```text
c=x(x+1)/2 in Z_2,
B(x)=4c,
q0=A(x)-4c in Q_2^*.
```

Then

```text
g(x)-q0 = 4c(1-i)=4c*pi,
v_pi(g(x)/q0-1)>=5.
```

For nonintegral `x`, put `t=x^-1 in 2Z_2`.  Then

```text
g(x)=x^3 H(t),

H(t)=1+(2-2i)t+(-1-2i)t^2-t^3,
h(t)=1-3t^2-t^3 in Q_2^*,

H(t)-h(t)=2(1-i)t(1+t)=2*pi*t(1+t),
v_pi(H(t)/h(t)-1)>=5.
```

The strong square lemma `U_5 subset K^{*2}` therefore makes the relative
norm rational modulo squares.  After `kappa=0`, this is equivalent to
`lambda=0`.

This proves all four characters without checking any of the sixteen global
classes.  It is optional for the shortest N13 descent, because the
`F_8`-valued equation `kappa=0` already yields
`i=j=0,k=s`, and the scalar identity closes the remaining fake class.

## 6. Hensel and valuation API audit

Useful existing Mathlib declarations:

```text
Padic.valuation
Padic.addValuation
Padic.valuation_mul
Padic.valuation_inv
Padic.valuation_pow
Padic.norm_le_one_iff_val_nonneg

PadicInt.toZMod
PadicInt.toZModPow
PadicInt.ker_toZMod
PadicInt.ker_toZModPow

TrivSqZeroExt.fst_mul
TrivSqZeroExt.snd_mul
TrivSqZeroExt.fst_pow
TrivSqZeroExt.snd_pow
TrivSqZeroExt.inr_mul_inr

PadicInt.hensels_lemma
HenselianRing
IsAdicComplete.henselianRing
```

Two cautions:

* `Padic.valuation` and `padicValRat` give zero a finite value.  For a
  regime theorem use `Padic.addValuation`, or split with
  `Padic.norm_le_one_iff_val_nonneg` and handle `x=0` before inversion.

* `PadicInt.hensels_lemma` is specialized to `Z_p`.  The abstract
  `HenselianRing` interface only lifts a root whose derivative is a unit.
  For `T^2-u` at residue characteristic two, the derivative is not a unit,
  so neither directly proves `U_5 subset K^{*2}` for this degree-six local
  field.

The missing reusable analytic lemma is:

```lean
theorem isSquare_of_one_sub_mem_pi_pow_five
    {u : O_K^x}
    (h : u-1 in P^5) :
    IsSquare (u : K)
```

Its proof is the strong Hensel inequality at the approximate root `1`:

```text
v_pi(1-u) > 2 v_pi(2) = 4.
```

It can be implemented either by generalizing the Newton proof in
`Mathlib.NumberTheory.Padics.Hensel` to a complete discretely valued field,
or by the convergent binomial series.  It should not block the first-jet
descent because Sections 3--4 are purely algebraic.

## 7. Shortest Lean layering

Recommended order:

```text
N13GaussianCubic
  g over Q(i), sextic/cubic equivalence
  the five small identities for zeta,e1,e2,a,q

N13TwoJet
  k=F_8, Dual=k[epsilon]/epsilon^2
  firstJet multiplication/square/scalar lemmas
  exact generator values and F_8 linear independence

N13TwoJetLocal
  integral/nonintegral Q_2 regime adapter
  local fake image lies in ker(firstJet)

N13FakeTwoDescent
  global S-unit envelope
  firstJet equation gives two representatives
  N13SexticSquareclass collapses them to one fake class
```

Only if a complete identification with the seven PARI characters is later
needed:

```text
N13TwoUnitFiltration
  pi-adic normal form through pi^5
  U_5 square lemma
  lambda=trace and full local squareclass dimension
```

The strongest immediately formalizable nonempty result is `N13TwoJet`:
it needs only `AdjoinRoot`, `ZMod 2`, and `TrivSqZeroExt`.  It proves the
actual `16 -> 2` linear reduction and is not a placeholder for completion
infrastructure.
