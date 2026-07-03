# Q3177 (dm1): Paper 2 Round 8 — Resolving Two Bottlenecks

Date: 2026-07-03

## Executive answer

R8 has two separate jobs.

The first job is analytic: resolve the Hickerson--Mortenson/Appell--Lerch description of

```text
f_{1,3,4}(X,-X^3,X)
```

at a torsion specialization.  The safe conclusion is:

```text
D-A = -f_{1,3,4}(X,-X^3,X)
```

is not an honest weight-1 theta series.  It is an indefinite-theta / mixed mock-Jacobi object.  The failure of multiplicativity and the large values such as `chi(17)=9` are exactly what one should expect after the R7/R8 computation.

The second job is elementary and more important for Paper 2: prove the mechanism without invoking HM at all.  The sigma reflection

```text
sigma_k(r) = -(6k+1)-r
```

preserves the row quadratic exactly, flips the sign `(-1)^r`, has no integral fixed point, and cancels the interior of each row.  The only surviving atoms are the two slabs

```text
Slab+ = { k >= 0,  r <= -(6k+1) },
Slab- = { k <= -1, r >= -6k }.
```

Thus the missing kernel is already proved in elementary form as

```text
MissingKernel = Theta_u * Theta_v * F_slab,
```

where `F_slab` is the signed slab sum.  HM is only needed to name `F_slab` analytically as a mixed mock-Jacobi/Appell--Lerch object.

---

## Bottleneck 1. HM torsion resolution

### 1.1 Definitions and the five Appell--Lerch terms

Use the standard notation

```text
j(x;q) = (x;q)_infty (q/x;q)_infty (q;q)_infty,

m(x,q,z) = 1/j(z;q) * sum_{r in Z} (-1)^r q^{r(r-1)/2} z^r
                              / (1 - q^{r-1}xz).
```

For the Hecke-type double sum, use

```text
f_{a,b,c}(x,y,q)
  = sum_{sg(r)=sg(s)} sg(r)(-1)^{r+s} x^r y^s
      q^{a*r(r-1)/2 + b*r*s + c*s(s-1)/2}.
```

For `(a,b,c)=(1,3,4)`, the discriminant is

```text
b^2 - ac = 9 - 4 = 5.
```

The Appell--Lerch part obtained by substituting `(1,3,4)` into the HM `g_{a,b,c}` expression is

```text
G_{1,3,4}(x,y,q)
  = j(x;q) m(-q^2 y/x^3, q^5, -1)
    + sum_{t=0}^3 (-x)^t q^{t(t-1)/2} j(q^{3t}y; q^4)
        m(q^{14-5t} x^4/y^3, q^20, -1).
```

Equivalently, the five Appell--Lerch terms are

```text
H0 =  j(x;q)                         m(-q^2 y/x^3,    q^5,  -1),
H1 =  j(y;q^4)                       m( q^14 x^4/y^3, q^20, -1),
H2 = -x j(q^3y;q^4)                  m( q^9  x^4/y^3, q^20, -1),
H3 =  x^2 q j(q^6y;q^4)              m( q^4  x^4/y^3, q^20, -1),
H4 = -x^3 q^3 j(q^9y;q^4)            m( q^-1 x^4/y^3, q^20, -1).
```

The full HM form is

```text
f_{1,3,4}(x,y,q) = G_{1,3,4}(x,y,q) + T_{1,3,4}(x,y,q),
```

where `T_{1,3,4}` is a finite theta quotient.  For Paper 2, the Appell--Lerch terms above are the computable mock part, and the finite quotient is the modular theta part.

Important caveat: the published HM theorem should be quoted with its exact convention.  Some versions state a closed theorem first for `f_{n,n+p,n}` and special divisibility families, while the general `(a,b,c)` formula is implemented through the same `g_{a,b,c}` Appell--Lerch expression plus a finite theta correction.  So the paper should not invent a theta quotient from memory.  It should either quote the exact HM/Mortenson--Zwegers general theorem being used, or define

```text
T_{1,3,4} := f_{1,3,4} - G_{1,3,4}
```

and then evaluate that finite quotient by the residue algorithm.

### 1.2 Specializing `x=X`, `y=-X^3`

First keep the nome `q` separate from the monomial `X`.  Then

```text
G_{1,3,4}(X,-X^3,q)
  = j(X;q) m(q^2, q^5, -1)
    + j(-X^3;q^4) m(-q^14 X^-5, q^20, -1)
    - X j(-q^3X^3;q^4) m(-q^9 X^-5, q^20, -1)
    + X^2 q j(-q^6X^3;q^4) m(-q^4 X^-5, q^20, -1)
    - X^3 q^3 j(-q^9X^3;q^4) m(-q^-1 X^-5, q^20, -1).
```

Now tie the monomial to the nome by setting `X=q`.  The Appell--Lerch part becomes

```text
G_{1,3,4}(q,-q^3,q)
  = j(q;q) m(q^2, q^5, -1)
    + j(-q^3;q^4) m(-q^9,  q^20, -1)
    - q j(-q^6;q^4) m(-q^4,  q^20, -1)
    + q^3 j(-q^9;q^4) m(-q^-1, q^20, -1)
    - q^6 j(-q^12;q^4) m(-q^-6, q^20, -1).
```

Since

```text
j(q;q)=0,
```

the first displayed product must be treated by a limiting convention.  With the standard choice `z=-1`, the factor

```text
m(q^2,q^5,-1)
```

is finite as a formal Appell--Lerch value, so this first term contributes `0` directly.  If a different but equivalent HM representation moves a simple pole into the paired `m`-factor, then the finite part is computed by the derivative formula below.

### 1.3 The Jacobi derivative and the `0 * infinity` finite part

Let

```text
J_1 = (q;q)_infty.
```

The Jacobi triple product gives the first-order expansion

```text
j(q e^eps; q) = eps * J_1^3 + O(eps^2).
```

More generally, if

```text
M(eps) = m(alpha e^{lambda eps}, Q, z)
```

has a simple pole at `eps=0`, and the pole comes from the unique integer `r0` satisfying

```text
Q^{r0-1} alpha z = 1,
```

then the residue is

```text
M(eps)
  = - 1/(lambda eps) * (-1)^{r0} Q^{r0(r0-1)/2} z^{r0} / j(z;Q)
    + O(1).
```

Therefore

```text
lim_{eps -> 0} j(qe^eps;q) M(eps)
  = - J_1^3/lambda * (-1)^{r0} Q^{r0(r0-1)/2} z^{r0} / j(z;Q).
```

This is the exact `eta^3` contribution: since `J_1 = q^{-1/24} eta(tau)`, the derivative term is an `eta^3`-type theta factor, up to the usual power of `q`.

For a theta quotient with a denominator `j(qe^eps;q)`, use the reciprocal rule:

```text
FP_{eps=0} N(eps) / j(qe^eps;q)
  = N'(0) / J_1^3
```

whenever `N(0)=0`.  If `N(0) != 0`, the quotient has an actual pole and the chosen HM representation is not the correct finite specialization until the pole is cancelled against another term.

### 1.4 Closed computable form for `D-A`

With the convention above, the clean closed form is

```text
D - A
  = -f_{1,3,4}(q,-q^3,q)
  = -R_0(q) - H_1(q) - H_2(q) - H_3(q) - H_4(q) - T^*(q),
```

where

```text
R_0(q)
  = 0
```

for the standard `z=-1` specialization, and in any equivalent representation containing a genuine `0 * infinity` collision,

```text
R_0(q)
  = - J_1^3/lambda * (-1)^{r0} Q^{r0(r0-1)/2} z^{r0}/j(z;Q).
```

The four nonzero Appell--Lerch terms are

```text
H_1(q) =  j(-q^3;q^4)    m(-q^9,  q^20, -1),
H_2(q) = -q j(-q^6;q^4)  m(-q^4,  q^20, -1),
H_3(q) =  q^3 j(-q^9;q^4) m(-q^-1, q^20, -1),
H_4(q) = -q^6 j(-q^12;q^4)m(-q^-6, q^20, -1).
```

The finite theta quotient is

```text
T^*(q) = FP_{X=q} T_{1,3,4}(X,-X^3,q).
```

This is explicitly computable: expand every theta quotient in `T_{1,3,4}` along `X=q e^eps`, replace every vanishing `j(qe^eps;q)` by `eps J_1^3`, cancel poles, and retain the constant term in `eps`.

Thus the repaired term is

```text
Corr_tau
  = -Theta_u Theta_v f_{1,3,4}(q,-q^3,q)
  = Theta_u Theta_v * (D-A)
```

with

```text
D-A = -R_0 - H_1 - H_2 - H_3 - H_4 - T^*.
```

Analytic classification:

```text
H_i terms        = Appell--Lerch / mock-Jacobi part,
R_0 and T^*      = eta^3 and theta-quotient modular part,
Corr_tau         = theta factors times mixed mock-Jacobi correction.
```

### 1.5 Even support and the natural nome

The observed inner coefficients are supported only at even exponents:

```text
F(q) = sum_{n >= 0} a[n] q^{2n}.
```

The natural normalization is therefore

```text
Q = q^2,
F(q) = F_even(Q).
```

This is a pullback `tau -> 2tau`, not evidence for honest weight-1 modularity.  No Dedekind eta factor is required merely to explain even support.  Eta factors enter only from Jacobi derivatives such as

```text
j(qe^eps;q)'|_{eps=0} = (q;q)_infty^3 = q^{-1/8} eta(tau)^3.
```

So the recommended paper normalization is:

```text
1. write the slab series in Q=q^2;
2. record any derivative terms as eta(tau)^3 times a q-power;
3. do not force a Dirichlet-character or multiplicative weight-1 interpretation.
```

The R8 multiplicativity failure is then not a negative result; it is a diagnostic confirming that the object is mixed mock-Jacobi rather than an honest theta series.

---

## Bottleneck 2. Atom-to-key dictionary

### 2.1 The correct triangular root variable

The inner exponent is

```text
Q_inner(k,r) = 2k(2k+1) + r(r+6k+1).
```

Complete the `r`-quadratic by setting

```text
n = r + 3k + 1,
A = 2n - 1 = 2r + 6k + 1.
```

Then

```text
r(r+6k+1) = (A^2 - (6k+1)^2)/4,
```

and

```text
Q_inner(k,r)
  = 2k(2k+1) + (A^2 - (6k+1)^2)/4
  = (A^2 - 20k^2 - 4k - 1)/4.
```

Since

```text
A = 2r + 6k + 1 = 2(r+3k+1)-1,
```

`A` is always odd.  This is the structural proof of the all-anchors-odd observation in the sigma/slab variables.

Thus the atom-to-key anchor dictionary should be

```text
anchor A = 2r + 6k + 1,
n        = r + 3k + 1.
```

If some older code reports the raw anchor as `2r-1`, then that is a different coordinate.  The triangular root coordinate of the row quadratic is the shifted root above.

### 2.2 Action of sigma on the anchor

The row reflection is

```text
sigma_k(r) = -(6k+1)-r.
```

It fixes `k`, hence sends

```text
n = r+3k+1
```

to

```text
n' = sigma_k(r)+3k+1
   = -(6k+1)-r+3k+1
   = -r-3k
   = 1-n.
```

Therefore

```text
A' = 2n' - 1 = 2(1-n)-1 = -A.
```

So in the natural triangular-root anchor,

```text
sigma: A -> -A.
```

This is the cleanest possible affine involution: the constant is `C=0`.

If instead one uses the unshifted coordinate

```text
A_raw = 2r - 1,
```

then

```text
A_raw' = 2sigma_k(r)-1
       = -2r - 12k - 3
       = (-12k-4) - A_raw.
```

So in that raw coordinate the affine constant is

```text
C(k) = -12k - 4.
```

This is why the shifted triangular root is the right key variable: it removes the row-dependent affine constant and makes sigma simply `A -> -A`.

### 2.3 Boundary divergence per key

The key is

```text
K(x) = (hblock(x), anchor(x)),
```

with

```text
hblock = (|k| + 1 - |u+v-1| + carry)//3,

carry = 1 if |k| = 0 and 1 <= (u-v) + |u+v-1|, else 0,

anchor = 2r + 6k + 1.
```

Let

```text
E(u,v,k,r)
  = 9*(5v^2 - 7v + 5u^2 - 3u
       + 2k(2k+1) + r(r+6k+1)).
```

Let `sgn_atom(u,v,k,r)` be the full signed coefficient from the residual kernel.  If no additional code sign is present, the inner sign is `(-1)^r`.

Then the per-key generating function is

```text
G_K(q)
  = sum_{(u,v,k,r) in Slab+ union Slab-}
        sgn_atom(u,v,k,r) * 1_{K(u,v,k,r)=K} * q^{E(u,v,k,r)}.
```

Coefficientwise,

```text
keyWeight(e,K) = [q^e] G_K(q).
```

This is the precise key-level boundary divergence.  The total missing kernel is obtained by summing over all keys:

```text
MissingKernel(q) = sum_K G_K(q).
```

If `u` and `v` are not part of the key projection, their sums factor out as `Theta_u Theta_v`, leaving the inner slab series in `(k,r)`.

---

## Q3. Disc-20 form and the Pell connection

### 3.1 Fundamental unit

The form

```text
4k^2 + 6kr + r^2
```

has discriminant

```text
D = 6^2 - 4*4*1 = 20.
```

The corresponding quadratic order is

```text
O_20 = Z[sqrt(5)],
```

which is the conductor-2 order inside the maximal order

```text
O_5 = Z[(1+sqrt(5))/2].
```

Let

```text
epsilon = (1+sqrt(5))/2.
```

Then

```text
epsilon^3 = 2 + sqrt(5)       has norm -1 and lies in O_20,
epsilon^6 = 9 + 4sqrt(5)      has norm +1 and lies in O_20.
```

For the proper automorph group of an oriented indefinite form of discriminant `20`, the norm-`+1` generator is therefore

```text
epsilon_20^+ = 9 + 4sqrt(5).
```

The Pell matrix has eigenvalues

```text
9 ± 4sqrt(5),
```

so it is exactly multiplication by `epsilon^6` on the associated real quadratic line.

There is no division in `9+4sqrt(5)`.  The clean relation is

```text
9 + 4sqrt(5) = ((1+sqrt(5))/2)^6 = (2+sqrt(5))^2.
```

### 3.2 Relation to the original discriminant-5 story

The field has always been

```text
K = Q(sqrt(5)).
```

The difference is the order:

```text
discriminant 5:   maximal order Z[(1+sqrt(5))/2],
discriminant 20:  conductor-2 order Z[sqrt(5)].
```

The slab form is a conductor-2 incarnation of the same `Q(sqrt(5))` Pell dynamics.  The stabilizer `<epsilon^6>` appearing in the coset story is precisely the norm-`+1` unit of the conductor-2 order.

So the disc-20 form is not a different field.  It is the same field with a stricter integrality condition.

### 3.3 Correct integral norm representation

The correct completion is

```text
4k^2 + 6kr + r^2
  = ((4k+3r)^2 - 5r^2)/4.
```

Equivalently, define

```text
X = 4k + 3r,
Y = r.
```

Then

```text
4 * (4k^2 + 6kr + r^2) = X^2 - 5Y^2.
```

The integrality condition is

```text
X ≡ 3Y mod 4.
```

Thus the form is the norm form

```text
N(X + Y sqrt(5)) = X^2 - 5Y^2
```

restricted to the congruence class `X ≡ 3Y mod 4`, then divided by `4`.

This is the proper integral representation.  The expression with `2k + 3r/2` is useful for completing the square but is not the integral lattice model.

For the full inner exponent, including linear terms, use the odd anchor `A=2r+6k+1`:

```text
Q_inner(k,r)
  = 2k(2k+1) + r(r+6k+1)
  = (A^2 - 20k^2 - 4k - 1)/4.
```

The homogeneous part is the discriminant-20 norm form; the linear terms select the shifted/odd coset.

---

## Q4. What can be proved now, without HM?

Theorems 1 and 2 are elementary.  They should be written into Paper 2 before any modular discussion.  HM is only needed later to identify the analytic type of the slab series.

---

## Theorem 1 proof sketch: sigma involution and interior cancellation

### Theorem 1. Row reflection cancellation

Fix an integer `k` and define

```text
sigma_k(r) = -(6k+1)-r.
```

Let

```text
Q_k(r) = 2k(2k+1) + r(r+6k+1).
```

Then:

```text
1. sigma_k is an involution;
2. Q_k(sigma_k(r)) = Q_k(r);
3. (-1)^{sigma_k(r)} = -(-1)^r;
4. sigma_k has no integral fixed point;
5. therefore every sigma-stable row interval cancels in signed pairs.
```

### Proof

First,

```text
sigma_k(sigma_k(r))
  = -(6k+1) - (-(6k+1)-r)
  = r,
```

so `sigma_k` is an involution.

Next write `C=6k+1`.  Then

```text
sigma_k(r) = -C-r,
```

and

```text
sigma_k(r) + C = -r.
```

Therefore

```text
sigma_k(r)(sigma_k(r)+C)
  = (-C-r)(-r)
  = r(r+C).
```

Since the term `2k(2k+1)` is fixed by sigma,

```text
Q_k(sigma_k(r)) = Q_k(r).
```

For the sign, compute

```text
sigma_k(r) - r = -(6k+1)-2r.
```

This is odd, because `6k+1` is odd and `2r` is even.  Hence

```text
(-1)^{sigma_k(r)} = -(-1)^r.
```

A fixed point would satisfy

```text
r = -(6k+1)-r,
2r = -(6k+1),
```

which has no integral solution because `6k+1` is odd.  Thus the action is free on integral row atoms.

Now let `I_k` be any finite interval of integers satisfying

```text
r in I_k  iff  sigma_k(r) in I_k.
```

The signed row contribution over `I_k` is

```text
sum_{r in I_k} (-1)^r q^{Q_k(r)}.
```

Pair each `r` with `sigma_k(r)`.  The exponents are equal and the signs are opposite, so every pair sums to zero.  Since there are no fixed points, the whole interval contributes zero.

This proves interior cancellation.

---

## Theorem 2 proof sketch: slab decomposition and factored missing kernel

### Theorem 2. Two-slab missing kernel

For each row `k`, the legal `r`-domain is

```text
k >= 0   : r <= -1,
k <= -1  : r >= 0.
```

Under the row reflection `sigma_k(r)=-(6k+1)-r`, the sigma-stable interiors are

```text
k >= 0   : -6k <= r <= -1,
k <= -1  : 0 <= r <= -6k-1.
```

These interiors cancel by Theorem 1.  The only surviving atoms are

```text
Slab+ = { k >= 0,  r <= -6k-1 },
Slab- = { k <= -1, r >= -6k }.
```

Consequently the missing kernel is

```text
MissingKernel = Theta_u * Theta_v * F_slab,
```

where

```text
F_slab(q)
  = sum_{k>=0, r<=-6k-1} c(k,r) q^{9Q_inner(k,r)}
    + sum_{k<=-1, r>=-6k} c(k,r) q^{9Q_inner(k,r)}.
```

Here `c(k,r)` is the signed inner coefficient, typically `(-1)^r` up to the fixed convention of the residual kernel.

### Proof

For `k>=0`, the legal condition is `r<=-1`.  The image of a legal `r` under sigma is legal exactly when

```text
sigma_k(r) <= -1
<=> -(6k+1)-r <= -1
<=> r >= -6k.
```

Thus the paired interior is

```text
-6k <= r <= -1,
```

and the unpaired legal part is

```text
r <= -6k-1.
```

This is `Slab+`.

For `k<=-1`, the legal condition is `r>=0`.  The image is legal exactly when

```text
sigma_k(r) >= 0
<=> -(6k+1)-r >= 0
<=> r <= -6k-1.
```

Thus the paired interior is

```text
0 <= r <= -6k-1,
```

and the unpaired legal part is

```text
r >= -6k.
```

This is `Slab-`.

By Theorem 1, the paired interiors cancel exactly.  Therefore the signed row sum is supported on `Slab+ union Slab-`.

Finally, the full exponent separates:

```text
E(u,v,k,r)
  = 9*Q_outer(u,v) + 9*Q_inner(k,r),

Q_outer(u,v) = 5v^2 - 7v + 5u^2 - 3u,
Q_inner(k,r) = 2k(2k+1) + r(r+6k+1).
```

The `u` and `v` sums are independent of the slab condition, so they factor as

```text
Theta_u * Theta_v.
```

The remaining `(k,r)` sum is exactly `F_slab`.  Therefore

```text
MissingKernel = Theta_u Theta_v F_slab.
```

By the R6/R7 identification,

```text
F_slab = D-A = -f_{1,3,4}(X,-X^3,X),
```

so

```text
MissingKernel = -Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

This proves the repair term without using any modularity theorem.

---

## What needs HM and what does not

### Proved now, elementary

```text
1. sigma preserves Q_inner;
2. sigma flips the sign;
3. sigma has no fixed integral row atom;
4. interiors cancel;
5. only Slab+ and Slab- survive;
6. the full missing kernel factors as Theta_u Theta_v times the slab sum;
7. the anchor is A=2r+6k+1 and sigma sends A to -A.
```

### Needs HM / Zwegers theory

```text
1. naming F_slab as a mixed mock-Jacobi object;
2. writing F_slab as Appell--Lerch sums plus theta quotient;
3. resolving torsion specializations with eta^3 derivative terms;
4. determining the exact non-holomorphic completion and shadow.
```

The paper can therefore be split cleanly:

```text
Mechanism and repair: elementary.
Analytic classification: HM/mock-Jacobi appendix or later section.
```

---

## Verification code skeleton

```python
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable, Iterator, List, Tuple


def sigma(k: int, r: int) -> int:
    """Row reflection r -> -(6k+1)-r."""
    return -(6 * k + 1) - r


def q_inner(k: int, r: int) -> int:
    """Inner quadratic from the residual kernel."""
    return 2 * k * (2 * k + 1) + r * (r + 6 * k + 1)


def anchor(k: int, r: int) -> int:
    """Triangular root anchor A=2n-1 with n=r+3k+1."""
    return 2 * r + 6 * k + 1


def n_from_atom(k: int, r: int) -> int:
    """The triangular index giving anchor=2n-1."""
    return r + 3 * k + 1


def in_legal_r_domain(k: int, r: int) -> bool:
    """Legal r-domain from even_missing_kernel_term."""
    if k >= 0:
        return r <= -1
    return r >= 0


def in_slab_plus(k: int, r: int) -> bool:
    return k >= 0 and r <= -(6 * k + 1)


def in_slab_minus(k: int, r: int) -> bool:
    return k <= -1 and r >= -6 * k


def in_slab(k: int, r: int) -> bool:
    return in_slab_plus(k, r) or in_slab_minus(k, r)


def assert_sigma_theorem(k_values: Iterable[int], r_values: Iterable[int]) -> None:
    """Finite verification of the elementary sigma identities."""
    for k in k_values:
        for r in r_values:
            rp = sigma(k, r)
            assert sigma(k, rp) == r
            assert q_inner(k, rp) == q_inner(k, r)
            assert (rp - r) % 2 == 1
            assert anchor(k, rp) == -anchor(k, r)
            assert anchor(k, r) % 2 == 1


def row_interior(k: int) -> range:
    """Sigma-stable interior interval for a row."""
    if k >= 0:
        return range(-6 * k, 0)          # -6k <= r <= -1
    return range(0, -6 * k)              # 0 <= r <= -6k-1


def signed_row_interior_sum(k: int) -> int:
    """Toy signed sum over the paired interior; should be zero coefficientwise by pairing."""
    return sum((-1) ** r for r in row_interior(k))


@dataclass(frozen=True)
class AppellLerchTerm:
    coeff: str
    arg: str
    base: str
    z: str = "-1"


def hm_terms_specialized() -> List[AppellLerchTerm]:
    """The four nonzero standard z=-1 HM terms after X=q."""
    return [
        AppellLerchTerm("j(-q^3;q^4)", "-q^9", "q^20"),
        AppellLerchTerm("-q*j(-q^6;q^4)", "-q^4", "q^20"),
        AppellLerchTerm("q^3*j(-q^9;q^4)", "-q^-1", "q^20"),
        AppellLerchTerm("-q^6*j(-q^12;q^4)", "-q^-6", "q^20"),
    ]
```

---

## Final synthesis

The two bottlenecks resolve as follows.

First, the HM side should be written as a finite Appell--Lerch expansion plus a finite theta quotient, with the torsion specialization handled by the Jacobi derivative

```text
j(qe^eps;q) = eps (q;q)_infty^3 + O(eps^2).
```

The standard `z=-1` five-term Appell--Lerch part leaves four visible `m(.,q^20,-1)` terms after `X=q`; any true `0*infinity` contribution is an explicit eta-cubed residue term.

Second, the elementary mechanism is already complete:

```text
sigma_k(r)=-(6k+1)-r
```

preserves the quadratic, flips the sign, cancels the interior, and leaves exactly two slabs.  The atom-to-key anchor is

```text
A = 2r + 6k + 1,
```

and sigma sends

```text
A -> -A.
```

The disc-20 form is the conductor-2 norm form in the same field `Q(sqrt(5))`, with norm-`+1` unit

```text
9+4sqrt(5) = ((1+sqrt(5))/2)^6.
```

So Paper 2 can now be written with a clean division of labor:

```text
elementary sections: sigma, slabs, factorization Theta_u Theta_v F_slab, repair;
analytic section: HM/Appell--Lerch expansion and mixed mock-Jacobi classification.
```
