# Q3077 (dm1): tau-boundary, half-theta truncation, and strip flux

Date: 2026-07-02

## Executive answer

Yes: after the change of variables

```text
m = l + 1,
t = u + v - 1,
d = u - v,
```

the involution is the central reflection

```text
tau(m,t,d) = (-m,-t,d).
```

The late failures are therefore not caused by a bad bulk involution. They are caused by the fact that the actual coefficient extractor is not a bilateral theta alone. It is a bilateral theta plus one-sided corrections. The bilateral term lives on a tau-stable lattice. The missing-half term and the strip terms live on half-spaces or oriented intervals whose endpoints are anchored at `j = 0` or `l = 0`, not at the tau center. Those anchored half-spaces create a boundary flux.

The right diagnostic object is not the full atom weight first. It is the orbit residual of the one-sided part:

```text
boundaryResidual(a) = oneSided(a) + oneSided(tau(a))
```

in the convention where the stored atom contribution is already signed. If the code stores the atom sign separately, the same test appears as

```text
boundaryResidual(a) = sign(a) * (oneSidedBody(a) - oneSidedBody(tau(a))).
```

In either convention, the bilateral part drops out of the orbit residual. Thus the exact tau-boundary is the set of tau-orbits for which this residual is nonzero. The keywise failure is the sum of those residuals over the key fiber.

The `e = 11763` atom

```text
(l,u,v,color) = (-5,-8,-12,holdU)
```

has

```text
m = -4,
t = -21,
d = 4,
u = -8,
v = -12.
```

Its tau image is

```text
(m,t,d) = (4,21,4),
(l,u,v) = (3,13,9).
```

The bilateral contribution is not the mystery. The one-sided body has already become asymmetric:

```text
oddBilat          = -2
oddMissingSigned  = +1
stripUSigned      = +2
stripVSigned      =  0
total             = +1
```

That is the signature of a boundary orbit: the bilateral part is trying to cancel in the symmetrized packet, while the one-sided correction has a leftover flux.

## 1. Exact prediction of tau-unpaired atoms

Let `A_e` be the atoms contributing to coefficient `e`, and write the signed contribution as

```text
W_e(a) = W_bil(a) + W_miss(a) + W_U(a) + W_V(a).
```

Here:

```text
W_bil   = oddBilat,
W_miss  = oddMissingSigned,
W_U     = stripUSigned,
W_V     = stripVSigned.
```

The structural claim from the code analysis is

```text
W_bil(a) + W_bil(tau(a)) = 0
```

on the symmetrized lattice. Therefore, for a two-point tau orbit, the only possible obstruction is

```text
R_partial(a)
  = W_miss(a) + W_miss(tau(a))
  + W_U(a)    + W_U(tau(a))
  + W_V(a)    + W_V(tau(a))
```

with the same signed-weight convention as above. Equivalently, if the code stores body values before multiplying by the atom sign, replace the plus signs by the corresponding signed difference:

```text
R_partial(a)
  = sign(a) * (
        body_miss(a) - body_miss(tau(a))
      + body_U(a)    - body_U(tau(a))
      + body_V(a)    - body_V(tau(a))
    ).
```

Then the exact keywise identity is

```text
keyWeight_e(k)
  = sum over tau-orbit representatives a with K(a)=k of R_partial(a).
```

So the exact prediction rule is:

```text
a tau-orbit is dangerous  <=>  R_partial(a) != 0,
a key fails               <=>  the dangerous-orbit residuals in that key do not sum to 0.
```

This distinction matters. A single atom can have a nonzero one-sided term and still be harmless if its tau mate has the opposite one-sided term. The unpaired atoms are not merely the atoms where `oddMissingSigned` or `stripUSigned` is nonzero. They are the atoms where the tau-orbit residual of the one-sided part is nonzero.

### Missing-half component

Use

```text
b = 2l + 1 = 2m - 1.
```

Under tau,

```text
b' = 2(-l-2) + 1 = -b - 2 = -2m - 1.
```

Thus, away from the central point `m = 0`, the sign side switches:

```text
m >= 1  =>  b >= 1   and b' <= -3,
m <= -1 =>  b <= -3  and b' >= 1.
```

At `m = 0`, one has `l = -1`, `b = -1`, and tau fixes `l`. This is the central exceptional line.

The prompt says the missing-half code uses

```text
b >= 0  ->  partial_neg_coeff,
b <  0  ->  partial_pos_coeff.
```

Therefore define a side selector for roots `j` of the relevant j-quadratic:

```text
P_m(j) = 1_{j < 0}   if m >= 1,
P_m(j) = 1_{j >= 0}  if m <= 0.
```

The exact missing-half boundary is then

```text
D_miss(a)
  = sum over bilateral roots j at a of eps(j) * P_m(j)
    + sum over bilateral roots j' at tau(a) of eps'(j') * P_{-m}(j').
```

Equivalently, if the bilateral root map `j -> j_tau` is known from the quadratic, this becomes the pointwise test

```text
D_miss(a)
  = sum_j eps(j) * (P_m(j) - P_{-m}(j_tau)).
```

The missing-half boundary therefore occurs exactly where the tau-paired roots lie on different sides of the `j = 0` cut, or where one side of the root pair is absent because the discriminant/integrality condition fails after the shifted transformation of the linear coefficient.

This is already an exact prediction method: solve the full bilateral root equation, apply the two half-line selectors, and keep precisely those tau-orbits with nonzero `D_miss`.

### Strip component

The strip function is best written as an oriented interval. Let

```text
H(x) = 1 if x >= 0, otherwise 0.
```

Then for integer `N,x`,

```text
strip0(N,x) = H(x) - H(x - N).
```

This is exactly the implementation-level rule:

```text
N > 0:  strip0(N,x) = +1 if 0 <= x < N, else 0,
N < 0:  strip0(N,x) = -1 if N <= x < 0, else 0,
N = 0:  strip0(N,x) = 0.
```

Equivalently, with

```text
I(N) = [1,N]      if N > 0,
I(N) = [N+1,0]    if N < 0,
I(N) = empty      if N = 0,
```

one has

```text
strip0(N,m-1) = sgn(N) * 1_{m in I(N)}.
```

Here the endpoint convention follows directly from `0 <= l < N` with `l = m - 1`: if `N > 0`, then `m = 1,...,N`. If your code has an extra upper-shift convention, replace `I(N)` by the corresponding shifted interval. The formulas below are unchanged in form.

Now put

```text
U = u = (t+d+1)/2,
V = v = (t-d+1)/2.
```

Under tau,

```text
U_tau = 1 - v = (d-t+1)/2,
V_tau = 1 - u = (1-t-d)/2.
```

The U-strip itself is

```text
S_U(m,t,d) = strip0(U,m-1)
           = H(m-1) - H(m-1-U).
```

Its tau pullback is

```text
S_U(tau(m,t,d))
  = strip0(U_tau,-m-1)
  = H(-m-1) - H(-m-1-U_tau).
```

Thus the same-component U-strip residual is the explicit function

```text
R_U(m,t,d)
  = S_U(m,t,d) - S_U(tau(m,t,d))
  = H(m-1) - H(m-1-U)
    - H(-m-1) + H(-m-1-U_tau).
```

In interval language,

```text
R_U(m,t,d)
  = sgn(U)     * 1_{m in I(U)}
    - sgn(U_tau) * 1_{m in -I(U_tau)}.
```

Here

```text
-I([a,b]) = [-b,-a].
```

Therefore the U-strip boundary is exactly the oriented symmetric difference

```text
I(U)  versus  -I(U_tau).
```

The V-strip formula is identical:

```text
R_V(m,t,d)
  = S_V(m,t,d) - S_V(tau(m,t,d))
  = H(m-1) - H(m-1-V)
    - H(-m-1) + H(-m-1-V_tau),
```

or

```text
R_V(m,t,d)
  = sgn(V)       * 1_{m in I(V)}
    - sgn(V_tau) * 1_{m in -I(V_tau)}.
```

If the color map sends a U-strip term to a V-strip term, use the cross residual instead:

```text
R_{U->V}(m,t,d)
  = S_U(m,t,d) - S_V(tau(m,t,d))
  = strip0(U,m-1) - strip0(V_tau,-m-1).
```

Likewise,

```text
R_{V->U}(m,t,d)
  = strip0(V,m-1) - strip0(U_tau,-m-1).
```

The important point is the shift

```text
x = m - 1,
x_tau = -m - 1 = -x - 2.
```

The strip is anchored at `x = 0`, i.e. `l = 0` or `m = 1`. But the tau center is `m = 0`, i.e. `l = -1`. Hence the mirror of the strip is displaced by one lattice unit. This is the concrete reason the strip is not tau-symmetric.

For the `e = 11763` atom,

```text
m = -4,
t = -21,
d = 4,
U = -8,
V = -12,
U_tau = 13,
V_tau = 9.
```

So

```text
I(U)       = [-7,0],
-I(U_tau) = [-13,-1].
```

The point `m = -4` lies in both intervals, but the orientations are opposite:

```text
sgn(U)     = -1,
sgn(U_tau) = +1.
```

Thus the strip defect is not merely a support-membership defect. It is an oriented-boundary defect. Depending on the global sign/color convention, this is exactly the source of a signed contribution of magnitude `2`, matching the reported `stripUSigned = +2` up to the sign convention used by the body printer.

### Minimal exact classifier

The classifier I would use is this:

```python
from dataclasses import dataclass
from typing import Callable, Iterable, Optional, Sequence

@dataclass(frozen=True)
class Atom:
    l: int
    u: int
    v: int
    color: str

@dataclass(frozen=True)
class MTD:
    m: int
    t: int
    d: int
    color: str

def tau_color(color: str) -> str:
    # Replace this with the actual color map from the implementation.
    # The mathematical tests below do not assume which colors swap.
    return color

def tau_atom(a: Atom) -> Atom:
    return Atom(
        l=-a.l - 2,
        u=1 - a.v,
        v=1 - a.u,
        color=tau_color(a.color),
    )

def to_mtd(a: Atom) -> MTD:
    return MTD(
        m=a.l + 1,
        t=a.u + a.v - 1,
        d=a.u - a.v,
        color=a.color,
    )

def from_mtd(x: MTD) -> Atom:
    # u and v are integral exactly when t+d+1 and t-d+1 are even.
    u_num = x.t + x.d + 1
    v_num = x.t - x.d + 1
    if u_num % 2 or v_num % 2:
        raise ValueError('nonintegral u or v from m,t,d')
    return Atom(
        l=x.m - 1,
        u=u_num // 2,
        v=v_num // 2,
        color=x.color,
    )

def H_ge0(n: int) -> int:
    return 1 if n >= 0 else 0

def strip0(N: int, x: int) -> int:
    # Oriented half-open interval: +[0,N) for N>0, -[N,0) for N<0.
    return H_ge0(x) - H_ge0(x - N)

def interval_I(N: int) -> Optional[tuple[int, int]]:
    # Returns the closed integer m-interval for strip0(N,m-1).
    if N > 0:
        return (1, N)
    if N < 0:
        return (N + 1, 0)
    return None

def in_interval(m: int, interval: Optional[tuple[int, int]]) -> bool:
    if interval is None:
        return False
    lo, hi = interval
    return lo <= m <= hi

def neg_interval(interval: Optional[tuple[int, int]]) -> Optional[tuple[int, int]]:
    if interval is None:
        return None
    lo, hi = interval
    return (-hi, -lo)

def sgn(n: int) -> int:
    return (n > 0) - (n < 0)

def U_value(m: int, t: int, d: int) -> int:
    num = t + d + 1
    if num % 2:
        raise ValueError('U is not integral')
    return num // 2

def V_value(m: int, t: int, d: int) -> int:
    num = t - d + 1
    if num % 2:
        raise ValueError('V is not integral')
    return num // 2

def strip_U_same_component_residual(m: int, t: int, d: int) -> int:
    U = U_value(m, t, d)
    U_tau = U_value(-m, -t, d)
    return strip0(U, m - 1) - strip0(U_tau, -m - 1)

def strip_V_same_component_residual(m: int, t: int, d: int) -> int:
    V = V_value(m, t, d)
    V_tau = V_value(-m, -t, d)
    return strip0(V, m - 1) - strip0(V_tau, -m - 1)

def strip_U_to_V_residual(m: int, t: int, d: int) -> int:
    U = U_value(m, t, d)
    V_tau = V_value(-m, -t, d)
    return strip0(U, m - 1) - strip0(V_tau, -m - 1)

def strip_V_to_U_residual(m: int, t: int, d: int) -> int:
    V = V_value(m, t, d)
    U_tau = U_value(-m, -t, d)
    return strip0(V, m - 1) - strip0(U_tau, -m - 1)

def b_value_from_m(m: int) -> int:
    return 2 * m - 1

def n_value_from_m(m: int) -> int:
    # n = 54l + 45 = 54(m-1) + 45 = 54m - 9 = 9(6m-1).
    return 54 * m - 9

def missing_side_selector(m: int, j: int) -> int:
    # Prompt convention: b>=0 uses partial_neg, b<0 uses partial_pos.
    b = b_value_from_m(m)
    if b >= 0:
        return 1 if j < 0 else 0
    return 1 if j >= 0 else 0

def orbit_boundary_residual_signed(
    a: Atom,
    one_sided_signed_weight: Callable[[Atom], int],
) -> int:
    # Use this if one_sided_signed_weight already includes the atom sign.
    return one_sided_signed_weight(a) + one_sided_signed_weight(tau_atom(a))

def orbit_boundary_residual_body(
    a: Atom,
    atom_sign: Callable[[Atom], int],
    one_sided_body_weight: Callable[[Atom], int],
) -> int:
    # Use this if body weights are printed before multiplying by atom sign.
    return atom_sign(a) * (
        one_sided_body_weight(a) - one_sided_body_weight(tau_atom(a))
    )
```

That code is deliberately only a classifier skeleton. The missing piece to plug in from the project is the actual `j`-quadratic root map and the actual color map. Once those are inserted, the classifier gives the exact tau-boundary without scanning irrelevant bilateral bulk.

## 2. Why the mod-9 pattern is natural

The j-coefficient quadratic has linear parameter

```text
n = 54l + 45 = 9(6l+5).
```

In `m` coordinates this is

```text
n = 54m - 9 = 9(6m-1).
```

Under tau,

```text
n_tau = 54(-m) - 9 = -54m - 9 = -n - 18 = -9(6m+1).
```

So tau does not merely send `n` to `-n`; it sends it to `-n - 18`. This is the same one-unit displacement that appeared in

```text
b_tau = -b - 2.
```

The common factor `9` is not cosmetic. Suppose the j-coefficient equation has the standard quadratic shape

```text
A j^2 + n j + C = e
```

or, equivalently,

```text
A j^2 + n j + C - e = 0.
```

Then the discriminant is

```text
Delta = n^2 - 4A(C-e)
      = 81(6m-1)^2 + 4A(e-C).
```

Modulo `9`, this reduces to

```text
Delta == 4A(e-C)  mod 9.
```

Integral roots require two things:

```text
1. Delta is a square.
2. -n +/- sqrt(Delta) is divisible by 2A.
```

Since `n` is divisible by `9`, the numerator congruence often forces `sqrt(Delta)` to lie in a restricted congruence class modulo `3`, `9`, or `18`. On a boundary face where the remaining constant term satisfies

```text
C == 0  mod 9,
```

one gets the natural condition

```text
e == 0  mod 9
```

provided the allowed square root class is also `0 mod 3` or `0 mod 9`.

This explains why the observed failures

```text
90    = 9 * 10,
702   = 9 * 78,
11763 = 9 * 1307
```

all being multiples of `9` is a serious clue. The factor `1307` is probably not the first thing to chase. The structural arithmetic is the common modulus `9`; the quotient is likely the value of a reduced boundary quadratic after dividing out the forced modulus.

The exact modular theorem should be obtained face-by-face. For each missing-half or strip boundary face, compute the allowed residues

```text
(e mod 9, m mod M, t mod M, d mod M, j mod M)
```

satisfying the discriminant and numerator congruences. The output should be a finite residue table. The relevant question is not only whether all failures satisfy `e == 0 mod 9`, but whether every boundary face capable of nonzero key flux forces `e == 0 mod 9`.

Here is the residue computation I would add next:

```python
from collections import defaultdict
from dataclasses import dataclass
from typing import Callable, Iterable

@dataclass(frozen=True)
class QuadraticModel:
    A: int
    # C_mod returns C modulo mod for a residue tuple.
    C_mod: Callable[[int, int, int, int], int]
    # Extra numerator condition for integral roots.
    numerator_ok: Callable[[int, int, int], bool]


def square_residues(mod: int) -> set[int]:
    return {(r * r) % mod for r in range(mod)}


def allowed_e_residues_mod9_for_face(
    model: QuadraticModel,
    m_modulus: int,
    t_modulus: int,
    d_modulus: int,
    j_modulus: int,
) -> dict[int, list[tuple[int, int, int, int]]]:
    out: dict[int, list[tuple[int, int, int, int]]] = defaultdict(list)
    sq9 = square_residues(9)
    for m in range(m_modulus):
        n = (54 * m - 9) % 9
        for t in range(t_modulus):
            for d in range(d_modulus):
                C = model.C_mod(m, t, d, 9) % 9
                for e in range(9):
                    Delta = (n * n - 4 * model.A * (C - e)) % 9
                    if Delta not in sq9:
                        continue
                    for j in range(j_modulus):
                        if model.numerator_ok(n, Delta, j):
                            out[e].append((m, t, d, j))
                            break
    return dict(out)
```

The expected result, if the mod-9 explanation is correct, is that the boundary faces that survive key aggregation have support only in the `e = 0 mod 9` bucket.

If the table instead shows several allowed residue classes, then `e = 90,702,11763` being `0 mod 9` is a first-hit artifact, not a universal obstruction.

## 3. Explicit strip boundary in `(m,t,d)`

The cleanest formula is the Heaviside form above. I restate it here because it is the local boundary calculation I would put in the proof.

Define

```text
S(N,m) = strip0(N,m-1) = H(m-1) - H(m-1-N).
```

For the U-strip,

```text
U       = (t+d+1)/2,
U_tau   = (d-t+1)/2.
```

Then

```text
R_U(m,t,d)
  = S(U,m) - S(U_tau,-m)
  = H(m-1) - H(m-1-U)
    - H(-m-1) + H(-m-1-U_tau).
```

For the V-strip,

```text
V       = (t-d+1)/2,
V_tau   = (1-t-d)/2,
```

and

```text
R_V(m,t,d)
  = H(m-1) - H(m-1-V)
    - H(-m-1) + H(-m-1-V_tau).
```

If colors swap U and V, use

```text
R_{U->V}(m,t,d)
  = H(m-1) - H(m-1-U)
    - H(-m-1) + H(-m-1-V_tau),
```

and

```text
R_{V->U}(m,t,d)
  = H(m-1) - H(m-1-V)
    - H(-m-1) + H(-m-1-U_tau).
```

This makes the boundary faces visible. The jumps of `S(U,m)` occur at

```text
m = 1,
m = U + 1.
```

The jumps of the tau-pulled strip occur at

```text
m = -1,
m = -U_tau - 1.
```

Thus the U-strip boundary is controlled by the four affine faces

```text
m = 1,
m = U + 1,
m = -1,
m = -U_tau - 1.
```

Substituting `U = (t+d+1)/2` and `U_tau = (d-t+1)/2`, these are

```text
m = 1,
2m = t + d + 3,
m = -1,
2m = t - d - 3.
```

Similarly the V-strip faces are

```text
m = 1,
2m = t - d + 3,
m = -1,
2m = -t - d - 3.
```

Those affine faces are the discrete Stokes boundary. The strip contribution is a finite interval in the bulk, but its failure under central reflection is governed by these faces. That is exactly why the next computation should be a boundary-face minimization rather than a full atom scan.

A compact face enumerator looks like this:

```python
from dataclasses import dataclass
from typing import Callable, Iterable

@dataclass(frozen=True)
class Face:
    name: str
    equation_value: Callable[[int, int, int], int]


def U(m: int, t: int, d: int) -> int:
    return (t + d + 1) // 2


def V(m: int, t: int, d: int) -> int:
    return (t - d + 1) // 2


def U_tau(m: int, t: int, d: int) -> int:
    return (d - t + 1) // 2


def V_tau(m: int, t: int, d: int) -> int:
    return (1 - t - d) // 2


STRIP_FACES: tuple[Face, ...] = (
    Face('U_left_m_eq_1',        lambda m, t, d: m - 1),
    Face('U_right_m_eq_U_plus_1', lambda m, t, d: m - (U(m, t, d) + 1)),
    Face('U_tau_left_m_eq_minus_1', lambda m, t, d: m + 1),
    Face('U_tau_right_m_eq_minus_Utau_minus_1',
         lambda m, t, d: m + U_tau(m, t, d) + 1),
    Face('V_left_m_eq_1',        lambda m, t, d: m - 1),
    Face('V_right_m_eq_V_plus_1', lambda m, t, d: m - (V(m, t, d) + 1)),
    Face('V_tau_left_m_eq_minus_1', lambda m, t, d: m + 1),
    Face('V_tau_right_m_eq_minus_Vtau_minus_1',
         lambda m, t, d: m + V_tau(m, t, d) + 1),
)


def active_faces(m: int, t: int, d: int) -> list[str]:
    return [face.name for face in STRIP_FACES if face.equation_value(m, t, d) == 0]
```

For threshold prediction, one should not require the atom to lie exactly on a jump face; the residual is supported on an oriented symmetric difference of intervals. But the first-hit values are attained when one of these affine boundary inequalities first admits a lattice point after imposing the root/discriminant and key constraints. That is the wavefront mechanism.

## 4. Compensation term: yes, it should be partial theta

The compensation should be a partial-theta or false-theta correction, probably a finite linear combination of such series indexed by boundary faces and residue classes.

The exact corrected identity is

```text
keyWeight_e(k) - B_e(k) = 0,
```

where

```text
B_e(k)
  = sum over tau-boundary orbits in key k of R_partial(a).
```

Equivalently, at the generating-series level,

```text
B_k(q)
  = sum_e B_e(k) q^e.
```

Because the bulk is bilateral, it cancels by the central reflection. Because the boundary is cut out by half-line selectors such as

```text
j >= 0,
j < 0,
0 <= l < N,
N <= l < 0,
```

its generating series is one-sided. Once a boundary face is parameterized, the exponent is still a quadratic form, but the summation range is a ray or a cone rather than all of `Z`. That is exactly a partial theta or false theta shape:

```text
sum_{r >= 0} eps(r) q^{A r^2 + B r + C}
```

or, before reducing a strip cone,

```text
sum_{N > 0} sum_{0 <= r < N} eps(N,r) q^{Q(N,r)}.
```

The strip double cone often telescopes. Using

```text
strip0(N,x) = H(x) - H(x-N),
```

one can express the strip correction as a difference of two half-space sums. After summing over the variable that controls `N`, these become boundary sums on the endpoint faces listed above. That is the discrete Stokes form: the divergence of a finite strip is supported at its endpoints.

So the expected correction has the schematic form

```text
B(q)
  = sum over missing-half faces F
      c_F * sum_{r >= 0, r == rho_F mod M_F}
              eps_F(r) q^{Q_F(r)}
    + sum over strip faces G
      c_G * sum_{r >= 0, r == rho_G mod M_G}
              eps_G(r) q^{Q_G(r)}.
```

This is very close to the familiar Hickerson-Mortenson phenomenon: an indefinite/bilateral bulk cancellation leaves a theta correction on the boundary of the cone. In the root-pair involution language, the even-Delta fixed-point residual is not an error in the involution. It is the contribution of the boundary/fixed locus that remains after the involution cancels the free orbits. Here the role of the fixed locus is played by the half-theta and strip boundary.

I would therefore not try first to invent a completely new involution on the original atoms. A fixed-point-free sign-reversing involution on the same key fiber would force the key weight to be zero. The observed key weight `+1` at `(-6,-17)` rules that out for the current atom set and current key. The principled rescue is instead:

```text
original identity = bilateral cancellation + explicit boundary correction.
```

If one insists on an involution, the natural one is on an enlarged set:

```text
A_e^sym = A_e union tau(A_e).
```

On `A_e^sym`, tau cancels perfectly. The difference between `A_e^sym` and `A_e` is exactly the boundary correction. This is often the cleanest proof architecture.

## 5. Wavefront and threshold prediction

The wavefront should be defined by boundary faces, not by the full support scan.

For a key `k`, define

```text
F(k) = min { e : B_e(k) != 0 }.
```

For a shell depth `h`, define

```text
F_h = min { F(k) : |hblock(k)| = h }.
```

The reported data are consistent with

```text
F_1 = 90          at the outer shell,
F_2 = 702         at the next shell,
F_6 <= 11763      with key (-6,-17).
```

I would not fit these three points to a simple numerical formula. The correct formula is obtained by minimizing the coefficient exponent over the boundary faces:

```text
F_h
  = min over boundary faces F
      min Q_F(parameters)
```

subject to:

```text
1. the key equations giving hblock = +/-h,
2. the anchor/color congruences,
3. the discriminant square condition for the j-quadratic,
4. the numerator divisibility condition for integral roots,
5. the one-sided selector giving nonzero R_partial.
```

Since the boundary faces are affine and the exponent is quadratic, this is a finite collection of congruence-restricted quadratic minimization problems. In good coordinates it should produce a quasipolynomial or a small table of quadratic forms by residue class.

That is the clean threshold formula I would seek:

```text
F_h = min_i min_{r in R_i(h)} Q_i(r),
```

where each `i` is a boundary face/residue class. The mod-9 observation says many or all of the relevant residue sets `R_i(h)` may force

```text
Q_i(r) == 0  mod 9.
```

## 6. What I would investigate first

I would do these in order.

### Step 1: print tau-orbit residuals, not just atom totals

For every atom in a failing key, print

```text
atom,
tau(atom),
key(atom),
key(tau(atom)),
oddBilat(atom),
oddBilat(tau(atom)),
oneSided(atom),
oneSided(tau(atom)),
R_partial(atom).
```

The first assertion should be

```text
oddBilat(atom) + oddBilat(tau(atom)) = 0
```

in signed convention. The second assertion should be

```text
keyWeight = sum R_partial over tau-orbit representatives in the key.
```

This will immediately separate bulk cancellation from boundary flux.

### Step 2: classify every residual by face

For each nonzero residual, attach labels:

```text
missing_half_positive_cut,
missing_half_negative_cut,
U_strip_left,
U_strip_right,
U_tau_left,
U_tau_right,
V_strip_left,
V_strip_right,
V_tau_left,
V_tau_right.
```

This tells whether `e = 11763` is a missing-half event, a strip event, or a mixed event. The body numbers suggest it is mixed but strip-dominated:

```text
oddMissingSigned = +1,
stripUSigned     = +2,
total boundary one-sided part = +3,
oddBilat         = -2,
net              = +1.
```

### Step 3: produce the mod-9 table by boundary face

For the j-quadratic, write the exact discriminant and numerator condition. Then compute allowed `e mod 9` for each boundary face. The test is:

```text
Do all nonzero boundary residuals lie in e = 0 mod 9?
```

If yes, the divisibility by `9` is structural. If not, the first failures happen to land in the zero class, and the next task is to explain why the other classes cancel or have larger minima.

### Step 4: minimize on faces

Stop scanning all atoms. For each face, substitute the face equation into the exponent and key equations. Then minimize the resulting quadratic over the allowed residues. This should predict the first shell hits:

```text
h = 1  ->  e = 90,
h = 2  ->  e = 702,
h = 6  ->  e = 11763 or an earlier value if one exists.
```

If the computed first hit for `h = 6` is exactly `11763`, the mystery is solved: it is the first lattice point of a congruence-restricted boundary quadratic.

### Step 5: derive the partial-theta correction

Once the active faces are known, write

```text
B(q) = sum over active faces of one-sided quadratic sums.
```

Then try to simplify by pairing opposite faces. The expected end product is a finite linear combination of partial theta or Hickerson-Mortenson theta corrections.

## Bottom line

The conjecture survives deep into the range because the bilateral bulk is genuinely protected by the central reflection, and the asymmetric one-sided pieces have not yet produced an uncanceled lattice point in the deeper key fibers. The failures grow inward because the tau-boundary is a moving wavefront: as `e` increases, boundary faces intersect key fibers farther from the outer shell. The `9`-divisibility is naturally explained by the j-quadratic linear coefficient

```text
n = 9(6m-1)
```

and the associated discriminant/numerator congruences. The right rescue is not a new fixed-point-free involution on the same atoms. The right rescue is a discrete-Stokes correction: bilateral bulk cancels, and the missing-half plus strip boundary contributes a partial-theta correction.
