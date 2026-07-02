# Q3077 (dm1): tau-boundary flux, strip asymmetry, and partial-theta compensation

Date: 2026-07-02

## Executive answer

Yes: after separating the bilateral theta part from the one-sided pieces, the failure is exactly a tau-boundary flux problem. In the coordinates

```text
m = l + 1
t = u + v - 1
d = u - v
```

the involution is

```text
τ(m,t,d) = (-m,-t,d),
```

so every noncentral cancellation should happen orbit-by-orbit under central reflection in the (m,t)-plane. The bilateral piece is the bulk term; it cancels on a complete τ-orbit. The residual is caused by cuts: the missing-half theta cut and the strip cut. Those cuts are not invariant under τ.

The clean formulation is this. Let x be an atom, let χ_e(x) be the root-packet support indicator at coefficient e, let σ(x) be the outer sign, with σ(τx) = -σ(x), and decompose the atom coefficient as

```text
W(x) = B(x) + C∂(x),
C∂(x) = M(x) + S_U(x) + S_V(x),
```

where B is oddBilat, M is oddMissingSigned, and S_U, S_V are the strip contributions with their color/sign multipliers included. The exact orbit flux is

```text
Φ_e(x) = σ(x) * ( χ_e(x) * C∂(x) - χ_e(τx) * C∂(τx) ).
```

For a complete noncentral orbit, B drops out because B(τx) = B(x) while σ(τx) = -σ(x). Therefore the unpaired or uncancelled atoms are precisely the atoms whose τ-orbit has nonzero Φ_e. If by “unpaired” one means literally “the τ-image is outside the root-packet support”, then the indicator obstruction is χ_e(x) != χ_e(τx). If by “uncancelled” one means “contributes nonzero keyWeight after the involution”, then the exact condition is Φ_e(x) != 0.

For the e = 11763 atom

```text
(l,u,v) = (-5,-8,-12)
(m,t,d) = (-4,-21,4)
τ(l,u,v) = (3,13,9)
τ(m,t,d) = (4,21,4)
```

the U-strip already shows the defect. Here U = u = -8 and V = v = -12. The original U-strip value is strip0(-8,-5) = -1, while the reflected U-strip value is strip0(1 - V, -m - 1) = strip0(13,3) = +1. Thus the oriented U-strip defect is -2, which is +2 after the sign convention used by the body-level diagnostic. That matches the reported stripUSigned = +2. The raw body decomposition

```text
oddBilat = -2
oddMissingSigned = +1
stripUSigned = +2
total = +1
```

is therefore exactly what a clipped τ-orbit should produce: the bulk term wants a partner, while the half-theta and strip cuts record why the partner is missing or mismatched.

## Q1. Exact prediction of tau-unpaired atoms

The exact predictor is not “deep l” by itself. It is the τ-orbit flux functional.

Define the canonical representative of a noncentral τ-orbit, for example by choosing the representative with (m,t) lexicographically positive after identifying (m,t,d) with (-m,-t,d). Then for each key K define

```text
BoundaryOrbit_e(K) = {
    x canonical : key(x) = K and
    χ_e(x) * C∂(x) - χ_e(τx) * C∂(τx) != 0
}.
```

Then the boundary contribution to the key fiber is

```text
keyWeight∂_e(K) = sum over x in BoundaryOrbit_e(K) of
                  σ(x) * ( χ_e(x) * C∂(x) - χ_e(τx) * C∂(τx) ).
```

This is the formula I would use as the oracle. It predicts exactly which atoms survive once the bilateral cancellation has been factored out.

There are two levels of exactness:

1. Strict support-unpaired atoms:

```text
χ_e(x) = 1 and χ_e(τx) = 0,
or
χ_e(x) = 0 and χ_e(τx) = 1.
```

These are literal root-packet support boundary failures.

2. Weight-uncancelled atoms:

```text
χ_e(x) * C∂(x) != χ_e(τx) * C∂(τx).
```

These include strict support failures, but can also include two-sided support where the one-sided pieces assign different boundary weights to the two sides.

For the conjecture, the second condition is the mathematically relevant one, because keyWeight sees weights, not just membership.

A useful diagnostic is therefore:

```python
from dataclasses import dataclass
from typing import Callable, Iterable, Optional


@dataclass(frozen=True)
class Atom:
    l: int
    u: int
    v: int
    color: str


def tau_atom(a: Atom) -> Atom:
    return Atom(l=-a.l - 2, u=1 - a.v, v=1 - a.u, color=a.color)


def mtd(a: Atom) -> tuple[int, int, int]:
    m = a.l + 1
    t = a.u + a.v - 1
    d = a.u - a.v
    return m, t, d


def heaviside_ge0(r: int) -> int:
    return 1 if r >= 0 else 0


def strip0(N: int, l: int) -> int:
    # Uniform form of ctf_strip0:
    # +1 on 0 <= l < N when N > 0,
    # -1 on N <= l < 0 when N < 0,
    # 0 when N = 0.
    return heaviside_ge0(l) - heaviside_ge0(l - N)


def strip_u_defect(a: Atom) -> int:
    # U = u, V = v in atom coordinates.
    # In (m,t,d), this is S_U(m,t,d) - S_U(τ(m,t,d)).
    m, _t, _d = mtd(a)
    return strip0(a.u, m - 1) - strip0(1 - a.v, -m - 1)


def strip_v_defect(a: Atom) -> int:
    m, _t, _d = mtd(a)
    return strip0(a.v, m - 1) - strip0(1 - a.u, -m - 1)


def boundary_flux(
    a: Atom,
    e: int,
    support: Callable[[Atom, int], bool],
    outer_sign: Callable[[Atom], int],
    missing_signed: Callable[[Atom, int], int],
    strip_u_signed: Callable[[Atom, int], int],
    strip_v_signed: Callable[[Atom, int], int],
) -> int:
    b = tau_atom(a)

    def one_sided(x: Atom) -> int:
        return (
            missing_signed(x, e)
            + strip_u_signed(x, e)
            + strip_v_signed(x, e)
        )

    return outer_sign(a) * (
        int(support(a, e)) * one_sided(a)
        - int(support(b, e)) * one_sided(b)
    )


def is_uncancelled_boundary_atom(
    a: Atom,
    e: int,
    support: Callable[[Atom, int], bool],
    outer_sign: Callable[[Atom], int],
    missing_signed: Callable[[Atom, int], int],
    strip_u_signed: Callable[[Atom, int], int],
    strip_v_signed: Callable[[Atom, int], int],
) -> bool:
    return boundary_flux(
        a=a,
        e=e,
        support=support,
        outer_sign=outer_sign,
        missing_signed=missing_signed,
        strip_u_signed=strip_u_signed,
        strip_v_signed=strip_v_signed,
    ) != 0
```

That is the first thing I would wire into the existing enumerator. It should reproduce e = 90, e = 702, and e = 11763 without looking at oddBilat at all except as a check that the bulk part is symmetric.

## Q2. The role of n = 54l + 45 = 9(6l + 5) and the mod-9 pattern

The mod-9 pattern is probably real, but it should be interpreted as a necessary congruence filter, not as a complete threshold law.

In m-coordinates,

```text
n = 54l + 45 = 54m - 9 = 9(6m - 1),
τn = -54m - 9 = -9(6m + 1).
```

Since 6m - 1 and 6m + 1 are never divisible by 3, both n and τn have exact 3-adic valuation 2:

```text
v_3(n) = v_3(τn) = 2.
```

That is a strong arithmetic constraint. If the j-coefficient is governed by a quadratic of the schematic form

```text
a j^2 + n j + c = e,
```

then completing the square gives

```text
(2a j + n)^2 = n^2 + 4a(e - c).
```

Because n^2 is divisible by 81, the existence of integer roots is controlled by the residue of 4a(e - c) modulo powers of 3. On the boundary, where the missing-half truncation changes side, the same n = 9 times a 3-adic unit appears. Thus the boundary quadratic naturally produces e-values in a fixed residue class modulo 9. The observed failures

```text
90    = 9 * 10
702   = 9 * 78
11763 = 9 * 1307
```

are exactly consistent with this.

I would not yet attach special meaning to the prime-looking quotient 1307. The data given only supports the statement “boundary failures occur at e ≡ 0 mod 9.” It does not yet support a stronger statement such as a fixed class modulo 27 or 81, since the quotients 10, 78, and 1307 already behave differently modulo 9.

The right arithmetic test is this:

```text
For every boundary-defect family F, derive the boundary energy polynomial

    e = E_F(r,s,...) = 9 * Q_F(r,s,...).

Then failures occur exactly when e / 9 is represented by one of the integer quadratic forms Q_F subject to the parity, color, key, and root-packet inequalities.
```

If 1307 is special, it should appear as a represented value of one of these boundary forms, possibly with a prime-splitting condition in the discriminant of that form. If not, the important arithmetic is simply the factor 9 forced by n.

So my answer is: yes, n = 9(6l + 5) explains why the first visible failures are 9-multiples; no, it does not by itself explain why 11763 is the first large interior failure. The latter is a minimization problem over boundary-defect lattice points.

## Q3. Explicit strip boundary in (m,t,d)

Let

```text
U = u = (t + d + 1) / 2
V = v = (t - d + 1) / 2
l = m - 1.
```

The uniform Heaviside form of the strip is

```text
strip0(N,l) = H(l) - H(l - N),
```

where H(r) = 1 for r >= 0 and H(r) = 0 for r < 0. Therefore

```text
strip0(N,m - 1) = H(m - 1) - H(m - 1 - N).
```

Equivalently, as an interval in m,

```text
if N > 0:  strip0(N,m - 1) = +1 on 1 <= m <= N,
if N < 0:  strip0(N,m - 1) = -1 on N + 1 <= m <= 0,
if N = 0:  strip0(N,m - 1) = 0.
```

This also fixes an off-by-one point: for positive U, the support is

```text
1 <= m <= U = (t + d + 1) / 2,
```

not 1 <= m <= (t + d - 1) / 2, assuming the code convention really is 0 <= l < N.

Under τ,

```text
m -> -m
t -> -t
d -> d
U -> Uτ = 1 - V
V -> Vτ = 1 - U.
```

Therefore the U-strip τ-defect, written as a function of the original (m,t,d), is

```text
∂τ S_U(m,t,d)
  = strip0(U, m - 1) - strip0(1 - V, -m - 1)
  = H(m - 1) - H(m - 1 - U)
    - H(-m - 1) + H(V - m - 2).
```

Similarly the V-strip defect is

```text
∂τ S_V(m,t,d)
  = strip0(V, m - 1) - strip0(1 - U, -m - 1)
  = H(m - 1) - H(m - 1 - V)
    - H(-m - 1) + H(U - m - 2).
```

This is the discrete Stokes form. The strip is a difference of two half-lines. Its τ-defect is a signed sum of four half-lines. Equivalently, its jumps live on the four endpoint hyperplanes

```text
m = 1,
m = U + 1,
m = -1,
m = V - 1
```

for the U-strip, with the analogous U/V-swapped endpoints for the V-strip.

For the e = 11763 atom,

```text
m = -4,
U = -8,
V = -12.
```

Then

```text
strip0(U, m - 1)       = strip0(-8,-5) = -1,
strip0(1 - V, -m - 1) = strip0(13,3)  = +1,
∂τ S_U                 = -2.
```

So the strip defect is already nonzero before considering the missing-half theta piece. This is why the boundary is not a small numerical accident; it is built into the geometry of the strip cut.

## Q4. Should the compensation term be a partial theta series?

Yes. The compensation term should be a partial theta correction, or a finite linear combination of partial theta corrections, because both one-sided mechanisms are half-line cuts.

The missing-half term is literally a partial theta: it chooses one side of a quadratic root sum, switching from the negative half to the positive half when b = 2l + 1 = 2m - 1 changes sign.

The strip term is also a difference of partial theta cuts. Since

```text
strip0(N,l) = H(l) - H(l - N),
```

summing strip0(N,l) against a quadratic q-exponent gives

```text
sum H(l)       * q^{Q(l,...)}
-
sum H(l - N)  * q^{Q(l,...)}.
```

Each summand is one-sided. After the remaining variables are summed out, these are partial theta series or theta-like boundary series. Thus the natural correction is

```text
Comp(K;q) = - sum over canonical τ-orbits with key K of Φ_e(x) q^e,
```

or, after reorganizing by boundary rays,

```text
Comp(K;q) = finite sum over boundary families F of
            epsilon_F * sum over r >= 0 of q^{Q_F(r)}
```

with the parity and color restrictions inherited from the atom model.

This is exactly the expected shape from a discrete Stokes principle:

```text
bulk bilateral theta cancels under τ,
boundary half-lines do not,
the residual is a one-sided theta correction.
```

This also explains why a “modified involution” on the original atom set is unlikely to be the clean rescue. The map τ is essentially forced by the key-preserving central reflection (m,t,d) -> (-m,-t,d). A shifted reflection such as m -> -m - 1 would make one strip endpoint look more symmetric, but it would break the b/n root pairing and generally would not preserve the same key. The better rescue is to enlarge the atom set by ghost boundary atoms, or equivalently to add the explicit partial-theta compensation. In the enlarged set, τ pairs the bulk plus ghosts perfectly; after deleting the ghosts, their total is exactly the correction term.

## Wavefront interpretation and threshold prediction

The observed progression

```text
e = 90:    failures only in hblock = ±1 boundary shell
e = 702:   first deeper failure at hblock = -2
e = 11763: failures span hblocks [-7,5]
```

is naturally a wavefront. The wavefront is not moving because τ changes; τ is fixed. It moves because the root-packet support grows with e. As e increases, the quadratic root windows widen. More lattice points reach the half-line cuts m = 0, m = 1, and the strip endpoint hyperplanes. When a new hblock first intersects one of these boundary-defect loci, a new shell starts contributing.

The exact threshold for a shell H should be expressible as

```text
e_H = min E(m,t,d,j,color)
      subject to:
        hblock(m,t,d,color) = H,
        parity/integrality constraints,
        key is noncentral,
        Φ_e(m,t,d,j,color) != 0.
```

Because E is quadratic, this is an integer quadratic minimization over a finite union of boundary cones. The mod-9 observation says that, after symbolic simplification on those cones, E should factor as 9 times an integral quadratic form:

```text
e_H = 9 * min Q_F(parameters)
```

over the boundary families F that meet hblock H.

That is the clean threshold formula to look for. It may not be a single closed-form expression for all H; more likely it is the lower envelope of several quadratic forms, one for each missing-half or strip boundary family.

## What I would investigate first

1. Prove the bulk lemma symbolically:

```text
B(τx) = B(x), σ(τx) = -σ(x), key(τx) = key(x).
```

This isolates the problem completely from oddBilat.

2. Replace the current “atom has no τ partner” diagnostic by the orbit-flux diagnostic:

```text
χ_e(x) * C∂(x) - χ_e(τx) * C∂(τx).
```

This should predict every nonzero keyWeight row at e = 90, 702, and 11763.

3. Symbolically expand the strip defects using

```text
∂τ S_U = H(m - 1) - H(m - 1 - U) - H(-m - 1) + H(V - m - 2)
∂τ S_V = H(m - 1) - H(m - 1 - V) - H(-m - 1) + H(U - m - 2).
```

This should turn the strip contribution into named boundary rays.

4. Do the same for oddMissingSigned. Write the positive-half and negative-half truncations with Heaviside functions in the root variable j. Then compute their τ-defect after the root-pair map. This should identify the missing-half boundary rays.

5. For each boundary ray, derive the exponent polynomial e = E_F(parameters). Check whether E_F is always divisible by 9. Then tabulate represented values of E_F / 9. This will decide whether 1307 is arithmetically special or merely the first large represented value reaching the observed hblock depth.

6. Build the compensation as the negative of the boundary flux and simplify it family-by-family into partial theta series. The target form should be a finite sum of unilateral q-series, not an ad hoc table of exceptional atoms.

## Bottom line

The late failure is not mysterious once the support is viewed as a clipped bilateral object. The involution is correct in the bulk. The failure is caused by the half-line cuts. The correct repair is not to abandon τ, but to separate the bilateral term, compute the one-sided τ-flux, and add the resulting partial-theta boundary correction.

The mod-9 pattern is also not accidental: the root quadratic uses n = 9 times a 3-adic unit, so the boundary exponent families should live in e ≡ 0 mod 9. The precise breakdown values should be predicted by the minimum represented values of the boundary quadratic forms, shell by shell.