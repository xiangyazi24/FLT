# Q3170 (dm1): Paper 2 Round 2 — `M^2 ≡ -I mod 9` and the root-packet/fiber issue

Date: 2026-07-03

## Executive answer

The confirmed congruence

```text
M^2 ≡ -I mod 9
```

is important, but it should be interpreted carefully.  It is a **deck anti-periodicity on the Pell/cone coordinates**, not automatically an action on root-packet fibers.

The correct separation of layers is:

```text
Layer 1: root-packet/fiber layer
  variables: (l,u,v) plus root variables n_i
  key: (hblock, anchor)
  tau: central reflection in (m,t,d)

Layer 2: even-k/cone layer
  variables: (u,v,k,r) in even_k_exp
  cone block: Q_kr(k,r)
  sigma: (k,r) -> (k, -r-6k-1)

Layer 3: Pell/norm layer
  variables: X=4k+3r+1, Z=5r+1
  Pell automorph: M = [[9,-4],[-20,9]]
  confirmed: M^2 ≡ -I mod 9
```

The critical point is that `(hblock, anchor)` is **not the same coordinate system** as `(k,r)`.  The anchor is a root-packet root variable, and in the displayed counterexample it is the root variable `n=-17` from the last `j(54k+18,18,r)` block.  It is not the Pell coordinate `r`, not the same as the cone coordinate `r`, and not obviously transformed by `M` unless the full root-packet key map is carried along.

So the best theorem framing is not simply “`M` acts on fibers.”  The right theorem is:

```text
The cone/Pell deck group explains the q^9 boundary charge after projecting
from root packets to the missing-kernel cone.  To make it act fiberwise, one
must lift the deck action to decorated atoms carrying the root-packet key.
```

The most publishable statement is a boundary-charge theorem:

```text
keyWeight is the Z/9-deck boundary charge of the tau pairing.
Off e ≡ 0 mod 9 the deck charge is zero; on e ≡ 0 mod 9 it is the fiberwise
shadow of the discriminant-5 false theta cone D-A.
```

I would avoid the slogan “keyWeight vanishes iff 9 ∤ e” unless it is phrased as a support theorem.  The data says nonmultiples of 9 have no failures, but not that every multiple of 9 fails.

## Q1. Relation between `(k,r)` in `even_k_exp` and `(hblock, anchor)` in the root packet

The root packet and the cone block are two different projections of the same expanded summand.

You gave:

```text
even_k_exp(u,v,k,r)
  = j(-18,90,v)
  + j(18,90,u)
  + j(18,18,2k)
  + j(54k+18,18,r).
```

The root-packet fiber key uses root data from the four `j` blocks.  In the counterexample, the relevant root variables are

```text
n in {-3, 15, 29, -17},
```

and the key anchor `-17` is the root variable from the final block

```text
j(54k+18,18,r).
```

Therefore:

```text
anchor = root variable of a j-block after the root-packet extraction,
not the raw cone variable r in even_k_exp.
```

This distinction is essential.  The variable `r` in the cone block is an index in the Hecke-Rogers cone.  The anchor is a root-packet coordinate produced after applying the root-pair/fiber extraction to the `j(A,B,variable)` pieces.  In the final block, the anchor is controlled by both the displayed `r` and the row parameter `54k+18`, because the roots of the row depend on the coefficient as well as the index.

### Is `hblock` a function of `k` only?

Almost certainly no.

`hblock` is a fiber label in the root packet, so it must encode how the four root variables combine after the row decomposition.  Since the four root variables come from

```text
v,
u,
2k,
r with row coefficient 54k+18,
```

any fiber label built from them can depend on `u`, `v`, `k`, and the row/strip choice.  Even if one component of `hblock` is largely controlled by `k`, the counterexample already shows that the key

```text
(hblock, anchor)=(-6,-17)
```

is not recoverable from `(k,r)` alone unless the root-packet map is explicitly known.

### What to instrument

Add a diagnostic map in the code/probe layer:

```text
rootKey(u,v,k,r) = (hblock, anchor)
```

and print it alongside the cone coordinates:

```text
(u,v,k,r)
root variables from the four j-blocks
(hblock, anchor)
Pell coordinates (X,Z)
sigma(k,r)
M(k,r) or M^2(k,r) when integral
```

The theorem you need before claiming `M` acts on fibers is:

```text
rootKey(T(u,v,k,r)) = transformKey(rootKey(u,v,k,r))
```

for the proposed deck transformation `T`.  Without this theorem, `M` is only acting on the cone/Pell projection.

## Q2. Does `M` descend to fibers or permute `(hblock, anchor)` keys?

Not directly, at least not as the one-step matrix `M` on `(X,Z)`.

You define

```text
X = 4k + 3r + 1,
Z = 5r + 1,
M = [[9,-4],[-20,9]].
```

The inverse relations are

```text
r = (Z-1)/5,
k = (5X - 3Z - 2)/20.
```

Now apply `M`:

```text
X' = 9X - 4Z,
Z' = -20X + 9Z.
```

If `Z ≡ 1 mod 5`, then

```text
Z' ≡ -Z ≡ -1 mod 5,
```

so `M` does **not** preserve the original `(k,r)` lattice/coset.  It sends the cone lattice to the opposite congruence coset.  This is already enough to say:

```text
M alone cannot descend to the original root-packet fibers without an additional
coset/sign/deck correction.
```

By contrast, `M^2` does preserve the original congruence conditions.  Explicitly,

```text
M^2 = [[161,-72],[-360,161]].
```

In `(k,r)` coordinates this gives the affine transformation

```text
T = M^2:
  k' = 377k + 72r + 52,
  r' = -288k - 55r - 40.
```

Modulo `9`, this is

```text
k' ≡ -k - 2 mod 9,
r' ≡ -r + 5 mod 9.
```

This is the affine version of the confirmed statement `M^2 ≡ -I mod 9` in Pell coordinates.  It is anti-periodic, not periodic.

### Does this permute keys?

It can only permute keys after lifting to the decorated state.  The map `T=M^2` changes `(k,r)` drastically and does not specify how `u` and `v` should change.  But the root-packet key depends on the four `j` blocks, so a fiber action must be a transformation of

```text
(u,v,k,r; root variables; hblock; anchor),
```

not only `(k,r)`.

The most likely situation is:

```text
M^2 preserves the boundary energy and q^9 residue class,
but it sends a root-packet fiber to a different fiber unless accompanied by
compensating shifts in u,v and/or the root-pair representatives.
```

So the answer is:

```text
M^2 descends to the cone coefficient system.
It does not yet descend to root-packet fibers until the key map is lifted.
```

## Q3. Dihedral group `<M, sigma>` and its action on fibers

The group generated by the Pell translation `M` and the reflection

```text
sigma(k,r) = (k, -r - 6k - 1)
```

is the expected infinite dihedral group of the indefinite binary form.

Conceptually:

```text
M       = hyperbolic translation / unit action along the Pell orbit,
sigma   = wall reflection preserving Q_kr and flipping (-1)^r,
<M,sigma> = D_infinity orbit group of the discriminant-5 cone.
```

This group explains the **cone** cancellation pattern:

1. The full bilateral cone is invariant under the group.
2. `sigma` pairs the two sides of the wall and flips the sign.
3. The A/D cone cut selects a non-invariant fundamental region.
4. The residual is the signed crossing number through that cut.

But the root-packet fiber action is again subtler.  The group acts naturally on `(k,r)` and on Pell coordinates `(X,Z)`, while the fiber key lives in root-packet coordinates.  Therefore define a decorated action:

```text
DecoratedAtom = (u,v,k,r, rootData, key)
```

and try to lift the generators:

```text
sigma_hat : DecoratedAtom -> DecoratedAtom
M_hat     : DecoratedAtom -> DecoratedAtom  or  M2_hat
```

with properties:

```text
energy(sigma_hat x) = energy(x),
energy(M2_hat x) = energy(x) or same q^9 boundary class,
key(sigma_hat x) = key(x) or controlled key transform,
weight(sigma_hat x) = -weight(x),
```

depending on the exact fiber notion.

### What likely explains the keyWeight pattern

The keyWeight pattern is not simply “orbits of `<M,sigma>` have zero sum.”  It is:

```text
keyWeight is the signed intersection number of a root-packet fiber with the
A/D Shintani cone boundary after projecting to the `(k,r)` block.
```

If a fiber is closed under the lifted sigma/deck action, the signed intersection is zero.  If the fiber straddles the boundary and the tau ghost lies outside support, the intersection number is nonzero.

So the group explains the pattern only after you add:

```text
projection from root packet to cone,
finite key map,
boundary window,
lifted/decorated action.
```

## Q4. Best theorem framing for the paper

The three proposed framings were:

```text
(a) keyWeight vanishes iff 9 does not divide e; when 9|e, it is the Z/9-deck boundary charge
(b) Missing kernel GF = Z/9-periodic false theta
(c) tau is Z/9-approximate involution on support lattice
```

### Ranking

The strongest publishable framing is a refined version of **(a)** plus the generating-function identification from **(b)**:

```text
Main theorem.
The failure of the tau fiber pairing is a q^9-supported boundary divergence.
Equivalently, the missing-kernel generating function is a q^9-dilated
Hecke-Rogers false theta cone.  Off e ≠ 0 mod 9 the boundary charge vanishes.
```

I would not use the wording “iff 9 does not divide e” unless you mean the support of the obstruction, not failure at every fiber.  The data says:

```text
9 ∤ e  => no failure,
9 | e  => failure possible, but not guaranteed.
```

So the clean theorem is:

```text
keyWeight obstruction is supported on e ∈ 9Z.
```

### Why not (c)?

“tau is a Z/9-approximate involution” is a useful slogan but less precise.  A referee will ask:

```text
Approximate in what category?
What is the quotient?
What is the actual deck group?
```

If you want to use it, put it in the introduction as intuition, not as the main theorem.

### Suggested title-level theorem

```text
Theorem.
For Chan's Theta_10 root-packet expansion, the tau-pairing defect is the
boundary divergence of a Z/9-deck current.  Its generating function is the
q^9-dilated discriminant-5 Hecke-Rogers false theta factor

    D-A = -f_{1,3,4}(X,-X^3,X).

In particular, all fiber obstructions vanish for e not divisible by 9.
```

This is both mathematically sharp and directly connected to Papers 2/3.

## Q5. Shell depth onset formula

The M-orbit geometry suggests the right **method** for shell onset, but a literal formula needs the root-key constraints.

### Cone-only shell distance

For the sigma wall, the straddling boundary is

```text
k >= 0: r <= -6k - 1,
k < 0: r >= -6k.
```

For the `k >= 0` side, define shell distance

```text
s = -r - 6k - 1 >= 0,
```

so

```text
r = -6k - 1 - s.
```

For the cone quadratic

```text
Q_kr(k,r) = 4k^2 + 6kr + r^2 + 2k + r,
```

substitution gives

```text
Q_kr(k, -6k-1-s) = 4k^2 + 6ks + 2k + s^2 + s.
```

Thus, cone-only, the minimal wall energy at shell `s` is achieved at `k=0`:

```text
Q_min_cone(s) = s^2 + s.
```

This is the first term in any onset formula.

### Why this does not yet give `90` and `792`

The observed onsets

```text
shell 1: e = 90 = 9*10,
shell 2: e = 792 = 9*88,
```

are much larger than `9*(s^2+s)` alone.  Therefore shell onset is not only cone-wall distance.  It also includes:

```text
u/v theta factors,
root-packet key constraints,
parity/coset restrictions,
strip/missing-half support inequalities.
```

The correct formula is a constrained quadratic minimization:

```text
onset_s(K-class) = 9 * min {
    E_boundary(u,v,k,r,...) :
    shell(k,r)=s,
    rootKey(u,v,k,r,...) belongs to the target fiber class,
    parity/coset/support constraints hold
}.
```

Globally:

```text
onset_s = min over all eligible key classes of onset_s(K-class).
```

### How `M` enters

The Pell automorph `M` or `M^2` organizes all lattice points at a fixed norm into orbits.  Shell onset should be found by reducing the minimization to a finite set of residues in one Shintani domain:

```text
1. Fix shell distance s.
2. Reduce by the deck subgroup that preserves the relevant coset/key data.
3. Enumerate the finite residue classes modulo 9 and the support congruences.
4. Minimize the positive representative of the quadratic energy in that domain.
5. Propagate higher solutions by M-orbits.
```

This is exactly the same shape as the prime-sector table in Paper 3, but now the finite quotient is the `mod 9` deck quotient coming from `M^2 ≡ -I`.

### Concrete theorem target

```text
ShellOnsetTheorem.
For each shell distance s, the first possible keyWeight obstruction is

  onset_s = 9 * min_{c in C_s} Q_s(c),

where C_s is a finite set of residue/key/support classes modulo the Z/9 deck,
and Q_s is the reduced boundary quadratic.
```

Then the numerically observed values become checks:

```text
onset_1 = 90,
onset_2 = 792,
```

and shell 3 can be predicted before brute-force scanning.

## Q6. Paper 2 + Paper 3 fusion

Yes, there is likely a single theorem subsuming both, but it should be formulated at the level of **local unit/deck obstruction**, not as a claim that the two phenomena are literally the same congruence.

### Common structure

Both stories have the same skeleton:

```text
1. A real-quadratic indefinite theta cone over Q(sqrt(5)).
2. A finite coset/support condition.
3. A natural involution/reflection that cancels the bilateral bulk.
4. A unit/deck group that fails to act trivially on the finite coset.
5. A residual boundary charge supported on a smaller congruence subseries.
```

Paper 2 / keyWeight side:

```text
local obstruction: prime 3 / mod 9 deck
confirmed: M^2 ≡ -I mod 9
consequence: tau pairing is exact off the q^9 boundary subseries
```

Paper 3 / nonmultiplicative norm side:

```text
local obstruction: prime 2 and ramified prime 5 through O_K/(2sqrt5)
eps has order 3 mod 2 and order 2 mod sqrt5
consequence: eps^6 stabilizes L, eps does not; coefficients do not descend to ideals
```

The common `3` is structural:

```text
Paper 2: q^9 = (q^3)^2 / mod-9 additive deck at inert prime 3.
Paper 3: F_4^× has order 3 at inert prime 2.
```

Both are cubic-sector obstructions inside the same discriminant-5 cone mechanism.

### Fable's “-1 not in `<eps^6>`” claim

I would restate this more cautiously.

A precise version is:

```text
Both anomalies measure anti-invariance of the natural deck/unit action on a
finite local quotient.  In Paper 2 the anti-invariance is M^2 ≡ -I mod 9.
In Paper 3 the nontrivial unit phase is eps mod (2sqrt5), whose stabilizer on
L is eps^6 rather than eps.
```

That is defensible.

I would not yet state:

```text
both anomalies are exactly -1 not in <eps^6>
```

unless you define a single group and a single quotient in which this sentence is literally true.

### Unified paper theorem

A unified paper could say:

```text
Theorem schema.
Let C be the discriminant-5 Hecke-Rogers cone arising from Chan's Theta_10.
The bilateral theta attached to C has a dihedral deck group generated by a Pell
translation and a wall reflection.  Finite local coset conditions break this
deck symmetry.  The broken symmetry has two shadows:

  (i) an additive mod-9 boundary charge in root-packet fibers, causing exactly
      the q^9-supported keyWeight obstruction;

  (ii) a multiplicative mod-(2sqrt5) unit phase, causing norm support without
       multiplicativity and prime coefficients governed by a sector invariant.
```

This would fuse Paper 2 and Paper 3 into one conceptual story:

```text
Chan's Theta_10 dissection produces a discriminant-5 false theta boundary.
The boundary is controlled by a dihedral/Pell deck group.
The q^9 and eps^6 phenomena are the additive and multiplicative local
manifestations of the same broken deck symmetry.
```

### Should they be one paper?

I would keep them separate unless the unified theorem is fully proved.

Best strategy:

```text
Paper 2: keyWeight counterexample and q^9 boundary-charge theorem.
Paper 3: norm-supported nonmultiplicative false theta and prime-sector theorem.
Fusion note/paper: the common dihedral deck mechanism, after both sides are solid.
```

The fusion is conceptually powerful, but it raises the proof burden.  For publication, the safest route is to prove the two shadows cleanly first.

## Recommended next experiments

### 1. Instrument the key map

Dump the following table for every atom near the counterexample and for a few M/sigma images:

```text
(l,u,v,k,r)
(m,t,d)
four root variables n_i
(hblock, anchor)
(X,Z)
M(X,Z), M^2(X,Z)
sigma(k,r)
rootKey after each defined transform
support flag
keyWeight contribution
```

This will answer Q1/Q2 empirically and identify the correct decorated action.

### 2. Verify M-coset behavior

Use this small script as a sanity checker.

```python
from dataclasses import dataclass
from typing import Tuple


@dataclass(frozen=True)
class KR:
    k: int
    r: int


def pell_coords(x: KR) -> Tuple[int, int]:
    X = 4 * x.k + 3 * x.r + 1
    Z = 5 * x.r + 1
    return X, Z


def from_pell(X: int, Z: int) -> KR | None:
    if (Z - 1) % 5 != 0:
        return None
    r = (Z - 1) // 5
    num = 5 * X - 3 * Z - 2
    if num % 20 != 0:
        return None
    k = num // 20
    return KR(k, r)


def M(X: int, Z: int) -> Tuple[int, int]:
    return 9 * X - 4 * Z, -20 * X + 9 * Z


def M2_on_kr(x: KR) -> KR:
    X, Z = pell_coords(x)
    X1, Z1 = M(*M(X, Z))
    y = from_pell(X1, Z1)
    if y is None:
        raise ValueError((x, X1, Z1))
    return y


def sigma(x: KR) -> KR:
    return KR(x.k, -x.r - 6 * x.k - 1)


def qkr(x: KR) -> int:
    k, r = x.k, x.r
    return 4 * k * k + 6 * k * r + r * r + 2 * k + r


for x in [KR(0, 0), KR(0, -2), KR(1, -8), KR(-1, 3)]:
    y = M2_on_kr(x)
    print(x, "M2=", y, "mod9=", (y.k % 9, y.r % 9), "Q", qkr(x), qkr(y))
    z = sigma(x)
    print("  sigma=", z, "Q", qkr(z))
```

Expected facts:

```text
M does not preserve the original KR lattice/coset.
M^2 does preserve it.
M^2 is affine anti-periodic modulo 9 in KR coordinates.
sigma preserves Q_kr and flips the wall side.
```

### 3. Define shell distance and minimize

```python
from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class KR:
    k: int
    r: int


def shell_distance(x: KR) -> Optional[int]:
    k, r = x.k, x.r
    if k >= 0 and r <= -6 * k - 1:
        return -r - 6 * k - 1
    if k < 0 and r >= -6 * k:
        return r + 6 * k
    return None


def qkr(x: KR) -> int:
    k, r = x.k, x.r
    return 4 * k * k + 6 * k * r + r * r + 2 * k + r


def cone_onset(shell: int, k_bound: int = 100) -> tuple[int, KR]:
    best: tuple[int, KR] | None = None
    for k in range(0, k_bound + 1):
        r = -6 * k - 1 - shell
        x = KR(k, r)
        val = qkr(x)
        if best is None or val < best[0]:
            best = (val, x)
    if best is None:
        raise ValueError(shell)
    return best


for s in range(1, 6):
    print(s, cone_onset(s))
```

This gives only the cone onset.  To match observed keyWeight onsets, add the root-key/support constraints to the minimization.

## Bottom line

The confirmation `M^2 ≡ -I mod 9` is the missing algebraic bridge between the q^9 keyWeight phenomenon and the discriminant-5 cone geometry.  But the root-packet key layer is not the same as the cone `(k,r)` layer.  The immediate next theorem should therefore be a decorated-lift theorem, not a bare Pell-orbit theorem:

```text
Lift the dihedral cone deck action to decorated root atoms, or prove exactly
which part of the root key it changes.
```

Once that is done, the clean paper statement is:

```text
The keyWeight counterexample is a Z/9 boundary charge of the discriminant-5
Pell/Shintani deck.  The same deck, viewed multiplicatively through the unit
coset stabilizer eps^6, produces the nonmultiplicative norm theta series of
Paper 3.
```
