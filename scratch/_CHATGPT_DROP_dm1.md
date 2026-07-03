# Q3172 (dm1): Paper 2 Round 4 — shell = hblock, two-sided theta, and global/local charge

Date: 2026-07-03

## Executive answer

The new experiments substantially improve the framing.

The correct headline is no longer “first counterexample” and no longer “`9 | e`.”  The right headline is:

```text
The LRS root-packet obstruction is present from the first nonzero layer e=9,
but it is globally balanced.  The new phenomenon is a shell filtration by
hblock.  The hblock shells open at a two-sided unary theta sequence

    e(h) = 18 h(17h - 12),    h in Z.
```

Equivalently, for `j >= 1`, the two shell-opening branches are

```text
h = +j:  e_j^- = 18j(17j - 12),
h = -j:  e_j^+ = 18j(17j + 12).
```

This produces the observed interleaving:

```text
90, 522, 792, 1656, 2106, 3402, 4032, 5760, ...
```

The companion branch is not noise.  It is the negative-hblock side of the same theta series.  The right object is two-sided from the beginning.

The strongest conceptual theorem is now:

```text
hblock is the signed shell coordinate of the LRS root-packet boundary.  The
set of first appearances of hblock values is governed by a unary theta series
with quadratic exponent 18h(17h-12).  Individual key fibers carry nonzero
boundary charge from e=9 onward, but the total charge over all keys is expected
to vanish by a global divergence/telescoping theorem.
```

## 1. The two-sided shell-opening theta

The two experimental branches are

```text
onset_j     = 18j(17j - 12),
companion_j = 18j(17j + 12).
```

They are the positive and negative halves of one integer-indexed quadratic:

```text
e(h) = 18 h(17h - 12),    h in Z.
```

Indeed:

```text
h =  j > 0  gives 18j(17j - 12),
h = -j < 0  gives 18j(17j + 12).
```

Thus the complete shell-opening generating function is

```text
Theta_shell(q) = sum_{h in Z} q^{18 h(17h - 12)}.
```

If `Q = q^18`, this is

```text
Theta_shell(Q) = sum_{h in Z} Q^{17h^2 - 12h}.
```

Completing the square gives

```text
17h^2 - 12h = ((17h - 6)^2 - 36) / 17.
```

So

```text
Theta_shell(Q)
  = Q^{-36/17} * sum_{n ≡ -6 mod 17} Q^{n^2/17},
```

where `n = 17h - 6`.  If one records positive absolute residues, this is exactly the two-residue support

```text
n ≡ 6 or 11 mod 17.
```

This explains the observation that both residue classes `6` and `11` modulo `17` contribute.  They are not two unrelated series; they are the two orientations of the same coset theta.

### Modular-form status

`Theta_shell` is a unary theta series with rational characteristic.  After multiplying by the harmless fractional prefactor `Q^{36/17}`, it is a standard weight-`1/2` theta constant attached to the one-dimensional lattice/coset

```text
17 Z - 6.
```

It should be treated as a vector-valued or congruence-subgroup unary theta of weight `1/2`, not as an eta quotient.  The safest paper statement is:

```text
The shell-opening support is governed by the unary theta series

    sum_{h in Z} Q^{17h^2 - 12h}.

Equivalently, it is the theta series of the coset 17Z-6, shifted by Q^{-36/17}.
```

I would not claim a specific eta-product identity unless one is later proved.  Unary theta is the right identification.

## 2. What hblock measures geometrically

The new data strongly indicates:

```text
hblock = signed normal shell coordinate of the LRS boundary.
```

The root-packet key

```text
(hblock, anchor)
```

is therefore not an arbitrary bookkeeping pair.  It decomposes the LRS boundary into:

```text
hblock: signed distance/shell transverse to the base LRS wall,
anchor: tangential coordinate along the root-pair orbit inside that shell.
```

This interpretation explains all four observations:

1. `hblock=0` is the base wall layer and appears immediately at `e=9`.
2. New shells `±j` open only when the shell-opening theta reaches `e(h=±j)`.
3. The companion branch is the opposite orientation of hblock.
4. The anchor involution `n -> 12-n` is fiber-specific because the tangential coordinate depends on the chosen shell/fiber, while hblock records only the normal displacement.

### Likely algebraic form

At the LRS level, the full exponent should admit a normal form of the schematic shape

```text
E_LRS = 18 h(17h - 12) + R_h(anchor, auxiliary variables),
```

where

```text
h = hblock,
R_h >= 0
```

on the admissible LRS support.  The equality `R_h=0` gives the first opening of shell `h`.

This is the precise sense in which `hblock` is the shell index.  It is the coordinate that appears quadratically in the leading normal energy.

### What determines hblock from `(l,u,v,root variables)`?

The data is not yet enough to write the exact formula, but the form of the theorem is clear.  There should be an explicit affine-linear map

```text
hblock = H(l,u,v,n,branch)
```

or, more likely, a piecewise affine-linear map depending on the LRS branch.  The anchor then records the companion tangential root coordinate.  The root-pair involution

```text
n -> 12 - n
```

acts primarily on the anchor coordinate, while `hblock` records the shell containing that anchor pair.

The immediate task is to extract this map from the implementation and write it as a theorem:

```text
LRSKey(atom) = (H(atom), A(atom)),
H(atom) is the signed shell normal coordinate,
A(atom) is the anchor/tangential coordinate.
```

## 3. The hblock=0 base layer

The base layer is now the simplest local obstruction object.

You found at `e=9`:

```text
(0,-1):  1
(0, 1):  1
(0, 3): -1
(0, 5): -2
(0, 7):  1
```

and the sum is

```text
1 + 1 - 1 - 2 + 1 = 0.
```

This strongly suggests that `hblock=0` is a one-dimensional boundary transfer along the anchor coordinate.  It is already locally nonzero at the first possible exponent, but its total charge cancels.

### Generating function expectation

Because hblock `0` has bad keys at every `e=9n` from `n=1` onward, its support is dense in the `q^9` variable.  Therefore it is unlikely to be a sparse unary theta by itself.  It is more likely one of the following:

```text
1. a finite-difference/telescoping series along anchors;
2. a rational q-series in q^9, such as a finite combination of q^a/(1-q^b);
3. a partial-theta boundary series whose signed total telescopes to zero;
4. a coefficientwise transfer operator between adjacent anchor fibers.
```

The right object to fit is not just the set of bad keys.  Define the per-anchor charge series

```text
C_a(Q) = sum_{n >= 1} keyWeight(e=9n, hblock=0, anchor=a) Q^n.
```

Then test:

```text
C_0_total(Q) = sum_a C_a(Q).
```

The e=9 data suggests

```text
C_0_total(Q) = 0
```

or perhaps zero after including all anchors and all LRS branches.  If true, the base layer is a pure redistribution of charge between keys, not a global obstruction.

### Recognizability

I would not call the hblock=0 series an eta quotient yet.  Dense support at every `Q^n` is more characteristic of a rational/false-theta transfer series than a theta series.  The right first theorem is a telescoping theorem:

```text
sum_anchor keyWeight(9n,0,anchor) = 0 for all n.
```

Only after this is proved should one try to identify individual `C_a(Q)`.

## 4. Refining Fable's fiber onset formula

Fable's proposed fiber formula was

```text
onset_j(fiber) = 18j((|l|+|v|)j - |v|).
```

For the minimizing fiber

```text
(l,u,v)=(-5,-8,-12),
```

this gives

```text
|l| + |v| = 17,
|v| = 12,
```

and hence

```text
18j(17j - 12),
```

which matches the observed positive-hblock branch.

### Refinement: use chamber distances, not absolute values

The absolute values are a clue but probably not the final theorem.  In the chamber containing the minimizing fiber, `l<0` and `v<0`, so

```text
|l| = -l,
|v| = -v,
|l|+|v| = -(l+v).
```

A more structural formula is therefore:

```text
onset_j(l,v) = 18j( L(l,v) * j - V(l,v) ),
```

where `L(l,v)` and `V(l,v)` are positive distances to the relevant LRS support walls.  In this chamber,

```text
L(l,v) = -l - v,
V(l,v) = -v.
```

The formula then becomes

```text
onset_j(l,v) = 18j( (-l-v)j + v ).
```

For `l=-5`, `v=-12`, this is exactly `18j(17j-12)`.

### What it implies about the LRS normal form

It implies that, in a fixed chamber/fiber, the full LRS energy has normal coordinate `h=hblock` and leading term

```text
18 [ L h^2 - V h ].
```

For the opposite hblock orientation, one gets the companion branch

```text
18 [ L h^2 + V h ]
```

with `h=j>0`, or uniformly

```text
18 h (L h - V)
```

for signed `h` if the sign convention is chosen correctly.

This is exactly the two-sided theta form.  The companion branch is not a refutation of the formula; it is the negative hblock orientation.

### Proof target

The theorem to prove is:

```text
LRS normal form in a chamber.
For each LRS chamber C and fiber parameter (l,u,v), there are wall-distance
functions L_C(l,u,v), V_C(l,u,v) such that

    E_LRS(atom) = 18 hblock (L_C hblock - V_C) + R_C(anchor, other variables),

with R_C >= 0 on the admissible support.
```

Then the global shell-opening sequence is obtained by minimizing over chambers/fibers.

## 5. Is the total sum over all keys always zero?

This is now one of the most important questions.

The e=9 data shows local nonzero key charges but total charge zero:

```text
sum_K keyWeight(9,K) = 0.
```

The natural conjecture is:

```text
GlobalCharge(e) := sum_K keyWeight(e,K) = 0 for every e.
```

This is exactly what one expects if keyWeight is a discrete boundary divergence on the key graph.

### Divergence interpretation

Think of keys as vertices and boundary pairings as directed edges.  Each defective atom contributes a signed current along an edge between keys.  The local keyWeight is the divergence at one vertex:

```text
keyWeight(e,K) = div J_e(K).
```

Then summing over all keys gives

```text
sum_K div J_e(K) = 0
```

provided there is no external boundary after all LRS branches are included.

This explains the phenomenon:

```text
global q-series identity can still be true,
while the fiber-local keyWeight=0 proof fails.
```

The local charges are nonzero, but they are internal transfers between key fibers.

### Caveat

You must be precise about what is being summed.  The theorem should include:

```text
all keys,
all LRS branches,
all signs,
the exact same exponent e.
```

If one sums only `normal_bad` keys or only a single branch, the total may not vanish.

### Suggested theorem

```text
Global telescoping theorem.
For every exponent e,

    sum_{K} keyWeight(e,K) = 0.

Equivalently, the LRS boundary charge is globally exact, but not fiberwise zero.
```

This theorem would be a major repair of the original proof strategy.  It says the old conjecture was too local, not globally false.

## 6. Correct theorem architecture for Paper 2

The correct architecture is now clear.

### The old framing to remove

Do not headline:

```text
9|e is necessary.
```

It is vacuous because atoms already occur only at `e` divisible by `9`.

Do not headline:

```text
first counterexample onset.
```

Bad keys already occur at `e=9`.

Do not headline:

```text
M^2 ≡ -I mod 9 explains the LRS fiber counterexample.
```

`M` acts at the cone/Pell layer, not directly at the LRS key layer.

### New headline

Use:

```text
A fiber-local cancellation failure with a shell-filtration law.
```

or more mathematically:

```text
The LRS boundary charge is globally telescoping but not fiberwise zero; its
key support is filtered by hblock shells whose openings form a two-sided unary
theta series.
```

### Suggested main theorem package

#### Theorem 1: LRS key decomposition

Define the LRS atom, exponent, sign, and key

```text
K = (hblock, anchor).
```

#### Theorem 2: hblock is shell

Prove or state with verified cases:

```text
A bad key with |hblock| > j cannot occur below the j-th shell-opening level.
The first appearance of hblock h occurs at

    e(h) = 18 h(17h - 12).
```

Equivalently, the shell-opening generating function is

```text
Theta_shell(q) = sum_{h in Z} q^{18h(17h-12)}.
```

#### Theorem 3: local nonzero from the base layer

Show:

```text
Bad keys exist at every e=9n from n=1 onward, already in hblock=0.
```

If not yet proved for all n, state as a conjecture with strong data.

#### Theorem 4: global telescoping

Prove/conjecture:

```text
sum_{hblock,anchor} keyWeight(e,hblock,anchor) = 0 for all e.
```

This explains why the global q-series identity survives despite local key failures.

#### Theorem 5: boundary generating function

Connect to the cone/Paper 3 layer:

```text
Boundary_GF = Theta_u * Theta_v * (D-A),
D-A = -f_{1,3,4}(X,-X^3,X).
```

#### Theorem 6: cone/Pell shadow

State separately:

```text
The discriminant-5 cone factor has Pell deck anti-periodicity M^2 ≡ -I mod 9
and the norm/coset stabilizer eps^6.  This is the global cone shadow of the
LRS boundary, not the direct hblock-key action.
```

## 7. Answering the six questions directly

### Q1. Is the two-sided onset support a theta function?

Yes.  The complete shell-opening support is the unary theta series

```text
Theta_shell(q) = sum_{h in Z} q^{18h(17h-12)}.
```

In `Q=q^18`, it is

```text
sum_{h in Z} Q^{17h^2-12h}
  = Q^{-36/17} sum_{n≡-6 mod17} Q^{n^2/17}.
```

It is a weight-`1/2` unary theta with rational characteristic, best viewed as a vector-valued theta/coset theta.  I would not identify it as an eta quotient unless later proven.

### Q2. What does hblock measure geometrically?

`hblock` is the signed normal shell coordinate of the LRS boundary.  The `anchor` is the tangential coordinate along the root-pair fiber.  Geometrically, the key `(hblock,anchor)` is a normal/tangential coordinate system for the LRS boundary charge.

### Q3. What is the hblock=0 generating function?

It is likely a one-dimensional anchor-transfer or telescoping series, not a sparse theta.  Since hblock=0 bad keys occur at every `e=9n`, its support is dense in the `q^9` variable.  The most promising theorem is not eta-product identification but a telescoping identity:

```text
sum_anchor keyWeight(9n,0,anchor) = 0.
```

Individual anchor series may be rational or partial-theta-like; they should be fitted separately.

### Q4. Verify/refine Fable's formula

Refine absolute values into chamber distances.  In the chamber of the minimizing fiber `l=-5,v=-12`, the formula is

```text
onset_j = 18j(((-l-v)j + v)) = 18j(17j-12).
```

The general theorem should use wall-distance functions, not literal absolute values.  It implies a normal form

```text
E_LRS = 18[L hblock^2 - V hblock] + residual,
```

with nonnegative residual on the support.

### Q5. Does total boundary charge vanish globally?

Very likely, and this should become a central theorem.  The e=9 data supports the divergence interpretation:

```text
local key charges are nonzero,
but their total over keys is zero.
```

If true for all e, it explains exactly why the fiber-local proof fails while the global q-series identity can remain true.

### Q6. Correct paper architecture?

The headline should be:

```text
The LRS root-packet cancellation is globally telescoping but not fiberwise.
Its local defects are organized by hblock shells, and the shell-opening levels
form a two-sided unary theta series.
```

Then the Paper 3 factorization appears as the global generating function of those boundary transfers:

```text
Theta_u * Theta_v * (D-A),
D-A = -f_{1,3,4}(X,-X^3,X).
```

## 8. Concrete next computations

### 8.1 Extract per-hblock onset data

For each hblock `h`, compute the first exponent and confirm:

```text
first_e(h) = 18h(17h-12).
```

Include `h=0`, where this formula gives `0`; the first nonzero bad-key layer for hblock 0 is `e=9`, so hblock 0 should be treated as the base transfer layer rather than a shell opening.

### 8.2 Test global telescoping

For many exponents `e=9n`, compute:

```text
TotalCharge(e) = sum_{hblock,anchor} keyWeight(e,hblock,anchor).
```

If this is always zero, it should become the main theorem.

### 8.3 Fit hblock=0 anchor series

For each anchor `a`, compute

```text
C_a(Q) = sum_{n>=1} keyWeight(9n,0,a) Q^n.
```

Look for:

```text
finite differences,
periodicity in anchor mod something,
rational functions,
partial theta pieces.
```

### 8.4 Extract the LRS normal form

For actual LRS atoms, compute

```text
R(atom) = E_LRS(atom) - 18*hblock*(17*hblock - 12).
```

Then test:

```text
R(atom) >= 0,
R(atom)=0 exactly at shell-opening wavefronts.
```

This is the direct path to a proof.

## 9. Minimal code skeleton for the theta and count analysis

```python
from collections import defaultdict
from dataclasses import dataclass
from typing import Iterable


def shell_opening(h: int) -> int:
    """Two-sided hblock shell-opening exponent."""
    return 18 * h * (17 * h - 12)


def positive_onset(j: int) -> int:
    return shell_opening(j)


def companion_onset(j: int) -> int:
    return shell_opening(-j)


for j in range(1, 6):
    print(j, positive_onset(j), companion_onset(j))


@dataclass(frozen=True)
class Key:
    hblock: int
    anchor: int


def total_charge(charges: dict[Key, int]) -> int:
    return sum(charges.values())


def charges_by_hblock(charges: dict[Key, int]) -> dict[int, int]:
    out: defaultdict[int, int] = defaultdict(int)
    for key, value in charges.items():
        out[key.hblock] += value
    return dict(out)


def bad_key_count(charges: dict[Key, int]) -> int:
    return sum(1 for value in charges.values() if value != 0)
```

Expected opening sequence:

```text
j=1: 90, 522
j=2: 792, 1656
j=3: 2106, 3402
j=4: 4032, 5760
j=5: 6570, 9540
```

## Bottom line

The corrected Round 4 picture is coherent and publishable:

```text
Bad keys are not rare first appearing at high energy; they exist from e=9.
The real structure is a shell filtration.
hblock is the shell coordinate.
The shell-opening support is the two-sided unary theta

    sum_{h in Z} q^{18h(17h-12)}.

Local key charges can be nonzero while the global charge likely telescopes to
zero.  The norm/cone false theta of Paper 3 is the global generating function
of this LRS boundary transfer after summing and reindexing.
```

This is a much stronger and cleaner narrative than the old divisibility framing.
