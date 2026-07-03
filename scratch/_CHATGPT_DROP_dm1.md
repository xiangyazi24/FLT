# Q3173 (dm1): Paper 2 Round 5 — Ramanujan Theta + Factorization + All Anchors Odd

Date: 2026-07-03

## Executive answer

The R5 results support a sharper paper thesis:

> The bad-key/counterexample set is not just filtered by `hblock`; it is theta-filtered.  The shell-opening factor is a unary Ramanujan/Jacobi theta component, and if the shell-copy factorization conjecture holds, the full bad-key enumerator is a base-layer object multiplied by that theta component.

The central identity is

```text
Θ(q) = Σ_{n∈Z} q^{18 n(17n+12)}
     = Σ_{h∈Z} q^{18 h(17h-12)}
     = f(q^522, q^90)
     = j(-q^90; q^612)
     = (-q^90;q^612)_∞ (-q^522;q^612)_∞ (q^612;q^612)_∞.
```

The change from `n` to `h` is `h = -n`.  Thus the empirical shell onset

```text
onset(h) = 18h(17h-12)
```

is exactly the two-sided exponent set of `f(q^522,q^90)`.

The factorization conjecture should be written as a generating-function identity

```text
Bad(q) = N_0(q) Θ(q),
```

or coefficientwise

```text
Bad(E) = Σ_{n∈Z} N_0(E - 18n(17n+12)),
```

with `N_0(t)=0` for negative `t`.  This is the cleanest formulation of “every shell is a translated copy of the base layer.”

The main caution: the number `612` is the Jacobi-product modulus / q-period.  It should not automatically be called the scalar modular level or conductor.  The natural object is a weight `1/2` unary theta component with a rational characteristic of denominator `17`, scaled by `72`; a safe ambient congruence level for the vector-valued theta description is `68*72 = 4896`, while the scalar stabilizer may be described more economically only after fixing the exact representation/stabilizer.

---

## Q1. What modular form is `f(q^522,q^90)`?

Use Ramanujan's general theta function

```text
f(a,b) = Σ_{n∈Z} a^{n(n+1)/2} b^{n(n-1)/2}.
```

Then

```text
f(q^522,q^90)
  = Σ_{n∈Z} q^{522 n(n+1)/2 + 90 n(n-1)/2}
  = Σ_{n∈Z} q^{306n^2 + 216n}
  = Σ_{n∈Z} q^{18n(17n+12)}.
```

Equivalently, with `Q=q^18`,

```text
Θ(q) = f(Q^29,Q^5) = j(-Q^5; Q^34),
```

where

```text
j(x;Q) = (x;Q)_∞(Q/x;Q)_∞(Q;Q)_∞.
```

So the product is

```text
j(-q^90;q^612)
 = (-q^90;q^612)_∞ (-q^522;q^612)_∞ (q^612;q^612)_∞.
```

### Theta-constant description

Complete the square:

```text
18n(17n+12)
  = (18/17)((17n+6)^2 - 36).
```

Therefore

```text
q^(648/17) Θ(q)
  = Σ_{m ≡ 6 mod 17} q^{18m^2/17}.
```

Using the standard unary theta components

```text
θ_{m,r}(τ) = Σ_{x ≡ r mod 2m} q^{x^2/(4m)},       q = e^{2πiτ},
```

we get

```text
q^(648/17) Θ(τ)
  = θ_{17,6}(72τ) + θ_{17,23}(72τ).
```

This is the most precise modular interpretation: `Θ` is a shifted unary theta component for the discriminant modulus `17`, pulled back by `τ ↦ 72τ`.

### Level / conductor / character

The product modulus is

```text
612 = 36*17 = 18*34.
```

But this is not automatically the scalar modular level.  The base unary theta components `θ_{17,r}` live in the weight-`1/2` Weil representation attached to the finite quadratic module with modulus `17`; the usual ambient level for the vector-valued theta system is `4*17 = 68`.  Pulling back by `72τ` gives the safe ambient level

```text
68*72 = 4896 = 2^5 * 3^2 * 17.
```

The specific two-residue component `{6,23}` is not, by itself, a Dirichlet-character theta series unless it is projected into a character sum.  So I would not assign it a single primitive Dirichlet character or a single primitive L-function yet.  It is better described as:

```text
weight 1/2 unary theta component,
rational characteristic denominator 17,
scale 72,
Jacobi product modulus 612,
Weil-representation character rather than a single Dirichlet character.
```

### Eta quotient?

It is not a plain eta quotient in the usual sense.  An eta quotient selects residue classes by divisor structure.  This product selects exactly two classes in the `Q=q^18` variable:

```text
(-Q^5;Q^34)_∞ (-Q^29;Q^34)_∞ (Q^34;Q^34)_∞.
```

That is naturally a Jacobi theta product / Siegel-function type object.  It may be expressible using Siegel functions and eta factors, but the canonical identity for the paper is the `j(-q^90;q^612)` identity, not an eta quotient.

### L-function?

The Mellin transform of the normalized theta component decomposes into unary theta L-series supported on the progression `m ≡ 6 mod 17`.  After decomposing the progression indicator into Dirichlet characters modulo `17` or `34`, it becomes a finite linear combination of elementary theta L-series.  It is not naturally a single newform L-function unless a later character projection produces one.

---

## Q2. Why are all anchors odd?

This should be a structural lemma, not an empirical fact.

The key point is that a `j`-block is built from triangular exponents.  For an integer block variable `n`,

```text
T_n = n(n-1)/2 = ((2n-1)^2 - 1)/8.
```

Thus the natural root variable of the triangular block is

```text
A = 2n - 1,
```

which is always odd.

For a general Jacobi block

```text
j(-q^r;q^M) = Σ_{n∈Z} q^{M n(n-1)/2 + r n}
```

after absorbing the two signs, set `A=2n-1`.  Since `n=(A+1)/2`, the exponent is

```text
E(n)
  = M(A^2-1)/8 + r(A+1)/2
  = (M A^2 + 4r A + 4r - M)/8.
```

The exponent is therefore naturally organized by an odd square-root variable `A`.  If the packet anchor is this root variable, or any signed/even translate of it,

```text
anchor = ±A + 2c,
```

then

```text
anchor ≡ A ≡ 1 mod 2.
```

That proves all anchors are odd.

This also explains why the observation is robust across the range `e=9..4050`: an even anchor would require `A` even, hence `n=(A+1)/2` half-integral, so it is not in the integer `j`-block lattice.

Important distinction: the completed-square variable of the scaled theta,

```text
17n + 6
```

is not always odd.  Therefore the observed “all anchors odd” is not coming from the final `17n+6` theta square.  It is coming earlier, from the triangular-root variable `2n-1` inside the `j(a,b,n)` packet structure.

### Parity theorem package

```text
Theorem, Odd-anchor theorem.
Every root-packet anchor attached to an integral j-block is odd.

Proof.
Write the j-block exponent in triangular form.  The block root variable is
A=2n-1 or A=2n+1, depending on convention.  In either convention A is odd.
All permitted packet translations preserve parity because they are even translations.
Hence every emitted anchor is odd. ∎
```

This converts the empirical result “zero even anchors through `4050`” into a one-line structural theorem once the paper records the exact anchor extraction map.

---

## Q3. Is the transition at `e=126` meaningful?

Yes, but it should be stated carefully.

The identity

```text
126 = 90 + 36
```

is not random.  The `90` is the first nonzero shell-opening exponent, and the `36` is the square defect in the theta characteristic:

```text
18h(17h-12)
  = (18/17)((17h-6)^2 - 36).
```

So `36=6^2` is the characteristic defect attached to the residue shift `6/17`.

However, because the `hblock=0` column sum is also nonzero starting at `e=126`, the transition should not be explained only as “the `90` shell translates a base coefficient at `36`.”  Under a charge-level factorization, the coefficient at `126` would schematically have the form

```text
[q^126] C(q)
  = [q^126] C_0(q) + [q^36] C_0(q),
```

because below `126` the theta factor contributes only `1` and `q^90`.

The confirmed fact that the `hblock=0` column is already nonzero at `126` means the first term `[q^126]C_0` is itself active.  The `90+36` relation is therefore best interpreted as a resonance between:

```text
first shell opening = 90,
theta characteristic defect = 36,
first global/base charge obstruction = 126.
```

The concrete test is:

```text
Compute the charge quotient C_0 if C(q)=C_0(q)Θ(q).
Then inspect C_0(36) and C_0(126).
```

If `C_0(36)=0` and `C_0(126)≠0`, then the transition is intrinsic to the base layer and merely numerologically aligned with `90+36`.  If both are nonzero, the first global charge receives both the base obstruction and the first translated shell contribution.  Either way, the appearance of `36` is meaningful because it is the discriminant/characteristic defect of the theta factor.

---

## Q4. What is `N_0`?

If factorization holds, `N_0` is not optional: it is uniquely determined by formal division by `Θ`, because `Θ(0)=1`.

```text
N_0(q) = Bad(q) / Θ(q).
```

Coefficientwise this gives the recursion

```text
N_0(E)
  = Bad(E) - Σ_{t>0} Θ(t) N_0(E-t),
```

where `t` ranges over positive shell-opening exponents.

Since the first positive theta exponents are

```text
90, 522, 792, 1656, 2106, 3402, 4032, ...,
```

we have

```text
N_0(E) = Bad(E)          for E < 90.
```

Thus the reported first values

```text
E       9  18  27  36  45  54  63  72  81
N_0     5   6   6   8   9  10  10  11  11
```

are literally the base-layer bad counts before the first shell translation can interfere.

### Is `N_0` a quadratic-form representation number?

The early growth looks like a one-dimensional lattice count, not like a classical positive-definite binary quadratic representation number.

A positive-definite binary quadratic representation number `r_Q(n)` usually has divisor-like arithmetic fluctuations and average size `n^{o(1)}` for individual coefficients.  The observed rough growth `O(sqrt(e/9))` is more suggestive of one of the following:

```text
1. an interval count of admissible odd anchors;
2. a degenerate / rank-one quadratic representation count;
3. an indefinite-form count with a cutoff window;
4. an Ehrhart/quasi-polynomial count from a packet polytope;
5. a weighted count of odd root variables satisfying local congruences.
```

Because Q2 says all anchors are odd, the most natural ansatz is

```text
N_0(9m) = Σ_{A odd} w(A,m) * 1_{local inequalities and congruences hold},
```

with `A` the triangular root variable from the `j`-block.  If the weights are eventually periodic in `A mod M`, then `N_0(9m)` may become a finite sum of floor functions.  That would explain the smooth step pattern better than a genuine binary quadratic representation number.

### Practical identification strategy

1. Compute `N_0` by quotient recursion to a much larger bound.
2. Split `N_0` by anchor residue classes modulo small moduli, especially modulo `2`, `3`, `9`, `17`, `34`, and `68`.
3. Test whether `N_0(9m)` is a floor-sum / Ehrhart quasi-polynomial.
4. If not, test whether it equals a representation count of an indefinite or degenerate quadratic form with an explicit cutoff.
5. Only after that should one try to match it to a modular form database or a classical representation-number formula.

The first nine values are too few to identify the arithmetic function uniquely.  But they are enough to say that `N_0` is probably the base packet-count function, and the all-odd anchor theorem gives the right variable in which to express it.

---

## Q5. What is the second fiber?

For a fiber with parameters

```text
a = |l|,
b = |v|,
```

the theta factor is

```text
Θ_{a,b}(q)
  = f(q^{18(a+2b)}, q^{18a})
  = Σ_{n∈Z} q^{18((a+b)n^2 + bn)}.
```

The two positive branches are, for `j ≥ 1`,

```text
lower_j = 18j((a+b)j - b),
upper_j = 18j((a+b)j + b).
```

For the minimizing fiber

```text
a = |l| = 5,
b = |v| = 12,
a+b = 17,
```

this gives

```text
Θ_{5,12}(q) = f(q^522,q^90).
```

The first few nonzero exponents in this same fiber are

```text
j=1:   90,   522
j=2:  792,  1656
j=3: 2106,  3402
j=4: 4032,  5760
```

So if “second fiber” means the second two-sided shell within the already identified fiber, the answer is

```text
j=2 branch: 792 and 1656.
```

### If “second fiber” means the next admissible cross-fiber

The relation

```text
|u| = |l| + |v| - 9
```

gives, in the present case,

```text
|l| = 5,
|u| = 8,
|v| = 12,
|l|+|v| = 17,
17 - |u| = 9.
```

If the admissible fibers are the `17`-split fibers generated by the `9`-defect, then the natural ordered candidates are:

| fiber `(a,b)` | theta | first lower branch | first upper branch |
|---:|---:|---:|---:|
| `(5,12)` | `f(q^522,q^90)` | `90` | `522` |
| `(8,9)` | `f(q^468,q^144)` | `144` | `468` |
| `(9,8)` | `f(q^450,q^162)` | `162` | `450` |
| `(12,5)` | `f(q^396,q^216)` | `216` | `396` |

Under ordering by first onset, the second cross-fiber is therefore

```text
(a,b) = (8,9),
Θ_{8,9}(q) = f(q^468,q^144).
```

Under ordering by the companion branch alone, `(12,5)` has the smallest companion `396`, but its first onset is later, at `216`.  For shell-opening purposes the first-onset order is the better ordering.

Diagnostic: if the fiber system allowed the pair `(5,8)`, it would produce

```text
f(q^378,q^90),
```

which would compete with or precede the verified minimizing companion `q^522`.  Since the confirmed minimizing fiber is `f(q^522,q^90)`, the pair `(5,8)` must be inadmissible in the actual fiber index set, or “minimizing” must mean something stricter than first lower onset.

---

## Q6. Minimal complete paper / theorem package

The minimal paper should be built around the sentence:

```text
The counterexample set is a theta-filtered modular object.
```

A good title would be:

```text
A Ramanujan Theta Filtration of the hblock Counterexample Set
```

or, more cautiously,

```text
Unary Theta Structure in the hblock Obstruction Set
```

### Proposed paper structure

#### 1. Introduction

State the empirical discovery and the corrected interpretation:

```text
Bad keys occur from e=9 onward, but global charge cancels until e=126.
The missing kernel coefficient is not an isolated accident; it sits inside a
unary theta shell filtration.
```

Main displayed identity:

```text
Θ(q)=f(q^522,q^90)=j(-q^90;q^612).
```

Main conditional identity:

```text
Bad(q)=N_0(q)Θ(q).
```

#### 2. Definitions

Define:

```text
root packet
anchor
bad key
charge
hblock
hblock shell
base layer N_0
Bad(q)
Θ(q)
```

The `hblock` definition should be stated exactly:

```text
hblock = (|l+1| + 1 - |u+v-1| + carry)//3.
```

Then state that this is a translation coordinate, not just a label.

#### 3. Shell theorem

```text
Theorem 1, hblock shell opening.
For every h∈Z, the hblock shell opens at

    E_h = 18h(17h-12).

Moreover the shell-opening generating function is

    Σ_{h∈Z} q^{E_h} = f(q^522,q^90).
```

Proof: change `h=-n` and use the Ramanujan theta exponent calculation.

#### 4. Jacobi/Ramanujan product theorem

```text
Theorem 2, Jacobi product.
The shell-opening series satisfies

    Σ_{h∈Z} q^{18h(17h-12)}
      = (-q^90;q^612)_∞(-q^522;q^612)_∞(q^612;q^612)_∞.
```

Proof: Jacobi triple product with `x=-q^90`, `Q=q^612`.

Then add a modularity remark:

```text
After multiplying by q^(648/17), this is the unary theta component
θ_{17,6}(72τ)+θ_{17,23}(72τ).
```

Do not overclaim scalar level `612`.

#### 5. Fiber theorem

```text
Theorem 3, fiber theta.
For a fiber with parameters a=|l| and b=|v|, the fiber-opening series is

    Θ_{a,b}(q)=f(q^{18(a+2b)}, q^{18a}).

The two branches are

    E_j^- = 18j((a+b)j-b),
    E_j^+ = 18j((a+b)j+b).
```

For `(a,b)=(5,12)`, this gives the verified minimizing fiber

```text
f(q^522,q^90).
```

#### 6. Odd-anchor theorem

```text
Theorem 4, all anchors odd.
Every root-packet anchor emitted by an integral j-block is odd.
```

Proof: write the triangular exponent using `A=2n-1`.  This should replace the finite check through `4050` with a structural proof.

#### 7. Charge theorem

```text
Theorem 5, first global charge obstruction.
The global charge and the hblock=0 charge are zero below e=126 and nonzero at e=126.
```

This theorem should be stated as a computed/proved finite result first.  Then add the structural interpretation:

```text
126 = 90 + 36,
36 = 6^2,
18h(17h-12) = (18/17)((17h-6)^2 - 36).
```

The exact proof target is to express the charge functional through the same theta/base decomposition, or to show why the first nonzero base charge occurs at the theta defect threshold.

#### 8. Factorization theorem / conjecture

State this as conditional until the shell-copy bijection is proven.

```text
Conjecture 6, shell-copy factorization.
There is a multiplicity-preserving translation from the hblock=0 layer to each
hblock shell h, shifting e by 18h(17h-12).  Equivalently,

    Bad(q)=N_0(q) f(q^522,q^90).
```

Then the coefficient statement is

```text
Bad(E)=Σ_{n∈Z}N_0(E-18n(17n+12)).
```

Proof route:

```text
1. Define the translation map T_h on packet keys.
2. Prove T_h preserves badness and multiplicity.
3. Prove every bad key has a unique decomposition into base key + h shell.
4. Sum over h.
```

#### 9. Base layer theorem / problem

```text
Problem 7, identify N_0.
Determine a closed formula for the base-layer enumerator N_0(q).
```

Initial data:

```text
N_0(9),...,N_0(81) = 5,6,6,8,9,10,10,11,11.
```

Expected shape:

```text
N_0(9m) is a weighted count of odd j-block anchors in a growing interval,
possibly an Ehrhart/quasi-polynomial or a degenerate quadratic representation count.
```

#### 10. Verification section

Include reproducible scripts for:

```text
1. shell-onset verification;
2. theta-product coefficient comparison;
3. factorization quotient N_0;
4. odd-anchor verification by block ID;
5. charge decomposition at e=126;
6. second-fiber enumeration.
```

---

## Reproducible code skeleton

The following code is only a harness.  It assumes the actual project code can supply `Bad(E)` and packet anchors.

```python
from __future__ import annotations

from collections import defaultdict
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

CoeffDict = Dict[int, int]


def fiber_exponent(n: int, a: int = 5, b: int = 12) -> int:
    """Exponent of f(q^(18(a+2b)), q^(18a)) at summation index n."""
    return 18 * ((a + b) * n * n + b * n)


def theta_opening_coeffs(emax: int, a: int = 5, b: int = 12) -> CoeffDict:
    """Return coefficients of Θ_{a,b} through emax.

    Θ_{a,b}(q) = Σ_{n∈Z} q^{18((a+b)n^2 + b n)}.
    """
    coeffs: CoeffDict = defaultdict(int)
    n = 0
    while True:
        progressed = False
        for k in (n, -n) if n else (0,):
            e = fiber_exponent(k, a=a, b=b)
            if 0 <= e <= emax:
                coeffs[e] += 1
                progressed = True
        if n > 0 and not progressed:
            # Since the quadratic grows in both directions, this is safe after
            # both +n and -n have exceeded the range.
            e_pos = fiber_exponent(n, a=a, b=b)
            e_neg = fiber_exponent(-n, a=a, b=b)
            if e_pos > emax and e_neg > emax:
                break
        n += 1
    return dict(coeffs)


def convolve(a: Mapping[int, int], b: Mapping[int, int], emax: int) -> CoeffDict:
    """Truncated Cauchy product."""
    out: CoeffDict = defaultdict(int)
    for ea, ca in a.items():
        if ca == 0:
            continue
        for eb, cb in b.items():
            e = ea + eb
            if e <= emax:
                out[e] += ca * cb
    return dict(out)


def recover_n0_from_bad(bad: Mapping[int, int], emax: int) -> CoeffDict:
    """Recover N_0 from Bad = N_0 * Θ, using Θ(0)=1."""
    theta = theta_opening_coeffs(emax)
    positive_theta_terms = sorted((e, c) for e, c in theta.items() if e > 0)

    n0: CoeffDict = {}
    for e in range(emax + 1):
        value = bad.get(e, 0)
        for t, c in positive_theta_terms:
            if t > e:
                break
            value -= c * n0.get(e - t, 0)
        n0[e] = value
    return n0


def check_factorization(bad: Mapping[int, int], emax: int) -> List[Tuple[int, int, int]]:
    """Return discrepancies (e, Bad(e), (N_0*Θ)(e))."""
    n0 = recover_n0_from_bad(bad, emax)
    theta = theta_opening_coeffs(emax)
    rebuilt = convolve(n0, theta, emax)
    discrepancies: List[Tuple[int, int, int]] = []
    for e in range(emax + 1):
        lhs = bad.get(e, 0)
        rhs = rebuilt.get(e, 0)
        if lhs != rhs:
            discrepancies.append((e, lhs, rhs))
    return discrepancies


def j_block_anchor(n: int, convention: str = "minus") -> int:
    """The odd triangular root variable from a j-block.

    convention='minus' gives A=2n-1.
    convention='plus' gives A=2n+1.
    """
    if convention == "minus":
        return 2 * n - 1
    if convention == "plus":
        return 2 * n + 1
    raise ValueError(f"unknown convention: {convention}")


def assert_all_anchors_odd(anchors: Iterable[int]) -> None:
    """Raise if any anchor is even."""
    even = [a for a in anchors if a % 2 == 0]
    if even:
        raise AssertionError(f"found even anchors: {even[:20]}")


def branch_pair(j: int, a: int, b: int) -> Tuple[int, int]:
    """Return the lower/upper j-branch exponents for Θ_{a,b}."""
    lower = 18 * j * ((a + b) * j - b)
    upper = 18 * j * ((a + b) * j + b)
    return lower, upper


def candidate_fibers_from_split(total: int = 17) -> List[Tuple[int, int, int, int]]:
    """Natural 17-split fibers relevant to |u|=|l|+|v|-9.

    Returns tuples (a,b,first_lower,first_upper).
    """
    candidates = [(5, 12), (8, 9), (9, 8), (12, 5)]
    out: List[Tuple[int, int, int, int]] = []
    for a, b in candidates:
        if a + b != total:
            continue
        lower, upper = branch_pair(1, a, b)
        out.append((a, b, lower, upper))
    return sorted(out, key=lambda row: (row[2], row[3]))


if __name__ == "__main__":
    # Confirmed first base-layer values supplied in R5.
    n0_first = {
        9: 5,
        18: 6,
        27: 6,
        36: 8,
        45: 9,
        54: 10,
        63: 10,
        72: 11,
        81: 11,
    }

    theta = theta_opening_coeffs(6000)
    print("first theta exponents:", sorted(theta)[:10])
    print("candidate split fibers:", candidate_fibers_from_split())
    print("N0 first values:", [n0_first[9 * m] for m in range(1, 10)])
```

---

## The compact theorem package to put in the paper

Here is the minimal complete theorem package.

### Theorem A — hblock is a shell coordinate

```text
The statistic

    hblock = (|l+1|+1-|u+v-1|+carry)//3

is a translation coordinate.  The h-shell opens at

    E_h = 18h(17h-12).
```

Status: confirmed experimentally; needs formal proof from the packet inequalities.

### Theorem B — shell opening is Ramanujan theta

```text
Σ_{h∈Z} q^{18h(17h-12)} = f(q^522,q^90).
```

Status: proven algebraically.

### Theorem C — Jacobi triple product

```text
f(q^522,q^90)
  = (-q^90;q^612)_∞(-q^522;q^612)_∞(q^612;q^612)_∞.
```

Status: proven by JTP.

### Theorem D — modular interpretation

```text
q^(648/17) f(q^522,q^90)
  = θ_{17,6}(72τ)+θ_{17,23}(72τ).
```

Status: proven by completing the square.  Interpret as a weight-`1/2` unary theta component with denominator `17` and scale `72`.

### Theorem E — fiber theta

```text
For a fiber with a=|l| and b=|v|,

    Θ_{a,b}(q)=f(q^{18(a+2b)},q^{18a}).
```

Status: algebraic once the fiber onset formula is proven.

### Theorem F — all anchors odd

```text
Every anchor is odd.
```

Status: should be structural.  Proof comes from the triangular root variable `A=2n-1` in every integral `j`-block.

### Theorem G — charge transition

```text
The first nonzero global charge, and the first nonzero hblock=0 column charge,
occur at e=126.
```

Status: confirmed computationally.  The structural explanation should use the theta characteristic defect `36=6^2` and the charge quotient/base-layer charge.

### Conjecture H — shell-copy factorization

```text
Bad(q)=N_0(q) f(q^522,q^90).
```

Equivalent coefficient formula:

```text
Bad(E)=Σ_{n∈Z}N_0(E-18n(17n+12)).
```

Status: current R5 factorization conjecture.  The proof should be a bijection between each h-shell and the hblock=0 layer.

### Problem I — identify `N_0`

```text
Find a closed arithmetic/combinatorial formula for N_0.
```

Expected answer: a weighted odd-anchor count, likely closer to an Ehrhart/floor-sum or rank-one/degenerate quadratic count than to a classical positive-definite binary representation number.

---

## Final synthesis

The paper should not merely report that bad keys exist at every `e=9n`.  The stronger and more publishable statement is:

```text
The bad-key set has a theta shell geometry.  The shell coordinate is hblock,
the shell openings are exactly the Ramanujan theta f(q^522,q^90), every anchor
is forced odd by the j-block triangular root, and the first uncancelled charge
at e=126 is aligned with the 6^2 characteristic defect of the theta.
```

If the factorization conjecture is proven, the paper becomes very clean:

```text
Counterexample enumerator = base layer × unary theta.
```

Then the remaining arithmetic content is concentrated in `N_0`.  That is exactly the right architecture: prove the universal theta shell once, prove the odd-anchor theorem once, and reduce the complicated enumeration to the base layer.
