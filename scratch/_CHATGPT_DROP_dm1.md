# Q3156 (dm1): Prime nonvanishing strategy for the `Q(sqrt(5))` cone series

Date: 2026-07-03

## Repo note

I attempted to read `theorems.md` from the repository, but the GitHub connector did not find it at the repo root and repository search returned no match.  The analysis below is therefore based on the theorem list and context in the prompt, plus the established Q31xx setup.

## First correction: the norm of `eps`

With

```text
phi = (1 + sqrt(5)) / 2,
eps = phi^2 = phi + 1,
```

one has

```text
N(phi) = -1,
N(eps) = N(phi)^2 = +1.
```

So `eps = phi^2` is the totally positive norm-`+1` fundamental unit.  The norm-`-1` unit is `phi`.  This correction does not change the coset-stabilizer story, but it matters in the write-up.

## Executive answer

The real bottleneck is not any one of L1--L4 in isolation.  The right proof should replace them by one finite **ray-class/Shintani sector theorem**:

```text
For every prime p == 1 mod 10, the active set

  A_p = { beta in L : -N(beta)=p and beta lies in the A- or D-cone }

has cardinality 1 or 2, and all elements of A_p have the same weight.
```

This single sector theorem implies:

```text
L1: existence, because |A_p| >= 1;
L4: bounded multiplicity, because |A_p| <= 2;
L2: cone separation, if the table shows the active atoms lie in one cone;
L3: parity coherence, if the table shows the active atoms have the same a-parity.
```

Then

```text
B_{(p-1)/10} = sum_{beta in A_p} W(beta)
```

is automatically one of

```text
{-2, -1, +1, +2}.
```

The hardest part is the Shintani-sector table, especially the statement that each prime ideal orbit contributes at most one selected representative after reduction by `<eps^6>`, and that the two conjugate prime-ideal orbits do not give opposite signs.  The slogan is:

```text
Prime nonvanishing is a finite sector-table theorem, not a Hecke-eigenform theorem.
```

## 1. Which of L1--L4 is the bottleneck?

The proposed lemmas are:

```text
L1: Existence
L2: Cone separation
L3: Parity coherence
L4: Bounded multiplicity
```

### L4 is not trivial from “two prime ideals”

For a split rational prime `p`, there are two prime ideals above `p`, but each ideal has infinitely many generators because the unit group is infinite.  Since `eps^6 L = L`, each generator in `L` has infinitely many `eps^6`-associates still in `L` and with the same norm.

The coefficient is finite only because the A/D cone window selects finitely many of these associates.  Therefore L4 is really a Shintani-window statement:

```text
A unit orbit of prime generators intersects the active A/D window at most once,
or, after including conjugation, the total intersection has size at most two.
```

This is not a consequence of ideal factorization alone.

### L1 is also a sector statement, but easier after the table

Existence asks that at least one associate of a prime generator lands in

```text
L ∩ (A ∪ D).
```

This mixes finite congruence data with archimedean cone data.  Once the six-sector table is built, existence should be just a table read-off.  Before the table, it is not automatic.

### L2 and L3 are consequences of the same finite table

Cone separation and parity coherence are best proved together.  A finite table should record, for each admissible sector/residue state:

```text
number of active atoms,
A-cone or D-cone,
a-parity,
weight.
```

Then L2 and L3 are simply projections of that table.

### Recommended replacement theorem

Instead of proving L1--L4 separately, prove:

```text
PrimeSectorTheorem.
Let p be a rational prime with p == 1 mod 10, and let N=(p-1)/10.
Then the active set

  A_p = { beta in L : -N(beta)=p and beta is in A or D }

has cardinality 1 or 2.  Moreover the weight W(beta) is constant on A_p.
```

Then Conjecture B follows immediately.

## 2. How the six sectors should interact with the cosets `eps^j L`

The unit action on coordinates is

```text
eps * (a + b phi) = (a+b) + (a+2b) phi.
```

The first six powers have matrices

```text
eps^0: [[ 1,  0], [ 0,  1]]
eps^1: [[ 1,  1], [ 1,  2]]
eps^2: [[ 2,  3], [ 3,  5]]
eps^3: [[ 5,  8], [ 8, 13]]
eps^4: [[13, 21], [21, 34]]
eps^5: [[34, 55], [55, 89]]
eps^6: [[89,144], [144,233]].
```

The affine coset is

```text
L = { a+b phi : b - 3a == 1 mod 10 }.
```

Since `eps^6 L = L`, the subgroup

```text
Gamma = <eps^6>
```

is the relevant unit stabilizer.  A `Gamma`-Shintani fundamental domain is six times wider than an `eps`-fundamental domain.  Thus it is natural to subdivide a `Gamma`-domain into six `eps`-sectors:

```text
C_0, C_1 = eps*C_0, ..., C_5 = eps^5*C_0.
```

At the same time, the six cosets

```text
L_j = eps^j L,   j = 0,...,5,
```

cycle modulo `Gamma`.  This is the correct meaning of the “six-sector” phenomenon: a unit translate moves both the archimedean sector and the finite congruence coset.

### Cone inequalities in `(a,b)` coordinates

For

```text
beta = a + b phi,
```

the inverse atom is

```text
k = (b - 3a - 1) / 10,
r = (4a + 2b - 2) / 10 = (2a + b - 1) / 5.
```

Therefore the active cones are:

```text
A-cone:  b - 3a - 1 >= 0  and  2a + b - 1 >= 0,
D-cone:  b - 3a - 1 <  0  and  2a + b - 1 <  0.
```

At infinity, the two boundary slopes are approximately

```text
b = 3a,
b = -2a.
```

The Shintani sector table should be built from these two real boundary lines plus the six finite coset translates `eps^j L`.

### Clean proof shape

The cleanest rigorous proof is:

1. Work modulo the stabilizer `Gamma=<eps^6>`.
2. Choose a `Gamma`-fundamental strip in the real embeddings.
3. Decompose it into six `eps`-sectors.
4. For each sector `j`, compute the finite residue class condition for membership in `L`.
5. For each admissible sector/residue state, record whether it lies in the A-window, D-window, or outside.
6. Prove a finite table theorem:

```text
For prime-norm orbits, the active window contains exactly one representative
in four of the six sector states and exactly two representatives in two of
the six sector states; all selected representatives have the same weight.
```

This table theorem simultaneously proves L1--L4.

I would not expect a one-line conceptual argument for the “exactly one or two” count.  The right proof is finite and explicit: reduce the unit/coset/cone interaction to six residue-sector cases and check those cases.

## 3. Can this be reduced to a Hecke character statement?

Only partially.

For the full coefficient function `B_N`, no: it is not a Hecke eigenform coefficient sequence and not a multiplicative ideal-counting function.  The obstruction is the archimedean Shintani window.  Multiplication of ideals is compatible with the finite ray-class data, but it is not compatible with the cone window because reducing a product back into a Shintani strip introduces a unit-carry/floor function.

For primes, yes in a weaker sense: after the finite sector table is proved, the prime coefficient can be viewed as a finite class function on prime ideals in a ray-class/sector quotient.  Schematically, for a prime ideal `pfrak` above `p`,

```text
B_{(p-1)/10} = S(class(pfrak))
```

for a six-state sector function `S` with values in

```text
{-2,-1,+1,+2}.
```

But `S` is a sector/window function, not a multiplicative character.  It may be expressible as a finite Fourier combination of ray-class characters when restricted to primes, but it does not make the full coefficient sequence multiplicative.

A useful wording is:

```text
Conjecture B should reduce to a finite ray-class sector table, not to a single Hecke character.
```

## 4. Relation with ADH sigma and known multi-sector techniques

The original Andrews--Dyson--Hickerson `sigma(q)` phenomenon is also real quadratic, not imaginary quadratic.  Its simplicity comes from a unit-invariant or effectively one-sector situation: the relevant weight descends to ideals, so prime coefficients are forced to be nonzero once a split prime is represented.

Here, `eps L` is disjoint from `L`, while `eps^6 L = L`.  Thus the natural coefficient does not descend to ideals under the full positive unit group.  It descends only after keeping track of six unit sectors.  This is the source of the multi-sector complication.

The standard techniques to use are:

```text
Shintani cone decompositions for real quadratic fields;
ray-class partial zeta functions with archimedean cone conditions;
finite quotient/ray-class tables modulo a conductor encoding L and parity;
Zwegers-style indefinite theta completions for the analytic object;
Hickerson--Mortenson/Appell--Lerch formulas for the q-series identity.
```

For the prime nonvanishing theorem, the most relevant tool is not the analytic completion.  It is the arithmetic Shintani reduction:

```text
reduce unit orbits modulo <eps^6>, then check the finite sector table.
```

## 5. The 2:1 distribution and the `Z/3Z` factor

The observed distribution

```text
|B(p)| = 2 with density 1/3,
|B(p)| = 1 with density 2/3
```

strongly suggests that the absolute-value distinction is controlled by the order-3 part of the CRT quotient.

You have

```text
(O_K / (2 sqrt(5)))^x ≅ F_4^x × F_5^x ≅ Z/3 × Z/4.
```

Here the `Z/3` factor comes from the inert prime `2`:

```text
O_K/(2) ≅ F_4,
F_4^x has order 3.
```

The natural explanation is:

```text
one of the three F_4^x states gives two active sectors,
the other two F_4^x states give one active sector.
```

Then Chebotarev/equidistribution of split prime ideals in the relevant ray class quotient predicts exactly

```text
1/3 and 2/3.
```

The `Z/4` factor coming from the ramified prime over `5` likely controls signs or a finer splitting, while the `Z/3` factor controls the absolute multiplicity.  This should be verified by the finite sector table; do not state it as a theorem until the table confirms which component controls which statistic.

## 6. Proof strategy for Conjecture B

Here is the route I would write into the paper or formalization plan.

### Step 1: Define the active prime set

For `p == 1 mod 10`, set `N=(p-1)/10` and define

```text
A_p = { beta = a+b phi in L : -N(beta)=p,
        beta lies in the A-cone or D-cone }.
```

Then

```text
B_N = sum_{beta in A_p} W(beta).
```

### Step 2: Replace atoms by ray-class generators

Use the inverse formulas

```text
k = (b - 3a - 1) / 10,
r = (2a + b - 1) / 5.
```

This turns membership in `L` and the A/D cones into finite congruence plus linear inequalities.

### Step 3: Reduce units modulo `<eps^6>`

Since `eps^6 L = L`, reduce generators only by `Gamma=<eps^6>`.  In the real embeddings this gives one compact Shintani strip.

### Step 4: Build the six-sector table

Inside one `Gamma` strip, decompose into the six `eps`-sectors and record:

```text
sector label j in Z/6,
residue class in (O_K/(2 sqrt5))^x,
L-membership,
A/D/outside,
a-parity,
weight.
```

This table is finite.  It is the central object.

### Step 5: Prove the prime orbit intersection theorem

For each split prime ideal orbit, prove:

```text
its Gamma-reduced representatives intersect the active table in exactly
one or two entries;
all active entries have the same weight.
```

This proves Conjecture B.

### Step 6: Use Chebotarev/equidistribution for density

Once the table is known, the 2:1 distribution follows from equidistribution of prime ideals among the relevant finite ray-class states.  If the table shows the absolute value depends only on the `F_4^x` component, this becomes a transparent `1 out of 3` versus `2 out of 3` result.

## 7. A finite table oracle

The following Python/Sage-style skeleton records the computation I would use before writing the proof.  It is not meant to replace the proof; it tells you exactly what finite table the proof must certify.

```python
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Tuple


@dataclass(frozen=True)
class PhiElt:
    a: int
    b: int


def eps_mul(x: PhiElt) -> PhiElt:
    return PhiElt(x.a + x.b, x.a + 2 * x.b)


def eps_pow_mul(x: PhiElt, j: int) -> PhiElt:
    y = x
    for _ in range(j % 6):
        y = eps_mul(y)
    return y


def in_L(x: PhiElt) -> bool:
    return (x.b - 3 * x.a - 1) % 10 == 0


def atom_from_beta(x: PhiElt) -> Optional[Tuple[int, int]]:
    num_k = x.b - 3 * x.a - 1
    num_r = 2 * x.a + x.b - 1
    if num_k % 10 != 0 or num_r % 5 != 0:
        return None
    return num_k // 10, num_r // 5


def cone_label(x: PhiElt) -> str:
    atom = atom_from_beta(x)
    if atom is None:
        return "not_L"
    k, r = atom
    if k >= 0 and r >= 0:
        return "A"
    if k < 0 and r < 0:
        return "D"
    return "out"


def parity_a(x: PhiElt) -> int:
    return x.a % 2


def weight(x: PhiElt) -> int:
    atom = atom_from_beta(x)
    if atom is None:
        return 0
    k, r = atom
    sign = 1 if x.a % 2 == 0 else -1
    if k >= 0 and r >= 0:
        return -sign
    if k < 0 and r < 0:
        return sign
    return 0


def residue_state(x: PhiElt, modulus: int = 20) -> Tuple[int, int]:
    return (x.a % modulus, x.b % modulus)


def six_sector_table(representatives: List[PhiElt]) -> List[Dict[str, object]]:
    rows: List[Dict[str, object]] = []
    for x in representatives:
        for j in range(6):
            y = eps_pow_mul(x, j)
            rows.append(
                {
                    "base": x,
                    "sector": j,
                    "residue20": residue_state(y, 20),
                    "in_L": in_L(y),
                    "cone": cone_label(y),
                    "parity_a": parity_a(y),
                    "weight": weight(y),
                }
            )
    return rows
```

For a proof, replace the sampled `representatives` by symbolic residue classes in the finite quotient.  The final theorem should be a finite case check over those residue classes plus the ordered cone-boundary sectors.

## 8. Additional literature to check

The most relevant nearby sources are:

```text
Andrews--Dyson--Hickerson, Partitions and indefinite quadratic forms, Invent. Math. 91 (1988).
```

This is the original ADH real-quadratic norm-support source.

```text
Zwegers, Maass waveforms arising from sigma and related indefinite theta functions.
https://arxiv.org/abs/1002.1175
```

This places ADH sigma-type functions into the indefinite theta / Maass waveform framework.

```text
Hickerson--Mortenson, Hecke-type double sums, Appell-Lerch sums, and mock theta functions.
https://arxiv.org/abs/1208.1421
```

This is the relevant `f_{a,b,c}` / Appell--Lerch technology.

```text
Mortenson, Ramanujan's 1psi1 summation, Hecke-type double sums, and Appell-Lerch sums.
https://arxiv.org/abs/1208.1359
```

Useful for alternative derivations of the HM formulas.

```text
Mortenson, A general formula for Hecke-type false theta functions.
https://arxiv.org/abs/2212.13236
```

This is newer and directly relevant to Hecke-type false theta decompositions.

```text
Bringmann--Kane, Multiplicative q-hypergeometric series arising from real quadratic fields.
https://arxiv.org/abs/0812.4397
```

This is important for the ADH generalization viewpoint and q-hypergeometric real-quadratic examples.

```text
Lovejoy--Osburn, Real quadratic double sums.
https://arxiv.org/abs/1502.01109
```

This gives real-quadratic double sums and ideal-counting interpretations.

```text
Bringmann--Nazaroglu, Quantum Modular Forms from Real Quadratic Double Sums.
https://arxiv.org/abs/2205.02643
```

This is useful for the modern modular/quantum modular context of real-quadratic double sums.

For the arithmetic proof of the sector theorem, also check the Shintani literature:

```text
Shintani, On evaluation of zeta functions of totally real algebraic number fields at non-positive integers.
Yamamoto, real quadratic class invariants / Shintani cone methods.
Neukirch or Cox for ray class fields and prime ideal equidistribution.
```

The search target should be not only “ADH” but also:

```text
real quadratic Shintani cone ray class partial zeta
indefinite theta real quadratic unit sector
Hecke-type double sums real quadratic ideal norms
```

## 9. Answers to the six questions

### Q1. Which of L1--L4 is the bottleneck?

The bottleneck is the combined Shintani-sector table, especially the bounded-intersection and no-opposite-sign assertions.  L4 is not a corollary of “two prime ideals” because units give infinitely many generators.  L1--L4 should be replaced by one finite prime-sector theorem; the four lemmas are then projections of that theorem.

### Q2. How does the six-sector structure interact with `eps^j L`?

The six `eps`-sectors inside a `<eps^6>` fundamental domain are locked to the six cosets `eps^j L`.  The active A/D cones cut this six-sector cylinder by two linear boundary lines.  The proof should enumerate the six sector/coset states and show that a prime orbit hits the active window in one or two same-weight states.

### Q3. Is there a simpler Hecke-character reformulation?

For the full coefficient sequence, no.  The cone window prevents ideal descent and destroys multiplicativity.  For primes only, yes: after the finite sector table, `B_{(p-1)/10}` becomes a finite ray-class sector function of the prime ideal above `p`.  That is weaker than a Hecke character but strong enough for nonvanishing and density.

### Q4. Known techniques for the multi-sector case?

Use Shintani cone decompositions, ray-class partial zeta functions with archimedean conditions, and finite sector tables.  Analytic indefinite-theta machinery explains modularity/completion, but the prime nonvanishing theorem is primarily an arithmetic Shintani reduction problem.

### Q5. Does the 2:1 distribution connect to `Z/3Z`?

Very likely yes.  The `Z/3` factor is `F_4^x` from the inert prime `2`.  The most plausible table is: one of the three `F_4^x` states gives two active atoms, and the other two states give one.  Chebotarev/equidistribution then gives `1/3` and `2/3`.  The table must confirm this before it is stated as a theorem.

### Q6. Additional literature?

Check ADH, Zwegers on sigma, Hickerson--Mortenson, Mortenson's later false-theta work, Bringmann--Kane, Lovejoy--Osburn, Bringmann--Nazaroglu, and the Shintani/ray-class zeta literature.  For this proof, the most useful phrase is probably “Shintani cone decomposition with ray class congruence,” not just “mock theta” or “Hecke character.”

## Bottom line

The prime nonvanishing conjecture should be attacked as a finite arithmetic-geometry table:

```text
unit stabilizer:        <eps^6>
finite congruence:      L modulo 10, plus parity
archimedean geometry:   A/D cone window in one Shintani strip
prime input:            two conjugate split prime ideal orbits
output:                 one or two same-weight active representatives
```

Once this table is proved, Conjecture B and the 2:1 density statement become natural consequences.  Without this table, the four lemmas L1--L4 are too interdependent to prove cleanly one at a time.
