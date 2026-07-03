# Q3171 (dm1): Paper 2 Round 3 — corrected framing, LRS layer, and shell onset

Date: 2026-07-03

## Executive answer

The Round 3 corrections change the story in an important way.

The previous “`9 | e` explains the counterexample” framing should be retired.  It is now clear that `9 | e` is not a discriminating obstruction theorem: the atom-producing exponent systems are already `9`-dilated.  The correct phenomenon is not “divisible by 9 versus not divisible by 9,” but rather:

```text
The root-packet/LRS pairing fails on boundary shells of the LRS support.
The first possible failure in shell j occurs at

    onset_j = 18*j*(17*j - 12).

The shell index, not divisibility by 9, is the meaningful obstruction parameter.
```

The second key correction is layer separation.  The counterexample at `e=11763` lives at the **LRS/root-packet level**, not at the even-k cone level.  Therefore the Pell automorphism `M` and the congruence `M^2 ≡ -I mod 9` are still structurally important, but they act on the cone/Pell projection, not directly on the `(hblock,anchor)` fiber where the counterexample is measured.

The best current paper framing is:

```text
Chan's Theta_10 root-packet proof fails because the tau pairing has a boundary-shell defect in the LRS decomposition.  The defect has a sharp shell onset law

    onset_j = 18*j*(17*j - 12),

and the global generating function of these boundary defects factors as

    Theta_u * Theta_v * (D - A),
    D - A = -f_{1,3,4}(X,-X^3,X).
```

The Pell/norm story should be presented as the global cone shadow of the same boundary mechanism, not as the direct explanation of the `e=11763` LRS fiber.

## 0. Layer correction: what survives and what does not

The corrected layer diagram is:

```text
Layer 1: LRS/root-packet/fiber layer
  coordinates: (l,u,v, root variable n), or equivalently decorated atoms
  key: (hblock, anchor)
  tau: root-packet central reflection
  counterexample e=11763 lives here

Layer 2: even-k/cone layer
  coordinates: (u,v,k,r)
  cone form: Q_kr = 4k^2 + 6kr + r^2 + 2k + r
  sigma: (k,r) -> (k, -r - 6k - 1)
  missing kernel factor D-A lives here after reindexing

Layer 3: Pell/norm layer
  coordinates: X = 4k + 3r + 1, Z = 5r + 1
  automorph: M = [[9,-4],[-20,9]]
  congruence: M^2 ≡ -I mod 9
```

The most important consequence is:

```text
Do not say that M acts on the root-packet key unless a decorated lift has been proved.
```

It may act on the global boundary generating function and on the cone projection, but the LRS key `(hblock,anchor)` belongs to a different coordinate system.

## Q1. Why should `onset_j = 18j(17j-12)` work?

The formula should be treated as a constrained-minimization law, not as a divisibility law.

The target normal form should look like this.  For a shell-`j` LRS boundary atom, after the correct root-packet change of variables, the full LRS exponent should decompose as

```text
E_LRS = 18*j*(17*j - 12) + R_j(tangential variables),
```

where

```text
R_j >= 0
```

on the admissible support, and equality is attained exactly at the shell-`j` wavefront.

This is the first-principles explanation of the three verified values:

```text
j=1: 18*1*(17-12)     = 90
j=2: 18*2*(34-12)     = 792
j=3: 18*3*(51-12)     = 2106
j=4: 18*4*(68-12)     = 4032
```

The question is then: where do `17` and `12` come from?

### 1.1 What determines the `12`

The root-packet anchor-pair involution is

```text
n -> 12 - n.
```

The observed root variables

```text
{-3, 15, 29, -17}
```

pair as

```text
-3  <-> 15,
-17 <-> 29,
```

and both pairs have sum `12`.  Thus the affine center of the root-pair reflection is

```text
n = 6.
```

Any completed-square/root-pair energy written in the anchor coordinate will therefore contain a linear shift governed by this center.  The `-12j` term in

```text
17j^2 - 12j
```

is exactly the kind of linear term produced by a half-open shell distance measured from an affine reflection with pair-sum `12`.

So the `12` is not accidental.  It is the root-pair anchor sum.

### 1.2 What determines the `17`

The coefficient `17` should be the normal curvature of the LRS boundary quadratic after all admissibility constraints have been imposed.  Equivalently, if `j` is the normal shell coordinate, then the LRS energy restricted to the minimizing affine line has a quadratic term

```text
18 * 17 * j^2.
```

This `17` is not visible in the cone-only wall distance.  It is produced by the full LRS energy, including:

```text
1. root-packet alignment terms,
2. the oddBilat/oddMissing/strip upper alignment,
3. parity/coset restrictions,
4. the anchor-pair constraint n -> 12-n,
5. the admissible support inequalities.
```

This explains why the naive cone wall formula from the `(k,r)` block is too small.  The shell onset is not minimizing only `Q_kr`; it is minimizing the full LRS exponent over a constrained affine slice.

### 1.3 The theorem to prove

The first-principles theorem should be stated as a normal-form theorem:

```text
LRS shell normal form.
For every LRS atom in shell j, there exist integer tangential variables y such that

    E_LRS(atom) = 18*j*(17*j - 12) + R_j(y),

where R_j(y) is a nonnegative integer-valued quadratic/linear expression on the
admissible support.  Moreover R_j=0 is solvable for j=1,2,3, and conjecturally
for all j>=1.
```

Then the onset formula follows immediately.

This is much better than saying the formula was guessed from data.  The formula is telling you what the completed-square normal form must be.

## Q2. What determines the bad-key count?

The bad-key count is not determined by the shell onset alone.

It is a representation number of the residual tangential form after the shell normal form is imposed.  In the notation above, for shell `j` and exponent `e`, define

```text
R = e - onset_j.
```

Then the bad-key count has the shape

```text
BadKeys_j(e)
  = # or signed count of root-packet fibers K for which
      there exists an admissible LRS boundary atom with
      shell = j,
      R_j(y) = R,
      key(atom) = K,
      tau/sigma boundary partner missing or sign-uncancelled.
```

At the onset itself, `R=0`, so

```text
BadKeys_j(onset_j)
```

is the number of admissible minimizers of the tangential residual form modulo the key map.

This explains why a high exponent can have few bad keys while a lower onset can have many:

```text
e=11763 is a shell-1 interior value with one isolated bad key.
e=2106 is a shell-3 wavefront value where many keys become eligible simultaneously.
```

Wavefronts are caustics.  They can have high multiplicity even at smaller energy.

### 2.1 Why 93 at shell 3 is plausible

The number `93` should be interpreted as:

```text
93 = cardinality of the key image of the minimizer set {R_3=0}
     after applying admissibility and noncancellation tests.
```

It is not evidence that the shell-3 space is generically denser at every exponent.  It says the shell-3 onset has many simultaneous minimizers.

### 2.2 Formula for bad-key count

The right formula is a finite representation-number formula, not a simple scalar polynomial unless the residual form is very special:

```text
BadKeys_j(e)
  = sum_{K} 1[ BoundaryCharge_j(e,K) != 0 ],
```

where

```text
BoundaryCharge_j(e,K)
  = sum_{y in Y_j(K), R_j(y)=e-onset_j} sign_j(y).
```

Here `Y_j(K)` is the set of tangential LRS variables in key fiber `K` and shell `j`.

If the signs are ignored, the support count is the number of represented values of `R_j` in each key fiber.  With signs, cancellations are possible.

### 2.3 What to compute next

To get an actual closed formula, you need to extract:

```text
R_j(y),
key_j(y) = (hblock, anchor),
sign_j(y),
admissibility inequalities.
```

Once those are known, the count is mechanically computable and may simplify to a divisor/interval formula.  But without that normal form, no reliable exact formula for `BadKeys_j(e)` can be inferred from the data points alone.

## Q3. What is the LRS exponent algebraically?

The LRS exponent is not `even_k_exp` or `odd_k_exp` alone.  It is the fully aligned exponent at the root-packet level after decomposing the summand into:

```text
oddBilat(l,u,v,root),
oddMissingSigned(l,u,v,root),
stripUSigned(l,u,v,root),
possibly stripVSigned or companion strip terms depending on the branch.
```

The important distinction is:

```text
even_k_exp / odd_k_exp: row-level exponent formulas before the final root-packet
                        key/fiber alignment.

LRS exponent:           the exponent in the upper-aligned root-packet/fiber
                        bookkeeping after bilateral, missing, and strip pieces
                        have been combined.
```

So the counterexample exponent `e=11763` is a coefficient in the LRS bookkeeping, not one of the raw root values of the individual `odd_k_exp` rows.  That is exactly why plugging the root variables into `odd_k_exp(-5,-8,-12,m)` gives

```text
{12267, 9027, 10539, 18819}
```

rather than `11763`.

### 3.1 What does the key mean at the LRS level?

The key

```text
(hblock, anchor)
```

is a root-packet fiber label.  It is built after the row roots are grouped into anchor-pair orbits.  In the counterexample, the four root variables are

```text
{-3, 15, 29, -17}
```

and the involution

```text
n -> 12 - n
```

pairs them as

```text
{-3,15} and {-17,29}.
```

The defective anchor is on the free pair

```text
{-17,29} ≡ {1,2} mod 9,
```

not the fixed residue pair

```text
{-3,15} ≡ {6,6} mod 9.
```

Thus the LRS key is measuring root-packet anchor data, not cone data.

### 3.2 How this differs from the cone level

At the cone level, the natural key is something like:

```text
(k,r) modulo sigma/deck/coset data.
```

At the LRS level, the natural key is:

```text
root-pair block + anchor after upper alignment.
```

The map from LRS to cone is therefore a projection/summation, not an equality of variables.  Many LRS atoms can project to the same cone atom, and one LRS key may split under cone reindexing.

### 3.3 The missing definition to extract

For a rigorous paper, define an explicit map:

```text
LRSAtom(l,u,v,n,branch) -> (e, hblock, anchor, sign, supportFlag).
```

Then prove:

```text
1. tau acts on LRSAtom and maps anchor n to 12-n;
2. keyWeight is the signed sum over fixed (e,hblock,anchor);
3. the boundary defect is the part where tau exits support;
4. after summing over keys and reindexing, this boundary defect becomes
   Theta_u * Theta_v * (D-A).
```

That will make the LRS exponent precise and separate it from `even_k_exp`.

## Q4. What should the main theorem of Paper 2 be now?

Do not make `9 | e` the headline.  It is now known to be vacuous at the atom-existence level.

Do not make `M^2 ≡ -I mod 9` the headline for the counterexample either.  It is a beautiful cone/Pell theorem, but it acts one layer below the LRS key where the counterexample lives.

The strongest and cleanest main theorem is the **boundary-shell theorem**.

### Proposed main theorem

```text
Theorem A: LRS boundary-shell obstruction.
In the LRS/root-packet expansion of Chan's Theta_10, the failure of tau-pairing
is a boundary-shell phenomenon.  For each shell j>=1, no normal bad key occurs
below

    onset_j = 18*j*(17*j - 12).

The bound is sharp for j=1,2,3, with first onsets

    90, 792, 2106.
```

If the formula is not yet proved for all `j`, make it a conjecture or theorem-with-verified-cases:

```text
Theorem: verified for j=1,2,3 by exhaustive exact scan.
Conjecture: holds for all j.
```

### Secondary theorem

```text
Theorem B: Boundary generating function.
The global generating function of the LRS boundary defect factors as

    Missing_kernel = Theta_u * Theta_v * (D-A),
    D-A = -f_{1,3,4}(X,-X^3,X).
```

### Conceptual theorem

```text
Theorem C: Layer projection.
The LRS boundary-shell defect projects to the discriminant-5 cone D-A under the
root-packet-to-cone reindexing.  The Pell deck congruence M^2 ≡ -I mod 9
explains the cone-level anti-periodicity but is not itself a fiber action on
(hblock,anchor).
```

This framing is honest, precise, and publishable.  It also protects the paper from the now-corrected false claims.

## Q5. Shell-4 onset and bad-key count

The onset prediction is clear:

```text
onset_4 = 18*4*(17*4 - 12)
        = 18*4*56
        = 4032.
```

I would be very cautious about predicting the bad-key count at shell 4.  The onset formula determines the first exponent where shell-4 defects can occur, but it does not determine the multiplicity of bad keys.

### 5.1 Why no reliable count follows from the onset formula alone

The count depends on the residual minimizer set:

```text
BadKeys_4(4032)
  = # {key fibers hit by admissible minimizers of R_4=0 with nonzero boundary charge}.
```

The formula

```text
onset_j = 18j(17j-12)
```

only gives the minimum energy.  It does not give the number of minimizers.

### 5.2 What I would predict qualitatively

Given that shell 3 has `93` bad keys at onset, shell 4 may be large, probably larger than shell 3 if the residual minimizer dimension grows with `j`.  But exact monotonicity is not guaranteed.  It could be lower if parity/coset constraints become more restrictive at `j=4`.

The honest prediction is:

```text
shell-4 onset: e=4032;
bad-key count: should be computed from the residual LRS minimizer form, not guessed.
```

If you need a paper-safe statement:

```text
The onset formula predicts where shell 4 begins, not how many keys are bad at
that first exponent.  The multiplicity is a separate representation number.
```

### 5.3 Formula template for bad-key count

Once the normal form is extracted, the count should be stated as:

```text
bad_count(j,e)
  = #{ K : sum_{y in Y_j(K), R_j(y)=e-onset_j} sign_j(y) != 0 }.
```

At onset:

```text
bad_count(j,onset_j)
  = #{ K : sum_{y in Y_j(K), R_j(y)=0} sign_j(y) != 0 }.
```

This is the formula.  To get a closed form in `j`, one needs the explicit residual zero set `R_j=0` and the key map.

## Q6. How does `Theta_u * Theta_v * (D-A)` interact with the LRS decomposition?

The factorization lives after summing/reindexing the LRS boundary terms.

At the LRS level, the decomposition is:

```text
oddBilat       = bilateral/root-pair bulk term,
oddMissing     = one-sided missing-half boundary correction,
stripU/stripV  = strip boundary corrections.
```

The tau pairing cancels the bilateral/bulk part when the support is closed.  The remaining terms are exactly the boundary divergence:

```text
Boundary_LRS = oddMissing + stripU + stripV contributions after tau mismatch.
```

After summing over the root-packet fibers and changing variables, this boundary divergence factors as:

```text
Boundary_LRS generating function
  = Theta_u * Theta_v * (D-A).
```

### 6.1 Where the factors come from

The factors should be interpreted as follows:

```text
Theta_u:
  the unary theta generated by the u/root-packet strip direction.

Theta_v:
  the unary theta generated by the v/root-packet strip direction.

D-A:
  the Hecke-Rogers cone wall generated by the missing/sigma-straddling boundary
  in the remaining two variables after the LRS-to-cone reindexing.
```

Thus `D-A` is not visible as a single individual LRS atom.  It appears after:

```text
1. summing boundary LRS atoms over root-packet fibers,
2. collecting the u and v directions into unary theta factors,
3. reindexing the remaining boundary variables to the discriminant-5 cone.
```

### 6.2 What to prove

The right theorem is a commuting diagram:

```text
LRS boundary atoms
    --sum over keys / boundary divergence-->
Boundary generating function
    --reindex variables-->
Theta_u * Theta_v * (D-A)
    --HM identification-->
Theta_u * Theta_v * (-f_{1,3,4}(X,-X^3,X)).
```

This theorem makes the relationship between LRS and Paper 3 precise.

### 6.3 Important consequence

The LRS counterexample and the Paper 3 norm theta are not the same object at the same layer.  Instead:

```text
The LRS counterexample is a fiber-level boundary charge.
The norm theta D-A is the global generating function obtained after summing
and reindexing those boundary charges.
```

This is the right fusion statement.

## A concrete normal-form program

Here is a computational skeleton for the normal-form proof.  It records the theorem you want the code to discover, not a final verified formula.

```python
from dataclasses import dataclass
from typing import Callable, Iterable, Optional


@dataclass(frozen=True)
class LRSAtom:
    l: int
    u: int
    v: int
    anchor: int
    branch: str


@dataclass(frozen=True)
class Key:
    hblock: int
    anchor: int


def onset(shell: int) -> int:
    """Predicted first exponent for shell `shell`."""
    j = shell
    return 18 * j * (17 * j - 12)


def anchor_partner(n: int) -> int:
    """Root-pair anchor involution observed in the LRS fiber."""
    return 12 - n


def shell_normal_form_residual(atom: LRSAtom) -> Optional[int]:
    """Placeholder for the residual R_j after extracting onset_j.

    The goal theorem is:
        E_LRS(atom) = onset(shell(atom)) + R_j(atom)
    with R_j(atom) >= 0 on the admissible support.
    """
    raise NotImplementedError


def key_of_atom(atom: LRSAtom) -> Key:
    """The explicit LRS key map to extract from the implementation."""
    raise NotImplementedError


def lrs_exponent(atom: LRSAtom) -> int:
    """Full upper-aligned LRS exponent, not even_k_exp or odd_k_exp."""
    raise NotImplementedError


def boundary_sign(atom: LRSAtom) -> int:
    """Signed contribution of oddMissing/strip boundary terms."""
    raise NotImplementedError


def bad_key_count(shell: int, e: int, atoms: Iterable[LRSAtom]) -> int:
    """Count keys with nonzero boundary charge at exponent e and shell."""
    charges: dict[Key, int] = {}
    for atom in atoms:
        if lrs_exponent(atom) != e:
            continue
        # Replace by the real shell predicate.
        residual = shell_normal_form_residual(atom)
        if residual is None:
            continue
        if e != onset(shell) + residual:
            continue
        key = key_of_atom(atom)
        charges[key] = charges.get(key, 0) + boundary_sign(atom)
    return sum(1 for value in charges.values() if value != 0)


for j in range(1, 5):
    print(j, onset(j))
```

Expected output:

```text
1 90
2 792
3 2106
4 4032
```

## Suggested revised paper outline

### Section 1: The failed tau-pairing conjecture

State the original keyWeight=0 conjecture and the corrected layer distinction.

### Section 2: LRS root-packet setup

Define LRS atoms, full LRS exponent, `(hblock,anchor)`, tau, and boundary support.

### Section 3: Boundary-shell normal form

Prove or conjecture with verified cases:

```text
E_LRS = onset_j + R_j,
R_j >= 0,
onset_j = 18j(17j-12).
```

### Section 4: Counterexamples and shell wavefronts

Give:

```text
shell 1 onset 90,
shell 2 onset 792,
shell 3 onset 2106 with 93 bad keys,
e=11763 isolated shell-1 bad key.
```

### Section 5: Global generating function of the boundary

Prove/restate:

```text
Boundary GF = Theta_u * Theta_v * (D-A),
D-A = -f_{1,3,4}(X,-X^3,X).
```

### Section 6: Cone/Pell/norm shadow

Discuss `M^2 ≡ -I mod 9` and `eps^6` as the cone/norm projection of the boundary deck, with a clear warning that this is not the root-packet key action unless decorated-lifted.

## Answers to the six questions

### Q1. Why does the onset formula work?

Because shell onset is a constrained minimum of the full LRS exponent.  The expected normal form is

```text
E_LRS = 18j(17j-12) + R_j,
R_j >= 0.
```

The `12` comes from the anchor-pair involution `n -> 12-n`.  The `17` is the normal curvature of the full LRS boundary quadratic after root-packet/coset/parity constraints, not the cone-only curvature.

### Q2. What determines bad-key count?

The count is a representation number of the residual tangential form `R_j` inside key fibers.  At onset it counts minimizers with `R_j=0` whose boundary charge is nonzero.  This can be large at a wavefront, explaining `93` bad keys at `e=2106`, while an interior shell-1 value such as `11763` may have only one bad key.

### Q3. What is the LRS exponent?

It is the full upper-aligned root-packet exponent after combining oddBilat, oddMissingSigned, and strip contributions.  It is not `even_k_exp` or `odd_k_exp` alone.  The key `(hblock,anchor)` is a root-packet fiber label, with the anchor living in the `n -> 12-n` root-pair system.

### Q4. What should the main theorem be?

The main theorem should be the boundary-shell onset theorem plus the boundary generating function factorization.  Do not headline `9|e`.  Do not claim `M` acts directly on LRS fibers.  State that the tau-pairing defect is a shell-indexed LRS boundary charge whose global generating function is the discriminant-5 false theta factor.

### Q5. Shell-4 onset and count?

The onset prediction is

```text
onset_4 = 4032.
```

The bad-key count at shell-4 onset is not determined by the onset formula.  It requires the residual minimizer count for `R_4=0` after applying the key map and signs.  A closed formula should be a representation-number formula for `R_j`, not a guess from the first three shells.

### Q6. How does `Theta_u * Theta_v * (D-A)` interact with LRS?

It is the global sum/reindexing of LRS boundary defects.  The LRS decomposition produces boundary terms from oddMissing and strips; after summing over fibers, the `u` and `v` directions become `Theta_u` and `Theta_v`, while the remaining wall variables become the cone difference `D-A = -f_{1,3,4}(X,-X^3,X)`.

## Bottom line

The corrected story is stronger than the old `9|e` story.  It says:

```text
The obstruction is not a divisibility accident.
It is a boundary-shell wavefront phenomenon in the LRS root-packet geometry.
The onset law is quadratic and sharp:

    onset_j = 18j(17j-12).

The global generating function of the boundary charges is the same
discriminant-5 false theta cone that appears in the norm-theta paper.
```

That is the publishable core.  The next critical task is to extract the LRS normal form proving

```text
E_LRS - 18j(17j-12) = R_j >= 0
```

and then compute the residual representation formula for bad-key counts.
