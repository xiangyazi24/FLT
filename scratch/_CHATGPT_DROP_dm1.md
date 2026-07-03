# Q3174 (dm1): Paper 2 Round 6 — From Statistics to Mechanism

Date: 2026-07-03

## Executive answer

R6 changes the story in the right direction.  The old R1--R5 language was descriptive:

```text
shells, hblock, onset, theta opening, tentative factorization.
```

The R5 experiments show that this descriptive layer is not the mechanism.  The correct mechanism is:

```text
The obstruction is the boundary defect of a mod-9 ghost symmetry.
```

More precisely:

```text
τ = M^2
τ ≡ -I mod 9
τ ≠ -I over Z
```

so `τ` is a genuine integral change of variables which only looks like the required involution after reduction mod `9`.  It pairs the interior algebraically, but it does not preserve the integral summation domain.  Therefore the surviving coefficient is not a shell product.  It is the divergence of the domain indicator across the `τ` boundary.

The key replacement for the failed factorization is:

```text
Bad = not N_0 * Θ_shell,
Bad = τ-boundary defect of the legal summation cone.
```

In generating-function form, the repair should be stated as

```text
Θ_10 = Main_τ + Corr_τ
```

with

```text
Corr_τ = Θ_u Θ_v (D - A)
       = - Θ_u Θ_v f_{1,3,4}(X, -X^3, X).
```

Here `D-A` is the signed departure-minus-arrival boundary series for the failed `τ` pairing.  This is the publishable mechanism.  The hblock/onset/factorization statistics should now be demoted to diagnostics and historical evidence.

---

## 1. What replaces the failed factorization?

The failed conjecture was

```text
Bad(q) ?= N_0(q) Θ_shell(q).
```

The experiments rule this out decisively:

```text
aggregate mismatches:             430/450
per-shell translated-copy rate:   about 5%
formal quotient Bad/Θ:            many negative coefficients
N_h(onset_h+x) != N_0(x):          generic
```

This means the bad set is not made by copying a base layer along a theta lattice.  The shell counts were measuring a shadow of a symmetry, not the symmetry itself.

### Correct structural object

Let `Λ` be the integral packet lattice.  Let `C ⊂ Λ` be the true legal summation cone/domain, and let `C_B` be the finite scan truncation.  Let

```text
χ_C(x) = 1 if x is in the legal summation domain,
       = 0 otherwise.
```

Let `wt(x)` be the full signed monomial weight of a packet, including coefficient sign, exponent, and key variables:

```text
wt(x) = s(x) q^{E(x)} z^{K(x)}.
```

The ghost map is

```text
τ = M^2.
```

It has the crucial property that the reduced algebra sees it as the missing involution:

```text
τ ≡ -I mod 9,
```

but the integral summation problem does not:

```text
τ ≠ -I over Z.
```

The expected cancellation is therefore valid only on the `τ`-paired interior.  The actual obstruction is the signed failure of the domain indicator to be invariant:

```text
δ_τ χ_C(x) = χ_C(x) - χ_C(τ^{-1}x).
```

Then the corrected structural description is

```text
BadSeries = boundary_τ(C; wt)
          = (1/2) Σ_{x∈Λ} δ_τχ_C(x) wt(x),
```

with the factor `1/2` present when `D` and `A` are raw boundary strips.  If `D` and `A` are defined as already pair-compressed boundary series, then the same formula is written without the explicit `1/2`:

```text
BadSeries = D - A.
```

The evaluated form of this boundary series is the confirmed defect:

```text
BadSeries = Θ_u Θ_v (D - A)
          = - Θ_u Θ_v f_{1,3,4}(X, -X^3, X).
```

This is the replacement for `N_0 * Θ_shell`.

### Interpretation

The counterexample set is a signed boundary, not a product set.

The old theta shell appeared because the Pell/coset dynamics leaves strong quadratic traces.  But the set of surviving terms is selected by the mismatch

```text
C Δ τC,
```

not by free translation along an independent theta coordinate.  Therefore shell asymmetry, negative hblocks appearing early, and `B`-dependent onsets are not bugs in the data.  They are exactly what a chiral boundary defect should produce.

A compact slogan for the paper:

```text
The obstruction is not a theta factorization.  It is a τ-boundary cocycle.
```

---

## 2. Precise theorem: key weight as boundary divergence

The theorem should be stated at the level of the signed monomial series first, and then coefficientwise.

### Theorem A — ghost symmetry and interior cancellation

Let `Λ` be the integral packet lattice and let `τ=M^2` be the Pell transformation attached to the coset `L`.  Assume:

```text
1. τ is an integral bijection of Λ.
2. τ ≡ -I mod 9 on the reduced packet data.
3. The signed monomial weight is τ-anti-invariant on the paired algebra:

       wt(τx) = -wt(x).
```

Then for every `τ`-invariant finite subset `S ⊂ Λ`,

```text
Σ_{x∈S} wt(x) = 0.
```

This is the exact mathematical replacement for the informal statement “the main terms pair under `τ`.”

### Theorem B — boundary divergence formula

For any finite truncation `C_B` of the legal summation domain,

```text
Σ_{x∈C_B} wt(x)
  = (1/2) Σ_{x∈Λ} (χ_B(x) - χ_B(τ^{-1}x)) wt(x),
```

where `χ_B` is the indicator of `C_B`.

Equivalently, if

```text
D_B = C_B \ τC_B,
A_B = τC_B \ C_B,
```

then

```text
Σ_{x∈C_B} wt(x)
  = (1/2) ( Σ_{x∈D_B} wt(x) - Σ_{x∈A_B} wt(x) ).
```

This is the exact boundary term.  The interior cancels; only the symmetric difference survives.

### Coefficientwise version

Let `Π_{e,K}` denote coefficient extraction at exponent `e` and key `K`.  Define

```text
keyWeight_B(e,K) = [q^e z^K] Σ_{x∈C_B} wt(x).
```

Then

```text
keyWeight_B(e,K)
  = [q^e z^K] (1/2) Σ_{x∈Λ} (χ_B(x)-χ_B(τ^{-1}x)) wt(x).
```

Equivalently,

```text
keyWeight_B(e,K)
  = [q^e z^K] boundary_τ(C_B; wt).
```

After evaluating the boundary strips and passing to the stable coefficient range, this becomes

```text
keyWeight(e,K)
  = [q^e z^K] Θ_u Θ_v (D-A)
  = -[q^e z^K] Θ_u Θ_v f_{1,3,4}(X,-X^3,X).
```

This is the theorem that should replace the old shell-copy theorem.

### Why this proves the missing kernel coefficient

If the original derivation implicitly assumed

```text
χ_C(x) = χ_C(τ^{-1}x),
```

then it silently threw away

```text
δ_τχ_C = χ_C - χ_C∘τ^{-1}.
```

The missing kernel coefficient is exactly the coefficient of this discarded boundary divergence.

---

## 3. The repair: corrected identity for `Θ_10`

The repaired identity should be stated as an identity of generating series, not as an enumeration claim.

Let `Main_τ` denote the part of the original expression whose summation domain is genuinely paired by `τ`, or equivalently the expression obtained after cancelling the `τ`-paired interior terms.

Then the corrected identity is

```text
Θ_10 = Main_τ + Corr_τ,
```

where

```text
Corr_τ = Θ_u Θ_v (D-A).
```

Using the confirmed boundary evaluation,

```text
D-A = -f_{1,3,4}(X,-X^3,X),
```

so the clean repaired formula is

```text
Θ_10 = Main_τ - Θ_u Θ_v f_{1,3,4}(X,-X^3,X).
```

Equivalently,

```text
Θ_10 + Θ_u Θ_v f_{1,3,4}(X,-X^3,X) = Main_τ.
```

This is likely the best published form because it says exactly what went wrong:

```text
The old identity was missing a boundary correction forced by the fact that
τ is only a mod-9 symmetry, not an integral symmetry of the summation domain.
```

### Sign convention

The sign should be fixed by the definition of `Defect`.

If

```text
Defect = Actual Θ_10 - Claimed main expression,
```

then the R6 statement gives

```text
Defect = - Θ_u Θ_v f_{1,3,4}(X,-X^3,X).
```

If instead

```text
Defect = Claimed main expression - Actual Θ_10,
```

then all signs reverse.  The paper should choose one convention and display it once.

Recommended convention:

```text
Corr_τ := Actual - Main_τ.
```

Then

```text
Corr_τ = Θ_u Θ_v(D-A)
       = -Θ_u Θ_v f_{1,3,4}(X,-X^3,X).
```

---

## 4. Meaning of shell asymmetry and chirality

The shell asymmetry is no longer mysterious after the factorization failure.

The old mental model was:

```text
hblock = shell coordinate,
positive and negative shells are two sides of one theta,
N_h should look like N_{-h} after translation.
```

R5 shows this is false:

```text
N_1 versus N_{-1}: 10.7% match
N_2 versus N_{-2}: 29.0% match
N_3 versus N_{-3}: 66.3% match
negative hblocks appear before positive predicted onsets
```

The correct interpretation is:

```text
hblock is a chiral boundary coordinate, not a symmetric shell coordinate.
```

The map `τ` is congruent to `-I` mod `9`, so modulo `9` it looks like it should reverse the packet.  But integrally it has drift.  It sends the legal cone to a shifted cone:

```text
C  ----τ---->  τC,
```

and the obstruction lives in

```text
C Δ τC.
```

There is no reason for this signed boundary to be symmetric under `h ↦ -h`.  In fact, asymmetry is expected unless the cone itself has an independent reflection symmetry interchanging the two sides.  R5 shows it does not.

### Why negative hblocks appear earlier

Negative hblocks appearing before the positive onset prediction means the predicted onset was not intrinsic.  It was the minimum of a restricted/truncated scan path.  Once `B` is enlarged, the legal cone exposes boundary points that were invisible before.

Geometrically:

```text
positive hblock side: boundary intersects the scan window later,
negative hblock side: boundary intersects the scan window earlier.
```

This is chirality.  It comes from the orientation of the Pell map and the fact that `τ` is an integral drift, not an exact reflection.

### Relation to theta branches

There is still a theta-like branch phenomenon, but it should not be treated as a product factor.  Even the old Ramanujan theta

```text
f(q^522,q^90)
```

has asymmetric first branches:

```text
90 and 522.
```

The completed square is centered at a nonintegral characteristic:

```text
18h(17h-12) = (18/17)((17h-6)^2 - 36),
```

so the two directions are already biased by the shift `6/17`.  The new data says the actual boundary defect is even more chiral: the summation cone selects one side earlier than the other.  Thus the branch language is useful as local intuition, but the correct invariant is the `τ`-boundary, not the theta branch count.

---

## 5. All anchors odd and why `τ` acts freely

This part is now solid and should remain in the paper.

The anchor is the triangular root variable

```text
A = 2n - 1.
```

Therefore

```text
A ≡ 1 mod 2.
```

All anchors are odd for structural reasons; no finite verification is needed except as a sanity check.

The putative fixed anchor of the `τ` action is the even residue/anchor value `6`.  Since anchors are always odd, that fixed point is never realized in the actual root-packet lattice.  Therefore `τ` acts freely on realized anchors.

This matters because it prevents a second possible source of defect.  The obstruction is not caused by fixed points of `τ`.  It is caused by the boundary:

```text
fixed-point defect: absent,
boundary defect: present.
```

This is a very clean causal statement.

---

## 6. The parity gap at `126`

The R5 parity gap refines the old `126 = 90 + 36` observation.

The confirmed mechanism is:

```text
first onset anchors at e=90,
new anchors at e=126,
126 = 90 + 2*18,
step 1 is forbidden by odd parity.
```

Since anchors are odd, the next legal anchor displacement after an onset anchor is not a one-step displacement.  It is a two-step displacement.  In the exponent scale, one step of the anchor lattice corresponds to `18`, so the first allowed parity-preserving jump contributes

```text
2*18 = 36.
```

Thus

```text
126 = 90 + 36
```

has a better explanation than the old completed-square numerology:

```text
36 is the first parity-allowed anchor displacement from the onset packet.
```

This does not contradict the completed-square observation.  It strengthens it.  The same number `36=6^2=2*18` is seen from two sides:

```text
theta characteristic defect: 36 = 6^2,
anchor parity gap:           36 = 2*18.
```

The paper should present the parity-gap explanation as the causal one, and the completed-square identity as supporting arithmetic structure.

---

## 7. Minimal theorem package for publishable Paper 2

The publishable Paper 2 should no longer try to prove a factorization theorem.  It should prove a mechanism theorem and a repair theorem.

### Theorem 1 — Coset ghost theorem

```text
For the coset L, the Pell transformation M has trace 18 and the map τ=M^2
satisfies

    τ ≡ -I mod 9,
    τ ≠ -I over Z.

Thus τ is a mod-9 ghost symmetry: it is the expected involution after reduction
modulo 9, but not an integral symmetry of the summation domain.
```

Purpose: identifies the exact source of the false cancellation.

### Theorem 2 — Odd-anchor/free-action theorem

```text
Every realized root-packet anchor has the form A=2n-1 and is therefore odd.
The only possible fixed anchor for τ is even, hence τ acts freely on realized
anchors.
```

Purpose: proves that the defect is not a fixed-point defect.

### Theorem 3 — Interior cancellation theorem

```text
On every τ-invariant finite subdomain, the signed packet weights cancel in
pairs.
```

Purpose: salvages the original idea: the main terms really do pair, but only in the interior.

### Theorem 4 — Boundary divergence theorem

```text
For every finite scan domain C_B,

    Σ_{x∈C_B} wt(x)
      = (1/2) Σ_{x∈Λ} (χ_B(x)-χ_B(τ^{-1}x)) wt(x).
```

Coefficientwise,

```text
keyWeight_B(e,K)
  = [q^e z^K] boundary_τ(C_B; wt).
```

Purpose: gives the precise causal formula.

### Theorem 5 — Boundary evaluation theorem

```text
The τ-boundary series factors along the free u and v directions and leaves a
one-dimensional anchor defect:

    boundary_τ(C; wt)
      = Θ_u Θ_v (D-A)
      = -Θ_u Θ_v f_{1,3,4}(X,-X^3,X).
```

Purpose: identifies the missing kernel coefficient explicitly.

### Theorem 6 — Corrected `Θ_10` identity

```text
Θ_10 = Main_τ - Θ_u Θ_v f_{1,3,4}(X,-X^3,X).
```

Equivalently,

```text
Θ_10 + Θ_u Θ_v f_{1,3,4}(X,-X^3,X) = Main_τ.
```

Purpose: states the repair.

### Theorem 7 — Stability / B-independence theorem

```text
For each fixed coefficient e and key K, there is a bound B_0(e,K) such that
for all B ≥ B_0(e,K),

    keyWeight_B(e,K) = keyWeight(e,K).

The stable value is the coefficient of the τ-boundary correction, not an hblock
onset count.
```

Purpose: removes dependence on fragile scan onsets.

### Appendix-only results

The following should be moved to an appendix or computational diagnostics section:

```text
hblock counts,
onset tables,
failed factorization data,
N_h versus N_{-h} mismatch tables,
finite anchor parity verification.
```

They are useful evidence, but not the theorem architecture.

---

## 8. B-independent characterization

The `B`-dependent onset failure is important.  It says:

```text
onset_h(B) is not a number-theoretic invariant.
```

A scan cutoff can hide legal packets.  Enlarging `B` changes the first observed packet in a given hblock.  Therefore the paper should stop using hblock onset as a primary invariant.

The B-independent characterization is:

```text
Counterexample structure = support/coefficient mass of the stable τ-boundary
of the legal summation cone.
```

Formally, define the infinite legal cone `C` first.  Then define

```text
∂_τ C = C Δ τC.
```

The signed boundary indicator is

```text
δ_τχ_C = χ_C - χ_C∘τ^{-1}.
```

The stable defect series is

```text
Defect(q,z)
  = (1/2) Σ_{x∈Λ} δ_τχ_C(x) wt(x).
```

Then for fixed `e,K`, define

```text
keyWeight(e,K) = [q^e z^K] Defect(q,z).
```

This is independent of `B`.  A finite scan is only a method of approximating the coefficient, and it is valid only once `B` is large enough to contain all boundary points contributing to that coefficient.

The practical test is not “does the onset match a formula?”  The practical test is:

```text
Does keyWeight_B(e,K) stabilize as B increases, and does the stable value equal
[q^e z^K](-Θ_u Θ_v f_{1,3,4}(X,-X^3,X))?
```

That is the right verification target.

---

## 9. What the counterexample set is, in one sentence

The counterexample set is the set of realized packets whose `τ` partner exists modulo `9` but lies outside the integral legal summation domain.

Equivalently:

```text
Counterexamples = unpaired terms on C Δ τC.
```

Weighted by the packet kernel, they generate

```text
-Θ_u Θ_v f_{1,3,4}(X,-X^3,X).
```

This is the causal explanation.

---

## 10. Recommended paper architecture

A minimal, mechanism-first paper could be:

### Section 1. The failed cancellation

State the original claimed pairing and show what it would require:

```text
an integral involution preserving the summation domain.
```

Then state the actual map:

```text
τ=M^2 ≡ -I mod 9 but τ≠-I over Z.
```

### Section 2. Root packets and odd anchors

Prove:

```text
A=2n-1,
all anchors odd,
τ has no realized fixed points.
```

### Section 3. Interior pairing

Prove the anti-invariance of the signed packet weight:

```text
wt(τx)=-wt(x).
```

Then prove cancellation on `τ`-invariant domains.

### Section 4. Boundary divergence

Prove the indicator identity:

```text
Σ_C wt = (1/2)Σ(χ_C-χ_C∘τ^{-1})wt.
```

This is the main conceptual theorem.

### Section 5. Evaluation of the boundary

Compute the boundary strips explicitly:

```text
D-A = -f_{1,3,4}(X,-X^3,X),
Corr_τ = -Θ_uΘ_v f_{1,3,4}(X,-X^3,X).
```

### Section 6. Corrected identity

State and prove:

```text
Θ_10 = Main_τ - Θ_uΘ_v f_{1,3,4}(X,-X^3,X).
```

### Section 7. Computational verification

Verify:

```text
1. M^2 ≡ -I mod 9 and M^2≠-I over Z;
2. all anchors are odd;
3. no τ fixed anchors are realized;
4. finite scans stabilize to the boundary correction;
5. the coefficient at e=126 is exactly the missing kernel coefficient;
6. shell factorization fails, as predicted by the boundary model.
```

The factorization failure becomes a confirmation of the mechanism, not a setback.

---

## 11. Verification harness

This is a skeleton for the exact tests the repository should contain.  It deliberately tests the mechanism, not the obsolete factorization conjecture.

```python
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, Iterable, Iterator, Mapping, MutableMapping, Sequence, Tuple

Vector = Tuple[int, ...]
Key = Tuple[int, ...]
CoeffKey = Tuple[int, Key]
Series = Dict[CoeffKey, int]


@dataclass(frozen=True)
class PacketTerm:
    """One signed packet term in the integral summation lattice."""

    point: Vector
    degree: int
    key: Key
    coeff: int

    def monomial_key(self) -> CoeffKey:
        return (self.degree, self.key)


def add_to_series(series: MutableMapping[CoeffKey, int], term: PacketTerm, scale: int = 1) -> None:
    """Accumulate a packet term into a sparse coefficient series."""
    ck = term.monomial_key()
    series[ck] = series.get(ck, 0) + scale * term.coeff
    if series[ck] == 0:
        del series[ck]


def matrix_vector_mul(matrix: Sequence[Sequence[int]], vector: Vector) -> Vector:
    """Multiply an integer matrix by an integer vector."""
    return tuple(sum(row[j] * vector[j] for j in range(len(vector))) for row in matrix)


def mod_vector(vector: Vector, modulus: int) -> Vector:
    """Reduce a vector modulo modulus."""
    return tuple(x % modulus for x in vector)


def assert_tau_is_mod9_ghost(tau_matrix: Sequence[Sequence[int]]) -> None:
    """Check τ ≡ -I mod 9 and τ != -I over Z."""
    dim = len(tau_matrix)
    minus_identity = tuple(
        tuple(-1 if i == j else 0 for j in range(dim))
        for i in range(dim)
    )
    tau_tuple = tuple(tuple(row) for row in tau_matrix)

    if tau_tuple == minus_identity:
        raise AssertionError("τ is literally -I over Z; not a ghost")

    for i, row in enumerate(tau_matrix):
        for j, value in enumerate(row):
            expected = -1 if i == j else 0
            if (value - expected) % 9 != 0:
                raise AssertionError(
                    f"τ is not -I mod 9 at entry {(i, j)}: {value} vs {expected}"
                )


def anchor_from_j_block(n: int) -> int:
    """Triangular root variable; structurally odd."""
    return 2 * n - 1


def assert_anchor_is_odd(n: int) -> None:
    """Check the structural parity lemma for a realized j-block index."""
    anchor = anchor_from_j_block(n)
    if anchor % 2 == 0:
        raise AssertionError(f"even anchor realized: n={n}, anchor={anchor}")


def boundary_divergence_series(
    terms: Iterable[PacketTerm],
    tau: Callable[[Vector], Vector],
    inverse_tau: Callable[[Vector], Vector],
    in_domain: Callable[[Vector], bool],
    term_at: Callable[[Vector], PacketTerm],
) -> Series:
    """Compute the raw τ-boundary divergence.

    This implements

        (1/2) Σ_x (χ(x)-χ(τ^{-1}x)) wt(x).

    To avoid fractions, the function returns the doubled boundary series:

        Σ_x (χ(x)-χ(τ^{-1}x)) wt(x).

    The caller can divide coefficients by 2 after verifying they are even, or
    can compare against a boundary series D-A that has been defined with the
    same raw normalization.
    """
    doubled: Series = {}
    seen_points = {term.point for term in terms}
    closure_points = set(seen_points)
    for point in tuple(seen_points):
        closure_points.add(tau(point))
        closure_points.add(inverse_tau(point))

    for point in closure_points:
        delta = int(in_domain(point)) - int(in_domain(inverse_tau(point)))
        if delta == 0:
            continue
        add_to_series(doubled, term_at(point), scale=delta)

    return doubled


def scan_series(terms: Iterable[PacketTerm], in_domain: Callable[[Vector], bool]) -> Series:
    """Direct finite-domain packet sum."""
    series: Series = {}
    for term in terms:
        if in_domain(term.point):
            add_to_series(series, term)
    return series


def compare_series(lhs: Mapping[CoeffKey, int], rhs: Mapping[CoeffKey, int]) -> Dict[CoeffKey, Tuple[int, int]]:
    """Return coefficient mismatches between two sparse series."""
    keys = set(lhs) | set(rhs)
    return {key: (lhs.get(key, 0), rhs.get(key, 0)) for key in keys if lhs.get(key, 0) != rhs.get(key, 0)}


def first_missing_kernel_coefficient(series: Mapping[CoeffKey, int]) -> Tuple[CoeffKey, int] | None:
    """Return the smallest nonzero coefficient in degree order."""
    nonzero = [(key, value) for key, value in series.items() if value]
    if not nonzero:
        return None
    return min(nonzero, key=lambda item: (item[0][0], item[0][1]))
```

The repository-specific implementation should supply:

```text
1. the actual packet lattice points;
2. the actual matrix M and τ=M^2;
3. the legal-domain predicate χ_C or χ_B;
4. the exact packet-term weight wt(x);
5. the closed-form boundary series -Θ_uΘ_v f_{1,3,4}(X,-X^3,X).
```

Then the central validation is:

```text
Direct finite scan = τ-boundary divergence = closed-form correction.
```

not

```text
Direct finite scan = N_0 * Θ_shell.
```

---

## 12. Final synthesis

Round 6 should be the pivot of Paper 2.

The old summary was:

```text
The counterexample set appears to have theta shell statistics.
```

The corrected summary is:

```text
The original identity fails because the cancellation map is a mod-9 ghost:
τ=M^2 behaves like -I modulo 9 but not over the integers.  It pairs the interior
and acts freely on odd anchors, but the legal summation cone is not τ-invariant.
The surviving obstruction is exactly the τ-boundary divergence, evaluated as

    -Θ_u Θ_v f_{1,3,4}(X,-X^3,X).

Adding this term repairs the Θ_10 identity.
```

That is a mechanism.  It explains the failed factorization, the shell asymmetry, the early negative hblocks, the `B`-dependent onsets, the parity gap at `126`, and the missing kernel coefficient with one cause:

```text
integral boundary failure of a mod-9 ghost symmetry.
```
