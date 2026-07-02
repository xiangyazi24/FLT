# Q3074 (dm1): independent analysis of the `tau` boundary failure

Date: 2026-07-02

## Executive diagnosis

The data are exactly what I would expect from a **correct bulk involution** applied to a support set that is not actually closed under that involution.

Let `A_e` be the supported atoms at coefficient/index `e`, let

```text
tau(l,u,v) = (-l-2, 1-v, 1-u),
```

and let `K(a)` be the colored key `(hblock, anchor)` of an atom. The intended proof uses

```text
K(tau(a)) = K(a),        sign(tau(a)) = -sign(a).
```

That proves `keyWeight = 0` only on the part of the fiber where `A_e` is `tau`-stable. The exact obstruction is the `tau`-boundary

```text
partial_tau A_e = { a in A_e : tau(a) notin A_e }.
```

For every noncentral key `k`, the actual identity is

```text
keyWeight_e(k) = sum_{a in partial_tau A_e, K(a)=k} sign(a).
```

So the failure at

```text
e = 11763,
k = (-6,-17),
a = (l,u,v,color) = (-5,-8,-12,holdU)
```

is not a mysterious failure of the sign-reversing idea. It is a one-point signed boundary flux. Its formal `tau` partner is

```text
tau(a) = (3,13,9,tauColor(holdU)),
```

with the obvious caveat that the exact target color depends on the color rule. That partner has the same colored key and opposite sign, but it lies outside the root-packet support at `e=11763`.

One important consistency note: the prompt says the conjecture survives for all `e < 11763`, but it also reports a failure at `e=90`. Those two statements cannot both be literally true unless the earlier checks were excluding the boundary shell or using a filtered notion of failure. I therefore interpret the mystery as: **after ignoring the already-known `hblock = +/-1` boundary shell, why does the first deeper unbalanced fiber appear so late?** Under that interpretation, the answer is: because the deeper fibers lie inside a temporarily `tau`-symmetric core of the support until the moving boundary reaches them.

## 1. Why it survives so long, and the clean threshold formula

The right abstraction is not “does `tau` preserve the key?” but rather:

```text
Does `tau` preserve the supported subset of each key fiber?
```

For a fixed colored key `k`, the ambient fiber is usually one-dimensional after the two key coordinates are fixed. Choose an integer parameter `t` on that fiber:

```text
a = a_k(t).
```

The involution then has the form

```text
tau(a_k(t)) = a_k(s_k - t)
```

for some integer center parameter `s_k`. If `t` is literally `l`, then `s_k = -2` because `l -> -l-2`, i.e. reflection about `l=-1`.

Now suppose the root packet cuts out a finite interval, perhaps with a congruence condition,

```text
T_e(k) = { t in r_k + M Z : L_e(k) <= t <= R_e(k) }.
```

Then the fiber is `tau`-stable if and only if

```text
T_e(k) = s_k - T_e(k).
```

Ignoring the harmless residue bookkeeping for the moment, this is the endpoint condition

```text
L_e(k) + R_e(k) = s_k.
```

In the literal `l`-coordinate this becomes

```text
L_e(k) + R_e(k) = -2.
```

This is the clean local threshold test. A left-side boundary defect appears when

```text
there exists t with L_e(k) <= t <= R_e(k) but s_k - t > R_e(k),
```

which is equivalent to

```text
L_e(k) + R_e(k) < s_k.
```

A right-side boundary defect appears when

```text
there exists t with L_e(k) <= t <= R_e(k) but s_k - t < L_e(k),
```

which is equivalent to

```text
L_e(k) + R_e(k) > s_k.
```

Thus the support is protected for small `e` precisely while every noncentral key fiber under consideration has symmetric endpoints, or while any endpoint asymmetry contributes only in excluded/canceling boundary shells.

For the reported singleton at `e=11763`, the atom has `l=-5` and the missing partner has `l=3`. Therefore the relevant support interval contains `-5` but not `3`. In the `l`-interval picture this means the right endpoint is at most `2` while the left side has already reached `-5`. The support window has shifted/rounded far enough away from the `tau` center `-1` to expose a one-atom overhang.

A clean threshold formula should be written as follows. For a shell depth `m`, define

```text
F_m = min { e : there exists a noncentral key k with |hblock(k)| = m and keyWeight_e(k) != 0 }.
```

Equivalently,

```text
F_m = min { e : exists a supported atom a with |hblock(K(a))| = m,
                 tau(a) unsupported,
                 and the signed tau-boundary mass at K(a) does not cancel }.
```

If the support endpoints come from root-packet inequalities, then `L_e(k)` and `R_e(k)` are floor/ceiling functions of algebraic roots, often square-root expressions in `e`. The threshold is therefore obtained by solving

```text
L_e(k) + R_e(k) != s_k
```

with the congruence/color restrictions imposed. This is usually a finite union of integer quadratic minimization problems, one for each boundary face and residue class. In favorable cases it collapses to a piecewise quadratic quasipolynomial in the shell parameter.

So the protection for small `e` is not a theorem-level phenomenon; it is a geometry-of-numbers gap. The first lattice point in the defective collar simply occurs late.

## 2. Is the inward growth a wavefront?

Yes, with one qualification: it is a wavefront in the **first-hit envelope**, not necessarily in the set of every individual failing `e`.

The natural wavefront function is

```text
m_max(E) = max { |hblock(k)| : exists e <= E and keyWeight_e(k) != 0 }.
```

The data fit this picture:

```text
e = 90:       failures already occur, but only in hblock = +/-1.
e in [80,459]: reported failures remain in hblock = +/-1.
e = 702:      first reported deeper failure, at hblock = -2.
e = 11763:    a much deeper failure appears, at hblock = -6.
```

This is exactly what happens when the support has a `tau`-symmetric interior and an asymmetric collar. As `e` grows, the collar intersects key fibers farther from the outer shell. The wavefront is the projection of the root-packet boundary into `(hblock, anchor)` space.

I would not model the front as depending only on `|hblock|`. The `e=11763` example has key `(-6,-17)`, so the anchor is also moving. The true first-hit function is two-dimensional:

```text
F(h,a0) = min { e : keyWeight_e((h,a0)) != 0 }.
```

Then the shell front is the projection

```text
F_m = min_{anchor a0, color packet} F(+/-m,a0).
```

This distinction matters because a visually clean shell pattern can be a projection of a slanted boundary curve in the `(hblock, anchor)` plane.

Prediction strategy:

1. For each root-packet support inequality, identify the face on which `tau(a)` first fails support.
2. Parameterize atoms on that face.
3. Minimize the coefficient/index expression `e` subject to fixed `hblock` and the key congruences.
4. The resulting minima are the predicted breakdown values `F_m`.

This should be dramatically cheaper and more revealing than scanning all atoms, because boundary minimization has one fewer free variable.

## 3. Boundary compensation: the discrete Stokes form

There is an exact compensation term. Define

```text
B_e(k) = sum_{a in A_e, K(a)=k, tau(a) notin A_e} sign(a).
```

Then the true fiber identity is

```text
keyWeight_e(k) = B_e(k).
```

Equivalently, the rescued cancellation statement is

```text
keyWeight_e(k) - B_e(k) = 0.
```

This is the discrete Stokes interpretation. The bulk consists of complete two-point `tau`-orbits. Complete orbits have zero divergence because their signs cancel. The only contribution is flux through the boundary of the support region.

A more structural version is obtained by augmenting the support:

```text
A_e^sym = A_e union tau(A_e).
```

The augmented set is `tau`-stable, so its noncentral key weights cancel. Hence the original supported sum is exactly the negative of the missing mirror contribution. In formulas,

```text
0 = sum_{a in A_e^sym, K(a)=k} sign(a)
  = keyWeight_e(k) + sum_{a in tau(A_e) \ A_e, K(a)=k} sign(a).
```

Using `sign(tau(a)) = -sign(a)`, this is the same boundary formula above.

This gives a principled rescue:

```text
correctedKeyWeight_e(k) = keyWeight_e(k) - B_e(k).
```

The remaining mathematical task is to express `B_e(k)` in a closed form. Since boundary atoms lie on root-packet faces, `B_e` should be a lower-dimensional q-series: a sum over boundary faces, colors, and congruence classes. If the boundary faces themselves telescope in `anchor` or `hblock`, then the final correction may be a small number of one-dimensional false-theta/Appell-Lerch-type edge sums.

The reported `e=11763` grand total `-23` is also meaningful in this language. It says that after summing over the displayed noncentral rows, the total boundary flux is `-23`. Therefore the boundary terms are not merely local artifacts that cancel globally, unless an omitted central sector contributes `+23` or the displayed total is over a truncated subset.

## 4. Can a modified involution pair the boundary atoms?

Not on the same atom set while preserving the same key and sign data.

A sign-reversing involution on a finite key fiber implies equal positive and negative signed mass in that fiber. Therefore it forces

```text
keyWeight_e(k) = 0.
```

At `e=11763`, the key `(-6,-17)` has `keyWeight = 1`. That is a parity/mass obstruction. There is no fixed-point-free sign-reversing involution of the existing atoms in that key fiber.

There are only three possible ways out:

1. **Add mirror atoms.** Enlarge the support to `A_e union tau(A_e)` by adding phantom/missing boundary partners. Then `tau` works perfectly, and the original expression equals the boundary correction.
2. **Weaken the invariant.** Pair across different keys or across central/noncentral sectors. This cannot prove the original keywise conjecture, but it might prove a coarser aggregate identity if the aggregate signed mass is zero.
3. **Change the object being counted.** Modify colors, weights, or support conventions so that the problematic boundary mass is removed or transferred. This is not a modified involution on the original atoms; it is a modified theorem.

A piecewise involution of the form

```text
modifiedTau = T_lambda o tau
```

where `T_lambda` is a key-preserving lattice translation is worth testing only if the boundary fiber contains opposite-signed atoms that can absorb the defect. The single-key weight `1` says that such a complete pairing cannot exist inside `K=(-6,-17)` for the current support.

There is a tempting set-theoretic trick: reflect the actual support interval `[L,R]` about its own midpoint, `t -> L+R-t`, rather than reflecting about the algebraic `tau` center `s_k/2`. That pairs the finite set as a set. But it will generally fail to be the q-series involution: it need not reverse the sign, preserve the colored root-packet data, or match the transformations used in the summand. The observed nonzero key weight proves that no such reflection can be a valid sign-reversing involution for the current weighted fiber.

## 5. Is `e = 11763 = 9 * 1307` arithmetic?

The factor `9` is a serious clue; the factor `1307` is less likely to be intrinsically meaningful until the boundary quadratic form is identified.

The relevant observed values are all divisible by `9`:

```text
90    = 9 * 10,
702   = 9 * 78,
11763 = 9 * 1307.
```

That suggests the defective boundary family may live on an `e == 0 mod 9` residue class. This would be natural if the root-packet support or the coefficient exponent is controlled by quadratic forms with denominator `3` or `9`, or if an integrality condition requires a discriminant to be a square in a residue class modulo `9`.

What I would test is not “is 1307 special?” but rather:

```text
For every tau-boundary atom, what is e mod 9?
For every first-hit shell value F_m, what is F_m mod 9?
For each failed support face, which residues mod 9 are allowed?
```

If all deep boundary failures lie in one residue class, then the residue is structural. If only the first few examples are `0 mod 9`, then the pattern may be a sampling artifact.

The quotient `1307` should be interpreted as the value of the reduced boundary form after dividing out the common modulus. In other words, I would expect a formula of the schematic shape

```text
e = 9 * Q_boundary(parameters) + r_face,
```

with `r_face = 0` for the observed defective face. The number `1307` is then probably `Q_boundary` evaluated at the primitive boundary parameters corresponding to `(-5,-8,-12,holdU)`.

A useful diagnostic is to compute, for the bad atom and its missing partner, every linear form used by the support inequalities. The failed inequality should reveal whether `11763/9 = 1307` is a norm, a discriminant quotient, or just the minimized value of a face polynomial.

## 6. Analogies with known late-failure phenomena

This phenomenon is very familiar in sign-reversing combinatorics.

The closest analogies are:

* **Franklin-type involutions for partition identities.** Almost every object cancels, but boundary/staircase objects remain unpaired. Those exceptional objects occur at sparse quadratic indices, such as generalized pentagonal numbers.
* **Reflection-principle and Weyl-denominator cancellations.** Interior lattice points cancel under reflections. Points on or beyond walls produce boundary terms, singular weights, or chamber corrections.
* **Finite/truncated q-series identities.** Infinite products or bilateral sums often have exact involutions, while finite root windows introduce edge terms. The edge terms can remain invisible for a long initial range.
* **Indefinite theta and false/mock theta decompositions.** A sign function cuts the lattice by cones. Reflections cancel the bulk, but cone boundaries produce lower-dimensional correction series.
* **Ehrhart/quasipolynomial first-hit effects.** The first lattice point in a thin rational cone or boundary collar can occur very late, and its occurrence is governed by congruence classes. This gives exactly the illusion of a true identity verified through a long finite range.

So the “late failure” is not pathological. It is a standard warning sign: a proposed involution is valid on the ambient algebraic expression but not on the truncated/integer support region.

## What I would investigate first

First, I would stop summing whole fibers and directly audit the `tau`-boundary. For every supported atom, record whether the partner is supported, which support inequality fails for the partner, and the residue of `e` modulo `9`, `18`, and `27`.

The first concrete target should be the atom

```text
(-5,-8,-12,holdU) at e = 11763.
```

Compute its missing partner

```text
(3,13,9,tauColor(holdU))
```

and identify the exact failed support face. Once that face is known, repeat the calculation for `e=90` and `e=702`. If the same face, after translating shell/anchor parameters, explains all three, then the wavefront has a single governing boundary formula. If different faces are involved, the compensation term is a sum of several face contributions.

Second, I would compute first-hit tables:

```text
F(hblock)              = first e with any nonzero keyWeight at that hblock,
F(abs(hblock))         = first e with any nonzero keyWeight at that shell depth,
F(hblock, anchor)      = first e for the exact key,
F(face, hblock)        = first e caused by each failed support face.
```

Third, I would fit these first-hit values to the boundary minimization problem, not to the full atom enumeration. The boundary problem is lower-dimensional and should expose the formula.

Here is the instrumentation I would add. It is deliberately written to audit the involution boundary rather than to re-prove the identity by brute-force summation.

```python
from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Callable, DefaultDict, Dict, FrozenSet, Iterable, List, Mapping, Optional, Sequence, Tuple


@dataclass(frozen=True, order=True)
class Atom:
    l: int
    u: int
    v: int
    color: str


Key = Tuple[int, int]
Face = str


def tau_atom(atom: Atom, tau_color: Callable[[str], str]) -> Atom:
    """The proposed bulk involution on atoms."""
    return Atom(
        l=-atom.l - 2,
        u=1 - atom.v,
        v=1 - atom.u,
        color=tau_color(atom.color),
    )


def boundary_audit_for_e(
    e: int,
    atoms_at_e: Iterable[Atom],
    key_of: Callable[[Atom], Key],
    sign_of: Callable[[Atom], int],
    tau_color: Callable[[str], str],
    failed_faces: Callable[[int, Atom], Tuple[Face, ...]],
) -> Dict[str, object]:
    """
    Audit tau-cancellation at one e.

    `atoms_at_e` must be the actual supported atoms at coefficient/index e.
    `failed_faces(e, atom)` should return the support inequalities that fail for `atom`.
    For a missing tau partner, calling `failed_faces(e, tau(atom))` identifies the boundary face.
    """
    atoms: FrozenSet[Atom] = frozenset(atoms_at_e)

    key_weight: DefaultDict[Key, int] = defaultdict(int)
    boundary_weight: DefaultDict[Key, int] = defaultdict(int)
    boundary_count_by_key: Counter[Key] = Counter()
    boundary_count_by_face: Counter[Tuple[Face, int, int]] = Counter()
    residue_count_by_face: Counter[Tuple[Face, int]] = Counter()
    missing_examples: DefaultDict[Key, List[Tuple[Atom, Atom, Tuple[Face, ...]]]] = defaultdict(list)

    for atom in atoms:
        key = key_of(atom)
        sgn = sign_of(atom)
        partner = tau_atom(atom, tau_color)
        key_weight[key] += sgn

        if partner not in atoms:
            faces = failed_faces(e, partner)
            boundary_weight[key] += sgn
            boundary_count_by_key[key] += 1

            hblock, anchor = key
            if not faces:
                boundary_count_by_face[("UNKNOWN", hblock, anchor)] += 1
                residue_count_by_face[("UNKNOWN", e % 9)] += 1
            else:
                for face in faces:
                    boundary_count_by_face[(face, hblock, anchor)] += 1
                    residue_count_by_face[(face, e % 9)] += 1

            if len(missing_examples[key]) < 5:
                missing_examples[key].append((atom, partner, faces))

    mismatches = {
        key: (key_weight[key], boundary_weight.get(key, 0))
        for key in sorted(key_weight)
        if key_weight[key] != boundary_weight.get(key, 0)
    }

    nonzero_keys = {
        key: wt
        for key, wt in sorted(key_weight.items())
        if wt != 0
    }

    return {
        "e": e,
        "nonzero_keys": nonzero_keys,
        "boundary_weight": dict(boundary_weight),
        "boundary_count_by_key": dict(boundary_count_by_key),
        "boundary_count_by_face": dict(boundary_count_by_face),
        "residue_count_by_face_mod9": dict(residue_count_by_face),
        "missing_examples": dict(missing_examples),
        "identity_mismatches": mismatches,
    }


def first_hit_by_shell(
    e_values: Iterable[int],
    atoms_for_e: Callable[[int], Iterable[Atom]],
    key_of: Callable[[Atom], Key],
    sign_of: Callable[[Atom], int],
    tau_color: Callable[[str], str],
    failed_faces: Callable[[int, Atom], Tuple[Face, ...]],
) -> Dict[int, Tuple[int, Key, int]]:
    """
    Return the first e at which each |hblock| shell has nonzero keyWeight.
    The value is shell -> (e, key, keyWeight).
    """
    first: Dict[int, Tuple[int, Key, int]] = {}

    for e in sorted(e_values):
        audit = boundary_audit_for_e(
            e=e,
            atoms_at_e=atoms_for_e(e),
            key_of=key_of,
            sign_of=sign_of,
            tau_color=tau_color,
            failed_faces=failed_faces,
        )
        nonzero_keys: Mapping[Key, int] = audit["nonzero_keys"]  # type: ignore[assignment]

        for key, weight in nonzero_keys.items():
            hblock, _anchor = key
            shell = abs(hblock)
            if shell not in first:
                first[shell] = (e, key, weight)

    return first


def interval_defect(left: int, right: int, tau_center_sum: int = -2) -> int:
    """
    For a one-dimensional fiber parameter t with tau(t)=tau_center_sum-t,
    return the endpoint defect. Zero means the integer interval endpoints are tau-symmetric.
    """
    return left + right - tau_center_sum


def has_left_overhang(left: int, right: int, tau_center_sum: int = -2) -> bool:
    """True when the support interval reaches too far to the left for tau-closure."""
    return left + right < tau_center_sum


def has_right_overhang(left: int, right: int, tau_center_sum: int = -2) -> bool:
    """True when the support interval reaches too far to the right for tau-closure."""
    return left + right > tau_center_sum
```

The most important assertion to check in real data is this:

```text
keyWeight_e(k) == boundaryWeight_e(k)
```

for every noncentral key. If that equality holds, then the entire problem has been reduced from a mysterious q-series identity failure to an explicit boundary enumeration problem.

## Bottom line

The conjecture survives deep into the computation because `tau` is a valid involution on a large symmetric core of the root-packet support, and the asymmetric boundary collar reaches deeper `hblock` fibers only at sparse, arithmetically constrained `e` values. The inward progression is best viewed as a boundary wavefront in `(hblock, anchor)` space. A boundary compensation term is not only possible; it is the exact correction forced by the involution. A modified involution on the original atoms cannot pair everything at `e=11763`, because the key `(-6,-17)` has nonzero signed mass. The factor `9` is probably structural; the quotient `1307` should be decoded as a value of the reduced boundary quadratic form rather than treated as an isolated numerological factor.
