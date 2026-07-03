# Q3169 (dm2): Paper 2 counterexample — targeted response

Date: 2026-07-03

## Summary

The prompt gives enough structure to identify the likely failure mechanism, but not enough to reconstruct every numerical support-window inequality from Chan's paper. The central point is this:

```text
The tau pairing is algebraically correct on the quadratic/fiber equation, but the finite support window is only almost tau-stable. The defect is a half-open-boundary defect. It appears exactly when an e/9 boundary becomes integral, i.e. when 9 | e.
```

Thus the counterexamples are not random failures of the quadratic symmetry. They are boundary atoms on the 9-dissection wall. The `sigma(k,r) = (k, -r - 6k - 1)` involution removes the internal `(k,r)` sign obstruction, so the remaining defect must be in the support cut in the `(l,u,v)` or `(m,t,d)` variables.

I will write

```text
m = l + 1,
t = u + v - 1,
d = u - v.
```

Then the inverse change of variables is

```text
l = m - 1,
u = (t + d + 1)/2,
v = (t - d + 1)/2.
```

Therefore the integral lattice condition is

```text
t + d + 1 even, equivalently t + d == 1 mod 2.
```

The tau involution is

```text
tau(m,t,d) = (-m,-t,d).
```

In the original variables this is

```text
l' = -m - 1 = -l - 2,
u' = (-t + d + 1)/2,
v' = (-t - d + 1)/2.
```

For the specific point mentioned in the prompt,

```text
(m,t,d) = (4,21,4)
```

one has

```text
(l,u,v) = (3,13,9),
tau(m,t,d) = (-4,-21,4),
(l',u',v') = (-5,-8,-12).
```

So if the atom support contains the ordinary nonnegative root-packet cone in `(l,u,v)`, the tau partner is visibly outside that cone. The only way a fiber-local tau proof can work is if the actual finite dissection window supplies an additional, nontrivial identification/correction. The observed `9 | e` failures say that this window is not exactly tau-stable on the 9-boundary.

---

## Q1. Why `9 | e` breaks tau-symmetry

The algebraic mechanism is a floor/ceiling endpoint jump. More precisely, the dissection support is controlled by affine bounds whose endpoints contain `e/9` or an equivalent quotient from the 9-dissection. Under tau, the relevant affine form changes sign, so the reflected support condition uses a complementary floor/ceiling expression.

The basic identity is

```text
floor(x) + floor(-x) = -1  if x is not an integer,
floor(x) + floor(-x) =  0  if x is an integer.
```

Equivalently, the reflected half-open intervals match perfectly away from integral endpoints, but differ by one endpoint when the endpoint lands on the lattice.

Thus the break is not merely that the exponent formula has a visible factor of 9. The factor of 9 matters because it is the denominator of the support-window endpoint. When `e/9` is not integral, the tau-reflected half-open bounds are complementary and no lattice point lies exactly on the wall. When `9 | e`, the wall is an honest lattice wall. The half-open convention includes the boundary atom on one side and excludes the reflected boundary atom on the other side.

This is exactly the type of mechanism suggested in the question: the support bounds become integral at `9 | e`, and the tau partner can fall into the one-endpoint gap.

The formula

```text
n = 54*l + 45 = 9*(6*l + 5)
```

should be read as one affine branch of the 9-dissection boundary. In terms of `m = l + 1`, this is

```text
n = 54*m - 9 = 9*(6*m - 1).
```

So the boundary branch is invisible unless the relevant exponent is divisible by 9. After division by 9, the remaining residue modulo 6 chooses which affine branch of the boundary one is on. This reconciles the two facts:

```text
necessary trigger: 9 | e,
branch selection: e/9 lies in a particular residue class modulo 6.
```

The counterexamples should therefore be interpreted as boundary-wall atoms of the support window, not as failures of the quadratic tau symmetry itself.

---

## Q2. Can the residual keyWeight be written as a boundary divergence?

Yes, but with an important distinction:

```text
It can be written as a relative boundary divergence / boundary flux.
It cannot be written as an ordinary divergence on a closed finite fiber if the total residual in that fiber is nonzero.
```

The reason is elementary. On a finite closed graph,

```text
sum_vertices div(F) = 0.
```

Therefore a nonzero total `keyWeight` residual cannot be a pure divergence on a closed fiber. If the residual is nonzero, there must be flux through a boundary, a ghost vertex, or a quotient identification.

The natural correction is to define the tau-defect boundary

```text
partial_tau S_e = S_e symmetric_difference tau(S_e).
```

The residual is supported on this set. For an atom `x`, let `w(x)` be its signed contribution. Then the tau-pairing defect is schematically

```text
rho_e(x) = w(x) * 1_{x in S_e} + w(tau x) * 1_{tau x in S_e}.
```

If tau reverses the sign, then this vanishes whenever both `x` and `tau x` are present. Hence `rho_e` is supported exactly where one of the two endpoints is missing.

A relative edge correction can be defined as follows. For every unmatched atom `x in S_e \ tau(S_e)`, add a formal edge from the missing ghost point `tau(x)` to `x`, and set

```text
F(tau(x) -> x) = w(x).
```

Then the divergence of `F` produces the observed interior residual at `x`, while the opposite contribution is carried by the ghost/boundary endpoint. This gives

```text
rho_e = div(F) + boundary_flux.
```

So the fiber-local proof can be rescued, but only after adding a correction term equal to the tau-boundary flux. Without that boundary term, a nonzero residual cannot be killed by an internal divergence.

The `(k,r)` involution `sigma(k,r) = (k, -r - 6k - 1)` is useful here because it preserves the quadratic `(k,r)` value and flips `(-1)^r`. Thus the remaining correction can be localized to the tau-boundary in `(m,t,d)` rather than spread through the full five-variable atom set.

---

## Q3. Does the missing partner re-enter by a deck transformation / period `P`?

For the particular point `(4,21,4)`, the reflected point is

```text
tau(4,21,4) = (-4,-21,4).
```

To identify these two points by a translation, one would need a period containing

```text
P = (4,21,4) - (-4,-21,4) = (8,42,0).
```

There is no natural reason for this to be a deck period. A genuine translation period would have to satisfy all of the following conditions:

```text
1. Preserve the parity lattice: t + d == 1 mod 2.
2. Preserve the quadratic/fiber exponent, at least modulo the dissection modulus.
3. Preserve the support inequalities, including their half-open endpoints.
4. Preserve the signed character, or change it by exactly the sign needed for cancellation.
```

Condition 2 is already very restrictive. For a quadratic form `Q`, translation by `P` changes the value by

```text
Q(x + P) - Q(x) = B(P,x) + Q(P),
```

where `B` is the associated bilinear form. Unless `P` lies in the radical modulo the relevant modulus, this depends on `x` and is not a fiber-preserving deck transformation. The forms in this problem are nondegenerate in the tau variables, so a large atom-dependent vector such as `(8,42,0)` is not a plausible exact period.

Thus my answer is:

```text
No natural deck translation explains the missing partner.
```

A quotient by the artificially chosen period `(8,42,0)` would identify this particular pair, but that would not be a structural proof. A valid quotient proof would need a fixed period lattice, independent of the counterexample, with a verified invariant quadratic form and character. The prompt does not provide such a period, and the observed mechanism is better explained by boundary flux than by periodic re-entry.

A weaker possibility remains: the missing point may reappear in a different exponent fiber or in another branch of the dissection under a unit action. That is not the same as tau working on `Z^2/P` inside the original fiber.

---

## Q4. Explicit support set `S` in `(m,t,d)`

The part that can be derived unambiguously from the prompt is the lattice change of variables. Define

```text
Lambda = { (m,t,d) in Z^3 : t + d == 1 mod 2 }.
```

Then

```text
l = m - 1,
u = (t + d + 1)/2,
v = (t - d + 1)/2.
```

If the root-packet support includes the standard nonnegative cone

```text
l >= 0,
u >= 0,
v >= 0,
```

then its pullback to `(m,t,d)` is

```text
m >= 1,
t + d >= -1,
t - d >= -1,
t + d == 1 mod 2.
```

Equivalently,

```text
m >= 1,
t >= |d| - 1,
t + d == 1 mod 2.
```

So the base cone is

```text
S_base = {
  (m,t,d) in Z^3 :
  m >= 1,
  t >= |d| - 1,
  t + d == 1 mod 2
}.
```

However, this base cone is not the full finite support of Chan's 9-dissection packet. The actual support must also include the finite e-dependent dissection window. Abstractly, the correct form is

```text
S_e = Lambda ∩ C_root ∩ W_e,
```

where

```text
C_root = pullback of the root-packet cone in (l,u,v),
W_e    = the e-dependent half-open 9-dissection window.
```

The failure described in Q1 is specifically a failure of tau-stability of `W_e` on the boundary `9 | e`.

So the tau-symmetry condition that Paper 2 needs is not merely

```text
(m,t,d) in S_base <=> (-m,-t,d) in S_base,
```

which is plainly false. The needed condition is the stronger finite-packet statement

```text
(m,t,d) in S_e <=> (-m,-t,d) in S_e,
```

after including all companion branches and signs. The counterexamples show that this statement fails exactly on the 9-boundary.

Because the prompt does not give the explicit constants defining `W_e`, I cannot honestly write the complete numerical inequality list for `S_e`. But the conversion rule is exact: every original inequality

```text
A*l + B*u + C*v + D >= 0
```

becomes

```text
A*(m - 1) + B*(t + d + 1)/2 + C*(t - d + 1)/2 + D >= 0,
```

plus the parity condition `t + d == 1 mod 2`. The half-open 9-window inequalities are the ones whose floor/ceiling endpoints jump at `9 | e`.

For implementation/proof auditing, `S_e` should be defined in code only through this pullback, not by retyping hand-simplified inequalities. That avoids losing endpoint conventions.

```python
from dataclasses import dataclass
from typing import Callable, Iterable, Optional, Sequence, Tuple

MTD = Tuple[int, int, int]
LUV = Tuple[int, int, int]
Ineq = Callable[[int, int, int, int], bool]  # example signature: (e,m,t,d) -> bool


def to_mtd(l: int, u: int, v: int) -> MTD:
    """Convert (l,u,v) to (m,t,d)."""
    return (l + 1, u + v - 1, u - v)


def from_mtd(m: int, t: int, d: int) -> Optional[LUV]:
    """Convert (m,t,d) to (l,u,v), returning None off the parity lattice."""
    if (t + d + 1) % 2 != 0:
        return None
    if (t - d + 1) % 2 != 0:
        return None
    l = m - 1
    u = (t + d + 1) // 2
    v = (t - d + 1) // 2
    return (l, u, v)


def tau_mtd(x: MTD) -> MTD:
    """Tau involution in (m,t,d)."""
    m, t, d = x
    return (-m, -t, d)


def base_support_mtd(x: MTD) -> bool:
    """Pullback of l,u,v >= 0. This is not the full Chan support window."""
    luv = from_mtd(*x)
    if luv is None:
        return False
    l, u, v = luv
    return l >= 0 and u >= 0 and v >= 0


def support_mtd(e: int, x: MTD, window_ineqs: Sequence[Ineq]) -> bool:
    """Full support once the Paper 2 half-open window inequalities are supplied."""
    luv = from_mtd(*x)
    if luv is None:
        return False
    if not base_support_mtd(x):
        return False
    m, t, d = x
    return all(pred(e, m, t, d) for pred in window_ineqs)


def tau_defect(e: int, x: MTD, window_ineqs: Sequence[Ineq]) -> bool:
    """True exactly when support is not tau-stable at x."""
    return support_mtd(e, x, window_ineqs) != support_mtd(e, tau_mtd(x), window_ineqs)
```

---

## Q5. Is the `9 = 3 x 3` phenomenon structurally connected to the order-6 stabilizer `eps^6`?

There is probably a structural connection through the prime `3`, but I would not state it as a literal common `Z/3` subgroup without more evidence.

In `Q(sqrt(5))`, the rational prime `3` is inert. Equivalently, the ring of integers modulo `3` has size

```text
Norm((3)) = 9.
```

This makes `9` a natural modulus for residue packets over `Q(sqrt(5))`: it is the size of the additive residue field `O_K/(3)`, not just an accidental decimal integer.

The order-6 or six-step stabilizer in ADH-type unit/cone dynamics has a different origin. The factorization

```text
6 = 2 x 3
```

usually reflects an orientation/sign/Galois reversal factor `2` together with a three-step chamber or residue cycle. Thus the same prime `3` can appear in both:

```text
9 = size of the additive mod-3 residue packet,
6 = signed/oriented return period with a 3-chamber component.
```

But this does not imply a literal common multiplicative `Z/3` subgroup modulo 3. In fact, because `3` is inert in `Q(sqrt(5))`, one has

```text
O_K/(3) ≅ F_9,
(F_9)^* has order 8.
```

The multiplicative group of `F_9` has order `8`, so it has no subgroup of order `3`. Therefore the common source cannot simply be a shared multiplicative `Z/3` subgroup of the residue-field units.

The safer structural statement is:

```text
The common root is the mod-3 / inert-prime structure, not necessarily a literal Z/3 subgroup.
```

The `9 | e` condition is an additive residue-window phenomenon: the support boundary lands on the mod-3 residue lattice only when the norm-9 packet divides the exponent. The `eps^6` stabilizer is a unit/cone return phenomenon: after six signed chamber steps, the ADH packet returns to the same labeled chamber. The factor `3` in both is meaningful, but the two manifestations live in different structures.

---

## Final answer to the five questions

1. **Why `9 | e` breaks tau:** because the support window has half-open endpoints with denominator `9`; tau reflects the window, and the floor/ceiling complement changes by one exactly when `e/9` is integral. This creates unmatched boundary atoms.

2. **Compensation term:** yes as a relative boundary divergence / boundary flux on `partial_tau S_e`; no as a pure divergence on a closed finite fiber if the residual total is nonzero.

3. **Deck transformation:** no natural translation period explains `(4,21,4)`. Identifying it with its tau partner would require a period containing `(8,42,0)`, which is not a plausible quadratic/fiber-preserving deck period. Boundary flux is the better explanation.

4. **Support set:** the exact pullback lattice is `t + d == 1 mod 2`, with `l=m-1`, `u=(t+d+1)/2`, `v=(t-d+1)/2`. The base nonnegative cone is `m >= 1` and `t >= |d|-1`. The full `S_e` is this pulled-back root cone intersected with the e-dependent half-open 9-dissection window. The missing constants of that window are not specified in the prompt, but those are exactly the inequalities whose endpoints jump at `9 | e`.

5. **Connection to `eps^6`:** there is a real mod-3 structural connection, but probably not a literal common `Z/3` subgroup. In `Q(sqrt(5))`, `3` is inert and has norm `9`, explaining the 9-dissection boundary. The six-step unit stabilizer reflects a signed/oriented chamber return with a 3-component. Same prime, different algebraic manifestation.
