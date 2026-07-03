# Q3175 (dm1): Paper 2 Round 7 — Concrete Computation: HM Expansion and Slab Decomposition

Date: 2026-07-03

## Executive answer

R7 should make the paper pivot from descriptive statistics to two computable objects:

```text
1. the HM/Appell-Lerch expansion of the anchor defect
       f_{1,3,4}(X,-X^3,X),

2. the finite tau-boundary slab decomposition of the legal summation domain.
```

The most important correction to the R5 story remains:

```text
The counterexample is not N_0 times a shell theta.
It is a signed tau-boundary cocycle.
```

The repaired term is

```text
Corr_tau = -Theta_u * Theta_v * f_{1,3,4}(X,-X^3,X).
```

The HM calculation says that the last factor is a finite sum of Appell-Lerch pieces plus a finite theta quotient.  Therefore the correction is a mixed mock-Jacobi object, after multiplication by the two ordinary theta factors `Theta_u` and `Theta_v`.

The slab calculation says that the support is not governed by an intrinsic `hblock` onset.  It is governed by the finite list of walls of the legal cone and by how `tau` moves those walls.  The low-degree defect is dominated by the `r=0` missing-kernel wall, not by the artificial `B` truncation walls and not by a base-layer theta product.

---

## Q1. HM expansion of `f_{1,3,4}(X,-X^3,X)`

### Definitions

Use Hickerson--Mortenson's notation:

```text
j(x;q) = (x;q)_∞(q/x;q)_∞(q;q)_∞,

m(x,q,z) = 1/j(z;q) * Σ_{r∈Z} (-1)^r q^{r choose 2} z^r /(1-q^{r-1}xz),

f_{a,b,c}(x,y,q)
  = Σ_{sg(r)=sg(s)} sg(r)(-1)^{r+s}x^r y^s
      q^{a binom(r,2)+brs+c binom(s,2)}.
```

For `a=1,b=3,c=4`, the discriminant parameter is

```text
Delta = b^2 - ac = 9 - 4 = 5 > 0.
```

So this is an indefinite Hecke-type double sum and is in the HM/Appell-Lerch regime.

### Generic HM Appell-Lerch part

Let

```text
G_{1,3,4}(x,y,q) := g_{1,3,4}(x,y,q,-1,-1).
```

Substituting `a=1,b=3,c=4,Delta=5` into the HM `g_{a,b,c}` expression gives the explicit Appell-Lerch part

```text
G_{1,3,4}(x,y,q)
  = j(x;q) m(-q^2 y/x^3, q^5, -1)
    + Σ_{t=0}^{3} (-x)^t q^{binom(t,2)} j(q^{3t}y; q^4)
        m(q^{14-5t} x^4/y^3, q^{20}, -1).
```

Thus the five Appell-Lerch summands are:

```text
j(x;q)                         * m(-q^2 y/x^3,       q^5,  -1),
j(y;q^4)                       * m( q^14 x^4/y^3,    q^20, -1),
(-x) j(q^3y;q^4)               * m( q^9  x^4/y^3,    q^20, -1),
x^2 q j(q^6y;q^4)              * m( q^4  x^4/y^3,    q^20, -1),
(-x^3) q^3 j(q^9y;q^4)         * m( q^-1 x^4/y^3,    q^20, -1).
```

The full HM statement has the shape

```text
f_{1,3,4}(x,y,q) = G_{1,3,4}(x,y,q) + T_{1,3,4}(x,y,q),
```

where

```text
T_{1,3,4}(x,y,q) := f_{1,3,4}(x,y,q) - G_{1,3,4}(x,y,q)
```

is a finite theta quotient.  I am writing it this way deliberately: the special pair `(1,3,4)` is not one of the very simple symmetric families `f_{n,n+p,n}` and is also not in the clean divisibility family with `b` divisible by both `a` and `c`.  The Appell-Lerch part is immediate from HM's general `g_{a,b,c}` formula; the theta quotient is obtained by HM's finite residue-matching algorithm.  It should not be replaced by an unverified canned formula.

### Specialization `x=X`, `y=-X^3`, `q=X` or formal `q`

First keep the nome as `q` and specialize only the Hecke variables:

```text
x = X,
y = -X^3.
```

Then

```text
-y/x^3 = 1,
-x^4/y^3 = X^{-5} with the sign included below,
```

and the Appell-Lerch part becomes

```text
G_{1,3,4}(X,-X^3,q)
  = j(X;q) m(q^2, q^5, -1)
    + j(-X^3;q^4) m(-q^14 X^-5, q^20, -1)
    - X j(-q^3X^3;q^4) m(-q^9 X^-5, q^20, -1)
    + X^2 q j(-q^6X^3;q^4) m(-q^4 X^-5, q^20, -1)
    - X^3 q^3 j(-q^9X^3;q^4) m(-q^-1 X^-5, q^20, -1).
```

If the paper uses the same symbol `X` for the nome and the monomial variable, then set `q=X` at the end:

```text
G_{1,3,4}(X,-X^3,X)
  = j(X;X) m(X^2, X^5, -1)
    + j(-X^3;X^4) m(-X^9,  X^20, -1)
    - X j(-X^6;X^4) m(-X^4,  X^20, -1)
    + X^3 j(-X^9;X^4) m(-X^-1, X^20, -1)
    - X^6 j(-X^12;X^4) m(-X^-6, X^20, -1)
    + T_{1,3,4}(X,-X^3,X).
```

This last display has a warning: `j(X;X)=j(q;q)=0` in the formal HM normalization.  Therefore the first coefficient theta factor vanishes in the literal `q=X` specialization, and the remaining expression must be interpreted by the same limiting/specialization convention used for the original Hecke sum.  In practice the safer paper notation is to keep the nome `q` and the monomial `X` separate until after cancellation of removable zeros/poles.

### Is the specialization generic or torsion?

It is not completely generic.

The relation

```text
y = -x^3
```

forces the first Appell-Lerch parameter to collapse to

```text
m(q^2,q^5,-1),
```

which is a rational-characteristic or torsion Appell-Lerch value: the first argument is `q^2` relative to the base `q^5`, i.e. a `2/5` characteristic.

The other four Appell-Lerch arguments are

```text
-q^{14}X^{-5},
-q^9 X^{-5},
-q^4 X^{-5},
-q^{-1}X^{-5}
```

with base `q^20`.  These are generic in `X`, but they become torsion as soon as `X` is specialized to a rational power of `q`.  Thus the honest statement is:

```text
The specialization y=-X^3 is a torsion/rational-characteristic specialization in at least one Appell-Lerch summand, and becomes fully torsion if X is tied to the nome q.
```

### Final named-object form of the correction

The repaired correction should be written as

```text
Corr_tau
  = -Theta_u Theta_v f_{1,3,4}(X,-X^3,X)
  = -Theta_u Theta_v [G_{1,3,4}(X,-X^3,X) + T_{1,3,4}(X,-X^3,X)].
```

Equivalently:

```text
Corr_tau
  = -Theta_u Theta_v * (finite Appell-Lerch sum)
    -Theta_u Theta_v * (finite theta quotient).
```

So the named modular/mock modular decomposition is:

```text
Theta_u Theta_v * Appell-Lerch terms       = mixed mock-Jacobi part,
Theta_u Theta_v * theta quotient           = modular theta/Jacobi part,
full Corr_tau                              = mixed mock-Jacobi correction.
```

Do not call the whole correction quasi-modular.  The HM expansion naturally gives mock-Jacobi / mixed mock modular structure.  Quasi-modularity only appears after taking Taylor coefficients, derivatives, or special degenerations of Jacobi variables.

---

## Q2. Explicit slab decomposition

### Important structural correction

The domain is not literally one convex intersection of half-spaces because the `r` condition depends on the sign of `k`:

```text
k >= 0  => r <= -1,
k < 0   => r >= 0.
```

Thus the legal domain is a union of two affine polyhedral chambers:

```text
S = S_+ ∪ S_-.
```

This is actually useful.  It makes the boundary finite and explicit.

### Variables

Use

```text
x = (l,u,v,k,r).
```

Let the `l`-window returned by `cone_even_rho_l_window` be written as

```text
L_-(rho) <= l <= L_+(rho),
```

where `rho` is the affine parameter used by the code.  In the paper, this must be replaced by the exact affine formula from `cone_even_rho_l_window`.  Everything below is already in half-space form once those two affine functions are inserted.

### Truncation walls for `(u,v)`

The rectangle `ctf_rect_points(B)` contributes four artificial truncation walls:

```text
ell_u^-  = u + B       >= 0,
ell_u^+  = B - u       >= 0,
ell_v^-  = v + B       >= 0,
ell_v^+  = B - v       >= 0.
```

These walls are not intrinsic.  In a stable coefficient calculation they should eventually stop contributing.

### `l`-window walls

The `l` window contributes two walls:

```text
ell_l^-  = l - L_-(rho)  >= 0,
ell_l^+  = L_+(rho) - l  >= 0.
```

These are intrinsic if the window is part of the true legal cone, and artificial if it is a scan window.  The paper should distinguish those two cases explicitly.

### `k,r` chambers

For `k >= 0`, the missing-kernel rule gives `r <= -1`, so

```text
S_+ = {
  ell_l^- >= 0,
  ell_l^+ >= 0,
  ell_u^- >= 0,
  ell_u^+ >= 0,
  ell_v^- >= 0,
  ell_v^+ >= 0,
  ell_k^+ := k >= 0,
  ell_r^+ := -r - 1 >= 0
}.
```

For `k < 0`, equivalently `k <= -1`, the rule gives `r >= 0`, so

```text
S_- = {
  ell_l^- >= 0,
  ell_l^+ >= 0,
  ell_u^- >= 0,
  ell_u^+ >= 0,
  ell_v^- >= 0,
  ell_v^+ >= 0,
  ell_k^- := -k - 1 >= 0,
  ell_r^- := r >= 0
}.
```

The exponent on this domain is

```text
E(u,v,k,r)
  = 9*(5v^2 - 7v + 5u^2 - 3u + 2k(2k+1) + r(r+6k+1)).
```

The low-degree boundary is therefore controlled by the small values of this quadratic on the chamber walls, especially the two kernel walls

```text
r = -1 in S_+,
r = 0  in S_-.
```

### Displacement fields

Let `tau` be represented on the lattice by an integral affine map

```text
tau(x) = T*x + t.
```

For a wall

```text
ell_i(x) = a_i · x + b_i,
```

the displacement field is

```text
d_i(x) = ell_i(tau x) - ell_i(x)
       = a_i · (T-I)x + a_i · t.
```

If the paired wall has opposite orientation, which is the natural situation for a map satisfying `tau ≡ -I mod 9`, the more invariant quantity is

```text
d_i^paired(x) = ell_i^*(tau x) - ell_i(x),
```

where `ell_i^*` is the tau-paired wall form.  If `ell_i^* = -ell_i` up to an affine constant, this is the quantity expected to be divisible by `9`.

This distinction matters.  From

```text
tau ≡ -I mod 9
```

one gets, for a homogeneous linear wall `ell`,

```text
ell(tau x) ≡ -ell(x) mod 9.
```

Therefore

```text
ell(tau x) - ell(x) ≡ -2ell(x) mod 9,
```

which is not generally divisible by `9`.  The divisible field is normally the paired/opposite-wall field

```text
ell(tau x) + ell(x) ≡ 0 mod 9
```

or, with affine constants included,

```text
ell_i^*(tau x) - ell_i(x) ≡ 0 mod 9.
```

So the paper should not state blindly that every raw `ell_i∘tau - ell_i` is divisible by `9`.  The correct theorem is:

```text
For each oriented wall W_i there is a tau-paired oriented wall W_i^* such that

    ell_i^*(tau x) - ell_i(x) is divisible by 9.
```

That is exactly the mathematical content of “tau is a mod-9 ghost symmetry.”

### Boundary slabs

For a chamber `C` with wall forms `ell_i >= 0`, the tau-boundary decomposes into finite slabs

```text
C \ tau^{-1}C
  = ⋃_i { x∈C : ell_i(tau x) < 0 }.
```

To avoid double-counting overlaps, use the ordered disjoint version

```text
Slab_i(C)
  = { x∈C : ell_i(tau x) < 0 and ell_j(tau x) >= 0 for all j<i }.
```

For the two chambers above there are eight oriented wall forms per chamber.  Thus:

```text
raw oriented chamber slabs:  16,
intrinsic wall types:         8,
artificial B walls:           4 u/v walls, duplicated across chambers,
low-e dominant walls:         r=-1 and r=0 kernel walls.
```

The finite list of intrinsic wall types is:

```text
1. lower l-window wall,
2. upper l-window wall,
3. lower u-wall,
4. upper u-wall,
5. lower v-wall,
6. upper v-wall,
7. k-sign wall,
8. r-kernel wall.
```

For a stable infinite-domain theorem, the `u/v` rectangle walls should disappear after taking `B -> infinity`, leaving the true cone walls and the kernel wall.  In the observed low-degree defect, the dominant slab is the kernel wall:

```text
S_+ side: r = -1,
S_- side: r = 0.
```

This is exactly where `even_missing_kernel_term` says the contribution changes sign/nonzero status.

### Slab theorem to state

```text
Theorem, Tau-boundary slab decomposition.
Let S_B = S_{B,+} ∪ S_{B,-} be the finite legal scan domain above.  Then

    S_B Δ tau(S_B)

is a finite disjoint union of ordered slabs attached to the oriented walls of
S_{B,+} and S_{B,-}.  The signed packet series over this boundary equals

    Theta_u Theta_v (D-A)
      = -Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

The proof is purely polyhedral once the exact `tau` matrix and `cone_even_rho_l_window` affine formulas are inserted.

---

## Q3. Fiber chamber inequality and B-independent onset

The old onset formula was

```text
onset_h(fiber) = 18h(Lh - V),
L = -(l+v),
V = -v.
```

On the hyperplane

```text
u = l + v + 9,
```

this becomes

```text
L = -l-v = 9-u,
V = -v,

onset_h(l,v)
  = 18h((-l-v)h + v)
  = 18h(-h*l - (h-1)*v).
```

This is a linear objective in the fiber variables `(l,v)` for each fixed `h`.

Therefore the B-independent question is a linear-programming question over the realized fiber chamber:

```text
P = { (l,v) : there exist u,k,r satisfying the legal chamber inequalities,
              u = l+v+9 }.
```

For fixed `h`, minimize

```text
Phi_h(l,v) = -h*l - (h-1)*v
```

over `P`.

### Dichotomy

There are only two possibilities:

```text
1. finite minimum:
   Phi_h is nonnegative on the recession cone rec(P), and the minimum is attained at a vertex.
   Then onset_h has a B-independent limiting formula.

2. unbounded below:
   there is a recession direction w∈rec(P) with Phi_h(w)<0.
   Then the apparent onset is genuinely B-dependent and no shell-opening theorem exists.
```

The new B=25 observations strongly suggest that the second case occurs for at least the larger `h` values tested, or that the scan window was previously cutting off the true minimizing vertices.  In either case, the R5 formula

```text
18h(17h-12)
```

is not a theorem-level invariant.

### Practical conclusion

Do not base Paper 2 on `min_fiber onset_h` unless the following chamber theorem is proven:

```text
The fiber chamber P has a recession cone on which every Phi_h is nonnegative,
and its minimizing vertex is the previously observed fiber (-5,-12).
```

The experiments now say this is probably false.

The B-independent replacement is:

```text
The stable counterexample coefficient is the coefficient of the tau-boundary correction,
not the first appearance of an hblock shell in a finite B scan.
```

### Fiber theorem that is safe

The safe theorem is not an onset theorem.  It is the following dichotomy theorem:

```text
Theorem, Fiber LP dichotomy.
For each fixed h, the stable fiber onset problem is the integer linear program

    minimize 18h(-h*l-(h-1)*v)
    over the realized fiber chamber P.

If Phi_h is negative on the recession cone of P, then no B-independent finite
onset exists.  If Phi_h is nonnegative on the recession cone, the stable onset
is attained at a finite list of vertices and can be computed from the chamber
walls.
```

This theorem is publishable because it explains why the old onset formula was fragile and gives the exact replacement computation.

---

## Q4. Antisymmetrized count modularity

The prediction

```text
N_j(e) - N_{-j}(e) is quasi-modular,
N_j(e) + N_{-j}(e) is not,
```

is not sound as stated.

The reason is simple: `N_j(e)` is an unsigned count.  HM modularity applies to signed generating functions, not to raw support counts.  Forgetting signs usually destroys modularity.

### What is sound

Define a signed hblock-refined charge series

```text
C_h(q) = Σ_e charge_h(e) q^e,
```

or with an hblock marker `w`,

```text
C(w,q) = Σ_{h,e} charge_h(e) w^h q^e.
```

Then the tau boundary gives a mock-Jacobi object:

```text
C(w,q) = coefficient/specialization of
         -Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

The antisymmetric part

```text
C^-(w,q) = (C(w,q)-C(w^{-1},q))/2
```

is again mock-Jacobi, or a component of the same mixed mock modular object.

If one takes Taylor coefficients at `w=1`, derivatives of a Jacobi/mock-Jacobi object can produce quasi-Jacobi or quasi-modular corrections.  That is the correct route by which quasi-modularity might appear.

### What is not automatic

The raw count

```text
N_j(e)-N_{-j}(e)
```

has no reason to be modular unless it equals a signed charge after a constant-sign theorem on each slab.  The paper would need to prove something like:

```text
On each dominant boundary slab, all packet signs are constant after fixing hblock.
```

or more generally

```text
N_j(e)-N_{-j}(e) = linear combination of signed charge coefficients.
```

Without such a theorem, the modular object is the signed charge, not the unsigned antisymmetrized count.

### Correct R7 statement

Replace the fable prediction by:

```text
The signed h-antisymmetrized boundary charge is mock-Jacobi/mixed mock modular.
Its Jacobi Taylor coefficients may be quasi-modular or quasi-mock modular.
Unsigned hblock counts need not be modular.
```

This is both mathematically safer and more directly tied to the repair term.

---

## B-independent characterization of the counterexample structure

The B-independent object is the stable tau-boundary coefficient:

```text
Defect(q,z)
  = (1/2) Σ_{x∈Λ} (χ_S(x)-χ_S(tau^{-1}x)) wt(x).
```

Equivalently,

```text
Defect(q,z)
  = -Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

For every fixed coefficient `(e,K)`, finite scans are valid only after stabilization:

```text
keyWeight_B(e,K) = keyWeight(e,K) for all B >= B_0(e,K).
```

Thus the right verification target is:

```text
stabilized finite scan coefficient
  = coefficient of the tau-boundary correction.
```

The wrong target is:

```text
finite-B hblock onset
  = formula 18h(17h-12).
```

The onset formula can still be reported as an artifact of a particular scan chamber, but it should not be a main theorem.

---

## Minimal theorem package for Paper 2 after R7

### Theorem 1 — Ghost symmetry

```text
For the coset L, the Pell matrix M has trace 18 and determinant 1.  The map

    tau = M^2

satisfies

    tau ≡ -I mod 9,
    tau != -I over Z.
```

This is the source of the false cancellation.

### Theorem 2 — Odd anchor / free action

```text
Every realized anchor is A=2n-1 and hence odd.  The only possible fixed anchor
for tau is even, so tau acts freely on realized keys.
```

Thus the defect is a boundary defect, not a fixed-point defect.

### Theorem 3 — Interior cancellation

```text
On any tau-invariant finite subdomain, the signed packet weights cancel in tau-pairs.
```

### Theorem 4 — Boundary divergence

```text
For the legal domain S,

    Σ_{x∈S} wt(x)
      = (1/2) Σ_{x∈Λ} (χ_S(x)-χ_S(tau^{-1}x)) wt(x).
```

Coefficientwise:

```text
keyWeight(e,K)
  = [q^e z^K] boundary_tau(S;wt).
```

### Theorem 5 — Slab decomposition

```text
S = S_+ ∪ S_-
```

with the two chambers listed above, and

```text
S Δ tau(S)
```

is a finite union of oriented wall slabs.  The low-degree stable slabs are the missing-kernel walls `r=-1` and `r=0`.

### Theorem 6 — Boundary evaluation

```text
boundary_tau(S;wt)
  = Theta_u Theta_v (D-A)
  = -Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

### Theorem 7 — HM/mock modular description

```text
f_{1,3,4}(X,-X^3,X)
  = finite Appell-Lerch sum + finite theta quotient.
```

Therefore

```text
Corr_tau = -Theta_u Theta_v f_{1,3,4}(X,-X^3,X)
```

is a mixed mock-Jacobi correction.

### Theorem 8 — Corrected identity

```text
Theta_10 = Main_tau - Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

This is the repair.

---

## Code skeleton: HM terms and slab bookkeeping

This code is intentionally repository-neutral.  It does not attempt to guess the hidden formulas inside `cone_even_rho_l_window` or the concrete `tau` matrix.  Insert those two pieces from the repository and the displacement/slab table becomes literal.

```python
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Dict, Iterable, List, Mapping, MutableMapping, Sequence, Tuple

Vector = Tuple[int, ...]
Matrix = Tuple[Tuple[int, ...], ...]


@dataclass(frozen=True)
class HMTerm:
    """A symbolic Appell-Lerch summand coeff * m(arg, base, z)."""

    coeff: str
    arg: str
    base: str
    z: str = "-1"


def hm_terms_f_1_3_4_generic() -> List[HMTerm]:
    """Return the five Appell-Lerch terms in G_{1,3,4}(x,y,q)."""
    return [
        HMTerm("j(x;q)", "-q^2*y/x^3", "q^5"),
        HMTerm("j(y;q^4)", "q^14*x^4/y^3", "q^20"),
        HMTerm("(-x)*j(q^3*y;q^4)", "q^9*x^4/y^3", "q^20"),
        HMTerm("x^2*q*j(q^6*y;q^4)", "q^4*x^4/y^3", "q^20"),
        HMTerm("(-x^3)*q^3*j(q^9*y;q^4)", "q^-1*x^4/y^3", "q^20"),
    ]


def hm_terms_f_1_3_4_specialized() -> List[HMTerm]:
    """Return the Appell-Lerch terms after x=X, y=-X^3."""
    return [
        HMTerm("j(X;q)", "q^2", "q^5"),
        HMTerm("j(-X^3;q^4)", "-q^14*X^-5", "q^20"),
        HMTerm("-X*j(-q^3*X^3;q^4)", "-q^9*X^-5", "q^20"),
        HMTerm("X^2*q*j(-q^6*X^3;q^4)", "-q^4*X^-5", "q^20"),
        HMTerm("-X^3*q^3*j(-q^9*X^3;q^4)", "-q^-1*X^-5", "q^20"),
    ]


@dataclass(frozen=True)
class AffineForm:
    """Integral affine form ell(x)=coeffs dot x + const."""

    name: str
    coeffs: Tuple[int, ...]
    const: int = 0

    def eval(self, x: Vector) -> int:
        return sum(a * xi for a, xi in zip(self.coeffs, x)) + self.const

    def displacement(self, tau_matrix: Matrix, tau_shift: Vector | None = None) -> "AffineForm":
        """Return ell(tau x)-ell(x) as an affine form."""
        if tau_shift is None:
            tau_shift = tuple(0 for _ in self.coeffs)
        dim = len(self.coeffs)
        new_coeffs = []
        for j in range(dim):
            pulled = sum(self.coeffs[i] * tau_matrix[i][j] for i in range(dim))
            new_coeffs.append(pulled - self.coeffs[j])
        new_const = self.const + sum(self.coeffs[i] * tau_shift[i] for i in range(dim)) - self.const
        return AffineForm(f"d_{self.name}", tuple(new_coeffs), new_const)

    def paired_displacement(
        self,
        paired: "AffineForm",
        tau_matrix: Matrix,
        tau_shift: Vector | None = None,
    ) -> "AffineForm":
        """Return paired(tau x)-self(x), the mod-9 ghost displacement."""
        if tau_shift is None:
            tau_shift = tuple(0 for _ in self.coeffs)
        dim = len(self.coeffs)
        new_coeffs = []
        for j in range(dim):
            pulled = sum(paired.coeffs[i] * tau_matrix[i][j] for i in range(dim))
            new_coeffs.append(pulled - self.coeffs[j])
        new_const = paired.const + sum(paired.coeffs[i] * tau_shift[i] for i in range(dim)) - self.const
        return AffineForm(f"d_{self.name}_to_{paired.name}", tuple(new_coeffs), new_const)

    def is_divisible_by(self, modulus: int) -> bool:
        return all(c % modulus == 0 for c in self.coeffs) and self.const % modulus == 0


def chamber_walls(B: int, l_lower: AffineForm, l_upper: AffineForm, chamber: str) -> List[AffineForm]:
    """Return wall forms for S_+ or S_- in variables (l,u,v,k,r)."""
    walls = [
        l_lower,
        l_upper,
        AffineForm("u_lower", (0, 1, 0, 0, 0), B),
        AffineForm("u_upper", (0, -1, 0, 0, 0), B),
        AffineForm("v_lower", (0, 0, 1, 0, 0), B),
        AffineForm("v_upper", (0, 0, -1, 0, 0), B),
    ]
    if chamber == "+":
        walls.extend([
            AffineForm("k_nonnegative", (0, 0, 0, 1, 0), 0),
            AffineForm("r_le_minus_1", (0, 0, 0, 0, -1), -1),
        ])
    elif chamber == "-":
        walls.extend([
            AffineForm("k_le_minus_1", (0, 0, 0, -1, 0), -1),
            AffineForm("r_nonnegative", (0, 0, 0, 0, 1), 0),
        ])
    else:
        raise ValueError("chamber must be '+' or '-'")
    return walls


def even_k_exp(u: int, v: int, k: int, r: int) -> int:
    """Exponent from ch10_even_residual_probe.py, as given in the prompt."""
    return 9 * (
        5 * v * v - 7 * v
        + 5 * u * u - 3 * u
        + 2 * k * (2 * k + 1)
        + r * (r + 6 * k + 1)
    )


def fiber_objective(h: int, l: int, v: int) -> int:
    """onset_h/18 on the hyperplane u=l+v+9."""
    return h * (-h * l - (h - 1) * v)
```

---

## Final synthesis

The two computations point to the same final architecture:

```text
1. Polyhedral side:
   counterexamples are the oriented slabs of S Δ tau(S), dominated at low e by
   the missing-kernel r-wall.

2. Analytic side:
   the slab series is -Theta_u Theta_v f_{1,3,4}(X,-X^3,X), and HM expands the
   f_{1,3,4} factor into Appell-Lerch sums plus a theta quotient.

3. Repair:
   Theta_10 = Main_tau - Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

This is enough for a publishable Paper 2.  It does not need a true shell product, and it should no longer depend on finite-B onset statistics.
