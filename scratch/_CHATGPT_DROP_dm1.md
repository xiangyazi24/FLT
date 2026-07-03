# Q3181 (dm1): Paper 2 Round 9 — Shadow Computation and Proof Sketches

Date: 2026-07-03

## Executive answer

R9 is the point where the paper can become short and rigorous.

The central elementary mechanism is now complete:

```text
sigma_k(r) = -(6k+1)-r
```

preserves the inner quadratic, flips the sign `(-1)^r`, has no integral fixed point, and cancels the sigma-stable interior.  The missing kernel is exactly the two-slab remainder

```text
Slab+ = { k >= 0,  r <= -(6k+1) },
Slab- = { k <= -1, r >= -6k }.
```

The analytic classification should now skip the full Hickerson--Mortenson expansion in the main body.  Use Zwegers directly on the two-slab indefinite theta.  HM can be reserved for an appendix or follow-up paper.

The most important correction in R9 is this:

```text
W(q) = 1/2 * sum_{r in Z} (-1)^r q^{9r(r+1)} = 0.
```

It is not a nonzero unary theta correction.  The bilateral row cancels by the involution `r -> -r-1`.  Thus, with the sign-difference convention stated in the prompt, there is no actual extra modular wall term.  The k=0 issue is a normalization artifact of `sgn(0)=0`, and the bilateral correction cancels identically.

The mockness is therefore entirely the Zwegers mockness of the sign-difference indefinite theta attached to the two negative vectors

```text
c1 = (-1, 3),      Q(c1) = -5,
c2 = (-3, 14),     Q(c2) = -20.
```

A clean nonzero-shadow check is the first coefficient in the `c1` unary theta, at exponent `q^(9/4)` in the natural normalization; it is nonzero and cannot be cancelled by the `c2` contribution, whose first fractional exponent is different.

---

## Q1. The k=0 wall correction

### Q1a. Identification of `W(q)`

The proposed correction is

```text
W(q) = 1/2 * sum_{r in Z} (-1)^r q^{9r(r+1)}.
```

This bilateral series is identically zero.

Indeed, pair `r` with

```text
r' = -r - 1.
```

Then

```text
r'(r'+1) = (-r-1)(-r) = r(r+1),
```

but

```text
(-1)^{r'} = (-1)^{-r-1} = -(-1)^r.
```

So every pair cancels, and there is no fixed point because `r=-1/2` is not integral.  Therefore

```text
sum_{r in Z} (-1)^r q^{9r(r+1)} = 0,
W(q)=0.
```

This is the exact identification.  It can also be viewed as the vanishing of an odd theta characteristic.  If one writes

```text
r(r+1) = (r+1/2)^2 - 1/4,
```

then

```text
sum_{r in Z} (-1)^r q^{9r(r+1)}
  = q^(-9/4) sum_{r in Z} (-1)^r q^{9(r+1/2)^2},
```

and the theta function is odd under `r+1/2 -> -(r+1/2)`.

Important: the half-row series

```text
sum_{r <= -1} (-1)^r q^{9r(r+1)}
```

is not the correction.  It is a partial theta.  The actual difference between the slab indicator and the `sgn`-difference indicator includes both half-rows and cancels bilaterally.

### Q1b. Does the wall correction matter for modularity?

With the convention in the prompt,

```text
F_slab = F_Zwegers + W = F_Zwegers.
```

So yes, the wall issue is irrelevant to the modularity classification, but for a stronger reason than expected: the correction is zero.

If a different convention is used, for example if one keeps only the `r <= -1` half-row, then that object is a partial theta and should not be inserted as a modular correction.  The paper should use the bilateral sign-difference normalization because it is the one compatible with Zwegers.

### Q1c. Which boundary causes the correction?

The only possible `sgn(0)` ambiguity is the wall

```text
k = 0.
```

The second sign is

```text
sgn(6k+r+1/2).
```

Its zero would occur at

```text
r = -6k - 1/2,
```

which is never an integer.  Thus there is no lattice correction on that boundary.

For `k=0`, the sign-difference indicator is

```text
( sgn(0) - sgn(r+1/2) ) / 2.
```

It gives `+1/2` for `r <= -1` and `-1/2` for `r >= 0`, while the actual slab gives `1` for `r <= -1` and `0` for `r >= 0`.  The difference is `+1/2` on both half-rows, hence exactly `W(q)`, and `W(q)=0`.

So the final statement should be:

```text
There is a formal k=0 normalization discrepancy, but its bilateral theta series vanishes identically.  No nonzero wall correction remains.
```

---

## Q2. Shadow computation

### Q2a. Covariant shadow formula

Let the homogeneous inner form be

```text
Q0(k,r) = 4k^2 + 6kr + r^2.
```

Its symmetric bilinear form is

```text
B((k,r),(k',r'))
  = Q0((k,r)+(k',r')) - Q0(k,r) - Q0(k',r')
  = 8kk' + 6kr' + 6rk' + 2rr'.
```

The two negative vectors are

```text
c1 = (-1, 3),      Q0(c1) = -5,
c2 = (-3, 14),     Q0(c2) = -20.
```

They encode the two signs because

```text
B(c1,(k,r)) = 10k,
B(c2,(k,r)) = 10(6k+r).
```

The second wall in the slab is the shifted wall

```text
6k+r+1/2 = 0,
```

so it is harmless to write it as an affine version of the `c2` wall.

A standard Zwegers completion of the sign-difference series replaces

```text
sgn(B(c_i,x))
```

by an error function

```text
E_i(x;y) = E( sqrt(18y) * B(c_i,x) / sqrt(-Q0(c_i)) ),
```

with the obvious affine shift for `c2`.  Here `q=e^{2*pi*i*tau}` and `y=Im(tau)`.  The factor `18y` reflects the scale `9Q0` in the exponent; changing the normalization of `Q` changes this constant but not the unary theta factors.

In this normalization the antiholomorphic derivative is a sum of two unary theta kernels:

```text
-∂Fhat/∂bar(tau)
  = C * ( S_{c1}(tau) - S_{c2}(tau) ),
```

where `C` is an explicit nonzero normalization constant depending only on the chosen `E`-function convention, and

```text
S_c(tau)
  = sum_{x in lattice/coset} chi(x)
      B(c,x) / sqrt(-Q0(c))
      exp( -18*pi*y * B(c,x)^2 / (-Q0(c)) )
      q^{9Q_inner(x)}.
```

This is the direct shadow formula before Poisson summation.  After Poisson summation along the negative direction, each `S_c` becomes a holomorphic unary theta series on the positive line `c^perp`.

### Q2b. Explicit unary theta form

For the first wall,

```text
c1^perp = Z*(0,1),
```

because `B(c1,(0,1))=0`.  The wall coordinate is `r`, and on `k=0`

```text
Q_inner(0,r) = r(r+1) = (r+1/2)^2 - 1/4.
```

The corresponding nonzero unary shadow component is the odd-characteristic theta derivative

```text
Theta_1^sh(tau)
  = sum_{r in Z} (-1)^r (2r+1) q^{9(r+1/2)^2}.
```

Equivalently, in Jacobi notation,

```text
Theta_1^sh(tau)
  = (1/(pi*i)) * ∂/∂z theta_1(z | 18tau) evaluated at z=1/2,
```

up to the conventional power of `q` and the conventional theta normalization.  It is not the vanishing theta

```text
sum (-1)^r q^{9(r+1/2)^2};
```

the derivative factor `(2r+1)` is what makes the shadow nonzero.

For the second wall, the positive line is generated by

```text
p2 = (1,-6),       Q0(p2)=4,
```

since `B(c2,p2)=0`.  The affine wall is

```text
6k+r+1/2=0,
```

so the resulting unary theta is a characteristic theta on the coset of the `p2`-line shifted by the half-wall.  A convenient normalized form is

```text
Theta_2^sh(tau)
  = sum_{n in Z} alpha(n) q^{36(n+alpha0)^2},
```

where the characteristic `alpha0` is determined by the affine shift `6k+r+1/2=0` and the linear term in `Q_inner`.  In the natural continuous boundary parametrization `r=-6k-1/2`, one obtains

```text
Q_inner(k,-6k-1/2) = 4k^2 - k - 1/4
                   = 4(k-1/8)^2 - 5/16.
```

Thus a usable paper notation is

```text
Theta_2^sh(tau)
  = sum_{k in Z} beta(k) q^{36(k-1/8)^2},
```

again up to the same global `q`-power and normalization convention.  The multiplier `beta(k)` records the parity character inherited from `(-1)^r` after the affine half-wall is converted to a characteristic.  Rather than forcing this into a simple `theta_2` or `theta_3`, it is cleaner to denote it by a unary theta with rational characteristic:

```text
vartheta_{36, -1/8}^{chi}(tau).
```

The final shadow should therefore be stated as

```text
Shadow(F_slab)
  = C1 * sum_{r in Z} (-1)^r (2r+1) q^{9(r+1/2)^2}
    - C2 * vartheta_{36,-1/8}^{chi}(tau),
```

where `C1,C2` are the explicit Zwegers normalization constants.  For the proof of mockness, the constants are irrelevant except that they are nonzero.

Recommended paper definition:

```text
vartheta_{m,a,chi}^{(1)}(tau)
  := sum_{n in Z+a} chi(n) n q^{m n^2}.
```

Then write

```text
Shadow(F_slab)
  = C1 * vartheta_{9,1/2,(-1)^n}^{(1)}(tau)
    - C2 * vartheta_{36,-1/8,chi_2}^{(1)}(tau).
```

This is explicit, avoids overclaiming an eta product, and is exactly the unary-theta shadow supplied by Zwegers.

### Q2c. Simplest coefficient proving the shadow is nonzero

Use the first `c1` coefficient.

In

```text
Theta_1^sh(tau)
  = sum_{r in Z} (-1)^r (2r+1) q^{9(r+1/2)^2},
```

the terms `r=0` and `r=-1` both contribute positively at exponent

```text
9*(1/2)^2 = 9/4.
```

Indeed,

```text
r=0:   (-1)^0*(1)  = 1,
r=-1:  (-1)^(-1)*(-1) = 1.
```

So the coefficient of `q^(9/4)` in the `c1` shadow component is `2*C1`, nonzero.

The `c2` component has a different first fractional exponent under the half-wall normalization, so it cannot cancel this `q^(9/4)` term.  Therefore the shadow is nonzero.  This proves genuine mockness.

---

## Q3. Proof sketch for Theorem 1: sigma involution

### Theorem 1. Sigma row cancellation

For each integer `k`, define

```text
sigma_k(r) = -(6k+1)-r.
```

Let

```text
Q_inner(k,r) = 2k(2k+1) + r(r+6k+1).
```

Then `sigma_k` is a fixed-point-free involution of the `r`-row, preserves `Q_inner`, reverses the sign `(-1)^r`, and hence cancels every sigma-stable row interval in signed pairs.

### Proof sketch

Fix `k` and write

```text
C = 6k+1.
```

Then

```text
sigma_k(r) = -C-r.
```

First, `sigma_k` is an involution because

```text
sigma_k(sigma_k(r)) = -C - (-C-r) = r.
```

Second, it preserves the exponent.  Since

```text
sigma_k(r)+C = -r,
```

we have

```text
sigma_k(r)(sigma_k(r)+C)
  = (-C-r)(-r)
  = r(r+C).
```

The remaining term `2k(2k+1)` is independent of `r`, so

```text
Q_inner(k,sigma_k(r)) = Q_inner(k,r).
```

Third, it flips the sign.  Since

```text
sigma_k(r)-r = -(6k+1)-2r
```

is odd, we get

```text
(-1)^{sigma_k(r)} = -(-1)^r.
```

Fourth, it has no integral fixed point.  A fixed point would satisfy

```text
r = -C-r,
2r = -C = -(6k+1),
```

which is impossible because `6k+1` is odd.

Equivalently, define the anchor

```text
A = 2r+6k+1.
```

Then `A` is always odd, and

```text
A(sigma_k(r)) = -A(r).
```

A fixed point would require `A=0`, impossible for odd `A`.

Finally, let `I_k` be any finite row interval with

```text
r in I_k  iff  sigma_k(r) in I_k.
```

The signed row sum over `I_k` is

```text
sum_{r in I_k} (-1)^r q^{9Q_inner(k,r)}.
```

Pair each `r` with `sigma_k(r)`.  The exponents are equal and the signs are opposite.  Since there are no fixed points, every pair cancels, so the total is zero.

This proves the interior cancellation theorem.

---

## Q4. Proof sketch for Theorem 2: slab decomposition and factorization

### Theorem 2. Two-slab decomposition and missing-kernel factorization

Define

```text
Slab+ = { (k,r) in Z^2 : k >= 0,  r <= -(6k+1) },
Slab- = { (k,r) in Z^2 : k <= -1, r >= -6k }.
```

Then the signed residual kernel after sigma cancellation is supported exactly on

```text
Slab+ union Slab-.
```

Moreover, since the exponent and sign split into an `(u,v)` part and a `(k,r)` part, the missing kernel factors as

```text
MissingKernel(q) = Theta_u(q) * Theta_v(q) * F_slab(q),
```

where

```text
F_slab(q)
  = sum_{k>=0, r<=-(6k+1)} (-1)^r q^{9Q_inner(k,r)}
    - sum_{k<=-1, r>=-6k} (-1)^r q^{9Q_inner(k,r)}.
```

The minus sign in the second sum is the orientation sign coming from the sign-difference indicator

```text
( sgn(k) - sgn(6k+r+1/2) ) / 2.
```

If the code incorporates this orientation into the atom coefficient, write both slab sums with the code coefficient `c(k,r)` instead.

### Proof sketch

For `k>=0`, the legal half-row in the missing-kernel probe is

```text
r <= -1.
```

A legal point remains legal after sigma precisely when

```text
sigma_k(r) <= -1.
```

Using `sigma_k(r)=-(6k+1)-r`, this is

```text
-(6k+1)-r <= -1
<=> r >= -6k.
```

Thus the sigma-stable interior for `k>=0` is

```text
-6k <= r <= -1,
```

and the unpaired remainder is

```text
r <= -6k-1 = -(6k+1).
```

This is `Slab+`.

For `k<=-1`, the legal half-row is

```text
r >= 0.
```

It remains legal after sigma precisely when

```text
sigma_k(r) >= 0
<=> -(6k+1)-r >= 0
<=> r <= -6k-1.
```

Thus the sigma-stable interior for `k<=-1` is

```text
0 <= r <= -6k-1,
```

and the unpaired remainder is

```text
r >= -6k.
```

This is `Slab-`.

By Theorem 1, the sigma-stable interiors cancel in signed pairs.  Hence only the two slabs survive.

Now use the separated exponent

```text
E(u,v,k,r)
  = 9*( Q_outer(u,v) + Q_inner(k,r) ),

Q_outer(u,v) = 5v^2 - 7v + 5u^2 - 3u,
Q_inner(k,r) = 2k(2k+1) + r(r+6k+1).
```

The sign also separates:

```text
(-1)^{u+v+r} = (-1)^{u+v} * (-1)^r.
```

Therefore the `(u,v)` sums factor from the slab sum:

```text
Theta_u(q) = sum_u (-1)^u q^{9(5u^2-3u)},
Theta_v(q) = sum_v (-1)^v q^{9(5v^2-7v)},
```

with the exact ranges determined by the legal outer summation.  The remaining inner factor is precisely `F_slab(q)`.  This proves

```text
MissingKernel(q) = Theta_u(q) Theta_v(q) F_slab(q).
```

Finally, the R6/R7 identification gives

```text
F_slab(q) = D-A = -f_{1,3,4}(X,-X^3,X)
```

under the paper's variable convention, so the repaired identity is

```text
Theta_10 = Main_tau + Theta_u Theta_v F_slab
         = Main_tau - Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

---

## Q5. Proof sketch for Theorem 3: Pell structure

### Theorem 3. Discriminant-20 Pell structure and mock regime

The homogeneous inner form

```text
Q0(k,r) = 4k^2 + 6kr + r^2
```

has discriminant `20` and is a conductor-2 norm form in `Q(sqrt(5))`.  Its automorph is generated by the matrix

```text
M = [ [-3, -4],
      [ 16, 21] ],
```

which has trace `18`, determinant `1`, and eigenvalues

```text
9 ± 4sqrt(5) = epsilon^±6,
```

where

```text
epsilon = (1+sqrt(5))/2.
```

Since `M ≡ I mod 2`, the parity character `(-1)^r` is invariant under the Pell automorph.  The sign character is therefore even with respect to the Pell dynamics, putting the slab theta in the Zwegers/Rogers mock regime rather than in the honest weight-1 theta regime.

### Proof sketch

Introduce Pell coordinates

```text
x = r + 3k,
y = k.
```

Then

```text
x^2 - 5y^2
  = (r+3k)^2 - 5k^2
  = r^2 + 6kr + 4k^2
  = Q0(k,r).
```

The full inner exponent is a shifted norm:

```text
Q_inner(k,r)
  = Q0(k,r) + 2k + r
  = x^2 - 5y^2 + x - y.
```

The anchor is

```text
A = 2r+6k+1 = 2x+1.
```

The matrix

```text
M = [ [-3, -4],
      [ 16, 21] ]
```

preserves `Q0`.  Direct multiplication gives

```text
M^T * [ [4,3], [3,1] ] * M = [ [4,3], [3,1] ],
```

where `[ [4,3], [3,1] ]` is the Gram matrix for `Q0(k,r)`.

The matrix has

```text
det(M)=1,
tr(M)=18,
```

so its eigenvalues are

```text
(18 ± sqrt(18^2-4))/2 = 9 ± 4sqrt(5).
```

In Pell coordinates `(x,y)`, the conjugate matrix is

```text
M_Pell = [ [ 9, -20],
           [ -4,  9] ],
```

which is the standard multiplication matrix for the unit

```text
9 - 4sqrt(5)
```

or its inverse, depending on the chosen orientation.  Thus the automorph group is generated by

```text
epsilon_20 = 9 + 4sqrt(5) = ((1+sqrt(5))/2)^6 = (2+sqrt(5))^2.
```

Finally,

```text
M ≡ I mod 2.
```

Therefore `r mod 2` is preserved by the Pell automorph, and the character `(-1)^r` is Pell-even.  In the indefinite theta classification, the honest modular theta case comes from compatible odd cancellation under the automorph.  Here the parity does not remove the two-cusp sign defect; the sign-difference completion has nonzero unary shadow.  Hence the resulting slab series is a mixed mock-Jacobi object, not an honest weight-1 modular form.

---

## Q6. Overall paper strategy

### Q6a. Introduction level for a combinatorics / number theory audience

The introduction should be concrete and short.  Avoid starting with HM, Zwegers, or long computational tables.  Start with the failed identity and the repair.

A good introduction outline:

```text
Paragraph 1. The object.
Define Theta_10 at a high level as the theta/kernel series whose published or
expected decomposition misses a residual term.  State that the paper identifies
and repairs the missing term.

Paragraph 2. The false cancellation.
Explain that the original argument implicitly pairs summands by a symmetry.  The
symmetry is real modulo 9 but not integral on the summation domain.  Hence the
interior cancels but a boundary remains.

Paragraph 3. The elementary mechanism.
State sigma_k(r)=-(6k+1)-r.  It preserves the exponent, flips the sign, has no
fixed point, and leaves exactly two slabs.  This is the heart of the paper.

Paragraph 4. The repair.
Display the corrected identity:

    Theta_10 = Main_tau + Theta_u Theta_v F_slab
             = Main_tau - Theta_u Theta_v f_{1,3,4}(X,-X^3,X).

Paragraph 5. Analytic classification.
State that F_slab is an indefinite theta series of discriminant 20.  Its
Zwegers completion has nonzero unary shadow, so it is mock/mixed mock-Jacobi,
not an honest modular theta series.

Paragraph 6. Computation.
Briefly mention that the earlier shell/onset statistics motivated the search
but are not the theorem.  The numerical tables verify the boundary formula and
show the failure of multiplicativity.
```

For JCTA or a DNA-style conference audience, the introduction should emphasize:

```text
1. exact cancellation mechanism,
2. explicit repair term,
3. small two-slab formula,
4. nonzero shadow / mock classification,
5. reproducible verification.
```

It should not foreground the failed shell product except as motivation.  The factorization failure is useful context, but the paper's contribution is the mechanism and the repair.

### Q6b. Should the full HM expansion be included?

Recommendation: do not include the full HM expansion in the main paper.

Use Zwegers directly because:

```text
1. the slab is already an indefinite theta with two sign walls;
2. the negative vectors c1,c2 are explicit;
3. the nonzero shadow is easy to exhibit;
4. the HM specialization has torsion and removable 0*infinity issues;
5. including HM would distract from the elementary repair.
```

A compact appendix can say:

```text
By Hickerson--Mortenson, the same F_slab can be expanded as finitely many
Appell--Lerch sums plus a theta quotient.  We do not need this expansion for the
repair theorem; it gives an alternative analytic description.
```

Save the full HM torsion resolution for a follow-up paper unless a referee asks for it.

---

## Suggested main theorem package

### Theorem A. Sigma cancellation

```text
sigma_k(r)=-(6k+1)-r
```

is a fixed-point-free sign-reversing exponent-preserving involution on each row.

### Theorem B. Two-slab decomposition

After sigma cancellation, the residual kernel is supported exactly on

```text
Slab+ union Slab-.
```

### Theorem C. Missing-kernel factorization

```text
MissingKernel = Theta_u Theta_v F_slab,
```

where

```text
F_slab(q)
  = sum_{k>=0, r<=-(6k+1)} (-1)^r q^{9Q_inner(k,r)}
    - sum_{k<=-1, r>=-6k} (-1)^r q^{9Q_inner(k,r)}.
```

### Theorem D. Corrected identity

```text
Theta_10 = Main_tau + Theta_u Theta_v F_slab
         = Main_tau - Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

### Theorem E. Pell/mock classification

The homogeneous slab form has discriminant `20`, automorph generated by the unit

```text
9+4sqrt(5)=epsilon^6,
```

and Zwegers completion with negative vectors

```text
c1=(-1,3), c2=(-3,14).
```

The unary shadow is nonzero, so `F_slab` is genuinely mock/mixed mock-Jacobi and not an honest weight-1 modular theta series.

---

## Numerical evidence to include

Keep the tables short.  Suggested tables:

```text
Table 1. Sigma verification:
Q_inner(k,r)=Q_inner(k,sigma r), sign flip, no fixed point.

Table 2. Interior cancellation:
F_halfB - F_slab has zero mismatches through e=500.

Table 3. First coefficients of F_slab:
e/9 = 0: -1,
      2:  1,
      6: -2,
      8: -1,
     12:  1,
     14:  1,
     16:  1,
     20: -2,
     24: -2,
     26: -1,
     30:  1,
     34:  1,
     36:  1,
     38:  2,
     42: -2,
     48: -1,
     50: -2,
     52: -1,
     54: -1.

Table 4. Nonmultiplicativity diagnostics:
inner sum not multiplicative, e.g. 268/482 failures and chi(17)=9.
```

The nonmultiplicativity table should be used only to refute honest modular theta interpretations, not as a primary theorem.

---

## Verification code skeleton

```python
from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, Iterable, List, Tuple


def sigma(k: int, r: int) -> int:
    return -(6 * k + 1) - r


def q_inner(k: int, r: int) -> int:
    return 2 * k * (2 * k + 1) + r * (r + 6 * k + 1)


def anchor(k: int, r: int) -> int:
    return 2 * r + 6 * k + 1


def in_slab_plus(k: int, r: int) -> bool:
    return k >= 0 and r <= -(6 * k + 1)


def in_slab_minus(k: int, r: int) -> bool:
    return k <= -1 and r >= -6 * k


def slab_orientation(k: int, r: int) -> int:
    if in_slab_plus(k, r):
        return 1
    if in_slab_minus(k, r):
        return -1
    return 0


def wall_correction_term(max_abs_r: int) -> Dict[int, int]:
    terms: Dict[int, int] = {}
    for r in range(-max_abs_r, max_abs_r + 1):
        e = 9 * r * (r + 1)
        coeff = (-1) ** r
        terms[e] = terms.get(e, 0) + coeff
    return {e: c for e, c in terms.items() if c}


def assert_wall_correction_cancels(max_abs_r: int) -> None:
    # Symmetric truncations around the involution r -> -r-1 should cancel
    # once the truncation is chosen in complete pairs.
    for r in range(-max_abs_r, max_abs_r + 1):
        rp = -r - 1
        assert r * (r + 1) == rp * (rp + 1)
        assert ((-1) ** r) == -((-1) ** rp)


def assert_sigma_identities(k_values: Iterable[int], r_values: Iterable[int]) -> None:
    for k in k_values:
        for r in r_values:
            rp = sigma(k, r)
            assert sigma(k, rp) == r
            assert q_inner(k, rp) == q_inner(k, r)
            assert ((rp - r) % 2) == 1
            assert anchor(k, rp) == -anchor(k, r)
            assert anchor(k, r) % 2 == 1


def f_slab_coeffs(k_bound: int, r_bound: int) -> Dict[int, int]:
    coeffs: Dict[int, int] = {}
    for k in range(-k_bound, k_bound + 1):
        for r in range(-r_bound, r_bound + 1):
            orient = slab_orientation(k, r)
            if orient == 0:
                continue
            e = 9 * q_inner(k, r)
            coeff = orient * ((-1) ** r)
            coeffs[e] = coeffs.get(e, 0) + coeff
    return {e: c for e, c in coeffs.items() if c}


@dataclass(frozen=True)
class ShadowVector:
    name: str
    k: int
    r: int
    q_value: int


SHADOW_VECTORS: Tuple[ShadowVector, ...] = (
    ShadowVector('c1', -1, 3, -5),
    ShadowVector('c2', -3, 14, -20),
)


def q0(k: int, r: int) -> int:
    return 4 * k * k + 6 * k * r + r * r


def bilinear(a: Tuple[int, int], b: Tuple[int, int]) -> int:
    k, r = a
    kp, rp = b
    return 8 * k * kp + 6 * k * rp + 6 * r * kp + 2 * r * rp


def assert_shadow_vectors() -> None:
    c1 = (-1, 3)
    c2 = (-3, 14)
    assert q0(*c1) == -5
    assert q0(*c2) == -20
    # B(c1,(k,r)) = 10k and B(c2,(k,r)) = 10(6k+r).
    for k in range(-5, 6):
        for r in range(-5, 6):
            assert bilinear(c1, (k, r)) == 10 * k
            assert bilinear(c2, (k, r)) == 10 * (6 * k + r)
```

---

## Final synthesis

The paper should now be organized around one elementary theorem and one analytic theorem.

Elementary theorem:

```text
The missing kernel is the two-slab residue of a sign-reversing row involution.
```

Analytic theorem:

```text
The slab residue is a Zwegers indefinite theta with nonzero unary shadow.
```

The corrected identity is

```text
Theta_10 = Main_tau + Theta_u Theta_v F_slab
         = Main_tau - Theta_u Theta_v f_{1,3,4}(X,-X^3,X).
```

The k=0 wall does not add a nonzero modular correction; the proposed bilateral correction `W` vanishes identically.  The mockness is genuine and is witnessed by the nonzero `q^(9/4)` coefficient in the `c1` shadow component.
