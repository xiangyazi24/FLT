# Q3115 (dm1): R7 — non-multiplicativity of `B` and the order-6 character illusion

Date: 2026-07-02

## Executive answer

The right automorphic object is **not** a finite sum of Hecke eigenforms, and not a finite sum of Hecke characters.  The right object is a **real-quadratic Shintani / false-indefinite theta coefficient function**.

More explicitly, with the standard Hickerson--Mortenson convention,

```text
B(X) = D(X) - A(X) = -f_{1,3,4}(X, -X^3, X),
```

and the coefficient `B_N` is a signed count of generators in a fixed ray/coset of `Z[phi]`, cut by a real-archimedean Shintani cone.  The ray/coset part is finite and character-like; the archimedean cone cut is a **step function on the real unit circle**.  That step function is the source of the non-multiplicativity.

The prime phenomenon is then not mysterious.  At a split prime, there are only one or two relevant reduced generator orbits, so the coefficient is automatically tiny and lies in

```text
{-2, -1, 0, +1, +2}.
```

The observed absence of `0` at primes should be provable by a finite Shintani-sector table: in the prime case the possible selected representatives never occur in opposite-sign pairs.  The apparent order-6 character is a six-sector **archimedean window**, not a genuine order-6 Hecke character.  At composites, several prime-ideal choices interact; reducing their product back into the Shintani strip introduces unit-carry terms, and those carries destroy multiplicativity.

So the clean slogan is:

```text
B is not multiplicative because it is a ray-class norm count with an archimedean cone window.
The finite ray-class part is multiplicative; the Shintani window is not.
```

A correction to one premise: the classical Andrews--Dyson--Hickerson `sigma(q)` case is also real quadratic, attached to `Q(sqrt(6))` and norms `24n+1`.  Its unit group is infinite as well.  The finite-unit/order-6 picture belongs to imaginary quadratic `Q(sqrt(-3))` phenomena, not to the original ADH real-quadratic norm story.

## 1. Exact arithmetic model for `B_N`

Write

```text
E(k,r) = (4*k^2 + 2*k + r^2 + (6*k + 1)*r) / 2
       = 2*k^2 + k + 3*k*r + r*(r+1)/2.
```

Then

```text
A(X) = sum_{k >= 0, r >= 0} (-1)^r X^E(k,r),
D(X) = sum_{k < 0, r < 0} (-1)^r X^E(k,r),
B(X) = D(X) - A(X).
```

Let

```text
K = Q(sqrt(5)),
phi = (1 + sqrt(5))/2,
O_K = Z[phi],
Norm(a + b*phi) = a^2 + a*b - b^2.
```

For every atom `(k,r)`, define

```text
beta(k,r) = (r - 2*k) + (4*k + 3*r + 1)*phi.
```

Then the fundamental identity is

```text
-Norm(beta(k,r)) = 10*E(k,r) + 1.
```

This is the strongest way to package the norm support.  It proves immediately:

```text
B_N != 0  ==>  10*N + 1 is a norm from Z[phi].
```

Since primes inert in `Q(sqrt(5))` are exactly the primes `p == 2,3 mod 5`, this gives the observed inert-prime parity test.

Conversely, not every eligible norm has nonzero coefficient, because `B_N` is a signed cone count, not merely an existence count.

## 2. Ray/coset formula

Let

```text
beta = a + b*phi.
```

The inverse map from `beta` back to `(k,r)` is

```text
k = (b - 3*a - 1) / 10,
r = (4*a + 2*b - 2) / 10.
```

Thus `beta` comes from an integral atom exactly when

```text
b - 3*a == 1 mod 10.
```

The second integrality condition for `r` follows from this congruence.  Indeed, if `b = 3a + 1 mod 10`, then

```text
4a + 2b - 2 = 10a mod 20,
```

so it is divisible by `10`.

The cone conditions are the two linear inequalities

```text
A-cone:  b - 3*a - 1 >= 0   and   2*a + b - 1 >= 0,
D-cone:  b - 3*a - 1 <  0   and   2*a + b - 1 <  0.
```

The sign is

```text
A contributes -(-1)^r,
D contributes +(-1)^r,
r = (4*a + 2*b - 2)/10.
```

Therefore the exact coefficient formula is

```text
B_N = sum over beta = a + b*phi in O_K of
        W(beta)
```

where

```text
Norm(beta) = -(10*N + 1),
b - 3*a == 1 mod 10,
```

and

```text
W(beta) = -(-1)^r  if beta is in the A-cone,
W(beta) = +(-1)^r  if beta is in the D-cone,
W(beta) = 0        otherwise.
```

This formula is already the proof route for both norm support and non-multiplicativity.

## 3. What is `B` automorphically?

### 3.1 It is a false-indefinite theta coefficient function

The pure quadratic part of the `f_{1,3,4}` exponent has matrix

```text
[[1, 3],
 [3, 4]],
```

up to the usual factor of `1/2`.  Its determinant is

```text
1*4 - 3^2 = -5,
```

so the lattice has signature `(1,1)`.  The completed object is therefore a signature `(1,1)` indefinite theta object of weight `1`, vector-valued for the relevant discriminant/ray module.

The holomorphic q-series `B` is the false/mock holomorphic part obtained by cutting the lattice with a sign or cone kernel.  In the Hickerson--Mortenson description it is an Appell--Lerch expression plus a theta correction.  In the Zwegers description, the nonholomorphic completion replaces sharp signs by error functions attached to the two boundary lines.

So:

```text
B is a holomorphic false/mock part of an indefinite theta series.
It is not itself a holomorphic modular form.
It is not a Hecke eigenform.
It is not expected to have multiplicative coefficients.
```

### 3.2 It is not a finite sum of Hecke characters

There is a finite ray-class condition, but the cone condition is archimedean.  This is the key point.

Let

```text
epsilon = phi^2
```

be the totally positive fundamental unit.  For `alpha in K^*`, define the real-unit angle

```text
theta(alpha)
  = log(|alpha_1 / alpha_2|) / (2*log(epsilon))   mod 1,
```

where `alpha_1, alpha_2` are the two real embeddings.  Multiplication by `epsilon` shifts the numerator by `2*log(epsilon)`, so `theta` is a coordinate on the compact real unit torus

```text
R / (2*log(epsilon)) Z.
```

The coefficient `B_N` has the shape

```text
B_N = sum_{Norm(alpha)=-(10N+1)} chi_fin(alpha) * H(theta(alpha)),
```

where:

```text
chi_fin       = finite congruence/sign data modulo 10,
H             = step function recording A-cone versus D-cone versus outside,
theta(alpha)  = archimedean unit coordinate.
```

A finite Hecke character would replace `H(theta)` by an exponential

```text
exp(2*pi*i*m*theta).
```

But `H` is a discontinuous step function.  Its Fourier expansion is infinite:

```text
H(theta) = sum_{m in Z} h_m exp(2*pi*i*m*theta),
```

with infinitely many nonzero `h_m`, typically decaying like `1/m` because of the jumps.  Consequently the Dirichlet series attached to `B` is not a finite linear combination of Hecke L-functions.  It is an infinite Shintani/Lerch expansion:

```text
sum_{N >= 0} B_N / (10N+1)^s
  = sum_{finite ray characters rho} sum_{m in Z}
      c(rho,m) * L(s, rho * |alpha_1/alpha_2|^(pi*i*m/log(epsilon))).
```

This is the precise automorphic decomposition I would use.  It is a spectral expansion along the real unit torus, not an Euler product.

A rigorous non-finite proof route is:

1. Write `B_N` in the ray/coset formula above.
2. Reduce generators modulo totally positive units to a Shintani fundamental interval.
3. Observe that the cone/sign function on that interval is a step function with at least one jump.
4. A nonconstant step function on a circle is not a trigonometric polynomial.
5. Therefore the Hecke-character expansion has infinitely many nonzero archimedean modes.
6. Therefore `B` is not a finite sum of Hecke-character coefficient functions, and no Euler product or multiplicativity should survive.

## 4. The order-6 character illusion at primes

At a prime `p = 10N + 1`, the norm equation has only the two conjugate prime ideals above `p`, up to units.  After imposing the congruence

```text
b - 3*a == 1 mod 10,
```

and reducing by powers of `epsilon`, there are only one or two contributing reduced representatives.  Hence the coefficient is forced into a tiny set:

```text
B_N in {-2, -1, 0, +1, +2}.
```

Your data says the zero case never occurs and that the absolute values occur in the ratio

```text
|B_N| = 1 : |B_N| = 2 = 2 : 1.
```

The clean explanation to test is a six-sector Shintani table.

### Candidate six-sector theorem

There should be a unit-reduced coordinate `theta_p in R/Z` for the prime ideal above `p` and a phase shift `theta_0` such that

```text
B_{(p-1)/10} = S(theta_p - theta_0),
```

where `S` is a six-step function with values, up to a global sign and cyclic shift,

```text
2, 1, -1, -2, -1, 1.
```

These are exactly the numbers

```text
2*cos(k*pi/3),   k = 0,1,2,3,4,5.
```

But the mechanism is different from a character.  The function

```text
theta -> 2*cos(2*pi*theta)
```

is a character-like exponential combination.  The actual object is expected to be a **piecewise constant sector function** that happens to take the same six values on six sectors.  At primes, only one angle is sampled, so it looks like an order-6 character.  At composites, products add angles and then require reduction back into the Shintani strip; the step function does not respect addition.

This is the precise reason for the illusion:

```text
S(theta_1 + theta_2) is not S(theta_1) * S(theta_2).
```

By contrast, a true order-6 Hecke character would be

```text
chi(alpha) = exp(2*pi*i*theta(alpha)/6)
```

or a finite ray-class character, and would be multiplicative.

## 5. Why non-multiplicativity is expected

Let `M_i = 10N_i + 1` and suppose `M_1, M_2` are coprime eligible norms.  A generator for the product norm is, up to units,

```text
alpha = alpha_1 * alpha_2.
```

The finite ray-class data is multiplicative.  However, the Shintani angle satisfies

```text
theta(alpha) = theta(alpha_1) + theta(alpha_2)  mod 1,
```

and the coefficient uses the step function `H(theta)`, not an exponential.  Hence

```text
H(theta_1 + theta_2) != H(theta_1) * H(theta_2)
```

in general.

Equivalently, when one multiplies two reduced generators, the product usually leaves the fundamental Shintani strip.  One must multiply by a power of the unit to return to the strip.  That exponent is a floor function in logarithms:

```text
m(alpha_1 alpha_2)
  = floor((log-position of alpha_1 + log-position of alpha_2 - boundary) / log(epsilon)).
```

Floor functions produce carries.  The carries change the cone side and the parity sign.  This is exactly the same obstruction that prevents reduced binary quadratic forms or continued-fraction digits from being multiplicative term-by-term.

So the answer to Q2 is yes:

```text
non-multiplicativity is caused by the Shintani cone/window not being compatible with multiplication.
```

The proof route is to turn this sentence into the explicit ray/coset formula of Section 2 and then exhibit one pair of coprime eligible norms for which the Shintani carry changes the sign.  Your `1096/1188` failure rate is precisely what one expects from a non-character step function.

## 6. Prime nonvanishing route

The observed statement

```text
B_{(p-1)/10} != 0
```

for every prime `p = 10N+1` should be provable.

I would prove it in this order.

### Step 1: finite ray-unit table

Work with the unit action on coefficient pairs `(a,b)`:

```text
phi * (a + b*phi)     = b + (a+b)*phi,
epsilon * (a + b*phi) = (a+b) + (a+2b)*phi.
```

Reduce this action modulo `10` and record the orbit of the congruence class

```text
b - 3*a == 1 mod 10.
```

The parity sign `(-1)^r`, where

```text
r = (4*a + 2*b - 2)/10,
```

is also determined by a finite modulus, for example modulo `20` if needed.

### Step 2: Shintani sector table

For each admissible residue class, record which unit translates can land in the A-cone or D-cone inside one fundamental unit strip.  This produces a finite table of selected sectors and signs.

### Step 3: prime ideal input

For a split prime `p`, the principal ideals above `p` give only one conjugate pair of prime ideals.  Up to units, every generator is in one of these two orbits.  Therefore `B_{(p-1)/10}` is a sum of at most two entries from the finite sector table.

### Step 4: no-opposite-pair lemma

Check the finite table and prove:

```text
For prime-norm orbits satisfying b - 3*a == 1 mod 10,
the selected sector entries are either a singleton or two entries with the same sign.
```

This immediately implies

```text
B_{(p-1)/10} in {-2, -1, +1, +2},
```

and proves there are no prime cancellation zeros.

### Step 5: density ratio

The same table should split the unit circle into six equal sectors, two of which give absolute value `2` and four of which give absolute value `1`.  Equidistribution of split prime ideal angles in the real-unit torus then predicts

```text
|B(p)| = 1 with density 4/6 = 2/3,
|B(p)| = 2 with density 2/6 = 1/3.
```

This matches your data.  The density proof is a standard Hecke/prime-ideal equidistribution statement for real-quadratic ray classes with archimedean unit angle.

## 7. Composite cancellation zeros

For composite eligible norms, the number of ideal-factor choices grows.  If

```text
M = 10N + 1 = product of split prime powers times inert prime even powers,
```

then, after ignoring units, there are many choices of which prime above each split rational prime appears in the generator.  Each choice has a Shintani angle and sign.  The coefficient is a signed sum over these choices.

Thus the zeros are exactly:

```text
B_N = sum over ray-compatible divisor choices of sign(choice) * window(choice) = 0.
```

This explains why all observed zeros are composite.  At primes there are too few choices to cancel, and the finite table prevents opposite pairs.  At composites there are enough choices for cancellation.

The examples fit this perfectly:

```text
N = 45:   10N+1 = 451  = 11 * 41
N = 84:   10N+1 = 841  = 29^2
N = 112:  10N+1 = 1121 = 19 * 59
N = 127:  10N+1 = 1271 = 31 * 41
N = 133:  10N+1 = 1331 = 11^3
```

All primes listed are split in `Q(sqrt(5))`; the vanishing is not a failure of norm representability, but cancellation among split-prime choices and unit reductions.

## 8. Explicit L-function decomposition

A finite decomposition into Hecke L-functions is the wrong target.  The exact decomposition should be infinite, indexed by Fourier modes of the Shintani window.

A precise template is:

```text
D_B(s) = sum_{N >= 0} B_N / (10N+1)^s.
```

Let `G` be the finite ray group modulo the modulus needed to encode

```text
b - 3*a == 1 mod 10
```

and the parity sign.  For each finite character `rho` of `G`, and each integer `m`, define the Hecke character

```text
Psi_{rho,m}(alpha)
  = rho(alpha) * exp(2*pi*i*m*theta(alpha)).
```

Then

```text
D_B(s) = sum_{rho in G^} sum_{m in Z} c_{rho,m} L(s, Psi_{rho,m}),
```

where `c_{rho,m}` are the Fourier coefficients of the finite-ray-class and archimedean cone-window function.

This is the exact automorphic decomposition to pursue.  It gives a proof route for analytic continuation and asymptotics, but it does **not** give an Euler product for `D_B`, because an infinite linear combination of Euler products is not itself an Euler product.

A finite sum would imply the Shintani window is a trigonometric polynomial.  Since the window has jumps, that cannot be true.

## 9. Growth prediction

There is a simple rigorous bound from the representation formula:

```text
|B_N| <= C * number of ray-compatible generators with |Norm| = 10N+1
      <= C' * d_K(10N+1),
```

where `d_K` is the ideal divisor function of `K`.  In particular,

```text
|B_N| <= C'' * tau(10N+1)^2
```

is a very safe elementary bound, and with more care one should get a bound of the shape

```text
|B_N| <= C * 2^{omega(10N+1)} * product_{p^e || 10N+1} (e+1),
```

restricted to split-prime choices.

Therefore the worst-case order should be subpolynomial, of divisor-function type:

```text
max_{N <= X} |B_N| <= exp(O(log X / log log X)).
```

I would not conjecture a global `O(log N)` bound without more evidence.  The small observed maximum `7` up to `10^5` is consistent with strong cancellation and the fact that `10N+1` has few split prime factors in that range.  Along specially chosen products of many split primes whose Shintani angles align, the coefficient should grow.  The likely true maximal order is closer to a signed-divisor-function problem than to a bounded eigenvalue problem.

For typical `N`, a random-sign model over split-prime choices predicts much smaller values, roughly square-root in the number of contributing choices, and often zero.  That matches the large number of cancellation zeros.

## 10. Proof-route summary for Q1 and Q2

Here is the proof route I would actually implement.

### Theorem 1: exact ray/coset representation

Prove the atom identity

```text
-Norm((r - 2*k) + (4*k + 3*r + 1)*phi) = 10*E(k,r) + 1.
```

Then prove the inverse congruence formula

```text
k = (b - 3*a - 1)/10,
r = (4*a + 2*b - 2)/10.
```

This gives the exact formula for `B_N` as a signed ray/coset Shintani count.

### Theorem 2: automorphic nature

Construct the Zwegers completion of the signature `(1,1)` theta series by replacing the cone signs with error functions.  This proves that `B` is the holomorphic false/mock part of a weight-1 indefinite theta object.

### Theorem 3: non-multiplicativity mechanism

Reduce generators modulo the positive unit group.  Show that the coefficient is a finite-ray character times a discontinuous archimedean step function `H(theta)`.  Since `H` is not a character, multiplication of ideals does not preserve the coefficient.  This proves the conceptual non-multiplicativity.

### Theorem 4: infinite Hecke-character expansion

Fourier-expand `H(theta)` on the real unit torus.  This expresses the Dirichlet series of `B` as an infinite sum of Hecke L-functions with archimedean characters.  Prove infinitely many Fourier coefficients are nonzero because `H` has jumps.  This rules out finite Hecke-character/eigenform explanations.

### Theorem 5: prime finite-table theorem

Enumerate the finite ray-unit table modulo `10` or `20`, plus the six Shintani sectors.  Prove that for prime norm `p=10N+1`, selected representatives are never opposite-sign pairs.  This proves

```text
B_N in {-2,-1,+1,+2}
```

and the absence of prime cancellation zeros.  Equidistribution of prime ideal angles gives the `2/3` versus `1/3` absolute-value density.

## 11. Verification skeleton

This code is intended as a proof-development oracle.  It isolates the finite congruence and cone data; it does not use numerical q-series expansion.

```python
from collections import defaultdict
from dataclasses import dataclass
from math import isqrt
from typing import DefaultDict, Dict, Iterable, List, Optional, Tuple


@dataclass(frozen=True)
class PhiElt:
    """Element a + b*phi in Z[phi], phi=(1+sqrt(5))/2."""
    a: int
    b: int


def norm_phi(x: PhiElt) -> int:
    """Norm of a + b*phi, where phi^2=phi+1."""
    return x.a * x.a + x.a * x.b - x.b * x.b


def mul_phi(x: PhiElt) -> PhiElt:
    """Multiply by phi."""
    return PhiElt(a=x.b, b=x.a + x.b)


def mul_epsilon(x: PhiElt) -> PhiElt:
    """Multiply by epsilon=phi^2=1+phi."""
    return PhiElt(a=x.a + x.b, b=x.a + 2 * x.b)


def exponent_E(k: int, r: int) -> int:
    """Exponent of X in B(X)."""
    numerator = 4 * k * k + 2 * k + r * r + (6 * k + 1) * r
    if numerator % 2 != 0:
        raise ValueError((k, r, numerator))
    return numerator // 2


def beta_from_atom(k: int, r: int) -> PhiElt:
    """beta(k,r) = (r-2k) + (4k+3r+1)*phi."""
    return PhiElt(a=r - 2 * k, b=4 * k + 3 * r + 1)


def atom_from_beta(x: PhiElt) -> Optional[Tuple[int, int]]:
    """Recover (k,r) from beta=a+b*phi if beta is in the target coset."""
    num_k = x.b - 3 * x.a - 1
    num_r = 4 * x.a + 2 * x.b - 2
    if num_k % 10 != 0 or num_r % 10 != 0:
        return None
    return num_k // 10, num_r // 10


def in_target_coset(x: PhiElt) -> bool:
    return (x.b - 3 * x.a - 1) % 10 == 0


def cone_weight_for_B(k: int, r: int) -> int:
    """Weight in B = D - A."""
    parity = -1 if r % 2 else 1
    if k >= 0 and r >= 0:
        return -parity
    if k < 0 and r < 0:
        return parity
    return 0


def weight_from_beta(x: PhiElt) -> int:
    kr = atom_from_beta(x)
    if kr is None:
        return 0
    k, r = kr
    return cone_weight_for_B(k, r)


def check_norm_identity(k: int, r: int) -> bool:
    x = beta_from_atom(k, r)
    return -norm_phi(x) == 10 * exponent_E(k, r) + 1


def coeffs_B_by_atoms(nmax: int) -> Dict[int, int]:
    """Finite cone enumeration for B_N, used only as a test oracle."""
    out: DefaultDict[int, int] = defaultdict(int)
    bound = 4 * isqrt(2 * nmax + 1) + 50
    for k in range(-bound, bound + 1):
        for r in range(-bound, bound + 1):
            w = cone_weight_for_B(k, r)
            if w == 0:
                continue
            n = exponent_E(k, r)
            if 0 <= n <= nmax:
                assert check_norm_identity(k, r)
                out[n] += w
    return dict(out)


def unit_orbit_mod(x: PhiElt, modulus: int, steps: int) -> List[PhiElt]:
    """Orbit under epsilon=phi^2 modulo `modulus`."""
    out: List[PhiElt] = []
    y = PhiElt(x.a % modulus, x.b % modulus)
    for _ in range(steps):
        out.append(y)
        y = mul_epsilon(y)
        y = PhiElt(y.a % modulus, y.b % modulus)
    return out


def finite_admissible_residue_table(modulus: int = 20) -> List[Tuple[int, int, int]]:
    """List residue classes that can contribute, with their local parity sign.

    The modulus 20 is used so that r parity is visible.
    """
    rows: List[Tuple[int, int, int]] = []
    for a in range(modulus):
        for b in range(modulus):
            x = PhiElt(a, b)
            kr = atom_from_beta(x)
            if kr is None:
                continue
            _k, r = kr
            parity = -1 if r % 2 else 1
            rows.append((a, b, parity))
    return rows
```

A Sage version of the prime test should enumerate prime ideal generators, reduce by powers of `epsilon`, and compare the resulting sector table with the observed value of `B_{(p-1)/10}`.  The finite table is the piece that should turn the prime observations into a theorem.

```python
from typing import List, Optional, Tuple
from sage.all import QuadraticField, ZZ, factor


K = QuadraticField(5, 's')
s = K.gen()
phi = (1 + s) / 2
OK = K.ring_of_integers()
epsilon = phi ** 2


def eligible_norm_integer(M: int) -> bool:
    """Check the inert-prime norm criterion for Q(sqrt(5))."""
    if M <= 0:
        return False
    for p, e in factor(ZZ(M)):
        if int(p % 5) in (2, 3) and int(e) % 2:
            return False
    return True


def phi_coefficients(alpha) -> Tuple[int, int]:
    """Return a,b with alpha=a+b*phi, assuming alpha is integral.

    In a final script this should use the integral basis chosen by Sage for OK.
    This placeholder records the intended interface.
    """
    raise NotImplementedError("Extract coefficients in the basis 1, phi.")


def atom_from_coefficients(a: int, b: int) -> Optional[Tuple[int, int]]:
    num_k = b - 3 * a - 1
    num_r = 4 * a + 2 * b - 2
    if num_k % 10 or num_r % 10:
        return None
    return num_k // 10, num_r // 10


def cone_weight(k: int, r: int) -> int:
    parity = -1 if r % 2 else 1
    if k >= 0 and r >= 0:
        return -parity
    if k < 0 and r < 0:
        return parity
    return 0


def reduce_by_units_to_strip(alpha):
    """Reduce alpha by powers of epsilon into a chosen Shintani strip.

    The exact inequalities defining the strip should match the paper's cone
    convention.  This placeholder is where the floor/log carry appears.
    """
    raise NotImplementedError("Choose and implement a Shintani fundamental strip.")
```

## 12. Answers to the numbered questions

### Q1. What is `B` automorphically?

`B` is the holomorphic false/mock part of a weight-1 signature `(1,1)` indefinite theta series attached to `Q(sqrt(5))` with a ray/coset condition modulo `10`.  It is not a single eigenform and not a finite sum of Hecke characters.  Its Dirichlet series is naturally an infinite Fourier expansion of Hecke L-functions indexed by archimedean unit modes.

### Q2. Is non-multiplicativity caused by the Shintani cone?

Yes.  The finite ray-class part is multiplicative, but the Shintani cone/window is a discontinuous function of the real unit coordinate.  Multiplying ideals adds unit angles and then requires a unit reduction; the resulting floor-function carry changes the window value.  That is the source of non-multiplicativity.

### Q3. Can `B` be decomposed into L-function coefficients?

Yes, but not finitely.  Fourier-expand the Shintani window on the real unit torus.  This gives an infinite sum of Hecke L-functions with finite ray character modulo `10` and archimedean characters

```text
alpha -> exp(2*pi*i*m*theta(alpha)).
```

A finite combination would require the cone window to be a trigonometric polynomial, which it is not.

### Q4. Growth rate?

A rigorous divisor-type bound is expected:

```text
|B_N| <= exp(O(log N / log log N)).
```

Typical values can remain very small because the signed Shintani sum cancels.  I would not predict a global `O(log N)` bound without further evidence; along products of many split primes, growth should eventually exceed any fixed bound.

### Q5. Why no prime cancellation zeros?

For prime `10N+1`, there are only the two conjugate prime-ideal orbits.  The finite ray-unit/Shintani sector table should show that selected prime representatives are either singletons or same-sign pairs, never opposite-sign pairs.  That proves `B_N` is always one of

```text
{-2, -1, +1, +2}
```

at split primes.  Composite zeros occur because composite norms have multiple split-prime choices, and their signed sector contributions can cancel.

## Bottom line

The correct proof strategy is not to search for a hidden multiplicative eigenform.  The correct proof strategy is to formalize the exact ray-class Shintani coefficient formula.  Once that formula is in place, the observations become structurally natural:

```text
norm support      = ray-class norm equation,
prime smallness   = one prime-ideal orbit plus finite sector table,
2:1 ratio         = six-sector equidistribution,
nonmultiplicative = Shintani window/floor-carry effect,
composite zeros   = cancellation among split-prime choices.
```

This is the strongest route I see from the current data to a theorem.

## References for orientation

```text
Hickerson--Mortenson, Hecke-type double sums, Appell-Lerch sums, and mock theta functions:
https://arxiv.org/abs/1208.1421

Mortenson, Ramanujan's 1psi1 summation, Hecke-type double sums, and Appell-Lerch sums:
https://arxiv.org/abs/1208.1359

Mortenson, On the dual nature of partial theta functions and Appell-Lerch sums:
https://arxiv.org/abs/1208.6316

Lovejoy--Osburn, Real quadratic double sums:
https://arxiv.org/abs/1502.01109

Zwegers, Mock Theta Functions:
https://dspace.library.uu.nl/handle/1874/881

Zwegers, Maass waveforms arising from sigma and related indefinite theta functions:
https://arxiv.org/abs/1002.1175
```
