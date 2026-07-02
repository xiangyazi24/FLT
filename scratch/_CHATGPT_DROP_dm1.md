# Q3085 (dm1): ch10-9div

Date: 2026-07-02

## Executive answer

I am reading `ch10-9div` as the Chapter 10 / tenth-order mock theta identity involving Ramanujan's order-10 functions

\[
\phi(q)=\sum_{n\ge 0}\frac{q^{n(n+1)/2}}{(q;q^2)_{n+1}},
\qquad
\psi(q)=\sum_{n\ge 0}\frac{q^{(n+1)(n+2)/2}}{(q;q^2)_{n+1}}.
\]

The right formalization target is **not** a statement that coefficients are divisible by 9.  The `9` is an exponent dilation: `φ(q^9)` means that every exponent in `φ` has been multiplied by 9.  After the leading factor `q^2`, the whole term lies in the exponent class

\[
n \equiv 2 \pmod 9.
\]

The Lean-friendly way to state the identity is therefore to avoid fractional powers entirely.  Use a fresh variable `t`, let `ω` be a primitive cube root of unity, and state the first tenth-order identity as an equality of ordinary integer-power formal series in `t`:

\[
t^2\phi(t^9)
-
\frac{\psi(\omega t)-\psi(\omega^2t)}{\omega-\omega^2}
=
-t\,A(t),
\]

where, in the standard theta-quotient notation,

\[
A(t)
=
\frac{\Theta_{1,2}(t)}{\Theta_{3,6}(t)}
\frac{\Theta_{3,15}(t)\Theta_6(t)}{\Theta_3(t)}.
\]

If Chan writes the same identity using fractional powers of a variable `q`, it is obtained from this one by the substitution

\[
t=q^{1/3}.
\]

Then the same identity becomes

\[
q^{2/3}\phi(q^3)
-
\frac{\psi(\omega q^{1/3})-\psi(\omega^2q^{1/3})}{\omega-\omega^2}
=
-q^{1/3}A(q^{1/3}).
\]

For formalization, the `t`-version is the correct one.  It keeps all exponents integral and turns the problem into a clean residue/dissection statement.

## The root-of-unity filter

For any formal series

\[
F(t)=\sum_{n\ge 0} a_n t^n,
\]

define its residue-3 components by

\[
F_r(Q)=\sum_{k\ge 0} a_{3k+r}Q^k,
\qquad r=0,1,2.
\]

Then

\[
F(t)=F_0(t^3)+tF_1(t^3)+t^2F_2(t^3).
\]

The antisymmetric cube-root filter is

\[
\mathcal R(F)(t)
=
\frac{F(\omega t)-F(\omega^2t)}{\omega-\omega^2}.
\]

Since

\[
\omega^n-\omega^{2n}
=
\begin{cases}
0,&n\equiv 0\pmod 3,\\
\omega-\omega^2,&n\equiv 1\pmod 3,\\
-(\omega-\omega^2),&n\equiv 2\pmod 3,
\end{cases}
\]

we get the coefficient-level formula

\[
\mathcal R(F)(t)
=
\sum_{n\equiv 1\bmod 3} a_n t^n
-
\sum_{n\equiv 2\bmod 3} a_n t^n.
\]

Equivalently,

\[
\mathcal R(F)(t)=tF_1(t^3)-t^2F_2(t^3).
\]

This is the main algebraic point.  The quotient by `ω-ω²` is only a convenient analytic notation for a residue selector.  In a purely formal proof, it can be replaced by the residue formula above.

## How the identity splits after `Q=t^3`

Write

\[
A(t)=A_0(t^3)+tA_1(t^3)+t^2A_2(t^3),
\]

and similarly

\[
\psi(t)=\psi_0(t^3)+t\psi_1(t^3)+t^2\psi_2(t^3).
\]

Then the integer-power identity

\[
t^2\phi(t^9)-\mathcal R(\psi)(t)=-tA(t)
\]

becomes

\[
t^2\phi(t^9)-t\psi_1(t^3)+t^2\psi_2(t^3)
=
-tA_0(t^3)-t^2A_1(t^3)-t^3A_2(t^3).
\]

Now set `Q=t^3`.  Comparing the three residue classes modulo 3 gives the ordinary `Q`-series identities

\[
A_2(Q)=0,
\]

\[
\psi_1(Q)=A_0(Q),
\]

and

\[
\phi(Q^3)+\psi_2(Q)=-A_1(Q).
\]

This is the cleanest `ch10-9div` form.  The term `φ(Q^3)` appears because

\[
t^2\phi(t^9)=t^2\phi((t^3)^3)=t^2\phi(Q^3).
\]

So the “9” has become a perfectly ordinary third-power argument after the residue split.

## Coefficient oracle for the 9-dilated term

If

\[
\phi(t)=\sum_{m\ge0} b_m t^m,
\]

then

\[
t^2\phi(t^9)=\sum_{m\ge0} b_m t^{9m+2}.
\]

Thus

\[
[t^n]\,t^2\phi(t^9)
=
\begin{cases}
b_{(n-2)/9},& n\ge2\text{ and }n\equiv2\pmod9,\\
0,&\text{otherwise.}
\end{cases}
\]

This is the exact “9-div” rule that should be implemented.  It is a support statement, not an arithmetic divisibility statement about `b_m`.

## Minimal implementation model

The following small coefficient-level model captures the transformation that should be formalized.  It deliberately works with coefficient functions, so it does not depend on analytic convergence or infinite-product infrastructure.

```python
from collections.abc import Callable

Coeff = Callable[[int], int]


def residue3_coeff(c: Coeff, r: int) -> Coeff:
    """Return the coefficient function of F_r(Q) = sum_k a_{3k+r} Q^k."""
    if r not in (0, 1, 2):
        raise ValueError("r must be 0, 1, or 2")

    def out(k: int) -> int:
        if k < 0:
            return 0
        return c(3 * k + r)

    return out


def shifted_dilate9_coeff(c: Coeff, shift: int = 2) -> Coeff:
    """Coefficient function of t^shift * F(t^9)."""
    if shift < 0:
        raise ValueError("shift must be nonnegative")

    def out(n: int) -> int:
        if n < shift:
            return 0
        m = n - shift
        if m % 9 != 0:
            return 0
        return c(m // 9)

    return out


def root_filter3_coeff(c: Coeff) -> Coeff:
    """
    Coefficients of (F(omega*t)-F(omega^2*t))/(omega-omega^2).

    This avoids adjoining omega by using the equivalent residue rule:
      residue 0 mod 3 -> 0
      residue 1 mod 3 -> +a_n
      residue 2 mod 3 -> -a_n
    """
    def out(n: int) -> int:
        if n < 0:
            return 0
        r = n % 3
        if r == 0:
            return 0
        if r == 1:
            return c(n)
        return -c(n)

    return out


def lhs_coeff(phi: Coeff, psi: Coeff) -> Coeff:
    """Coefficients of t^2*phi(t^9) - root_filter3(psi)(t)."""
    phi_part = shifted_dilate9_coeff(phi, shift=2)
    psi_part = root_filter3_coeff(psi)

    def out(n: int) -> int:
        return phi_part(n) - psi_part(n)

    return out
```

The corresponding Lean proof should use the same three lemmas:

1. `coeff_shift_dilate`: coefficient of `t^s * F(t^m)` is zero unless `n ≥ s` and `m ∣ n-s`.
2. `coeff_root_filter3`: the cube-root filter is `0,+1,-1` on residues `0,1,2 mod 3`.
3. `eq_of_residue3`: equality of formal series follows from equality on all three residue classes modulo 3.

## Lean-facing theorem shape

At the interface level, the first theorem should not mention fractional powers.  A good target statement is:

```lean
import Mathlib

noncomputable section

namespace Q3085

/-- Placeholder for the tenth-order mock theta function phi. -/
constant phi10 : Type

/-- Placeholder for the tenth-order mock theta function psi. -/
constant psi10 : Type

/-- Placeholder for the theta quotient
    A(t) = Theta_{1,2}/Theta_{3,6} * Theta_{3,15} * Theta_6 / Theta_3. -/
constant thetaQuotientA : Type

/-- In the real development, these placeholders should be replaced by
    `PowerSeries C` or by the project's formal q-series type. -/
constant Series : Type
constant X : Series
constant mul : Series -> Series -> Series
constant sub : Series -> Series -> Series
constant neg : Series -> Series
constant dilate : Nat -> Series -> Series
constant rootFilter3 : Series -> Series

/-- Integer-power form of Chan's first tenth-order identity.
    This is the version to formalize first; the fractional-power form is
    only a corollary after the substitution `t = q^(1/3)`. -/
constant chan10_15_integer_power_form :
  Series

end Q3085
```

The code block above is intentionally an interface sketch rather than a proposed source file.  The mathematical content to prove is the identity

\[
t^2\phi(t^9)-\mathcal R(\psi)(t)=-tA(t),
\]

plus the coefficient/residue lemmas that make the `9`-dilation rigorous.

## Final conclusion

For `ch10-9div`, the correct answer is:

* keep the identity in the integer-power variable `t`;
* treat `φ(t^9)` as a 9-dilated series;
* use the cube-root filter only as a modulo-3 residue selector;
* after setting `Q=t^3`, split into the three ordinary `Q`-series components

\[
A_2(Q)=0,
\qquad
\psi_1(Q)=A_0(Q),
\qquad
\phi(Q^3)+\psi_2(Q)=-A_1(Q).
\]

This removes fractional powers and makes the role of the `9` completely explicit.
