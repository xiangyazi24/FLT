The \(N=16\) case **does not have the same shape as the verified \(N=10\) case**. In particular, there is no honest package of the form

\[
b=b_{16}(u),\qquad c=c_{16}(u),
\]

with \(u\) the affine coordinate on

\[
E_{N16}:\quad w^2=u^3-u^2-u,
\]

and then a residual quadratic \(Q_{16}(u,X)\) whose root \(x_T\) gives \(w\) linearly. That would be a rational one-parameter Tate family for order \(16\). The standard \(N=16\) story already involves square-root conditions; one reference gives \(Z/16Z\) parametrisations over quadratic fields, not over \(\mathbb Q\), and its \(Z/16Z\) theorem is explicitly phrased using nested square-root membership conditions in the base field. citeturn932801view0turn997048view0

What you **can** and should formalize directly is the exact Tate algebra up to the residual quadratic. Then the missing final step is a separate birational map from that residual-discriminant curve to your \(E_{N16}\). Do not try to force the \(N=10\) one-line identity pattern.

There is also a sign sanity check: on

\[
w^2=u^3-u^2-u=u(u^2-u-1),
\]

the values \(u=\pm1\) give \(w^2=-1\), so they are not affine \(\mathbb Q\)-points. If your obstruction theorem says rational points have \(u\in\{-1,0,1\}\), then over \(\mathbb Q\) only \(u=0\) is actually realized on this affine model. If you intended three rational degenerate affine points, re-check the sign.

## Exact Tate order-16 algebra

Use the usual Tate normal form

\[
E(b,c):\quad y^2+(1-c)xy-by=x^3-bx^2,
\]

with \(P=(0,0)\). Thus

\[
a_1=1-c,\qquad a_2=-b,\qquad a_3=-b,\qquad a_4=a_6=0.
\]

The two-torsion cubic is

\[
F_2(b,c;X)
=
4X^3+\bigl((1-c)^2-4b\bigr)X^2+2b(c-1)X+b^2.
\]

Lean:

```lean
def tateTwoTorsionCubic (b c X : ℚ) : ℚ :=
  4 * X^3 + ((1 - c)^2 - 4*b) * X^2 + 2*b*(c - 1)*X + b^2
```

Define the auxiliary factors

\[
M=2b^2-bc^2-3bc+c^2,
\]

\[
N=b^2-bc-c^3,
\]

\[
L=b^3-3b^2c+bc^3+3bc^2-c^5-c^4-c^3,
\]

\[
K=b^3-3b^2c^2-2b^2c+bc^4+3bc^3+bc^2+c^5.
\]

Then the \(8P\) coordinates are

\[
\boxed{
x(8P)=
\frac{bNL}{c^2M^2}
}
\]

and

\[
\boxed{
y(8P)=
-\frac{b(b-c)N^2K}{c^3M^3}.
}
\]

Lean:

```lean
def tateM16 (b c : ℚ) : ℚ :=
  2*b^2 - b*c^2 - 3*b*c + c^2

def tateN16 (b c : ℚ) : ℚ :=
  b^2 - b*c - c^3

def tateL16 (b c : ℚ) : ℚ :=
  b^3 - 3*b^2*c + b*c^3 + 3*b*c^2 - c^5 - c^4 - c^3

def tateK16 (b c : ℚ) : ℚ :=
  b^3 - 3*b^2*c^2 - 2*b^2*c + b*c^4 + 3*b*c^3 + b*c^2 + c^5

def tateX8 (b c : ℚ) : ℚ :=
  b * tateN16 b c * tateL16 b c / (c^2 * (tateM16 b c)^2)

def tateY8 (b c : ℚ) : ℚ :=
  - b * (b - c) * (tateN16 b c)^2 * tateK16 b c /
    (c^3 * (tateM16 b c)^3)
```

The order-16 condition is obtained by imposing that \(8P\) is 2-torsion:

\[
2y(8P)+(1-c)x(8P)-b=0.
\]

After clearing the nondegenerate denominator, the polynomial is

\[
\boxed{
\begin{aligned}
\Phi_{16}(b,c)=\;&
2b^8-4b^7c^2-12b^7c
+b^6c^4+18b^6c^3+31b^6c^2 \\
&-35b^5c^4-45b^5c^3
+40b^4c^5+40b^4c^4 \\
&-10b^3c^8-10b^3c^7-30b^3c^6-22b^3c^5 \\
&+4b^2c^{10}+20b^2c^9+15b^2c^8+14b^2c^7+7b^2c^6 \\
&-bc^{12}-3bc^{11}-10bc^{10}-6bc^9-3bc^8-bc^7-c^{12}.
\end{aligned}
}
\]

Lean:

```lean
def Phi16 (b c : ℚ) : ℚ :=
  2*b^8 - 4*b^7*c^2 - 12*b^7*c
  + b^6*c^4 + 18*b^6*c^3 + 31*b^6*c^2
  - 35*b^5*c^4 - 45*b^5*c^3
  + 40*b^4*c^5 + 40*b^4*c^4
  - 10*b^3*c^8 - 10*b^3*c^7 - 30*b^3*c^6 - 22*b^3*c^5
  + 4*b^2*c^10 + 20*b^2*c^9 + 15*b^2*c^8 + 14*b^2*c^7 + 7*b^2*c^6
  - b*c^12 - 3*b*c^11 - 10*b*c^10 - 6*b*c^9 - 3*b*c^8 - b*c^7
  - c^12
```

The exact `field_simp; ring` identity is

\[
\boxed{
2\,\mathrm{tateY8}(b,c)+(1-c)\mathrm{tateX8}(b,c)-b
=
-\frac{b\,\Phi_{16}(b,c)}{c^3M^3}.
}
\]

Lean-shaped:

```lean
lemma tatePsi8_identity
    (b c : ℚ)
    (hc : c ≠ 0)
    (hM : tateM16 b c ≠ 0) :
    2 * tateY8 b c + (1 - c) * tateX8 b c - b
      =
    - b * Phi16 b c / (c^3 * (tateM16 b c)^3) := by
  unfold tateY8 tateX8 Phi16 tateM16 tateN16 tateL16 tateK16
  field_simp [hc, hM]
  ring
```

So, under the usual nondegeneracy hypotheses,

\[
8P\text{ is 2-torsion}
\quad\Longleftrightarrow\quad
\Phi_{16}(b,c)=0.
\]

## Residual quadratic for the independent 2-torsion point

Set

\[
r=x(8P)=\mathrm{tateX8}(b,c).
\]

Write

\[
A=(1-c)^2-4b,
\qquad
B=2b(c-1).
\]

Then define the residual quadratic around \(r\) by

\[
\boxed{
Q_{16}^{bc}(b,c;X)
=
4X^2+(A+4r)X+\bigl(B+Ar+4r^2\bigr).
}
\]

Lean:

```lean
def tateQ16bc (b c X : ℚ) : ℚ :=
  let r := tateX8 b c
  let A := (1 - c)^2 - 4*b
  let B := 2*b*(c - 1)
  4*X^2 + (A + 4*r)*X + (B + A*r + 4*r^2)
```

The key factor identity is

\[
\boxed{
F_2(b,c;X)-F_2(b,c;r)
=
(X-r)Q_{16}^{bc}(b,c;X).
}
\]

Lean:

```lean
lemma tateTwoTorsionCubic_sub_x8_factor
    (b c X : ℚ) :
    tateTwoTorsionCubic b c X
      - tateTwoTorsionCubic b c (tateX8 b c)
      =
    (X - tateX8 b c) * tateQ16bc b c X := by
  unfold tateTwoTorsionCubic tateQ16bc
  ring
```

Also,

\[
F_2(b,c;r)
=
\left(2y(8P)+(1-c)x(8P)-b\right)^2.
\]

So using the previous identity,

\[
\Phi_{16}(b,c)=0
\quad\Longrightarrow\quad
F_2(b,c;r)=0.
\]

Therefore, if \(x_T\) is the \(x\)-coordinate of an independent 2-torsion point and \(x_T\neq r\), then

\[
F_2(b,c;x_T)=0,
\qquad
F_2(b,c;r)=0,
\qquad
x_T\neq r,
\]

hence

\[
\boxed{
Q_{16}^{bc}(b,c;x_T)=0.
}
\]

That is the exact \(N=16\) analogue of the residual-quadratic step.

## Linear square identity from the residual quadratic

Let

\[
q_1=A+4r,
\qquad
q_0=B+Ar+4r^2.
\]

Define

\[
\eta=8x_T+q_1.
\]

Then

\[
Q_{16}^{bc}(b,c;x_T)=4x_T^2+q_1x_T+q_0,
\]

and the exact discriminant identity is

\[
\boxed{
\eta^2-\bigl(q_1^2-16q_0\bigr)
=
16Q_{16}^{bc}(b,c;x_T).
}
\]

Lean:

```lean
def eta16bc (b c X : ℚ) : ℚ :=
  let r := tateX8 b c
  let A := (1 - c)^2 - 4*b
  8*X + (A + 4*r)

def discQ16bc (b c : ℚ) : ℚ :=
  let r := tateX8 b c
  let A := (1 - c)^2 - 4*b
  let B := 2*b*(c - 1)
  let q1 := A + 4*r
  let q0 := B + A*r + 4*r^2
  q1^2 - 16*q0

lemma eta16bc_sq_sub_disc
    (b c X : ℚ) :
    eta16bc b c X^2 - discQ16bc b c
      =
    16 * tateQ16bc b c X := by
  unfold eta16bc discQ16bc tateQ16bc
  ring
```

So from the independent 2-torsion root,

\[
Q_{16}^{bc}(b,c;x_T)=0,
\]

you get

\[
\eta^2=\operatorname{disc}Q_{16}^{bc}(b,c).
\]

This is the correct “linear in \(x_T\)” square step.

## Where the requested \(E_{N16}\) identity fails

For \(N=10\), the corresponding discriminant simplifies immediately to

\[
u^3+u^2-u
\]

after the rational order-10 parametrization \(b=b_{10}(u), c=c_{10}(u)\). That is why you got the clean identity

\[
w^2-(u^3+u^2-u)
=
\frac{(u^2-4u-1)^4}{16}Q_u(x_T).
\]

For \(N=16\), the order-16 locus is not rationally parametrized by a single \(u\). The order-16 condition above is the polynomial \(\Phi_{16}(b,c)=0\); the standard field-theoretic formulation of \(Z/16Z\) involves additional square-root membership conditions, and the literature’s explicit \(Z/16Z\) constructions are over quadratic fields rather than a rational \(b(u),c(u)\) family over \(\mathbb Q\). citeturn997048view0

So the direct analogue

```lean
def b16 (u : ℚ) : ℚ := ...
def c16 (u : ℚ) : ℚ := ...
def Q16 (u X : ℚ) : ℚ := ...
def w16 (u xT : ℚ) : ℚ := ...
```

is the wrong target. The correct target must have one of these forms:

```lean
-- birational map from the Tate/discriminant model:
def u16_from_tate (b c xT : ℚ) : ℚ := ...
def w16_from_tate (b c xT : ℚ) : ℚ := ...
```

or, more naturally,

```lean
-- functions on the elliptic modular curve itself:
def b16 (u w : ℚ) : ℚ := ...
def c16 (u w : ℚ) : ℚ := ...
```

with

\[
w^2=u^3-u^2-u.
\]

The \(b,c\) functions cannot depend on \(u\) alone unless the map is degenerate.

## Recommended Lean route

The Lean-translatable core should be split like this:

```text
Tate normal form with P = (0,0)
  → compute 8P = (tateX8 b c, tateY8 b c)
  → 8P is 2-torsion
  → Phi16 b c = 0

independent T
  → xT root of tateTwoTorsionCubic
  → xT ≠ tateX8 b c
  → tateQ16bc b c xT = 0

quadratic discriminant
  → eta16bc b c xT ^ 2 = discQ16bc b c
```

Then add a **separate** birational-map lemma:

```lean
theorem EN16_point_of_Phi16_and_disc
    (b c xT : ℚ)
    (hPhi : Phi16 b c = 0)
    (hQ : tateQ16bc b c xT = 0)
    (nondeg : ...) :
    ∃ u w : ℚ,
      w^2 = u^3 - u^2 - u ∧
      ¬ (u = -1 ∨ u = 0 ∨ u = 1)
```

That is the honest analogue of the \(N=10\) endpoint. The missing content is the birational map from the \((b,c,\eta)\)-model cut out by

\[
\Phi_{16}(b,c)=0,
\qquad
\eta^2=\operatorname{disc}Q_{16}^{bc}(b,c)
\]

to your chosen model

\[
w^2=u^3-u^2-u.
\]

It is **not** a single `field_simp; ring` identity after substituting \(b=b_{16}(u),c=c_{16}(u)\), because such a \(u\)-only Tate parametrization is not available.
