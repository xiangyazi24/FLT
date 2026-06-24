There is a subtle but important difference from the \(N=10\) case: for \(N=12\), the Tate parameter is **not** a rational function of the final \(u\)-coordinate alone. The clean quotient parameter is a Tate parameter \(\alpha\). The final curve

\[
E_{N12}: w^2=u^3-u^2-4u+4
\]

is reached from the natural residual-quadratic curve by a \(2\)-isogeny. So the exact same shape

\[
b=b_{12}(u),\qquad c=c_{12}(u),\qquad
w=\text{linear in }x_T
\]

is not the right \(N=12\) package. The Lean-friendly package is instead:

\[
\alpha \mapsto b_{12}(\alpha),c_{12}(\alpha),
\]

then use the independent \(2\)-torsion root \(x_T\) to define an auxiliary \(\eta\), then a point \((u,w)\) on \(E_{N12}\).

The Tate-normal-form \(N=12\) parametrization below is the Kubert/Tate one; the cited paper states that curves with a point of order \(n=4,\dots,10,12\) admit Tate normal form, and gives the \(n=12\) formulas for \(b,c\) in terms of \(\alpha\). citeturn821005view0

---

## 1. Tate normal form and order-12 condition

Use

\[
E(b,c):\quad y^2+(1-c)xy-by=x^3-bx^2,
\]

with \(P=(0,0)\).

So

\[
a_1=1-c,\qquad a_2=-b,\qquad a_3=-b,\qquad a_4=0,\qquad a_6=0.
\]

The multiples are:

\[
2P=(b,bc),
\]

\[
3P=(c,b-c),
\]

\[
4P=
\left(
\frac{b(b-c)}{c^2},
-\frac{b^2(b-c^2-c)}{c^3}
\right),
\]

\[
5P=
\left(
-\frac{bc(b-c^2-c)}{(b-c)^2},
\frac{bc^2(b^2-bc-c^3)}{(b-c)^3}
\right),
\]

\[
6P=
\left(
\frac{(b-c)(b^2-bc-c^3)}{(b-c^2-c)^2},
\frac{c(b-c)^2(2b^2-bc^2-3bc+c^2)}{(b-c^2-c)^3}
\right).
\]

The point \(6P\) is \(2\)-torsion iff

\[
2y(6P)+(1-c)x(6P)-b=0.
\]

After clearing the denominator and the harmless factor \(c\), the order-12 polynomial is:

\[
\boxed{
\Phi_{12}(b,c)
=
3b^4-b^3c^2-9b^3c+10b^2c^2
+bc^4-5bc^3+c^6+c^4.
}
\]

The classical rational parametrization is:

\[
\boxed{
c_{12}(\alpha)
=
\frac{(3\alpha^2-3\alpha+1)(\alpha-2\alpha^2)}
{(\alpha-1)^3}
}
\]

and

\[
\boxed{
b_{12}(\alpha)
=
c_{12}(\alpha)\,
\frac{2\alpha-2\alpha^2-1}{\alpha-1}.
}
\]

Equivalently,

\[
b_{12}(\alpha)
=
\frac{
\alpha(1-2\alpha)(3\alpha^2-3\alpha+1)(2\alpha-2\alpha^2-1)
}
{(\alpha-1)^4}.
\]

These satisfy

\[
\Phi_{12}(b_{12}(\alpha),c_{12}(\alpha))=0.
\]

In Lean, this is just:

```lean
def Phi12 (b c : ℚ) : ℚ :=
  3*b^4 - b^3*c^2 - 9*b^3*c + 10*b^2*c^2
    + b*c^4 - 5*b*c^3 + c^6 + c^4

def c12 (a : ℚ) : ℚ :=
  ((3*a^2 - 3*a + 1) * (a - 2*a^2)) / (a - 1)^3

def b12 (a : ℚ) : ℚ :=
  c12 a * (2*a - 2*a^2 - 1) / (a - 1)
```

Then:

```lean
lemma Phi12_b12_c12 (a : ℚ) :
    Phi12 (b12 a) (c12 a) = 0 := by
  unfold Phi12 b12 c12
  field_simp
  ring
```

with the usual nonzero hypotheses if you want `field_simp` to avoid degenerate \(\alpha=1\).

---

## 2. Two-torsion cubic and known \(6P\)

For \(E(b,c)\), the two-torsion cubic is:

\[
\boxed{
F_{b,c}(X)
=
4X^3+\bigl((1-c)^2-4b\bigr)X^2
+2b(c-1)X+b^2.
}
\]

The known \(2\)-torsion point \(6P\) has

\[
\boxed{
x(6P)
=
\frac{\alpha(3\alpha^2-3\alpha+1)}{\alpha-1}
}
\]

after substituting \(b=b_{12}(\alpha)\), \(c=c_{12}(\alpha)\).

The residual quadratic numerator is:

\[
\boxed{
Q_{12}(\alpha,X)
=
A_{12}(\alpha)X^2+B_{12}(\alpha)X+C_{12}(\alpha),
}
\]

where

\[
A_{12}(\alpha)=4(\alpha-1)^7,
\]

\[
B_{12}(\alpha)
=
(\alpha-1)(2\alpha-1)(2\alpha^2-2\alpha+1)
(12\alpha^4-20\alpha^3+10\alpha^2-1),
\]

\[
C_{12}(\alpha)
=
-\alpha(2\alpha-1)^2(2\alpha^2-2\alpha+1)^2
(3\alpha^2-3\alpha+1).
\]

Then

\[
F_{b_{12}(\alpha),c_{12}(\alpha)}(X)
=
\frac{X-x(6P)}{(\alpha-1)^7}
Q_{12}(\alpha,X).
\]

So if \(T\) is an independent rational \(2\)-torsion point with \(x\)-coordinate \(x_T\neq x(6P)\), then

\[
Q_{12}(\alpha,x_T)=0.
\]

Lean definitions:

```lean
def F2Torsion (b c X : ℚ) : ℚ :=
  4*X^3 + ((1 - c)^2 - 4*b)*X^2 + 2*b*(c - 1)*X + b^2

def x6_12 (a : ℚ) : ℚ :=
  a * (3*a^2 - 3*a + 1) / (a - 1)

def A12 (a : ℚ) : ℚ :=
  4 * (a - 1)^7

def B12 (a : ℚ) : ℚ :=
  (a - 1) * (2*a - 1) * (2*a^2 - 2*a + 1)
    * (12*a^4 - 20*a^3 + 10*a^2 - 1)

def C12 (a : ℚ) : ℚ :=
  -a * (2*a - 1)^2 * (2*a^2 - 2*a + 1)^2
    * (3*a^2 - 3*a + 1)

def Q12 (a X : ℚ) : ℚ :=
  A12 a * X^2 + B12 a * X + C12 a
```

---

## 3. The discriminant square and the auxiliary quartic

For a root \(X=x_T\) of \(Q_{12}(\alpha,X)\), define

\[
H(\alpha)=2\alpha^2-2\alpha+1,
\]

\[
G(\alpha)=6\alpha^2-6\alpha+1.
\]

Let

\[
S(\alpha,X)
=
2A_{12}(\alpha)X+B_{12}(\alpha).
\]

Explicitly,

\[
S(\alpha,X)
=
8(\alpha-1)^7X+B_{12}(\alpha).
\]

Define

\[
\boxed{
\eta
=
\frac{S(\alpha,x_T)}
{(\alpha-1)(2\alpha-1)^3H(\alpha)}.
}
\]

Then the key quadratic-root identity is:

\[
\boxed{
\eta^2-H(\alpha)G(\alpha)
=
\frac{
16(\alpha-1)^5
}
{
(2\alpha-1)^6H(\alpha)^2
}
Q_{12}(\alpha,x_T).
}
\]

Thus \(Q_{12}(\alpha,x_T)=0\) gives

\[
\boxed{
\eta^2
=
(2\alpha^2-2\alpha+1)(6\alpha^2-6\alpha+1).
}
\]

Lean:

```lean
def H12 (a : ℚ) : ℚ :=
  2*a^2 - 2*a + 1

def G12 (a : ℚ) : ℚ :=
  6*a^2 - 6*a + 1

def S12 (a X : ℚ) : ℚ :=
  2 * A12 a * X + B12 a

def eta12 (a X : ℚ) : ℚ :=
  S12 a X / ((a - 1) * (2*a - 1)^3 * H12 a)
```

Identity:

```lean
lemma eta12_sq_sub
    (a X : ℚ) :
    eta12 a X^2 - H12 a * G12 a =
      (16 * (a - 1)^5 / ((2*a - 1)^6 * (H12 a)^2)) * Q12 a X := by
  unfold eta12 S12 A12 B12 C12 H12 G12 Q12
  field_simp
  ring
```

with nonzero denominator hypotheses in the actual formalization.

---

## 4. From the quartic to a 2-isogenous curve

The quartic

\[
\eta^2=H(\alpha)G(\alpha)
\]

maps to

\[
E' : y^2=x^3-4x^2+16x
\]

by

\[
\boxed{
x
=
\frac{2(\eta+1-4\alpha+4\alpha^2)}{\alpha^2}
}
\]

and

\[
\boxed{
y
=
-\frac{
4(6\alpha^3-10\alpha^2+2\alpha\eta+6\alpha-\eta-1)
}
{\alpha^3}.
}
\]

The exact identity is:

\[
\boxed{
y^2-(x^3-4x^2+16x)
=
-\frac{8(2\alpha^2-4\alpha+\eta+1)}{\alpha^6}
\left(\eta^2-H(\alpha)G(\alpha)\right).
}
\]

So if \(Q_{12}(\alpha,x_T)=0\), then \(\eta^2=HG\), hence

\[
y^2=x^3-4x^2+16x.
\]

Lean definitions:

```lean
def xAux12 (a eta : ℚ) : ℚ :=
  2 * (eta + 1 - 4*a + 4*a^2) / a^2

def yAux12 (a eta : ℚ) : ℚ :=
  -4 * (6*a^3 - 10*a^2 + 2*a*eta + 6*a - eta - 1) / a^3
```

Identity:

```lean
lemma aux12_curve_identity
    (a eta : ℚ) :
    yAux12 a eta^2
      - (xAux12 a eta^3 - 4*xAux12 a eta^2 + 16*xAux12 a eta)
    =
    (-8 * (2*a^2 - 4*a + eta + 1) / a^6)
      * (eta^2 - H12 a * G12 a) := by
  unfold xAux12 yAux12 H12 G12
  field_simp
  ring
```

---

## 5. The 2-isogeny to \(E_{N12}\)

The curve

\[
E' : y^2=x^3-4x^2+16x
\]

has the rational \(2\)-torsion point \((0,0)\). Quotienting by it gives

\[
Y^2=X^3+8X^2-48X=X(X-4)(X+12).
\]

The quotient map is:

\[
X=\frac{y^2}{x^2}=x-4+\frac{16}{x},
\]

\[
Y=y\left(1-\frac{16}{x^2}\right).
\]

Now put

\[
X=4(u-1),\qquad Y=8w.
\]

Equivalently,

\[
\boxed{
u=\frac{x}{4}+\frac{4}{x}
}
\]

and

\[
\boxed{
w=
\frac{y}{8}\left(1-\frac{16}{x^2}\right).
}
\]

Then

\[
\boxed{
w^2-(u^3-u^2-4u+4)
=
\frac{(x-4)^2(x+4)^2}{64x^4}
\left(y^2-(x^3-4x^2+16x)\right).
}
\]

Lean:

```lean
def uN12_of_aux (x : ℚ) : ℚ :=
  x / 4 + 4 / x

def wN12_of_aux (x y : ℚ) : ℚ :=
  y * (1 - 16 / x^2) / 8
```

Identity:

```lean
lemma isogeny12_to_EN12_identity
    (x y : ℚ) :
    wN12_of_aux x y^2
      - (uN12_of_aux x^3 - uN12_of_aux x^2 - 4*uN12_of_aux x + 4)
    =
    ((x - 4)^2 * (x + 4)^2 / (64 * x^4))
      * (y^2 - (x^3 - 4*x^2 + 16*x)) := by
  unfold uN12_of_aux wN12_of_aux
  field_simp
  ring
```

---

## 6. Final compositional \(u,w\) formulas from \(\alpha,x_T\)

Define

\[
\eta=\eta_{12}(\alpha,x_T),
\]

\[
x=xAux12(\alpha,\eta),
\qquad
y=yAux12(\alpha,\eta),
\]

then

\[
\boxed{
u=uN12\_of\_aux(x)
=
\frac{x}{4}+\frac{4}{x}
}
\]

and

\[
\boxed{
w=wN12\_of\_aux(x,y)
=
\frac{y}{8}\left(1-\frac{16}{x^2}\right).
}
\]

In one compositional block:

```lean
def u12_from_tate_and_T (a xT : ℚ) : ℚ :=
  let eta := eta12 a xT
  let x := xAux12 a eta
  uN12_of_aux x

def w12_from_tate_and_T (a xT : ℚ) : ℚ :=
  let eta := eta12 a xT
  let x := xAux12 a eta
  let y := yAux12 a eta
  wN12_of_aux x y
```

Then the main implication is:

```lean
theorem EN12_point_of_Q12_root
    (a xT : ℚ)
    (hQ : Q12 a xT = 0) :
    (w12_from_tate_and_T a xT)^2
      =
    (u12_from_tate_and_T a xT)^3
      - (u12_from_tate_and_T a xT)^2
      - 4 * (u12_from_tate_and_T a xT)
      + 4 := by
  -- expand definitions
  -- use eta12_sq_sub and hQ
  -- use aux12_curve_identity
  -- use isogeny12_to_EN12_identity
```

This is the cleanest Lean route: three small identities rather than one enormous `field_simp`.

---

## 7. Why there is no \(b_{12}(u),c_{12}(u)\) depending only on final \(u\)

The final curve

\[
E_{N12}: w^2=u^3-u^2-4u+4
\]

is reached after a \(2\)-isogeny. The Tate parameter \(\alpha\) is recovered from the final \((u,w)\) by the rational formula

\[
\boxed{
\alpha
=
\frac{
2u(u-4)(u-1)
}
{
4u^3+u^2w-12u^2-2uw+4w+8
}.
}
\]

So \(\alpha\) genuinely depends on \(w\), not only on \(u\). Consequently the correct inverse parametrization is

\[
b=b_{12}(\alpha(u,w)),
\qquad
c=c_{12}(\alpha(u,w)),
\]

not \(b=b_{12}(u)\), \(c=c_{12}(u)\).

That is the structural difference from your verified \(N=10\) algebra.

---

## 8. Degenerate values

The obstruction curve is

\[
E_{N12}: w^2=(u-1)(u-2)(u+2).
\]

The degenerate rational \(u\)-values are

\[
\boxed{
u\in\{-2,0,1,2,4\}.
}
\]

Explicitly:

\[
u=-2,1,2 \Rightarrow w=0,
\]

\[
u=0 \Rightarrow w=\pm2,
\]

\[
u=4 \Rightarrow w=\pm6.
\]

On the Tate side these correspond to degeneracies such as

\[
\alpha=0,\qquad \alpha=1,
\]

or to points where the displayed inverse formula for \(\alpha(u,w)\) hits the dual-isogeny kernel. In particular, nondegenerate Tate data with exact order \(12\), nonsingular curve, and independent \(2\)-torsion should land outside

\[
\{-2,0,1,2,4\}.
\]

For Lean, I would prove nondegeneracy by contradiction: assume the constructed \(u\) equals one of those five values, use the explicit formulas above plus denominator hypotheses to force one of the Tate degeneracies

\[
\alpha=0,\quad \alpha=1,\quad 2\alpha-1=0,\quad b=0,\quad c=0,
\]

or \(x_T=x(6P)\), contradicting exact order \(12\) and independence of \(T\).
