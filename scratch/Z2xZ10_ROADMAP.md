The clean route is **elementary after one normal-form step**. The hard gap is not modular-curve theory per se; it is formalizing the Tate-normal-form reduction from an arbitrary `WeierstrassCurve ℚ` plus a point of order `10` to explicit rational parameters `b,c`. Once you are in Tate normal form, the map to

\[
E_{20}:\quad w^2=u^3+u^2-u
\]

is just rational algebra.

Mathlib currently gives a computational Weierstrass-curve structure, invariants, `twoTorsionPolynomial`, and `IsElliptic`; the docs explicitly describe the two-torsion polynomial as the cubic whose roots are the \(X\)-coordinates of nonzero 2-torsion over a splitting field. citeturn205891view0 It also has affine nonsingular points and an abelian group law in `WeierstrassCurve.Affine.Point`. citeturn743118view0 I would not expect Mathlib to already contain Tate normal form, Kubert’s \(X_1(N)\) tables, or an \(X_1(2,10)\) modular-curve model. The classical Tate-normal-form fact that curves with a point of order \(n\), for \(4\le n\le10\) or \(n=12\), lie in a one-parameter family is standard, but it is not the same thing as having it formalized in Mathlib. citeturn833226academia1

---

## 1. Tate normal form and the exact order-10 parameter

Put the curve with a chosen point \(P\) of order \(10\) into Tate normal form

\[
E(b,c):\qquad y^2+(1-c)xy-by=x^3-bx^2,
\]

with

\[
P=(0,0).
\]

Here

\[
a_1=1-c,\qquad a_2=-b,\qquad a_3=-b,\qquad a_4=0,\qquad a_6=0.
\]

On this model, direct group-law calculation gives

\[
2P=(b,bc),
\]

\[
3P=(c,b-c),
\]

\[
4P=\left(\frac{b(b-c)}{c^2},
-\frac{b^2(b-c^2-c)}{c^3}\right),
\]

and

\[
5P=
\left(
-\frac{bc(b-c^2-c)}{(b-c)^2},
\frac{bc^2(b^2-bc-c^3)}{(b-c)^3}
\right).
\]

The point \(5P\) is 2-torsion exactly when

\[
2y(5P)+(1-c)x(5P)-b=0.
\]

After clearing the harmless factor \(-b/(b-c)^3\), this is equivalent to

\[
\Phi_{10}(b,c)=0,
\]

where

\[
\boxed{
\Phi_{10}(b,c)
=
b^3-3b^2c^2-2b^2c+bc^4+3bc^3+bc^2+c^5.
}
\]

For exact order \(10\), one also needs the usual nondegeneracy conditions

\[
b\ne0,\qquad c\ne0,\qquad b-c\ne0,
\]

and the curve discriminant nonzero. In practice these are forced by the fact that \(P\) has exact order \(10\) on a nonsingular curve.

---

## 2. Parametrize the order-10 condition

Set

\[
d=\frac bc.
\]

Then \(\Phi_{10}(b,c)=0\), divided by \(c^3\), becomes

\[
(d+1)c^2+3d(1-d)c+d(d-1)^2=0.
\]

The discriminant in \(c\) is

\[
d(d-1)^2(5d-4).
\]

Define

\[
r=
\frac{2(d+1)c-3d(d-1)}{d-1}.
\]

Then

\[
r^2=d(5d-4).
\]

Parametrize the conic \(r^2=d(5d-4)\) through the rational point \((d,r)=(1,1)\). Put

\[
t=\frac{r-1}{d-1},
\qquad
u=2-t.
\]

Then the Tate parameters become

\[
\boxed{
c=\frac{(u-1)(u+1)}{u(u^2-4u-1)}
}
\]

and

\[
\boxed{
b=\frac{(u-1)^3(u+1)}{u(u^2-4u-1)^2}.
}
\]

Equivalently, directly from \(b,c\),

\[
\boxed{
u=
\frac{5b^2-2bc^2-6bc-2c^3+c^2}{(b-c)^2}.
}
\]

This is the concrete \(X_1(10)\) Tate parameter rewritten in the coordinate that will become the \(u\)-coordinate on \(E_{20}\).

The values

\[
u=-1,\quad u=0,\quad u=1
\]

are degenerate/cuspidal in this family:

\[
u=\pm1 \implies b=0,
\]

so \(P=(0,0)\) is not a point of exact order \(10\), and

\[
u=0
\]

is a pole of the Tate parameterization. Thus a genuine elliptic curve with a genuine order-10 point gives

\[
u\notin\{-1,0,1\}.
\]

---

## 3. Add the independent rational 2-torsion point

The two-torsion polynomial of \(E(b,c)\) is

\[
F_{b,c}(X)
=
4X^3+\bigl((1-c)^2-4b\bigr)X^2+2b(c-1)X+b^2.
\]

This is the specialization of Mathlib’s `twoTorsionPolynomial`.

The known rational 2-torsion point \(5P\) has \(x\)-coordinate

\[
x_5
=
-\frac{bc(b-c^2-c)}{(b-c)^2}.
\]

After substituting the \(u\)-parameterized values of \(b,c\), this becomes

\[
\boxed{
x_5(u)=
-\frac{(u-1)^3(u+1)}{4u^2(u^2-4u-1)}.
}
\]

The cubic factors as

\[
F_u(X)=(X-x_5(u))Q_u(X),
\]

where

\[
\boxed{
Q_u(X)
=
4X^2
-
\frac{8(u^3-3u^2-u+1)}{(u^2-4u-1)^2}X
+
\frac{4(u-1)^3(u+1)}{(u^2-4u-1)^3}.
}
\]

Now use the extra \(Z/2\) in \(Z/2\times Z/10\). Let \(T\) be the independent rational 2-torsion point, distinct from \(5P\). In Tate coordinates, write its \(x\)-coordinate as \(x_T\). Since \(T\) is 2-torsion,

\[
F_u(x_T)=0.
\]

Since \(T\ne5P\), we have

\[
x_T\ne x_5(u),
\]

hence

\[
Q_u(x_T)=0.
\]

Now define

\[
\boxed{
w=
\frac{(u^2-4u-1)^2x_T-(u^3-3u^2-u+1)}{2}.
}
\]

The key identity is

\[
\boxed{
w^2-(u^3+u^2-u)
=
\frac{(u^2-4u-1)^4}{16}\,Q_u(x_T).
}
\]

So from \(Q_u(x_T)=0\), one gets

\[
\boxed{
w^2=u^3+u^2-u.
}
\]

That is the desired point on \(E_{20}\).

This is the cleanest algebraic bridge. No modular forms, no abstract modular curves, no division-polynomial API beyond the 2-torsion polynomial.

---

## 4. Lean-shaped algebra package

The core algebra can be packaged like this.

```lean
def b10 (u : ℚ) : ℚ :=
  ((u - 1)^3 * (u + 1)) / (u * (u^2 - 4*u - 1)^2)

def c10 (u : ℚ) : ℚ :=
  ((u - 1) * (u + 1)) / (u * (u^2 - 4*u - 1))

def x5_10 (u : ℚ) : ℚ :=
  - ((u - 1)^3 * (u + 1)) / (4 * u^2 * (u^2 - 4*u - 1))

def Q10 (u X : ℚ) : ℚ :=
  4 * X^2
  - (8 * (u^3 - 3*u^2 - u + 1) / (u^2 - 4*u - 1)^2) * X
  + 4 * (u - 1)^3 * (u + 1) / (u^2 - 4*u - 1)^3

def w10 (u xT : ℚ) : ℚ :=
  ((u^2 - 4*u - 1)^2 * xT - (u^3 - 3*u^2 - u + 1)) / 2
```

The main `ring` identity is:

```lean
lemma w10_sq_sub_E20
    (u xT : ℚ) :
    w10 u xT ^ 2 - (u^3 + u^2 - u)
      =
    ((u^2 - 4*u - 1)^4 / 16) * Q10 u xT := by
  unfold w10 Q10
  field_simp
  ring
```

Then:

```lean
lemma E20_point_of_Q10_root
    (u xT : ℚ)
    (hQ : Q10 u xT = 0) :
    (w10 u xT)^2 = u^3 + u^2 - u := by
  have h :=
    w10_sq_sub_E20 u xT
  rw [hQ, mul_zero] at h
  linarith
```

You will need denominator hypotheses for `field_simp`, especially

```lean
u ≠ 0
u^2 - 4*u - 1 ≠ 0
```

In the actual proof these come from the Tate parameterization/nondegenerate order-10 data. Over `ℚ`, the second also follows from

\[
u^2-4u-1=0 \Rightarrow (u-2)^2=5,
\]

which is impossible rationally.

---

## 5. Wrapper from `ZMod 2 × ZMod 10`

From

```lean
∃ f : (ZMod 2 × ZMod 10) →+ (E⁄ℚ).Point, Function.Injective f
```

extract

\[
P=f(0,1),\qquad T=f(1,0).
\]

Then:

\[
P\text{ has exact order }10,
\]

\[
5P=f(0,5)\text{ is nonzero 2-torsion},
\]

\[
T=f(1,0)\text{ is nonzero 2-torsion},
\]

and

\[
T\ne5P
\]

because \((1,0)\ne(0,5)\) in \(Z/2\times Z/10\).

Thus \(E(\mathbb Q)\) has a point \(P\) of exact order \(10\) and an independent rational 2-torsion point \(T\).

The clean formalization split is:

```lean
theorem injective_Z2xZ10_gives_order10_and_independent_2torsion :
  ... →
  ∃ P T : (E⁄ℚ).Point,
    orderOf P = 10 ∧
    2 • T = 0 ∧ T ≠ 0 ∧
    T ≠ 5 • P
```

Then prove a normal-form theorem:

```lean
theorem order10_point_to_tate_normal_form :
  ∃ b c : ℚ,
    TateCurve b c
    ∧ P_maps_to_origin
    ∧ P_has_order10_on_tate
    ∧ T_maps_to_some_2torsion_x xT
```

This is the largest formalization gap.

---

## 6. Explicit normal-form formulas from an arbitrary Weierstrass model

Suppose

\[
E:\quad y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6
\]

and \(P=(x_0,y_0)\) has order \(10\). Since \(P\) is not 2-torsion,

\[
2y_0+a_1x_0+a_3\ne0.
\]

Let

\[
s=
\frac{3x_0^2+2a_2x_0+a_4-a_1y_0}
     {2y_0+a_1x_0+a_3}.
\]

Use the change

\[
x=X+x_0,\qquad
y=Y+sX+y_0.
\]

Then \(P\) becomes \((0,0)\), and its tangent is \(Y=0\). The transformed coefficients satisfy

\[
a_6'=0,\qquad a_4'=0,
\]

and

\[
a_1'=a_1+2s,
\]

\[
a_2'=a_2-sa_1+3x_0-s^2,
\]

\[
a_3'=a_3+a_1x_0+2y_0.
\]

For an order-10 point, \(a_2'\ne0\) and \(a_3'\ne0\). Now scale with

\[
\rho=\frac{a_3'}{a_2'}.
\]

After

\[
X=\rho^2X',\qquad Y=\rho^3Y',
\]

the coefficients become

\[
a_2''=a_3''=\frac{(a_2')^3}{(a_3')^2}.
\]

Thus the Tate parameters are

\[
\boxed{
b=-\frac{(a_2')^3}{(a_3')^2},
}
\]

\[
\boxed{
c=1-\frac{a_1'a_2'}{a_3'}.
}
\]

The transformed \(x\)-coordinate of the independent 2-torsion point \(T=(x_T^{old},y_T^{old})\) is

\[
\boxed{
x_T=
\frac{x_T^{old}-x_0}{\rho^2}.
}
\]

Then use

\[
u=
\frac{5b^2-2bc^2-6bc-2c^3+c^2}{(b-c)^2}
\]

and

\[
w=
\frac{(u^2-4u-1)^2x_T-(u^3-3u^2-u+1)}{2}.
\]

That gives the requested rational point

\[
w^2=u^3+u^2-u.
\]

The proof of this final equation is the single identity above involving \(Q_u(x_T)\).

---

## 7. Honest assessment

This is tractable as elementary algebra **after** you build the Tate-normal-form layer.

The genuinely missing Mathlib/project infrastructure is:

1. extracting affine coordinates from nonzero points of `(E⁄ℚ).Point`;
2. proving the coordinate change to Tate normal form preserves the group law/order;
3. proving the explicit multiples \(2P,3P,4P,5P\) on Tate normal form;
4. proving the order-10 parameterization \(\Phi_{10}=0 \Rightarrow b=b_{10}(u), c=c_{10}(u)\);
5. proving the independent 2-torsion point gives a root of \(Q_u\).

Items 3–5 are mostly `field_simp` plus `ring`.

Item 2 is the real engineering cost. It is still elementary, but not a one-line algebra proof from the existing `WeierstrassCurve` API.

The best formalization strategy is therefore:

```text
ZMod 2 × ZMod 10 injection
  → exact order-10 point P and independent 2-torsion T
  → Tate normal form E(b,c), P=(0,0)
  → Φ₁₀(b,c)=0
  → u = (5b² - 2bc² - 6bc - 2c³ + c²)/(b-c)²
  → b=b10(u), c=c10(u)
  → T supplies xT root of Q10(u, X)
  → w = ((u² - 4u - 1)² xT - (u³ - 3u² - u + 1))/2
  → w² = u³ + u² - u
  → u ∉ {-1,0,1}
```

So the answer is: **yes, the forward direction can be reduced to pure algebra**, but only after you add a Tate-normal-form normalization theorem. Without that theorem, the original statement over arbitrary `WeierstrassCurve ℚ` still hides a substantial formalization gap.
