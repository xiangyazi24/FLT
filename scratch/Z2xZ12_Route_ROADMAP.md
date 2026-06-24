I’ll first verify whether the repo’s $E_{N12}$ is the actual $X_1(2,12)$ model or an isogenous curve, then derive Lean-ready rational maps only after that identification is secure.

The Derickx–Sutherland model is tiny, $v^2+(r^2+1)v+1=0$, equivalently a genus-one quartic after completing the square. It includes explicit universal $q,t$ data, so the forward map should reduce to direct algebra.

Verdict
N12 is tractable. It is not mis-modeled like the N16 case.
The actual genus-1 modular curve $X_1(2,12)$ is


$$E_X:\quad V^2=U^3-U^2+U,$$


with Cremona label 24a4 in the source model and


$$j(E_X)=\frac{2048}{3}.$$


The repo’s curve


$$E_{N12}:\quad w^2=u^3-u^2-4u+4$$


has


$$j(E_{N12})=\frac{35152}{9},$$


and is 2-isogenous to $E_X$, not isomorphic to it. This is fine: the forward direction can use the explicit 2-isogeny. The MIT/Sutherland model file for $X_1(2,12)$ gives exactly


$$V^2-U^3+U^2-U=0$$


and lists it as elliptic curve 24a4, with universal parameters $q,t$ and universal curve data. MIT Mathematics The repo curve $[0,-1,0,-4,4]$ is in the conductor-24 isogeny class and has $j=35152/9$. LMFDB+1
So the clean route is:


$$\text{Tate }(b,c,x_T)
\longrightarrow (q,t)
\longrightarrow (U,V)\in E_X
\overset{2\text{-isog}}{\longrightarrow}
(u,w)\in E_{N12}.$$


No modular-curve geometry obstruction appears.

1. Correct curve and isogeny
The true $X_1(2,12)$ elliptic model is


$$E_X:\quad V^2=U^3-U^2+U.$$


Its coefficients are


$$[0,-1,0,1,0],$$


so


$$b_2=-4,\qquad b_4=2,\qquad b_6=0,\qquad b_8=-1,$$




$$c_4=-32,\qquad \Delta=-48,$$


hence


$$j(E_X)=\frac{c_4^3}{\Delta}
      =\frac{(-32)^3}{-48}
      =\frac{2048}{3}.$$


The repo curve is


$$E_{N12}:\quad w^2=u^3-u^2-4u+4.$$


Its coefficients are


$$[0,-1,0,-4,4],$$


so


$$c_4=208,\qquad \Delta=2304,$$


hence


$$j(E_{N12})=\frac{208^3}{2304}=\frac{35152}{9}.$$


The explicit 2-isogeny is the quotient of


$$E_X:\quad V^2=U^3-U^2+U$$


by the rational 2-torsion point $(0,0)$. For a curve


$$Y^2=X^3+aX^2+bX,$$


the quotient by $(0,0)$ is


$$Y'^2=X'^3-2aX'^2+(a^2-4b)X',$$


with map


$$X'=\frac{Y^2}{X^2}=X+a+\frac{b}{X},\qquad
Y'=\frac{Y(X^2-b)}{X^2}.$$


Here $a=-1,b=1$, so the quotient is


$$Y'^2=X'^3+2X'^2-3X'.$$


Now translate


$$u=X'+1,\qquad w=Y'.$$


Then


$$w^2=(u-1)^3+2(u-1)^2-3(u-1)
    =u^3-u^2-4u+4.$$


Thus the isogeny $E_X\to E_{N12}$ is


$$\boxed{
u=U+\frac1U
}$$


and


$$\boxed{
w=\frac{V(U^2-1)}{U^2}.
}$$


Lean identity:
lean-- assuming V^2 = U^3 - U^2 + U and U ≠ 0u := U + 1 / Uw := V * (U^2 - 1) / U^2-- thenw^2 = u^3 - u^2 - 4*u + 4
More precisely,


$$w^2-(u^3-u^2-4u+4)
=
\frac{(U-1)^2(U+1)^2}{U^4}
\left(V^2-(U^3-U^2+U)\right).$$


That is the clean field_simp; ring certificate.

2. Explicit map from Tate $b,c,x_T$
Start with the Tate normal form


$$E_{b,c}:\quad
Y^2+(1-c)XY-bY=X^3-bX^2,$$


with $P=(0,0)$ of exact order $12$, and let


$$T=(x_T,y_T)$$


be the independent rational 2-torsion point. The 2-torsion condition gives


$$2y_T+(1-c)x_T-b=0.$$


So you only need $x=x_T$.
Define


$$\boxed{
q=\frac{cx}{x-b}
}$$


and


$$\boxed{
t=\frac{b(b-x)}
        {-b^2+2bx+(c-1)x^2}.
}$$


These are the same $q,t$ parameters used in the standard $X_1(2,12)$ model.
The universal $X_1(2,12)$ file uses


$$q=V$$


and


$$t=\frac{4V}{UV^2-U-3V^2-1}.$$


Solving this for $U$, with $V=q$, gives


$$\boxed{
V=q
}$$


and


$$\boxed{
U=\frac{4q+t(3q^2+1)}{t(q^2-1)}.
}$$


For Lean, introduce
leandef q12 (b c x : ℚ) : ℚ :=  c * x / (x - b)def t12 (b c x : ℚ) : ℚ :=  b * (b - x) / (-b^2 + 2*b*x + (c - 1)*x^2)
Then
leandef A12 (q t : ℚ) : ℚ :=  4*q + t*(3*q^2 + 1)def B12 (q t : ℚ) : ℚ :=  t*(q^2 - 1)
so
leanU = A12 q t / B12 q tV = q
and the final repo coordinates are


$$\boxed{
u=\frac{A^2+B^2}{AB}
}$$




$$\boxed{
w=\frac{q(A^2-B^2)}{A^2}
}$$


where


$$A=4q+t(3q^2+1),\qquad B=t(q^2-1).$$


Fully expanded as a composition:
leanlet q := q12 b c xTlet t := t12 b c xTlet A := 4*q + t*(3*q^2 + 1)let B := t*(q^2 - 1)u := (A^2 + B^2) / (A * B)w := q * (A^2 - B^2) / A^2
This is the explicit map you want.

3. The polynomial identity
The $q,t$ relation for $X_1(2,12)$ is


$$\begin{aligned}
R_{12}(q,t)={}&
-q^8t^3
+24q^6t^3
+88q^5t^2
+22q^4t^3
+128q^4t \\
&+80q^3t^2
+64q^3
+16q^2t^3
+64q^2t
+24qt^2
+3t^3.
\end{aligned}$$


With


$$A=4q+t(3q^2+1),\qquad B=t(q^2-1),$$


one has


$$U=\frac AB,\qquad V=q,$$


and the exact identity


$$\boxed{
V^2-(U^3-U^2+U)
=
-\frac{R_{12}(q,t)}{B^3}.
}$$


Equivalently,


$$q^2-\left(\frac AB\right)^3
+\left(\frac AB\right)^2
-\frac AB
=
-\frac{R_{12}(q,t)}{B^3}.$$


After applying the 2-isogeny to $E_{N12}$, the combined identity is


$$\boxed{
w^2-(u^3-u^2-4u+4)
=
-\frac{(A-B)^2(A+B)^2}{A^4B^3}
\,R_{12}(q,t).
}$$


This is the main Lean lemma:
leanlemma N12_map_identity (q t : ℚ)    (hA : A12 q t ≠ 0)    (hB : B12 q t ≠ 0) :  let A := A12 q t  let B := B12 q t  let u := (A^2 + B^2) / (A * B)  let w := q * (A^2 - B^2) / A^2  w^2 - (u^3 - u^2 - 4*u + 4)    =  - ((A - B)^2 * (A + B)^2 * R12 q t)      / (A^4 * B^3) := by  field_simp [A12, B12, R12, hA, hB]  ring
Then R12 q t = 0 closes the target curve equation.

4. Why $R_{12}(q,t)=0$ follows from Tate order 12 plus independent 2-torsion
The useful inverse formulas are:


$$\boxed{
b=\frac{t(q-1)^3(qt+1)}{4(t+1)^2}
}$$




$$\boxed{
c=\frac{q(qt+1)}{t+1}
}$$




$$\boxed{
x_T=-\frac{(q-1)^2(qt+1)}{4(t+1)}.
}$$


These come from taking the full-2 universal curve


$$Y^2=X^3+(t^2-2qt-2)X^2-(t^2-1)(qt+1)^2X$$


with


$$Q=((t+1)(qt+1),\ t(t+1)(qt+1)),$$


then translating $Q$ to the origin and scaling into Tate normal form.
The tangent slope at $Q$ is


$$\lambda=qt+t+1.$$


The translated coefficients before scaling are


$$A_1=2(qt+t+1),$$




$$A_2=-t(q-1)(qt+1),$$




$$A_3=2t(t+1)(qt+1).$$


The scaling factor is


$$\rho=\frac{A_3}{A_2}
     =-\frac{2(t+1)}{q-1}.$$


Then


$$b=-\frac{A_2^3}{A_3^2}
  =
\frac{t(q-1)^3(qt+1)}{4(t+1)^2},$$




$$c=1-\frac{A_1}{\rho}
  =
\frac{q(qt+1)}{t+1},$$


and the independent 2-torsion point $(0,0)$ in the full-2 model maps to


$$x_T=-\frac{(q-1)^2(qt+1)}{4(t+1)}.$$


Solving these three equations gives exactly


$$q=\frac{cx_T}{x_T-b},$$




$$t=\frac{b(b-x_T)}
        {-b^2+2bx_T+(c-1)x_T^2}.$$


So the Tate-to-$(q,t)$ formulas are not guessed; they are the inverse of the standard universal $X_1(2,12)$ construction.

5. The Tate order-12 polynomial and the branch issue
Using the Tate multiples, the condition that $6P$ is 2-torsion gives


$$\Phi_{12}(b,c)=0$$


where


$$\boxed{
\Phi_{12}(b,c)
=
3b^4-b^3c^2-9b^3c+10b^2c^2
+bc^4-5bc^3+c^6+c^4.
}$$


The $x$-coordinate of $6P$ on the Tate curve is


$$\boxed{
x(6P)
=
\frac{(b-c)(b^2-bc-c^3)}
     {(b-c^2-c)^2}.
}$$


The full 2-torsion cubic is


$$\boxed{
4x^3+\big((1-c)^2-4b\big)x^2
+2b(c-1)x+b^2=0.
}$$


Under $\Phi_{12}=0$, one root is $x(6P)$. The other two roots are the independent 2-torsion choices.
This is exactly where the branch split appears. Pulling $\Phi_{12}$ back through the inverse $q,t$-parametrization gives


$$\boxed{
\Phi_{12}(b(q,t),c(q,t))
=
\frac{(qt+1)^4}{256(t+1)^8}
\,R_{12}(q,t)\,K_{12}(q,t),
}$$


where


$$\boxed{
K_{12}(q,t)=q^4t+4q^3+6q^2t+4q+t.
}$$


The $K_{12}=0$ branch is the bad branch corresponding to choosing the 2-torsion point $6P$. Your hypothesis $T\neq 6P$ selects the $R_{12}=0$ branch.
So the Lean proof should be:
leanhave hprod : R12 q t * K12 q t = 0 := by  -- field_simp using Phi12(b,c)=0,  -- q = c*x/(x-b), t = b*(b-x)/(...)  -- and the 2-torsion cubic for xhave hKne : K12 q t ≠ 0 := by  -- K12=0 forces x = tateX6 b c,  -- hence T = 6 • P, contradiction to independencehave hR : R12 q t = 0 := by  exact eq_zero_of_mul_eq_zero_left hprod hKne
That is the one real branch-management step.
It is still elementary algebra: no Chabauty, no modular forms, no genus $>1$ geometry.

6. Nondegeneracy and bad $u$-values
The repo excludes


$$u\in\{-2,0,1,2,4\}.$$


On


$$E_{N12}: w^2=(u-1)(u-2)(u+2),$$


the values


$$u=-2,\quad u=1,\quad u=2$$


are the three rational 2-torsion points. The remaining two values


$$u=0,\quad u=4$$


give the other rational torsion points:


$$(0,\pm2),\qquad (4,\pm6).$$


Thus the bad set is exactly the finite affine rational torsion/cusp image set on the repo curve.
In the map above,


$$u=\frac{A^2+B^2}{AB}
  =
U+\frac1U.$$


So:


$$u=2 \iff (A-B)^2=0,$$




$$u=-2 \iff (A+B)^2=0,$$




$$u=0 \iff A^2+B^2=0,$$




$$u=1 \iff A^2-AB+B^2=0,$$




$$u=4 \iff A^2-4AB+B^2=0.$$


With


$$A=4q+t(3q^2+1),\qquad B=t(q^2-1),$$


the first two simplify to


$$A-B=2\big(q^2t+2q+t\big),$$




$$A+B=4q(qt+1).$$


On the $R_{12}=0$ branch, each bad equality forces a cusp/degenerate condition. The useful resultant checks are:


$$\operatorname{Res}_t(R_{12},A+B)
=
-64q^3(q-1)^3(q+1)^3(q^2+3),$$




$$\operatorname{Res}_t(R_{12},A-B)
=
-64q^3(q-1)^4(q+1)^4,$$




$$\operatorname{Res}_t(R_{12},A^2+B^2)
=
4096q^6(q-1)^8(q+1)^8,$$




$$\operatorname{Res}_t(R_{12},A^2-AB+B^2)
=
4096q^{10}(q-1)^6(q+1)^6,$$




$$\operatorname{Res}_t(R_{12},A^2-4AB+B^2)
=
4096q^6(q-1)^6(q+1)^6
(q^2-6q-3)(q^2+6q-3).$$


For rational $q$, the extra factors $q^2+3$, $q^2-6q-3$, and $q^2+6q-3$ have no rational roots. The remaining possibilities are $q=0,\pm1$, and those force degeneracies in the Tate data:


$$q=0 \implies cx_T=0,$$




$$q=1 \implies b=(1-c)x_T,$$




$$q=-1 \implies b=(1+c)x_T.$$


Using the 2-torsion cubic and the usual nonzero hypotheses $b\neq0$, $c\neq0$, $x_T\neq0$, these contradict nonsingularity/exact order/independence. For example:


$$q=1$$


gives $b=(1-c)x_T$, and substituting into the 2-torsion cubic gives


$$4cx_T^3=0,$$


impossible in the nondegenerate case. Similarly,


$$q=-1$$


gives $b=(1+c)x_T$, and the cubic gives


$$-4cx_T^2(-c+x_T)=0;$$


the remaining $x_T=c$ branch makes


$$\Phi_{12}(c(c+1),c)=2c^8,$$


again impossible for $c\neq0$.
So the bad $u$-values are removable by finite algebra.

7. Lean implementation plan
The shortest forward proof is not to parametrize $b,c$ alone. Use $x_T$.
Define:
leandef R12 (q t : ℚ) : ℚ :=  -q^8*t^3  + 24*q^6*t^3  + 88*q^5*t^2  + 22*q^4*t^3  + 128*q^4*t  + 80*q^3*t^2  + 64*q^3  + 16*q^2*t^3  + 64*q^2*t  + 24*q*t^2  + 3*t^3def q12 (b c x : ℚ) : ℚ :=  c*x / (x - b)def t12 (b c x : ℚ) : ℚ :=  b*(b - x) / (-b^2 + 2*b*x + (c - 1)*x^2)def A12 (q t : ℚ) : ℚ :=  4*q + t*(3*q^2 + 1)def B12 (q t : ℚ) : ℚ :=  t*(q^2 - 1)def uN12 (b c x : ℚ) : ℚ :=  let q := q12 b c x  let t := t12 b c x  let A := A12 q t  let B := B12 q t  (A^2 + B^2) / (A*B)def wN12 (b c x : ℚ) : ℚ :=  let q := q12 b c x  let t := t12 b c x  let A := A12 q t  let B := B12 q t  q * (A^2 - B^2) / A^2
Prove the generic target identity first:
leanlemma N12_target_identity    (q t : ℚ)    (hA : A12 q t ≠ 0)    (hB : B12 q t ≠ 0) :  let A := A12 q t  let B := B12 q t  let u := (A^2 + B^2) / (A*B)  let w := q * (A^2 - B^2) / A^2  w^2 - (u^3 - u^2 - 4*u + 4)    =  - ((A - B)^2 * (A + B)^2 * R12 q t)      / (A^4 * B^3) := by  field_simp [A12, B12, R12, hA, hB]  ring
Then prove:
leanlemma R12_of_tate_order12_independent_2torsion :  R12 (q12 b c xT) (t12 b c xT) = 0
using:
leanPhi12 b c = 0tateTwoTorsionCubic b c xT = 0xT ≠ tateX6 b c
The only slightly annoying step is the branch split:
leanK12(q,t)=0 ↔ xT = tateX6 b c
under the denominators and equations. That is the N12 analogue of the “independent 2-torsion selects the residual factor” step. It is much easier than N16 because the residual model is genus 1 and the map is already explicit.

Bottom line
Yes, Z2×Z12 forward is a good next target.
The repo’s $E_{N12}$ is not literally $X_1(2,12)$, but it is the correct 2-isogenous target:


$$X_1(2,12):\quad V^2=U^3-U^2+U,\qquad j=\frac{2048}{3},$$




$$E_{N12}:\quad w^2=u^3-u^2-4u+4,\qquad j=\frac{35152}{9}.$$


The explicit map is:


$$q=\frac{cx_T}{x_T-b},$$




$$t=\frac{b(b-x_T)}
        {-b^2+2bx_T+(c-1)x_T^2},$$




$$A=4q+t(3q^2+1),\qquad B=t(q^2-1),$$




$$\boxed{
u=\frac{A^2+B^2}{AB},
\qquad
w=\frac{q(A^2-B^2)}{A^2}.
}$$


And the key identity is:


$$w^2-(u^3-u^2-4u+4)
=
-\frac{(A-B)^2(A+B)^2}{A^4B^3}R_{12}(q,t).$$


So once you prove $R_{12}(q,t)=0$ from the Tate order-12 condition plus $T\neq6P$, the rest is pure field_simp + ring.
