# Q1935 (dm2): N=16 quartic descent and the N=10 quadratic twist

## Verdict

Yes: the N=16 quartic

\[
s^4-D^2s^2-D^4=t^2
\]

admits essentially the same infinite descent as the N=10 quartic

\[
s^4+D^2s^2-D^4=t^2.
\]

But I would **not** try to reuse the already-proved N=10 theorem by the quadratic twist relation.  The twist explains why the two obstruction curves have the same \(j\)-invariant, but it does not transport the existing integral/rational descent theorem over \(\mathbb Z\) into the N=16 statement over \(\mathbb Z\).  The twist sends the N=16 quartic to the N=10 quartic only after adjoining \(i\), i.e. after replacing \(s\) by \(i s\).  Your existing `QuarticDescent.lean` proof over integers will not apply directly to Gaussian-integer data.

The clean formalization path is instead:

1. copy/refactor the common N=10 descent infrastructure;
2. introduce a sign parameter \(\varepsilon\in\{1,-1\}\) where possible;
3. specialize \(\varepsilon=1\) for N=10 and \(\varepsilon=-1\) for N=16.

The sign-parametric identity is the key:

\[
t^2=s^4+\varepsilon D^2s^2-D^4
\quad\Longrightarrow\quad
(2s^2+\varepsilon D^2-2t)(2s^2+\varepsilon D^2+2t)=5D^4.
\]

For N=16, \(\varepsilon=-1\), so the center is \(2s^2-D^2\), not \(2s^2+D^2\).

## The obstruction-curve reduction

For N=16, set

\[
u=\left(\frac{s}{D}\right)^2,\qquad
w=\frac{s t}{D^3}.
\]

Then

\[
t^2=s^4-D^2s^2-D^4
\]

implies

\[
w^2=u^3-u^2-u.
\]

For N=10, the same substitution gives

\[
w^2=u^3+u^2-u.
\]

The two curves

\[
E_{10}: y^2=x^3+x^2-x,
\qquad
E_{16}: y^2=x^3-x^2-x
\]

have the same \(j\)-invariant and are quadratic twists by \(-1\).  In the usual model

\[
y^2=x^3+a x^2+b x,
\]

the \(d\)-quadratic twist is

\[
y^2=x^3+d a x^2+d^2 b x.
\]

With \(a=1,b=-1,d=-1\), this gives \(E_{16}\).

Equivalently, over \(\mathbb Q(i)\), the isomorphism is

\[
(x,y)\mapsto (-x, i y).
\]

At the quartic level, this is exactly the substitution

\[
S=i s,
\]

because

\[
S^4+D^2S^2-D^4=s^4-D^2s^2-D^4.
\]

That is why the twist is conceptually right but formally awkward: it proves that an N=16 integer solution gives an N=10 solution over \(\mathbb Z[i]\), not over \(\mathbb Z\).  Unless you want to rebuild the N=10 descent over the Gaussian integers, the twist is not the cheapest reuse mechanism.

## Direct N=16 descent skeleton

Assume a primitive positive solution

\[
s>0,\quad D>0,\quad \gcd(s,D)=1,\quad
s^4-D^2s^2-D^4=t^2.
\]

Replace \(t\) by \(|t|\) if needed.  Define

\[
U=2s^2-D^2-2t,\qquad
V=2s^2-D^2+2t.
\]

Then

\[
UV=5D^4.
\]

The positivity proof is parallel to N=10: from \(t^2=s^4-D^2s^2-D^4>0\), one gets \(s^2>\frac{1+\sqrt5}{2}D^2\), hence \(2s^2-D^2>2|t|\).  Thus \(U,V>0\).

The coprimality proof for \(U,V\) is also the same kind of argument as in N=10.  Once the coprime fourth-power factorization is applied, after choosing the orientation with the factor \(5\), you get

\[
U=a^4,\qquad V=5b^4,\qquad D=ab,\qquad \gcd(a,b)=1.
\]

Now sum the two factor equations:

\[
a^4+5b^4=4s^2-2D^2=4s^2-2a^2b^2.
\]

Therefore

\[
4s^2=a^4+2a^2b^2+5b^4=(a^2+b^2)^2+4b^4.
\]

So

\[
(a^2+b^2)^2+(2b^2)^2=(2s)^2.
\]

This is the N=16 analogue of the N=10 Pythagorean step.  The only sign change is:

```text
N=10: h = a^2 - b^2
N=16: h = a^2 + b^2
```

Parametrize the primitive Pythagorean triple:

\[
a^2+b^2=p^2-q^2,\qquad b^2=pq,\qquad s=p^2+q^2.
\]

Since \(\gcd(p,q)=1\) and \(pq=b^2\), both \(p\) and \(q\) are squares up to the usual positivity convention.  Write, after renaming,

\[
p=P^2,\qquad q=Q^2,\qquad b=PQ.
\]

Then

\[
a^2+b^2=P^4-Q^4,\qquad b^2=P^2Q^2,
\]

hence

\[
a^2=P^4-P^2Q^2-Q^4.
\]

Thus

\[
P^4-Q^2P^2-Q^4=a^2,
\]

which is the same N=16 quartic again, with the smaller parameter \(Q\).  Since the old parameter is

\[
D=ab=aPQ,
\]

and \(P,Q,a>0\), the new parameter \(Q\) is strictly smaller than \(D\).  This gives the infinite descent.

So the direct descent is not only possible; it is almost line-for-line the N=10 descent with the middle sign threaded through the algebra.

## Best refactor target

The best shared statement is a sign-parametric descent step.  Use

\[
\varepsilon^2=1
\]

and define the signed quartic predicate

\[
Q_\varepsilon(s,D,t):\quad
s^4+\varepsilon D^2s^2-D^4=t^2.
\]

Then the two important sign-parametric identities are:

\[
(2s^2+\varepsilon D^2-2t)(2s^2+\varepsilon D^2+2t)=5D^4,
\]

and after the oriented factor split

\[
U=a^4,\qquad V=5b^4,\qquad D=ab,
\]

the sum identity becomes

\[
4s^2=(a^2-\varepsilon b^2)^2+4b^4.
\]

For \(\varepsilon=1\), this is the N=10 identity

\[
4s^2=(a^2-b^2)^2+4b^4.
\]

For \(\varepsilon=-1\), this is the N=16 identity

\[
4s^2=(a^2+b^2)^2+4b^4.
\]

The Pythagorean descent then returns a new solution of the same sign:

\[
a^2=P^4+\varepsilon P^2Q^2-Q^4.
\]

So the formal refactor can be:

```text
signed_quartic_factor_identity
signed_quartic_split_sum_identity
signed_pythagorean_descent_algebra

quartic_descent_step_eps
  (eps : ℤ) (heps : eps ^ 2 = 1)
  ...

quartic_descent_N10 := quartic_descent_step_eps  1
quartic_descent_N16 := quartic_descent_step_eps (-1)
```

In practice, if the current 1128-line `QuarticDescent.lean` is already stable, the safer first Lean step is probably a separate `QuarticDescent16.lean` that reuses imported helper lemmas and duplicates only the sign-sensitive proof script.  After that compiles, refactor the two files into the sign-parametric core.

## Ring-verification snippets

These snippets are the algebraic core.  They are written so the coefficients can be checked by `ring`/`nlinarith`.

```lean
import Mathlib

namespace QuarticDescent16Check

/-- N=10 quartic predicate. -/
def Q10 (s D t : ℤ) : Prop :=
  s ^ 4 + D ^ 2 * s ^ 2 - D ^ 4 = t ^ 2

/-- N=16 quartic predicate: negative middle term. -/
def Q16 (s D t : ℤ) : Prop :=
  s ^ 4 - D ^ 2 * s ^ 2 - D ^ 4 = t ^ 2

/-- N=16 denominator-free map to `w^2 = u^3 - u^2 - u`. -/
example {s D t : ℤ} (h : Q16 s D t) :
    (s * t) ^ 2 = (s ^ 2) ^ 3 - D ^ 2 * (s ^ 2) ^ 2 - D ^ 4 * s ^ 2 := by
  unfold Q16 at h
  nlinarith [h]

/-- N=10 denominator-free map to `w^2 = u^3 + u^2 - u`. -/
example {s D t : ℤ} (h : Q10 s D t) :
    (s * t) ^ 2 = (s ^ 2) ^ 3 + D ^ 2 * (s ^ 2) ^ 2 - D ^ 4 * s ^ 2 := by
  unfold Q10 at h
  nlinarith [h]

/-- The sign-parametric factor identity. -/
example {eps s D t : ℤ}
    (heps : eps ^ 2 = 1)
    (h : t ^ 2 = s ^ 4 + eps * D ^ 2 * s ^ 2 - D ^ 4) :
    (2 * s ^ 2 + eps * D ^ 2 - 2 * t) *
      (2 * s ^ 2 + eps * D ^ 2 + 2 * t) = 5 * D ^ 4 := by
  calc
    (2 * s ^ 2 + eps * D ^ 2 - 2 * t) *
        (2 * s ^ 2 + eps * D ^ 2 + 2 * t)
        = (2 * s ^ 2 + eps * D ^ 2) ^ 2 - (2 * t) ^ 2 := by ring
    _ = 5 * D ^ 4 := by
      rw [h]
      nlinarith [heps]

/-- The N=16 factor identity in its concrete form. -/
example {s D t : ℤ} (h : Q16 s D t) :
    (2 * s ^ 2 - D ^ 2 - 2 * t) *
      (2 * s ^ 2 - D ^ 2 + 2 * t) = 5 * D ^ 4 := by
  unfold Q16 at h
  have h' : t ^ 2 = s ^ 4 + (-1 : ℤ) * D ^ 2 * s ^ 2 - D ^ 4 := by
    nlinarith [h]
  simpa using
    (show
      (2 * s ^ 2 + (-1 : ℤ) * D ^ 2 - 2 * t) *
        (2 * s ^ 2 + (-1 : ℤ) * D ^ 2 + 2 * t) = 5 * D ^ 4 from
      by
        calc
          (2 * s ^ 2 + (-1 : ℤ) * D ^ 2 - 2 * t) *
              (2 * s ^ 2 + (-1 : ℤ) * D ^ 2 + 2 * t)
              = (2 * s ^ 2 + (-1 : ℤ) * D ^ 2) ^ 2 - (2 * t) ^ 2 := by ring
          _ = 5 * D ^ 4 := by
            rw [h']
            norm_num)

/-- After the oriented split, the sign-parametric Pythagorean identity. -/
example {eps s D t a b : ℤ}
    (heps : eps ^ 2 = 1)
    (hU : 2 * s ^ 2 + eps * D ^ 2 - 2 * t = a ^ 4)
    (hV : 2 * s ^ 2 + eps * D ^ 2 + 2 * t = 5 * b ^ 4)
    (hD : D = a * b) :
    4 * s ^ 2 = (a ^ 2 - eps * b ^ 2) ^ 2 + 4 * b ^ 4 := by
  nlinarith [heps, hU, hV, hD]

/-- The concrete N=16 post-split identity: `h = a^2 + b^2`. -/
example {s D t a b : ℤ}
    (hU : 2 * s ^ 2 - D ^ 2 - 2 * t = a ^ 4)
    (hV : 2 * s ^ 2 - D ^ 2 + 2 * t = 5 * b ^ 4)
    (hD : D = a * b) :
    4 * s ^ 2 = (a ^ 2 + b ^ 2) ^ 2 + 4 * b ^ 4 := by
  nlinarith [hU, hV, hD]

/-- The final N=16 descent algebra. -/
example {a P Q : ℤ}
    (h : a ^ 2 + (P * Q) ^ 2 = P ^ 4 - Q ^ 4) :
    P ^ 4 - Q ^ 2 * P ^ 2 - Q ^ 4 = a ^ 2 := by
  nlinarith [h]

/-- The sign-parametric final descent algebra. -/
example {eps a P Q : ℤ}
    (h : a ^ 2 = P ^ 4 + eps * P ^ 2 * Q ^ 2 - Q ^ 4) :
    P ^ 4 + eps * Q ^ 2 * P ^ 2 - Q ^ 4 = a ^ 2 := by
  nlinarith [h]

/-- Quadratic-twist isomorphism over a ring containing an element `i` with `i^2=-1`. -/
example {R : Type*} [CommRing R] {i x y : R}
    (hi : i ^ 2 = -1)
    (h : y ^ 2 = x ^ 3 - x ^ 2 - x) :
    (i * y) ^ 2 = (-x) ^ 3 + (-x) ^ 2 - (-x) := by
  rw [show (i * y) ^ 2 = i ^ 2 * y ^ 2 by ring]
  rw [hi, h]
  ring

/-- Quartic-level twist: `S = i*s` turns N=16 into N=10 over a ring with `i`. -/
example {R : Type*} [CommRing R] {i s D t : R}
    (hi : i ^ 2 = -1)
    (h : s ^ 4 - D ^ 2 * s ^ 2 - D ^ 4 = t ^ 2) :
    (i * s) ^ 4 + D ^ 2 * (i * s) ^ 2 - D ^ 4 = t ^ 2 := by
  have hi4 : i ^ 4 = 1 := by
    calc
      i ^ 4 = (i ^ 2) ^ 2 := by ring
      _ = (-1 : R) ^ 2 := by rw [hi]
      _ = 1 := by ring
  calc
    (i * s) ^ 4 + D ^ 2 * (i * s) ^ 2 - D ^ 4
        = i ^ 4 * s ^ 4 + D ^ 2 * (i ^ 2 * s ^ 2) - D ^ 4 := by ring
    _ = s ^ 4 - D ^ 2 * s ^ 2 - D ^ 4 := by
      rw [hi4, hi]
      ring
    _ = t ^ 2 := h

end QuarticDescent16Check
```

## Formalization recommendation

Do **not** try to prove N=16 by invoking the final N=10 descent theorem through the quadratic twist.  That route changes the base ring from \(\mathbb Z\) or \(\mathbb Q\) to \(\mathbb Z[i]\) or \(\mathbb Q(i)\), and it does not preserve the “\(u\) is a rational square” structure used by the quartic model.

Do reuse the N=10 proof by extracting the shared descent lemmas:

```text
coprime factorization of U,V
positivity of U,V
coprime fourth-power split of UV = 5D^4
primitive Pythagorean parametrization
coprime product-square split
measure-decrease proof
```

Then make the few sign-sensitive algebraic identities parametric in `eps : ℤ` with `eps ^ 2 = 1`.  The only real mathematical replacement is:

```text
N=10: h = a^2 - b^2
N=16: h = a^2 + b^2
```

Everything after that is the same descent mechanism.
