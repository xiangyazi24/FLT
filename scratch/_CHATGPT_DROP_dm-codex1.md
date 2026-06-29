# Q2193 response: finite 2-descent/Selmer certificate for the N=12 obstruction curve

Curve:

\[
E : y^2 = x^3 - x^2 - 4x + 4 = (x+2)(x-1)(x-2).
\]

Write the three rational roots as

\[
e_1=-2,\qquad e_2=1,\qquad e_3=2.
\]

The main point of this design is that the full 2-descent can be made into a genuinely finite certificate. There are 64 global squareclass triples supported at the bad set \(\{2,3,\infty\}\). The real and \(\mathbf Q_3\) tests leave 8 triples. Four of those are killed by primitive residue contradictions modulo 16 at \(\mathbf Q_2\). The remaining four are exactly the visible Kummer classes coming from the known rational points.

The resulting certificate proves

\[
\operatorname{Sel}^{(2)}(E/\mathbf Q)
  = \{(1,1,1),\ (3,-3,-1),\ (2,-1,-2),\ (6,3,2)\},
\]

with squareclasses represented by signed squarefree integers supported on \(2\) and \(3\). Since these four classes are already in the image of \(E(\mathbf Q)\), the 2-Selmer bound gives \(\operatorname{rank} E(\mathbf Q)=0\). Reduction modulo 5 and 7 then gives the exact rational point list.

## 1. Full rational 2-torsion descent map

Let

\[
H = \{(d_1,d_2,d_3) \in (\mathbf Q^\*/\mathbf Q^{\*2})^3 : d_1d_2d_3=1\}.
\]

For an affine point \(P=(x,y)\) with \(x\ne e_i\) for all \(i\), define

\[
\delta(P) = ([x-e_1],[x-e_2],[x-e_3])
          = ([x+2],[x-1],[x-2]) \in H.
\]

The product is a square because

\[
(x+2)(x-1)(x-2)=y^2.
\]

Define \(\delta(O)=(1,1,1)\). For the 2-torsion points \(T_i=(e_i,0)\), use the standard limiting value of the functions \(x-e_i\):

\[
\delta_j(T_i)=[e_i-e_j]\quad (j\ne i),
\]

and

\[
\delta_i(T_i)=\left[\prod_{j\ne i}(e_i-e_j)\right].
\]

For this curve:

| point | Kummer class |
|---|---:|
| \(O\) | \((1,1,1)\) |
| \((-2,0)\) | \((3,-3,-1)\) |
| \((1,0)\) | \((3,-3,-1)\) |
| \((2,0)\) | \((1,1,1)\) |
| \((0,\pm2)\) | \((2,-1,-2)\) |
| \((4,\pm6)\) | \((6,3,2)\) |

The descent covering attached to a triple \(d=(d_1,d_2,d_3)\) is the intersection of two quadrics

\[
C_d:
\begin{cases}
 d_1 Z_1^2 - d_2 Z_2^2 = 3 Z_0^2,\\
 d_2 Z_2^2 - d_3 Z_3^2 = Z_0^2.
\end{cases}
\]

Indeed, if

\[
x+2=d_1u_1^2,\qquad x-1=d_2u_2^2,\qquad x-2=d_3u_3^2,
\]

then subtracting adjacent equations gives exactly the two displayed equations. Conversely, a rational point on \(C_d\) with \(Z_0\ne0\) gives

\[
x=d_1(Z_1/Z_0)^2-2,
\]

and then \(y\) is recovered because \(d_1d_2d_3\) is a squareclass square.

## 2. Global squareclass universe

The discriminant has finite bad prime support \(\{2,3\}\). At every good prime \(p\notin\{2,3\}\), the usual valuation argument says the local squareclasses \([x-e_i]\) are unramified. Thus the global Selmer search may be restricted to signed squarefree representatives supported at \(2\) and \(3\):

\[
D=\{1,-1,2,-2,3,-3,6,-6\}.
\]

The candidate triples are

\[
S=\{(d_1,d_2,d_3): d_i\in D,\ d_1d_2d_3\in \mathbf Q^{\*2}\}.
\]

Equivalently, with \(\odot\) denoting squareclass multiplication normalized back into \(D\), every candidate is

\[
(d_1,d_2,d_1\odot d_2).
\]

The full 64-candidate universe is therefore represented by the following multiplication table. The row is \(d_1\), the column is \(d_2\), and the entry is \(d_3\).

| \(d_1\backslash d_2\) | 1 | -1 | 2 | -2 | 3 | -3 | 6 | -6 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | -1 | 2 | -2 | 3 | -3 | 6 | -6 |
| -1 | -1 | 1 | -2 | 2 | -3 | 3 | -6 | 6 |
| 2 | 2 | -2 | 1 | -1 | 6 | -6 | 3 | -3 |
| -2 | -2 | 2 | -1 | 1 | -6 | 6 | -3 | 3 |
| 3 | 3 | -3 | 6 | -6 | 1 | -1 | 2 | -2 |
| -3 | -3 | 3 | -6 | 6 | -1 | 1 | -2 | 2 |
| 6 | 6 | -6 | 3 | -3 | 2 | -2 | 1 | -1 |
| -6 | -6 | 6 | -3 | 3 | -2 | 2 | -1 | 1 |

## 3. Local tests

### 3.1 Real test

Over \(\mathbf R\), only the sign matters. The real locus of \(E\) lies over

\[
[-2,1]\cup[2,\infty).
\]

Thus the sign pattern of \((x+2,x-1,x-2)\) is either

\[
(+,-,-)\quad\text{or}\quad(+,+,+).
\]

Since the product square condition already forces the product of the three signs to be positive, the real local condition is simply

\[
d_1>0.
\]

So the real test cuts the 64 candidates to the 32 triples with positive first coordinate.

### 3.2 The \(\mathbf Q_3\) test

At \(3\), the element \(2\) has squareclass \(-1\), because \(-2\equiv1\pmod3\) is a square in \(\mathbf Q_3\). Hence the projection

\[
D\longrightarrow \{1,-1,3,-3\}
\]

is

| global representative | \(\mathbf Q_3\)-class |
|---:|---:|
| 1 | 1 |
| -1 | -1 |
| 2 | -1 |
| -2 | 1 |
| 3 | 3 |
| -3 | -3 |
| 6 | -3 |
| -6 | 3 |

The locally soluble \(\mathbf Q_3\) squareclass triples are exactly

\[
L_3=\{(1,1,1),\ (3,-3,-1),\ (-1,-1,1),\ (-3,3,-1)\}.
\]

Equivalently, a global candidate \((d_1,d_2,d_3)\) passes the \(\mathbf Q_3\) test iff its coordinatewise projection to \(\{1,-1,3,-3\}\) lies in this four-element set.

A machine-checkable way to certify the negative direction is to enumerate the 16 product-square triples in \(\{1,-1,3,-3\}^3\), remove the four in \(L_3\), and prove that each of the remaining 12 has no primitive solution modulo 9 to the two covering equations. Explicitly, the 12 rejected \(\mathbf Q_3\)-projected classes are

\[
\begin{aligned}
&(1,-1,-1),\ (1,3,3),\ (1,-3,-3),\\
&(-1,1,-1),\ (-1,3,-3),\ (-1,-3,3),\\
&(3,1,3),\ (3,-1,-3),\ (3,3,1),\\
&(-3,1,-3),\ (-3,-1,3),\ (-3,-3,1).
\end{aligned}
\]

For each rejected class \(c=(c_1,c_2,c_3)\), the finite obligation is

\[
\neg\exists Z_0,Z_1,Z_2,Z_3\in\mathbf Z/9\mathbf Z,
\]

not all divisible by \(3\), such that

\[
 c_1Z_1^2-c_2Z_2^2=3Z_0^2,
 \qquad
 c_2Z_2^2-c_3Z_3^2=Z_0^2
 \pmod 9.
\]

This is not a black-box Selmer computation; it is a 12-row finite residue certificate.

A human proof of the same classification is also short:

* If no coordinate is divisible by \(3\), the first equation modulo \(3\) forces the two unit squareclasses in the first two coordinates to agree. This gives \((1,1,1)\) and \((-1,-1,1)\).
* If exactly \(d_1,d_2\) are divisible by \(3\), the second equation modulo \(3\) forces the unit class of \(d_3\) to be \(-1\), hence the first two unit classes are opposite. This gives \((3,-3,-1)\) and \((-3,3,-1)\).
* If exactly \(d_1,d_3\) or exactly \(d_2,d_3\) are divisible by \(3\), a modulo-3 then modulo-9 descent forces all four projective coordinates divisible by \(3\), impossible for a primitive representative.

### 3.3 Intersection of the real and \(\mathbf Q_3\) tests

The real test and the \(\mathbf Q_3\) test leave exactly these eight global triples:

\[
\begin{aligned}
S_{\infty,3}=\{&
(1,1,1),\
(1,-2,-2),\\
&(3,-3,-1),\
(3,6,2),\\
&(2,-1,-2),\
(2,2,1),\\
&(6,3,2),\
(6,-6,-1)
\}.
\end{aligned}
\]

Four of these are visible rational classes; four are false Selmer candidates to be killed at \(2\).

### 3.4 The \(\mathbf Q_2\) test

Use the same covering equations over \(\mathbf Q_2\). For the four extra triples in \(S_{\infty,3}\), there is no primitive solution modulo 16. This is the entire \(2\)-adic rejection certificate needed after the real and \(3\)-adic filters.

The four rejected triples and their simplified equations are:

| rejected triple | equations |
|---:|---|
| \((1,-2,-2)\) | \(Z_1^2+2Z_2^2=3Z_0^2\), \(2(Z_3^2-Z_2^2)=Z_0^2\) |
| \((3,6,2)\) | \(Z_1^2-2Z_2^2=Z_0^2\), \(2(3Z_2^2-Z_3^2)=Z_0^2\) |
| \((2,2,1)\) | \(2(Z_1^2-Z_2^2)=3Z_0^2\), \(2Z_2^2-Z_3^2=Z_0^2\) |
| \((6,-6,-1)\) | \(2Z_1^2+2Z_2^2=Z_0^2\), \(Z_3^2-6Z_2^2=Z_0^2\) |

The finite Lean obligation for each row is

\[
\neg\exists Z_0,Z_1,Z_2,Z_3\in\mathbf Z/16\mathbf Z,
\]

not all even, satisfying the row's equations modulo 16.

For a human check, the same contradiction can be phrased by parity:

* In \((1,-2,-2)\), the equation \(2(Z_3^2-Z_2^2)=Z_0^2\) forces either an impossible squareclass modulo 8 or forces \(Z_2,Z_3,Z_0\) even; in the latter case the first equation forces \(Z_1\) even, contradicting primitivity.
* In \((3,6,2)\), the equation \(2(3Z_2^2-Z_3^2)=Z_0^2\) gives the same parity split. If \(Z_2,Z_3\) are odd, then \(Z_0^2\equiv4\pmod8\), and \(Z_1^2-2Z_2^2=Z_0^2\) gives \(Z_1^2\equiv6\pmod8\), impossible.
* In \((2,2,1)\), the first equation forces \(Z_1,Z_2\) to have the same parity. The odd-odd case then forces \(Z_0\equiv0\pmod4\), and the second equation gives \(Z_3^2\equiv2\pmod8\), impossible; the even-even case descends to all coordinates even.
* In \((6,-6,-1)\), the equation \(2Z_1^2+2Z_2^2=Z_0^2\) forces \(Z_1,Z_2\) to have the same parity. The odd-odd case gives \(Z_0^2\equiv4\pmod8\), and then \(Z_3^2-6Z_2^2=Z_0^2\) gives \(Z_3^2\equiv2\pmod8\), impossible; the even-even case descends to all coordinates even.

Thus the only globally Selmer-surviving classes are

\[
S_{\mathrm{surv}}=\{(1,1,1),\ (3,-3,-1),\ (2,-1,-2),\ (6,3,2)\}.
\]

## 4. Surviving classes and rational witnesses

Each surviving class has an actual rational point on its covering, hence is in the true Kummer image.

| class | rational point on \(E\) | covering witness \((Z_0,Z_1,Z_2,Z_3)\) |
|---:|---:|---:|
| \((1,1,1)\) | \((2,0)\) | \((1,2,1,0)\) |
| \((3,-3,-1)\) | \((-2,0)\) | \((1,0,1,2)\) |
| \((2,-1,-2)\) | \((0,2)\) | \((1,1,1,1)\) |
| \((6,3,2)\) | \((4,6)\) | \((1,1,1,1)\) |

The last two rows have the same projective coordinates because the triple itself changes.

Consequently

\[
\#\operatorname{Sel}^{(2)}(E/\mathbf Q)=4.
\]

Since \(E\) has full rational 2-torsion, \(\#E(\mathbf Q)[2]=4\). The Kummer injection and the standard 2-descent exact sequence give

\[
\#E(\mathbf Q)/2E(\mathbf Q)=2^{\operatorname{rank}E(\mathbf Q)}\cdot \#E(\mathbf Q)[2]
=2^{\operatorname{rank}E(\mathbf Q)}\cdot4.
\]

Because \(E(\mathbf Q)/2E(\mathbf Q)\) injects into a 4-element Selmer group, the rank is zero.

## 5. Torsion and exact rational points

The finite point counts are

\[
\#E(\mathbf F_5)=8,
\qquad
\#E(\mathbf F_7)=8.
\]

Both primes are good. Torsion injects into good reduction, so

\[
\#E(\mathbf Q)_{\mathrm{tors}}\mid \gcd(8,8)=8.
\]

The curve visibly has eight rational points:

\[
O,\quad
(-2,0),\quad (1,0),\quad (2,0),\quad
(0,2),\quad (0,-2),\quad
(4,6),\quad (4,-6).
\]

Therefore the torsion subgroup has exactly these eight points. Since the rank is zero, this is the full rational point set:

\[
E(\mathbf Q)=
\{O,(-2,0),(1,0),(2,0),(0,\pm2),(4,\pm6)\}.
\]

This immediately implies the denominator residual: if

\[
x=A/B^2,\qquad y=C/B^3,\qquad \gcd(A,B)=1,
\]

and \((x,y)\in E(\mathbf Q)\), then \(x\in\{-2,0,1,2,4\}\). Hence \(A=xB^2\), so \(B\mid A\). With \(\gcd(A,B)=1\) and \(B>0\), this forces \(B=1\).

## 6. Lean-friendly certificate format

The following is the shape I would use in Lean. The point is not to ask Lean to compute a Selmer group. Instead, Lean checks finite lists of squareclasses, finite residue contradictions, and rational witnesses, then applies one general full-2-descent theorem.

```lean
import Mathlib

namespace FLT.N12

/-- Signed squarefree representatives supported at `{2,3}`. -/
inductive Sq236 : Type
  | one | negOne | two | negTwo | three | negThree | six | negSix
  deriving DecidableEq, Repr, Fintype

open Sq236

/-- Integer representative. -/
def Sq236.toInt : Sq236 → ℤ
  | one => 1
  | negOne => -1
  | two => 2
  | negTwo => -2
  | three => 3
  | negThree => -3
  | six => 6
  | negSix => -6

/-- Squareclass multiplication, normalized in `{±1,±2,±3,±6}`. -/
def Sq236.mul : Sq236 → Sq236 → Sq236
  | one, b => b
  | negOne, one => negOne
  | negOne, negOne => one
  | negOne, two => negTwo
  | negOne, negTwo => two
  | negOne, three => negThree
  | negOne, negThree => three
  | negOne, six => negSix
  | negOne, negSix => six
  | two, one => two
  | two, negOne => negTwo
  | two, two => one
  | two, negTwo => negOne
  | two, three => six
  | two, negThree => negSix
  | two, six => three
  | two, negSix => negThree
  | negTwo, one => negTwo
  | negTwo, negOne => two
  | negTwo, two => negOne
  | negTwo, negTwo => one
  | negTwo, three => negSix
  | negTwo, negThree => six
  | negTwo, six => negThree
  | negTwo, negSix => three
  | three, one => three
  | three, negOne => negThree
  | three, two => six
  | three, negTwo => negSix
  | three, three => one
  | three, negThree => negOne
  | three, six => two
  | three, negSix => negTwo
  | negThree, one => negThree
  | negThree, negOne => three
  | negThree, two => negSix
  | negThree, negTwo => six
  | negThree, three => negOne
  | negThree, negThree => one
  | negThree, six => negTwo
  | negThree, negSix => two
  | six, one => six
  | six, negOne => negSix
  | six, two => three
  | six, negTwo => negThree
  | six, three => two
  | six, negThree => negTwo
  | six, six => one
  | six, negSix => negOne
  | negSix, one => negSix
  | negSix, negOne => six
  | negSix, two => negThree
  | negSix, negTwo => three
  | negSix, three => negTwo
  | negSix, negThree => two
  | negSix, six => negOne
  | negSix, negSix => one

structure Triple where
  d₁ : Sq236
  d₂ : Sq236
  d₃ : Sq236
  deriving DecidableEq, Repr

/-- The 64 global candidates. -/
def candidates : List Triple :=
  (Fintype.elems : Finset Sq236).toList.bind fun a =>
  (Fintype.elems : Finset Sq236).toList.map fun b =>
    ⟨a, b, Sq236.mul a b⟩

/-- The four classes that should survive globally. -/
def visibleClasses : List Triple :=
  [⟨one, one, one⟩,
   ⟨three, negThree, negOne⟩,
   ⟨two, negOne, negTwo⟩,
   ⟨six, three, two⟩]

/-- The four real-and-Q3 surviving but Q2-rejected extra classes. -/
def q2RejectClasses : List Triple :=
  [⟨one, negTwo, negTwo⟩,
   ⟨three, six, two⟩,
   ⟨two, two, one⟩,
   ⟨six, negSix, negOne⟩]

/-- The eight classes that pass the real and Q3 tests. -/
def realQ3Classes : List Triple :=
  visibleClasses ++ q2RejectClasses

/-- Projection to Q_3 squareclasses `{±1,±3}`.
At Q_3, `2` is the same squareclass as `-1`. -/
inductive Sq3 : Type
  | one | negOne | three | negThree
  deriving DecidableEq, Repr, Fintype

open Sq3

def q3Proj : Sq236 → Sq3
  | Sq236.one => Sq3.one
  | Sq236.negOne => Sq3.negOne
  | Sq236.two => Sq3.negOne
  | Sq236.negTwo => Sq3.one
  | Sq236.three => Sq3.three
  | Sq236.negThree => Sq3.negThree
  | Sq236.six => Sq3.negThree
  | Sq236.negSix => Sq3.three

structure Triple3 where
  d₁ : Sq3
  d₂ : Sq3
  d₃ : Sq3
  deriving DecidableEq, Repr

/-- The four Q_3-locally soluble projected classes. -/
def q3GoodClasses : List Triple3 :=
  [⟨Sq3.one, Sq3.one, Sq3.one⟩,
   ⟨Sq3.three, Sq3.negThree, Sq3.negOne⟩,
   ⟨Sq3.negOne, Sq3.negOne, Sq3.one⟩,
   ⟨Sq3.negThree, Sq3.three, Sq3.negOne⟩]

/-- The two descent-cover equations modulo `n`. -/
def coverMod (n : ℕ) (T : Triple)
    (Z₀ Z₁ Z₂ Z₃ : ZMod n) : Prop :=
  let d₁ : ZMod n := T.d₁.toInt
  let d₂ : ZMod n := T.d₂.toInt
  let d₃ : ZMod n := T.d₃.toInt
  d₁ * Z₁^2 - d₂ * Z₂^2 = (3 : ZMod n) * Z₀^2 ∧
  d₂ * Z₂^2 - d₃ * Z₃^2 = Z₀^2

/-- Primitive modulo 2: not all four coordinates are even. -/
def primitiveMod2 (Z₀ Z₁ Z₂ Z₃ : ZMod 16) : Prop :=
  ¬ ((Z₀.val % 2 = 0) ∧ (Z₁.val % 2 = 0) ∧
     (Z₂.val % 2 = 0) ∧ (Z₃.val % 2 = 0))

/-- Primitive modulo 3: not all four coordinates are divisible by 3. -/
def primitiveMod3 (Z₀ Z₁ Z₂ Z₃ : ZMod 9) : Prop :=
  ¬ ((Z₀.val % 3 = 0) ∧ (Z₁.val % 3 = 0) ∧
     (Z₂.val % 3 = 0) ∧ (Z₃.val % 3 = 0))

/-- Q_2 rejection certificate: finite modulo-16 contradiction for the four extra classes. -/
theorem q2_reject_certificate
    (T : Triple) (hT : T ∈ q2RejectClasses) :
    ¬ ∃ Z₀ Z₁ Z₂ Z₃ : ZMod 16,
      primitiveMod2 Z₀ Z₁ Z₂ Z₃ ∧ coverMod 16 T Z₀ Z₁ Z₂ Z₃ := by
  -- Intended proof: `native_decide`, or four hand-written parity/mod-16 proofs.
  native_decide

/-- Q_3 rejection certificate: finite modulo-9 contradiction for every projected
class outside the four-element Q_3 local image. The implementation can either
state this over `Triple3`, or pull back to `Triple` using `q3Proj`. -/
theorem q3_reject_certificate :
    -- Schematic statement:
    -- for every product-square `Triple3` not in `q3GoodClasses`, no primitive
    -- residue solution modulo 9 exists for the projected covering equations.
    True := by
  -- Intended proof: `native_decide` over the finite list of 12 rejected classes.
  trivial

/-- Real certificate: a product-square candidate is real-soluble iff its first
coordinate is positive. -/
theorem real_certificate (T : Triple) :
    -- mathematically: `C_T(ℝ).Nonempty ↔ 0 < T.d₁.toInt`
    True := by
  trivial

/-- Final finite Selmer list after applying the real, Q_3, and Q_2 certificates. -/
theorem selmer2_certificate :
    -- mathematically: `Selmer2(E/ℚ) = visibleClasses`
    True := by
  trivial

/-- Hard general theorem used after the finite certificate.
This is the standard full rational 2-torsion descent theorem: the Kummer map
injects `E(ℚ)/2E(ℚ)` into the 2-Selmer set, and
`#(E(ℚ)/2E(ℚ)) = 2^rank * #E(ℚ)[2]`. -/
axiom full_two_torsion_descent_rank_bound :
    True

/-- Consequence of the certificate: rank zero. -/
theorem rank_zero_from_certificate :
    -- mathematically: `rank E(ℚ) = 0`
    True := by
  exact full_two_torsion_descent_rank_bound

/-- Finite-field torsion certificate: good reduction counts. -/
theorem reduction_counts :
    -- mathematically: `#E(𝔽_5)=8 ∧ #E(𝔽_7)=8`
    True := by
  -- Intended proof: finite enumeration over `ZMod 5` and `ZMod 7`.
  trivial

/-- Exact rational point list. -/
theorem rational_points_certificate :
    -- mathematically:
    -- `E(ℚ) = {O,(-2,0),(1,0),(2,0),(0,±2),(4,±6)}`
    True := by
  -- rank zero + torsion injection + eight visible points.
  trivial

end FLT.N12
```

The `native_decide` lines are intentional: they are the finite certificate checks. For a more conservative Lean development, replace them by hand-written lemmas over `ZMod 16` and `ZMod 9`, but the mathematical content is the same finite enumeration.

## 7. Theorems needed to turn the certificate into rank zero

The finite certificate itself is elementary. The genuinely global theorem is the standard full 2-descent theorem for a curve with full rational 2-torsion.

A clean theorem statement to aim for is:

**Full 2-descent theorem.** Let \(E:y^2=(x-e_1)(x-e_2)(x-e_3)\) over \(\mathbf Q\), with distinct \(e_i\in\mathbf Q\). Let \(S\) contain \(2\), \(\infty\), and all primes dividing \((e_i-e_j)\). If a finite list `selmerCert` is proved equivalent to the locally soluble covering list \(C_d\) for triples supported on \(S\), then the Kummer image of \(E(\mathbf Q)/2E(\mathbf Q)\) injects into `selmerCert`.

For this curve, `selmerCert` has four elements, and \(E[2](\mathbf Q)\) has four elements. Therefore rank zero follows immediately.

Then the point-list theorem needs only:

1. good reduction at 5 and 7;
2. finite counts \(\#E(\mathbf F_5)=\#E(\mathbf F_7)=8\);
3. torsion injects into good reduction;
4. the eight visible rational points are distinct.

## 8. Simpler route for the denominator residual

For the specific denominator residual, the full 2-torsion certificate above is honest but not the shortest route. The shorter route is the 2-isogeny descent from the shifted model

\[
X=x-1,\qquad Y=y,
\]

so

\[
F:Y^2=X(X-1)(X+3)=X^3+2X^2-3X.
\]

The point \((0,0)\) gives a rational 2-isogeny. The dual curve is

\[
F':Y^2=X^3-4X^2+16X.
\]

The isogeny-descent certificate is smaller:

* For \(F\), the isogeny descent image is \(\{1,-1,3,-3\}\), with all four classes visible.
* For \(F'\), the possible classes are \(\{1,-1,2,-2\}\). The negative classes are impossible over \(\mathbf R\) because \(X^2-4X+16=(X-2)^2+12>0\), and the class \(2\) is impossible modulo 16 from
  \[
  W^2=2m^4-4m^2n^2+8n^4.
  \]
  Hence the dual image is trivial.
* The 2-isogeny rank formula gives rank zero.
* The same reduction modulo 5 and 7 gives the exact torsion list.

So, for the residual alone, the 2-isogeny route has fewer finite local checks than the full 64-triple descent. The proof burden tradeoff is this:

* Full 2-torsion descent: larger elementary certificate, but conceptually symmetric and directly tied to the three roots \(-2,1,2\).
* 2-isogeny descent: much smaller local certificate, but it requires formalizing the isogeny-descent rank formula for the chosen kernel.

There is still no credible purely local denominator descent from

\[
B^2\mid(C-z^3)(C+z^3)
\]

that avoids the elliptic-curve rank-zero input. That congruence records local squareclass choices prime-by-prime, but it does not by itself produce a canonical smaller primitive model. The finite Selmer certificate above is the clean way to make those local choices global and checkable.
