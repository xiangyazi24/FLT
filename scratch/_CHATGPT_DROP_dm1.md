# Q2011 (dm1): Weil pairing Round 2 — exact Miller-function loop

This note gives the exact mathematical definition I would implement first in
Lean.  It is specialized to a short Weierstrass curve

```text
E : y^2 = x^3 + A*x + B
```

over a field `K` with `char K ≠ 2,3`; for the Mazur/Q use case this is enough.
The same structure generalizes to long Weierstrass equations, but the line
coefficients are messier.

The implementation target is not initially a proof of all Weil-pairing
properties.  The target is a computable function in the function field of the
affine coordinate ring, together with a clear invariant that later proves it is
the classical Miller function.

---

## 1. Coordinate-ring setup

Let

```text
A_E = K[X,Y] / (Y^2 - X^3 - A*X - B)
K(E) = Frac(A_E)
```

and let `x`, `y` denote the images of `X`, `Y` in `A_E`, embedded in `K(E)`.

For an affine point `R = (x_R,y_R)`, evaluation is the ring map

```text
ev_R : A_E → K,
ev_R(x) = x_R,
ev_R(y) = y_R.
```

A rational function in `K(E)` can be evaluated at `R` only when its denominator
is nonzero at `R`.  The symbolic Miller loop should therefore live in `K(E)`;
the evaluation loop should be a separate partial/computable specialization.

---

## 2. Normalized line and vertical functions

Let `O` be the point at infinity.  For affine points `R = (x_R,y_R)` and
`S = (x_S,y_S)`, define the normalized line function `ell(R,S)` as follows.

### Identity cases

For Miller-recursion purposes set

```text
ell(O,S) = 1,
ell(R,O) = 1.
```

Then the correction factor `g(O,S)` and `g(R,O)` below is also `1`, so adding
`O` does not change the Miller function.

### Vertical case: `S = -R`

If `R` and `S` are affine and `S = -R`, including the tangent-at-2-torsion case
`R = S` with `y_R = 0`, define

```text
ell(R,S) = x - x_R.
```

This is the vertical line through `R` and `S`.

### Tangent case: `R = S`, nonvertical

If `R = S` and `y_R ≠ 0`, define

```text
lambda(R,R) = (3*x_R^2 + A) / (2*y_R),
ell(R,R) = y - y_R - lambda(R,R)*(x - x_R).
```

### Secant case: `R ≠ S`, nonvertical

If `R,S` are affine and `S ≠ ±R`, define

```text
lambda(R,S) = (y_S - y_R) / (x_S - x_R),
ell(R,S) = y - y_R - lambda(R,S)*(x - x_R).
```

This normalization fixes the coefficient of `y` to be `1` for nonvertical
lines, and fixes the coefficient of `x` to be `1` for vertical lines.  That
normalization is what makes the final sign convention below stable.

For a point `T`, define the normalized vertical denominator

```text
v_T = 1                 if T = O,
v_T = x - x_T           if T = (x_T,y_T) is affine.
```

Finally define the Miller correction factor

```text
g(R,S) = ell(R,S) / v_{R+S}  ∈ K(E).
```

The key divisor identity, to be proved later, is

```text
div(g(R,S)) = [R] + [S] - [R+S] - [O].
```

When `R+S = O`, this says `div(g(R,S)) = [R] + [S] - 2[O]`, and indeed
`g(R,S)` is just the vertical line `x - x_R`.

---

## 3. Abstract Miller functions `f_{n,P}`

Fix a point `P ∈ E(K)`.  Define rational functions `f_{n,P} ∈ K(E)` by

```text
f_{1,P} = 1,
```

and the addition recursion

```text
f_{r+s,P} = f_{r,P} * f_{s,P} * g(rP, sP).
```

Equivalently, the two operations used by Miller's binary algorithm are

```text
f_{2r,P}     = f_{r,P}^2 * g(rP, rP),
f_{2r+1,P}   = f_{2r,P} * g(2rP, P).
```

The divisor invariant is

```text
div(f_{n,P}) = n*[P] - [nP] - (n-1)*[O].        (★)
```

Check of the recursion using the divisor identity for `g`:

```text
div(f_r f_s g(rP,sP))
 = r[P] - [rP] - (r-1)[O]
 + s[P] - [sP] - (s-1)[O]
 + [rP] + [sP] - [(r+s)P] - [O]
 = (r+s)[P] - [(r+s)P] - (r+s-1)[O].
```

If `P` has exact order `m`, then `mP = O`, so

```text
div(f_{m,P}) = m*[P] - m*[O].
```

This is the function used in the Weil pairing.

---

## 4. Exact binary Miller loop

Let

```text
m = (1 b_{r-1} b_{r-2} ... b_0)_2
```

be the binary expansion of `m`, with the leading `1` removed from the loop.

The loop state after processing a prefix is

```text
(n, T, F)
```

where

```text
n : Nat              -- processed binary prefix
T = nP               -- current elliptic-curve point
F = f_{n,P} ∈ K(E)   -- current Miller function
```

The initial state is

```text
n_0 = 1,
T_0 = P,
F_0 = 1.
```

For each next bit `b ∈ {0,1}`, perform the following steps.

### Doubling substep

Define

```text
D  = g(T,T),
F' = F^2 * D,
T' = 2T,
n' = 2n.
```

The invariant after this substep is

```text
T' = n' P,
F' = f_{n',P}.
```

### Optional addition substep, if `b = 1`

If the bit is `1`, define

```text
A  = g(T',P),
F_next = F' * A,
T_next = T' + P,
n_next = n' + 1.
```

The invariant becomes

```text
T_next = n_next P,
F_next = f_{n_next,P}.
```

### If `b = 0`

Set

```text
F_next = F',
T_next = T',
n_next = n'.
```

At the end of the loop,

```text
n = m,
T = mP,
F = f_{m,P}.
```

If `P` has exact order `m`, then `T = O`.

---

## 5. Same loop as a computable evaluation algorithm

For efficient computation of `f_{m,P}(Q)`, do not build the symbolic function.
Evaluate `g(R,S)` at `Q` at each step.

For an affine point `Q`, define

```text
gEval(R,S,Q) = ell(R,S)(Q) / v_{R+S}(Q),
```

provided `v_{R+S}(Q) ≠ 0` and `ell(R,S)` is not being evaluated at an undefined
point.  In explicit coordinates:

```text
if R = O or S = O:
  gEval(R,S,Q) = 1

if S = -R, R affine:
  gEval(R,S,Q) = x_Q - x_R

if R = S, y_R ≠ 0:
  lambda = (3*x_R^2 + A)/(2*y_R)
  numerator   = y_Q - y_R - lambda*(x_Q - x_R)
  denominator = if 2R = O then 1 else x_Q - x_{2R}
  gEval = numerator / denominator

if R,S affine and S ≠ ±R:
  lambda = (y_S-y_R)/(x_S-x_R)
  numerator   = y_Q - y_R - lambda*(x_Q - x_R)
  denominator = if R+S = O then 1 else x_Q - x_{R+S}
  gEval = numerator / denominator
```

The evaluated Miller loop is:

```text
millerEval(m,P,Q):
  bits = binary digits of m after the leading 1
  T = P
  f = 1
  for b in bits:
    f = f^2 * gEval(T,T,Q)
    T = 2T
    if b = 1:
      f = f * gEval(T,P,Q)
      T = T + P
  return f
```

Loop invariant:

```text
f = f_{n,P}(Q),
T = nP.
```

This evaluated version is partial: it requires that no denominator vertical
line encountered in the chosen addition chain vanishes at `Q`.

For the main Weil-pairing use, if `P,Q` are a `ZMod m`-basis of `E[m]`, then
`Q` is not in the cyclic subgroup generated by `P`; hence the vertical
denominators in `millerEval(m,P,Q)` should not vanish.  Similarly for
`millerEval(m,Q,P)`.  This is the clean case to formalize first.

---

## 6. Final Weil-pairing evaluation

Assume:

```text
P,Q ∈ E[m],
P ≠ O,
Q ≠ O,
P and Q are independent,
```

so the simple affine evaluations below avoid the supports of the relevant
divisors.

With the line and vertical normalizations above, define

```text
e_m(P,Q) = (-1)^m * f_{m,P}(Q) / f_{m,Q}(P).
```

Using the evaluated loop, this is

```text
weilPairingEval(m,P,Q) =
  (-1)^m * millerEval(m,P,Q) / millerEval(m,Q,P).
```

This is the convention I recommend locking in for Lean.  It has the expected
normalization on 2-torsion: if `P,Q` are distinct nonzero 2-torsion points, then
`f_{2,P} = x - x_P`, `f_{2,Q} = x - x_Q`, and

```text
e_2(P,Q) = (x_Q - x_P)/(x_P - x_Q) = -1.
```

Some references use the inverse convention.  If a later comparison theorem uses
the opposite convention, swap the ratio.  The primitive-root consequence is
unchanged, but the convention should be fixed early.

---

## 7. More robust divisor definition for degenerate evaluations

The simple formula above is enough for independent nonzero basis points.  For a
fully general Weil pairing, use auxiliary degree-zero divisors.

Choose divisors

```text
D_P ~ [P] - [O],
D_Q ~ [Q] - [O]
```

with disjoint support, and choose functions

```text
div(F_P) = m D_P,
div(F_Q) = m D_Q.
```

Then define

```text
e_m(P,Q) = F_P(D_Q) / F_Q(D_P).
```

This is the clean mathematical definition.  The Miller loop above computes the
special functions for the unshifted divisor `[P]-[O]`.  To use shifted divisors
computationally, one must multiply by correction functions translating
`[P]-[O]` to `D_P`; do not simply evaluate `f_{m,P}(Q+R)/f_{m,P}(R)` without
checking those correction factors.

For the Mazur full-rational-torsion obstruction, I would avoid this generality
at first: choose independent `P,Q` and use the simple ratio formula.

---

## 8. Lean implementation skeleton

A practical Lean file should separate the computable definitions from the proof
invariants.

### Point and function-field objects

Use the existing Mathlib point type for the short Weierstrass curve if possible.
For the function-field side, use the affine coordinate ring:

```lean
-- Informal names only.
abbrev CoordRing := K[X,Y] / (Y^2 - X^3 - A*X - B)
abbrev FuncField := FractionRing CoordRing
```

Define coordinate functions:

```lean
xFun : FuncField
yFun : FuncField
constFun : K → FuncField
```

### Normalized functions

```lean
def verticalFun (T : EPoint K) : FuncField :=
  match T with
  | O => 1
  | affine xT yT => xFun - constFun xT

noncomputable def lineFun (R S : EPoint K) : FuncField :=
  match R, S with
  | O, _ => 1
  | _, O => 1
  | affine xR yR, affine xS yS =>
      if hInv : S = -R then
        xFun - constFun xR
      else if hEq : R = S then
        let lambda := (3*xR^2 + A)/(2*yR)
        yFun - constFun yR - constFun lambda * (xFun - constFun xR)
      else
        let lambda := (yS-yR)/(xS-xR)
        yFun - constFun yR - constFun lambda * (xFun - constFun xR)

def gFun (R S : EPoint K) : FuncField :=
  lineFun R S / verticalFun (R + S)
```

For a genuinely computable version over `Q`, replace proposition-valued branches
by decidable coordinate tests.  The branch order should be:

```text
O case,
inverse/vertical case,
equal/tangent case,
secant case.
```

This avoids dividing by `x_S - x_R` in vertical cases and avoids dividing by
`2*y_R` at 2-torsion.

### Symbolic Miller state

```lean
structure MillerState where
  n : Nat
  T : EPoint K
  F : FuncField
```

Step functions:

```lean
def millerDouble (st : MillerState) : MillerState :=
  { n := 2 * st.n,
    T := st.T + st.T,
    F := st.F^2 * gFun st.T st.T }

def millerAddP (P : EPoint K) (st : MillerState) : MillerState :=
  { n := st.n + 1,
    T := st.T + P,
    F := st.F * gFun st.T P }
```

Binary loop:

```lean
def millerFunFromBits (P : EPoint K) (bits : List Bool) : MillerState :=
  bits.foldl
    (fun st b =>
      let stD := millerDouble st
      if b then millerAddP P stD else stD)
    { n := 1, T := P, F := 1 }
```

For `m`, take `bits = binaryDigitsAfterLeadingOne m`.  The output field `F` is
`f_{m,P}` and the output point is `mP`.

### Evaluated state

For evaluation at a fixed affine `Q`, use

```lean
structure MillerEvalState where
  n : Nat
  T : EPoint K
  value : K
```

with updates

```text
value := value^2 * gEval(T,T,Q)
T     := 2T

if bit = 1:
  value := value * gEval(T,P,Q)
  T     := T + P
```

This should be the fast executable path for examples and tests.

---

## 9. Proof obligations to attach later

The definitions above are enough to compute.  The mathematical proof should add
these lemmas in this order:

1. `div_verticalFun`:

   ```text
   div(v_T) = [T] + [-T] - 2[O]
   ```

2. `div_lineFun`:

   ```text
   div(ell(R,S)) = [R] + [S] + [-(R+S)] - 3[O]
   ```

3. `div_gFun`:

   ```text
   div(g(R,S)) = [R] + [S] - [R+S] - [O]
   ```

4. `miller_invariant`:

   for every loop state `(n,T,F)`,

   ```text
   T = nP,
   div(F) = n[P] - [T] - (n-1)[O].
   ```

5. `miller_final_divisor`:

   if `P` has order `m`, output `F` satisfies

   ```text
   div(F) = m[P] - m[O].
   ```

6. `weilPairingEval_pow_eq_one`:

   ```text
   e_m(P,Q)^m = 1.
   ```

7. Bilinearity and alternating/skew-symmetry:

   ```text
   e_m(P1+P2,Q) = e_m(P1,Q)*e_m(P2,Q),
   e_m(P,Q1+Q2) = e_m(P,Q1)*e_m(P,Q2),
   e_m(P,P) = 1,
   e_m(Q,P) = e_m(P,Q)^(-1).
   ```

8. Nondegeneracy:

   ```text
   if P ≠ O, then ∃ Q, e_m(P,Q) ≠ 1.
   ```

9. Primitive value on a basis:

   if `P,Q` are a `ZMod m`-basis of `E[m]`, then

   ```text
   IsPrimitiveRoot (e_m(P,Q)) m.
   ```

For the Mazur obstruction, item 9 plus rationality over `Q` is the key theorem.

---

## 10. Exact recommendation for Round 3

Implement first:

```text
lineFun,
verticalFun,
gFun,
millerFunFromBits,
gEval,
millerEval,
weilPairingEval.
```

Do not start with full divisors.  Make the functions executable on rational
short-Weierstrass examples.  Then prove the loop invariant in a separate layer
once a minimal divisor/order API exists.

The most important invariant to preserve in the code comments is:

```text
after processing prefix n:
  T = nP,
  F = f_{n,P},
  div(F) = n[P] - [nP] - (n-1)[O].
```

The final computable formula to expose is:

```text
weilPairingEval(m,P,Q)
  = (-1)^m * millerEval(m,P,Q) / millerEval(m,Q,P).
```

This is the exact Miller-function loop and final evaluation I recommend using
as the Lean implementation target.
