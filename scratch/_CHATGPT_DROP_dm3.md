# Q2094 (dm3): N=14 quartic descent algebra

Date: 2026-06-28.

Question: for the N=14 quartic descent, analyze

```text
s^4 + D^2*s^2 - 2*D^4 = t^2.
```

The coefficient is `-2*D^4`, not `-D^4` as in the nearby N=10/N=16-looking quartics.  What is the correct factorization, and does the same infinite descent pattern apply?

## 1. Correct identities

The clean first factorization is not the `2s^2 + D^2` identity.  It is

```text
s^4 + D^2*s^2 - 2*D^4
  = (s^2 - D^2) * (s^2 + 2*D^2).
```

So any integer solution satisfies

```text
(s^2 - D^2) * (s^2 + 2*D^2) = t^2.          (A)
```

The difference-of-squares identity asked in the prompt is also correct, but it is secondary.  Compute

```text
(2*s^2 + D^2)^2 - (2*t)^2
 = 4*s^4 + 4*D^2*s^2 + D^4
   - 4*(s^4 + D^2*s^2 - 2*D^4)
 = 9*D^4.
```

Therefore

```text
(2*s^2 + D^2 - 2*t) * (2*s^2 + D^2 + 2*t) = 9*D^4.      (B)
```

Equivalently,

```text
(2*t)^2 + (3*D^2)^2 = (2*s^2 + D^2)^2.                  (C)
```

So yes: the prompt's second guess is right:

```text
(2s^2 + D^2 - 2t)(2s^2 + D^2 + 2t) = D^4 + 8D^4 = 9D^4.
```

The earlier `5D^4` calculation is the coefficient-`-D^4` calculation; for N=14 the `-2D^4` contributes `+8D^4` after multiplying by `-4`.

## 2. The controlled factors are `A` and `B`

For descent, use

```text
A := s^2 - D^2,
B := s^2 + 2*D^2.
```

Then

```text
A*B = t^2,
B - A = 3*D^2,
A + B = 2*s^2 + D^2.
```

Assume a primitive positive nontrivial solution:

```text
D > 0,
 gcd(s,D) = 1,
 s > D,
 t > 0.
```

Then

```text
gcd(A,B) = gcd(s^2 - D^2, s^2 + 2D^2)
         = gcd(s^2 - D^2, 3D^2).
```

Because `gcd(s,D)=1`, we have `gcd(s^2 - D^2, D)=1`; hence

```text
gcd(A,B) | 3.
```

Thus the primitive split has exactly two possible branches.  Let

```text
δ := gcd(A,B) ∈ {1,3}.
```

Since `A*B` is a square and `A/δ`, `B/δ` are coprime, there are coprime positive integers `u < v` such that

```text
A = δ*u^2,
B = δ*v^2,
t = δ*u*v.                                             (D)
```

That is,

```text
s^2 - D^2     = δ*u^2,
s^2 + 2*D^2   = δ*v^2.                                 (E)
```

Subtracting gives

```text
δ*(v^2 - u^2) = 3*D^2.                                 (F)
```

This is the main structural split for N=14.

## 3. How identity (B) looks after the square split

Using `A = δu^2`, `B = δv^2`, we get

```text
2*s^2 + D^2 = A + B = δ*(u^2 + v^2),
2*t = 2*δ*u*v.
```

Therefore the two factors in (B) are

```text
2*s^2 + D^2 - 2*t = δ*(v-u)^2,
2*s^2 + D^2 + 2*t = δ*(v+u)^2.                         (G)
```

Their product is

```text
δ^2*(v^2-u^2)^2
 = δ^2*(3*D^2/δ)^2
 = 9*D^4.
```

So the `9D^4` identity is not wrong; it is just less primitive than the `A*B=t^2` split.  The exact factorization has a hidden `δ = 1 or 3` square multiplier.

## 4. The two branches

### Branch δ = 3: the genuine descending branch

If `δ=3`, then

```text
s^2 - D^2   = 3*u^2,
s^2 + 2D^2  = 3*v^2.
```

Subtracting and rearranging gives

```text
D^2 = v^2 - u^2,
s^2 = v^2 + 2*u^2.                                    (H)
```

Now `(D',s') := (u,v)` is again an N=14 solution, because

```text
s'^4 + D'^2*s'^2 - 2*D'^4
 = v^4 + u^2*v^2 - 2*u^4
 = (v^2-u^2)*(v^2+2u^2)
 = D^2*s^2.
```

So

```text
(D',s',t') = (u, v, D*s)                               (I)
```

is another solution.

This is a real descent in `s`, because

```text
s'^2 = v^2 = (s^2 + 2D^2)/3 < s^2
```

as soon as `s > D`.

Also note the branch flip: for the new solution,

```text
s'^2 - D'^2   = v^2 - u^2 = D^2,
s'^2 + 2D'^2  = v^2 + 2u^2 = s^2,
```

so the new solution has `δ'=1`.

### Branch δ = 1: the inverse/ascent branch

If `δ=1`, then

```text
s^2 - D^2   = u^2,
s^2 + 2D^2  = v^2.
```

Subtracting and rearranging gives

```text
3D^2 = v^2 - u^2,
3s^2 = v^2 + 2*u^2.                                  (J)
```

Again `(D',s') := (u,v)` is an N=14 solution, but now

```text
s'^4 + D'^2*s'^2 - 2*D'^4
 = v^4 + u^2*v^2 - 2u^4
 = (v^2-u^2)*(v^2+2u^2)
 = (3D^2)*(3s^2)
 = (3Ds)^2.
```

So

```text
(D',s',t') = (u, v, 3*D*s)                            (K)
```

is another solution.

But this is not a descent, since

```text
s'^2 = v^2 = s^2 + 2D^2 > s^2.
```

It is exactly the inverse of the `δ=3` descent.  Starting from a `δ=1` solution and applying (K) gives a larger `δ=3` solution; applying the `δ=3` descent to that larger solution returns the original one.

## 5. Consequence: the N=14 descent is not the same one-line descent

For N=14, the first factorization does not by itself give a uniform smaller primitive solution.

The structure is:

```text
δ = 3  gives a smaller solution (u,v,Ds).
δ = 1  gives a larger solution (u,v,3Ds).
```

Thus a minimal counterexample, ordered by `s`, would have to lie in the `δ=1` branch.  The main split reduces the problem to ruling out the `δ=1` branch by a secondary descent/obstruction.

This is the important difference from the N=10/N=16-style pattern.  The identity with `9D^4` is correct, but the coefficient `-2D^4` makes the descent branch-dependent instead of automatically descending.

## 6. The secondary core: reduction to `x^4 + 10x^2y^2 + y^4 = z^2`

The `δ=1` branch has a standard Pythagorean-triple reduction.

In the `δ=1` branch,

```text
s^2 = u^2 + D^2,
```

with `gcd(u,D)=1`.  Modulo `4`, `D` cannot be odd, because then `s^2 + 2D^2 = v^2` would be `2` or `3 mod 4`, impossible.  Hence `D` is even, and the primitive Pythagorean parametrization gives coprime positive integers `m > n`, of opposite parity, such that

```text
D = 2mn,
u = m^2 - n^2,
s = m^2 + n^2.
```

The remaining condition `s^2 + 2D^2 = v^2` becomes

```text
v^2
 = (m^2+n^2)^2 + 2*(2mn)^2
 = m^4 + 10*m^2*n^2 + n^4.                            (L)
```

Conversely, any coprime opposite-parity positive solution of

```text
z^2 = m^4 + 10*m^2*n^2 + n^4
```

produces a primitive `δ=1` solution of the N=14 quartic by

```text
D = 2mn,
s = m^2+n^2,
u = m^2-n^2,
t = u*z.
```

The `δ=3` branch gives the same auxiliary quartic from the other side.  There `D^2 = v^2-u^2`, so with the primitive Pythagorean parametrization

```text
u = 2mn,
D = m^2-n^2,
v = m^2+n^2,
```

and the condition `s^2 = v^2 + 2u^2` again becomes

```text
s^2 = m^4 + 10*m^2*n^2 + n^4.                         (M)
```

So the real N=14 core is the auxiliary quartic

```text
x^4 + 10*x^2*y^2 + y^4 = z^2.                         (Q10)
```

To finish an N=14 nonexistence proof by descent, isolate a lemma of the form:

```text
No coprime positive opposite-parity integers x,y,z satisfy
z^2 = x^4 + 10*x^2*y^2 + y^4.
```

Then the N=14 quartic is killed as follows:

1. Start with a primitive positive nontrivial N=14 solution.
2. Split `A=s^2-D^2`, `B=s^2+2D^2`.
3. Get `δ ∈ {1,3}` and `A=δu^2`, `B=δv^2`.
4. If `δ=3`, descend once to the smaller `δ=1` solution `(u,v,Ds)`.
5. In the `δ=1` branch, parametrize the primitive Pythagorean triple `u^2 + D^2 = s^2`.
6. The leftover condition is exactly `(Q10)`, contradiction by the auxiliary quartic descent.

## 7. Lean-facing decomposition

A clean Lean interface should not try to reuse the N=10/N=16 descent as a black box.  For N=14, split the proof into these lemmas:

```lean
-- algebraic identity
n14_factor_AB :
  s^4 + D^2*s^2 - 2*D^4 = (s^2 - D^2) * (s^2 + 2*D^2)

-- difference-of-squares identity
n14_diff_square :
  t^2 = s^4 + D^2*s^2 - 2*D^4 ->
  (2*s^2 + D^2 - 2*t) * (2*s^2 + D^2 + 2*t) = 9*D^4

-- primitive gcd control
gcd_n14_AB_dvd_three :
  Nat.Coprime s D ->
  Nat.gcd (s^2 - D^2) (s^2 + 2*D^2) ∣ 3

-- square splitting, after positivity and AB=t^2
n14_square_split :
  ∃ δ u v,
    (δ = 1 ∨ δ = 3) ∧
    s^2 - D^2 = δ*u^2 ∧
    s^2 + 2*D^2 = δ*v^2 ∧
    t = δ*u*v

-- branch transform
n14_transform :
  s^2 - D^2 = δ*u^2 ->
  s^2 + 2*D^2 = δ*v^2 ->
  δ ∈ {1,3} ->
  v^4 + u^2*v^2 - 2*u^4 = ((3/δ)*D*s)^2
```

For the `δ=3` branch, add the strict decrease lemma:

```lean
n14_delta_three_decreases :
  s > D ->
  s^2 + 2*D^2 = 3*v^2 ->
  v < s
```

For the `δ=1` branch, reduce to the auxiliary quartic:

```lean
n14_delta_one_to_Q10 :
  s^2 - D^2 = u^2 ->
  s^2 + 2*D^2 = v^2 ->
  Nat.Coprime s D ->
  ∃ m n,
    Nat.Coprime m n ∧
    m > n ∧
    Odd (m+n) ∧
    D = 2*m*n ∧
    s = m^2+n^2 ∧
    v^2 = m^4 + 10*m^2*n^2 + n^4
```

Then make the classical auxiliary descent its own theorem/axiom target:

```lean
no_Q10_primitive :
  ¬ ∃ m n z : ℕ,
    m > 0 ∧ n > 0 ∧
    Nat.Coprime m n ∧
    Odd (m+n) ∧
    z^2 = m^4 + 10*m^2*n^2 + n^4
```

With `no_Q10_primitive`, the N=14 descent becomes structurally clean and avoids pretending that the `9D^4` factorization alone gives a uniform infinite descent.

## Bottom line

The correct identity is

```text
(2s^2 + D^2 - 2t)(2s^2 + D^2 + 2t) = 9D^4.
```

But the real descent structure is controlled by

```text
(s^2-D^2)(s^2+2D^2)=t^2,
```

with

```text
gcd(s^2-D^2, s^2+2D^2) ∈ {1,3}.
```

After square splitting:

```text
s^2-D^2   = δu^2,
s^2+2D^2  = δv^2,
δ ∈ {1,3}.
```

The `δ=3` branch descends to `(u,v,Ds)`.  The `δ=1` branch ascends to `(u,v,3Ds)` and must be eliminated by the secondary quartic descent

```text
z^2 = x^4 + 10x^2y^2 + y^4.
```

So: the algebraic identity is `9D^4`, yes; the same naive infinite descent does not directly work without the extra `δ=1`/auxiliary-quartic analysis.