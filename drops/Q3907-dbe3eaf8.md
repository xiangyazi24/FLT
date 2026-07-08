ANSWER Q3907 dbe3eaf8

# Kubert bridges for cyclic orders 14 and 16

## Executive correction

The standard Kubert/Tate-normal-form computation is completely explicit, but it does **not** literally start with the two short Weierstrass obstruction curves in your statement.  For order `14`, the standard Tate/Rabarison bridge produces the plane cubic

```text
w^2 + u*w + w = u^3 - u,
```

equivalently after completing the square,

```text
z^2 = 1 - 2*u + u^2 + 4*u^3.
```

For order `16`, the standard bridge produces the square conditions

```text
d1(m) = (m^4 - 1)*(m^2 - 2*m - 1),
d2(m) = m*(m^2 + 1)*(m^2 + 2*m - 1).
```

Thus, if the FLT project wants the target curves

```text
N=14:  W^2 = U^3 + U^2 - 2*U,
N=16:  W^2 = U^3 - U^2 - U,
```

then there is one extra algebraic step to check: a project-specific birational map, quotient map, or descent map from the standard Kubert/Rabarison obstruction model to the chosen obstruction model.  Do not hide this step.  The standard bridge itself gives the equations below.

The good news is that the computation is finite and `ring_nf`-friendly: once Tate normal form and the relevant multiple-of-`P` formulas are in place, the bridge reduces to a few polynomial identities and nonvanishing/cusp exclusions.

---

## 1. Tate normal form

For a point `P` of order at least `4`, put the pair `(E,P)` in Tate normal form

```text
E(b,c):  y^2 + (1-c)*x*y - b*y = x^3 - b*x^2,
P = (0,0).
```

This is the usual Tate normal form used in Kubert's tables.  In a Lean file this should be packaged as:

```lean
-- schematic
structure TateNFPointOrder (N : ℕ) where
  b c : ℚ
  nonsing : tateDiscriminant b c ≠ 0
  exact_order : addOrderOf (tatePoint b c) = N
```

The bridge from an arbitrary rational point of exact order `N` to Tate normal form is:

```text
HasRationalPointOfOrder E N
  -> exists b c, TateNFPointOrder N b c
```

and is proved by the usual coordinate normalization sending `P` to `(0,0)` and `2P` to the appropriate Tate-normal-form position.  This part is uniform in `N` and should already be in or near `TateNFDivision.lean`.

---

## 2. Cyclic order 14

### 2.1 Standard obstruction equation

The standard computation is the following.

Let `F` be a field of characteristic not `2` or `7`.  A curve over `F` with a point of order `14` exists if and only if there are

```text
u ∈ F \ {-1,0,1},
z ∈ F,
z^2 = 1 - 2*u + u^2 + 4*u^3.
```

Equivalently, using

```text
z = 2*w + u + 1,
```

this is

```text
w^2 + u*w + w = u^3 - u.
```

So over `ℚ`, a rational point of order `14` gives a rational point `(u,w)` on

```text
C14: w^2 + u*w + w = u^3 - u
```

with

```text
u ∉ {-1,0,1}.
```

This is the standard cyclic `14` Kubert/Rabarison obstruction curve.

### 2.2 Explicit parameter `v`

In the geometric derivation one normalizes the relevant points on an auxiliary cubic to

```text
A      = (1, 1),
Abar   = (-1, -1),
B      = (v, u),
-Bbar  = (u, u).
```

The group labels are

```text
A      corresponds to 1,
B      corresponds to 2,
C=A+B  corresponds to 3,
-Bbar  corresponds to 5,
Abar   corresponds to 8.
```

The collinearity conditions give the quadratic equation

```text
u^2*(-3 - 6*u + u^2)
  + 2*u*(-1 + 4*u + u^2)*v
  + (u - 1)^2*v^2 = 0.
```

Solving for `v` gives

```text
v = u*(1 - 4*u - u^2 + 2*z) / (u - 1)^2
```

or the same formula with `-2*z`, where

```text
z^2 = 1 - 2*u + u^2 + 4*u^3.
```

In Lean, make the discriminant identity the central lemma:

```lean
-- schematic
lemma n14_collinearity_discriminant
    (u v z : ℚ)
    (hz : z^2 = 1 - 2*u + u^2 + 4*u^3)
    (hv : v = u*(1 - 4*u - u^2 + 2*z)/(u - 1)^2) :
    u^2*(-3 - 6*u + u^2)
      + 2*u*(-1 + 4*u + u^2)*v
      + (u - 1)^2*v^2 = 0 := by
  field_simp
  ring_nf
  -- use `hz`
```

The converse direction solves this quadratic and extracts `z` from `u,v`.

### 2.3 Rabarison/Tate-normal-form parameters

A Tate-normal-form version used in the literature is:

```text
w^2 + u*w + w = u^3 - u,

ã = (u^4 - u^3*w + u^2*(2*w - 4) - u*w + 1)
     / ((u + 1)*(u^3 - 2*u^2 - u + 1)),

b̃ = u*(1-u)*(u^5 - u^4 - 2*u^3*w + u^2 + u*(2*w - 1) - w)
     / ((u + 1)^2*(u^3 - 2*u^2 - u + 1)^2).
```

The corresponding curve is

```text
E_{ã,b̃}: y^2 + ã*x*y + b̃*y = x^3 + b̃*x^2,
```

and `(0,0)` has order `14`.

Your project's Tate normal form has

```text
y^2 + (1-c)*x*y - b*y = x^3 - b*x^2.
```

So translate signs by

```text
1 - c = ã,
-b = b̃,
```

that is

```text
c = 1 - ã,
b = -b̃.
```

These identities are just sign-convention bridges; formalize them separately so that the TateNFDivision lemmas can be reused.

### 2.4 Nondegeneracy/cusps for order 14

The excluded values are exactly the cuspidal/degenerate values:

```text
u = -1, 0, 1.
```

Concretely:

* the denominator `(u + 1)*(u^3 - 2*u^2 - u + 1)` in the Rabarison parameters degenerates at the cusp side;
* the geometric construction also requires the normalized points `A`, `B`, `Abar`, `Bbar` to remain distinct and the relevant lines not to collapse;
* in the square-root model, `u=-1,0,1` give only cusps/degenerate Tate normal forms.

For Lean, the bridge theorem should therefore output:

```lean
-- schematic
 theorem cyclic_order14_to_standard_obstruction
    (h : HasRationalPointOfOrder E 14) :
    ∃ u w : ℚ,
      w^2 + u*w + w = u^3 - u ∧
      u ≠ -1 ∧ u ≠ 0 ∧ u ≠ 1 := ...
```

If the final obstruction file is stated on

```text
W^2 = U^3 + U^2 - 2*U,
```

then add a separate, explicitly named map theorem:

```lean
-- schematic; fill with the actual project map, not a guessed one
 theorem standard_C14_to_project_N14_obstruction
    {u w : ℚ}
    (h : w^2 + u*w + w = u^3 - u)
    (hne : u ≠ -1 ∧ u ≠ 0 ∧ u ≠ 1) :
    ∃ U W : ℚ,
      W^2 = U^3 + U^2 - 2*U ∧
      U ≠ -2 ∧ U ≠ 0 ∧ U ≠ 1 := ...
```

That map is not the same as completing the square; completing the square gives

```text
(2*w + u + 1)^2 = 1 - 2*u + u^2 + 4*u^3,
```

not `W^2 = U^3 + U^2 - 2*U`.

---

## 3. Cyclic order 16

### 3.1 Standard condition

For order `16`, the geometric/Tate-normal-form computation is naturally nested because one first enforces a rational square root of `1-α^2`.  The explicit statement is:

There is a curve over `F` with a point of order `16` if and only if for some

```text
α ∈ F \ {-1,0,1}
```

at least one of the following four quantities lies in `F`:

```text
z1,z3 = α*sqrt(1-α^2)
        ± sqrt( α*(α^2-1)*(1 + sqrt(1-α^2) - α*(1 + α + sqrt(1-α^2))) ),

z2,z4 = α*sqrt(1-α^2)
        ± sqrt( α*(α^2-1)*(1 - sqrt(1-α^2) - α*(1 + α - sqrt(1-α^2))) ).
```

This is unpleasant to formalize directly, so over `ℚ` one rationally parametrizes the first square root.

### 3.2 Rational parametrization and square conditions

If

```text
sqrt(1 - α^2) ∈ ℚ,
```

then write either

```text
α = (m^2 - 1)/(m^2 + 1)
```

or

```text
α = 2*m/(m^2 + 1),
```

with

```text
m ∈ ℚ \ {-1,0,1}
```

up to the usual redundant parametrizations.

Substituting into the nested square condition gives the two explicit square obstructions:

```text
d1(m) = (m^4 - 1)*(m^2 - 2*m - 1),
d2(m) = m*(m^2 + 1)*(m^2 + 2*m - 1).
```

Thus, over `ℚ`, a point of order `16` gives

```text
∃ m z : ℚ,
  m ≠ -1 ∧ m ≠ 0 ∧ m ≠ 1 ∧
  (z^2 = d1(m) ∨ z^2 = d2(m)).
```

This is the standard cyclic `16` obstruction in an explicit form.

### 3.3 Tate-normal-form parameters for one branch

One normal form obtained over `ℚ(sqrt(d1))` is

```text
y^2 = x^3 + ((m^4 - 1)^2 - 4*m^2*(m^4 + 1))*x^2 + 16*m^8*x.
```

Equivalently, in a Tate-normal-form convention, one branch can be written as

```text
y^2 + ((m^4 + 2*m^2 - 1)/m^2)*x*y + (m^4 - 1)*y
  = x^3 + (m^2 - 1)*x^2.
```

For the other branch, a Tate-normal form is

```text
y^2 + (1-c)*x*y - b*y = x^3 - b*x^2,

b = - m*(m - 1)^2/(m^2 + 1)^2,
c = - 2*m*(m - 1)^2/((m^2 + 1)*(m + 1)^2).
```

This branch is associated with the `d2` square condition.

### 3.4 Nondegeneracy/cusps for order 16

The excluded `m` values

```text
m = -1, 0, 1
```

are cusp/degenerate parameters.  In the explicit formulas they cause one of the following:

* the marked point has smaller order;
* the Tate normal form is singular;
* a denominator in the parametrization vanishes;
* the supposed order-`16` construction collapses to a cusp on `X_1(16)`.

So the Lean theorem should output the nondegenerate condition explicitly:

```lean
-- schematic
 theorem cyclic_order16_to_standard_obstruction
    (h : HasRationalPointOfOrder E 16) :
    ∃ m z : ℚ,
      m ≠ -1 ∧ m ≠ 0 ∧ m ≠ 1 ∧
      (z^2 = (m^4 - 1)*(m^2 - 2*m - 1) ∨
       z^2 = m*(m^2 + 1)*(m^2 + 2*m - 1)) := ...
```

If the project's final obstruction curve is

```text
W^2 = U^3 - U^2 - U,
```

then again add a separate map theorem from the standard `d1/d2` obstruction to that model:

```lean
-- schematic; fill with the actual project map
 theorem standard_C16_to_project_N16_obstruction
    {m z : ℚ}
    (hm : m ≠ -1 ∧ m ≠ 0 ∧ m ≠ 1)
    (hz : z^2 = (m^4 - 1)*(m^2 - 2*m - 1) ∨
          z^2 = m*(m^2 + 1)*(m^2 + 2*m - 1)) :
    ∃ U W : ℚ,
      W^2 = U^3 - U^2 - U ∧
      U ≠ -1 ∧ U ≠ 0 ∧ U ≠ 1 := ...
```

---

## 4. Lean formalization plan

### File 1: Tate normal form extraction

Prove once:

```lean
theorem orderN_to_tateNF
    (N : ℕ)
    (hN : 4 ≤ N)
    (h : HasRationalPointOfOrder E N) :
    ∃ b c : ℚ,
      tateNonsingular b c ∧
      addOrderOf (tateP b c) = N := ...
```

or use the existing `TateNFDivision.lean` theorem.

### File 2: N=14 algebra

Use the group table/line-incidence derivation to prove:

```lean
theorem tateNF_order14_to_C14
    {b c : ℚ}
    (h : addOrderOf (tateP b c) = 14) :
    ∃ u w : ℚ,
      w^2 + u*w + w = u^3 - u ∧
      u ≠ -1 ∧ u ≠ 0 ∧ u ≠ 1 := ...
```

The main polynomial identity is the quadratic in `v`:

```text
u^2*(-3 - 6*u + u^2)
+ 2*u*(-1 + 4*u + u^2)*v
+ (u - 1)^2*v^2 = 0.
```

Then introduce

```text
z = ((u - 1)^2*v/u - (1 - 4*u - u^2))/2
```

when `u ≠ 0`, and verify

```text
z^2 = 1 - 2*u + u^2 + 4*u^3.
```

Equivalently use `w = (z - u - 1)/2` and verify

```text
w^2 + u*w + w = u^3 - u.
```

### File 3: N=16 algebra

Prove:

```lean
theorem tateNF_order16_to_C16_standard
    {b c : ℚ}
    (h : addOrderOf (tateP b c) = 16) :
    ∃ m z : ℚ,
      m ≠ -1 ∧ m ≠ 0 ∧ m ≠ 1 ∧
      (z^2 = (m^4 - 1)*(m^2 - 2*m - 1) ∨
       z^2 = m*(m^2 + 1)*(m^2 + 2*m - 1)) := ...
```

Here the algebra is longer but still finite.  Avoid nested radicals in Lean by choosing the rational parametrization of `α^2+s^2=1` first.

### File 4: standard obstruction to project obstruction

If your rational-point files are already for

```text
N=14: W^2 = U^3 + U^2 - 2*U,
N=16: W^2 = U^3 - U^2 - U,
```

put the additional transformations here and make them purely algebraic:

```lean
theorem C14_standard_to_C14_project : ... := by
  -- define U,W as rational functions of u,w
  -- field_simp; ring_nf

theorem C16_standard_to_C16_project : ... := by
  -- define U,W as rational functions of m,z
  -- field_simp; ring_nf
```

Do not mix this with the Tate-normal-form proof.  Keeping it separate makes it clear which identities are Kubert/Rabarison and which are project-specific model changes.

---

## 5. What to avoid

Do not state directly that Kubert's order-`14` table gives

```text
W^2 = U^3 + U^2 - 2*U.
```

The standard order-`14` computation gives

```text
w^2 + u*w + w = u^3 - u
```

or

```text
z^2 = 1 - 2*u + u^2 + 4*u^3.
```

Similarly, do not state directly that the standard order-`16` computation gives

```text
W^2 = U^3 - U^2 - U.
```

The standard computation gives the `d1/d2` square conditions above.  If those are equivalent to the chosen project obstruction model, formalize that equivalence as its own explicit rational-map lemma.
