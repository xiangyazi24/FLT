# Q1255 (dm1): complete 2-isogeny descent chain for `20.a4`

## Executive summary

Let

```text
E  : y^2 = x^3 + x^2 - x        = x(x^2 + x - 1)
E' : Y^2 = X^3 - 2X^2 + 5X     = X(X^2 - 2X + 5)
```

and let

```text
φ  : E  → E'
φ̂ : E' → E
```

be the standard 2-isogeny and its dual. The rational kernel points are

```text
ker φ(Q)  = {O, T},   T  = (0,0) ∈ E(Q)
ker φ̂(Q) = {O, T'},  T' = (0,0) ∈ E'(Q).
```

The two local obstructions you verified should be used as follows:

```text
C_E(5)(Q_5)      = ∅    via no primitive solution mod 125
C_E'(-1)(Q_2)    = ∅    via no primitive solution mod 16
```

The key point is that these obstructions do **not** make the two Selmer groups trivial. Each Selmer group still has the forced class coming from the rational kernel point:

```text
Sel^{φ̂}(E/Q)  = { 1, -1 }
Sel^{φ}(E'/Q) = { 1,  5 }.
```

Then the descent exact sequence gives

```text
#(E(Q)  / φ̂(E'(Q))) = 2
#(E'(Q) / φ(E(Q)))  = 2.
```

Finally the 2-isogeny product exact sequence gives

```text
#(E(Q) / 2E(Q)) = (#(E'(Q)/φE(Q)) * #(E(Q)/φ̂E'(Q))) / 2
               = (2 * 2) / 2
               = 2.
```

Since `E(Q)[2] = {O,(0,0)}` has cardinal `2`, Mordell-Weil finite generation gives

```text
#(E(Q) / 2E(Q)) = 2^rank(E/Q) * #E(Q)[2]
               = 2^(rank(E/Q) + 1).
```

Thus

```text
2^(rank(E/Q) + 1) = 2,
```

so

```text
rank(E/Q) = 0.
```

This is the formalization chain. The local computations eliminate the **extra Selmer generator** in each isogeny descent; the rational 2-torsion classes remain and are exactly what makes each Selmer group have size `2`.

## 1. The curves and the isogenies

For a curve in the form

```text
E_{a,b} : y^2 = x^3 + a x^2 + b x = x(x^2 + ax + b)
```

with rational 2-torsion point `T = (0,0)`, the standard 2-isogenous curve is

```text
E'_{a,b} : Y^2 = X^3 - 2a X^2 + (a^2 - 4b)X.
```

Here `a = 1`, `b = -1`, hence

```text
a' = -2a = -2,
b' = a^2 - 4b = 1 - 4(-1) = 5,
```

so

```text
E' : Y^2 = X^3 - 2X^2 + 5X.
```

The isogeny has kernel

```text
E[φ] = {O, (0,0)}.
```

The dual isogeny has kernel

```text
E'[φ̂] = {O, (0,0)}.
```

For this specific pair, both curves have exactly one nonzero rational 2-torsion point:

```text
E(Q)[2]  = {O, (0,0)}
E'(Q)[2] = {O, (0,0)}.
```

Indeed:

```text
E[2]  : x(x^2 + x - 1) = 0,      disc(x^2 + x - 1) = 5, not a square in Q;
E'[2] : X(X^2 - 2X + 5) = 0,     disc(X^2 - 2X + 5) = -16, not a square in Q.
```

For the rank calculation below, the important consequences are

```text
#E(Q)[2] = 2,
#E'[φ̂](Q) = 2,
φ(E(Q)[2]) = {O}.
```

The last equality holds because `E(Q)[2] = ker φ(Q)` for this curve.

## 2. The descent maps

For

```text
E_{a,b} : y^2 = x^3 + ax^2 + bx
```

with dual isogeny `φ̂ : E' → E`, the usual 2-isogeny descent map is

```text
α_E : E(Q) → Q*/Q*²
```

given by

```text
α_E(O)       = 1,
α_E((0,0))   = b,
α_E((x,y))   = x mod Q*²,    if x ≠ 0.
```

Its kernel is

```text
ker α_E = φ̂(E'(Q)).
```

Therefore it induces an injection

```text
E(Q) / φ̂(E'(Q)) ↪ Q*/Q*².
```

For this curve, `b = -1`, so the rational kernel point `T = (0,0)` contributes the nontrivial class

```text
α_E(T) = -1.
```

Thus

```text
{1, -1} ⊆ image(α_E) ⊆ Sel^{φ̂}(E/Q).
```

For the isogenous curve

```text
E' : Y^2 = X^3 - 2X^2 + 5X,
```

the analogous map is

```text
α_E' : E'(Q) → Q*/Q*²
```

with

```text
α_E'(O)       = 1,
α_E'((0,0))   = 5,
α_E'((X,Y))   = X mod Q*²,    if X ≠ 0.
```

Its kernel is

```text
ker α_E' = φ(E(Q)).
```

So it induces

```text
E'(Q) / φ(E(Q)) ↪ Q*/Q*²,
```

and the kernel point `T' = (0,0)` contributes

```text
α_E'(T') = 5.
```

Thus

```text
{1, 5} ⊆ image(α_E') ⊆ Sel^{φ}(E'/Q).
```

## 3. The homogeneous spaces

For

```text
E_{a,b} : y^2 = x^3 + ax^2 + bx,
```

the squareclass `d ∈ Q*/Q*²` is represented by a principal homogeneous space, usually written in one of the equivalent quartic forms

```text
C_E(d) : N^2 = d M^4 + a M^2 Z^2 + (b/d) Z^4,
```

or after clearing denominators by whatever integral normalization your Lean development uses.

The exact normalization does not matter for the abstract descent argument, but the local obstruction theorem must be stated for the **same** normalization used by the descent map.

For this curve, with `a = 1`, `b = -1`, the space is

```text
C_E(d) : N^2 = d M^4 + M^2 Z^2 - d^{-1} Z^4.
```

For `d = 5`, an integral cleared form is

```text
5 N^2 = 25 M^4 + 5 M^2 Z^2 - Z^4.
```

Your computation says that this has no primitive solution modulo `125`, hence

```text
C_E(5)(Q_5) = ∅.
```

For `E'`, with `a' = -2`, `b' = 5`, the space is

```text
C_E'(d) : N^2 = d M^4 - 2 M^2 Z^2 + (5/d) Z^4.
```

For `d = -1`, an equivalent integral form is obtained by substituting `d = -1`; use the exact integral model from your Lean code. Your computation says that the `d' = -1` space has no primitive solution modulo `16`, hence

```text
C_E'(-1)(Q_2) = ∅.
```

The formal local step should be a lemma of this shape:

```lean
-- Schematic only: use your actual homogeneous-space predicates.
theorem no_Q5_point_C_E_5
    (hmod : NoPrimitiveSolutionMod125_C_E_5) :
    ¬ LocallySolubleAt 5 (C_E 5) := by
  -- p-adic point -> clear denominators -> primitive Z_p solution
  -- -> reduce mod 125 -> contradiction.
  exact by
    -- your existing exhaustive computation supplies `hmod`
    -- and the valuation/clearing-denominators lemma supplies this implication
    admit

theorem no_Q2_point_C_Eprime_neg_one
    (hmod : NoPrimitiveSolutionMod16_C_Eprime_neg_one) :
    ¬ LocallySolubleAt 2 (C_Eprime (-1)) := by
  -- same pattern, reduce a primitive 2-adic solution modulo 16
  exact by
    admit
```

The final committed Lean proof must not use `admit`; these are just the theorem shapes.

## 4. The Selmer groups

The isogeny Selmer groups are the local-solubility subgroups:

```text
Sel^{φ̂}(E/Q)
  = { d ∈ Q*/Q*² | C_E(d)(Q_v) ≠ ∅ for every place v },

Sel^{φ}(E'/Q)
  = { d ∈ Q*/Q*² | C_E'(d)(Q_v) ≠ ∅ for every place v }.
```

They fit into the standard Kummer/Selmer exact sequences:

```text
0 → E(Q) / φ̂(E'(Q))
  → Sel^{φ̂}(E/Q)
  → Ш(E'/Q)[φ̂]
  → 0,
```

and

```text
0 → E'(Q) / φ(E(Q))
  → Sel^{φ}(E'/Q)
  → Ш(E/Q)[φ]
  → 0.
```

The first injection is induced by `α_E`; the second is induced by `α_E'`.

## 5. Candidate classes and the role of `d = 5`, `d' = -1`

The bad primes are `2` and `5`, so the standard support lemma says Selmer classes lie in the finite squareclass group supported on

```text
S = {∞, 2, 5}.
```

Equivalently, the ambient finite group is generated by

```text
[-1], [2], [5] ∈ Q*/Q*².
```

For this specific pair, the preliminary local conditions reduce both Selmer searches to the subgroup generated by `[-1]` and `[5]`. In other words, the candidate classes are

```text
H = {1, -1, 5, -5} ⊂ Q*/Q*².
```

This candidate reduction is a necessary formal lemma. In Lean, isolate it before using the two final obstructions:

```lean
-- Schematic names. Replace `SqClass` and membership predicates by your actual API.
theorem Sel_hat_E_subset_candidates :
    Sel_hat_E ≤ {1, -1, 5, -5} := by
  -- support at bad primes + local tests eliminating classes involving 2
  admit

theorem Sel_phi_Eprime_subset_candidates :
    Sel_phi_Eprime ≤ {1, -1, 5, -5} := by
  -- same support/local reduction for E'
  admit
```

Without this candidate-reduction lemma, the two obstructions alone are not enough: they rule out `5` in the first Selmer group and `-1` in the second, but they say nothing by themselves about classes involving `2`.

Now use the forced kernel classes:

```text
-1 ∈ Sel^{φ̂}(E/Q),   because α_E((0,0)) = -1;
 5 ∈ Sel^{φ}(E'/Q),  because α_E'((0,0)) = 5.
```

### First Selmer group

You verified

```text
C_E(5)(Q_5) = ∅.
```

Therefore

```text
5 ∉ Sel^{φ̂}(E/Q).
```

Since `Sel^{φ̂}(E/Q)` is a subgroup of `Q*/Q*²`, and since `-1 ∈ Sel^{φ̂}(E/Q)`, this also rules out `-5`:

```text
if -5 ∈ Sel^{φ̂}(E/Q), then (-1) * (-5) = 5 ∈ Sel^{φ̂}(E/Q), contradiction.
```

Together with the candidate reduction

```text
Sel^{φ̂}(E/Q) ⊆ {1, -1, 5, -5},
```

this proves

```text
Sel^{φ̂}(E/Q) = {1, -1}.
```

So

```text
#Sel^{φ̂}(E/Q) = 2.
```

### Second Selmer group

You verified

```text
C_E'(-1)(Q_2) = ∅.
```

Therefore

```text
-1 ∉ Sel^{φ}(E'/Q).
```

Since `5 ∈ Sel^{φ}(E'/Q)`, this also rules out `-5`:

```text
if -5 ∈ Sel^{φ}(E'/Q), then 5 * (-5) = -1 ∈ Sel^{φ}(E'/Q), contradiction.
```

Together with the candidate reduction

```text
Sel^{φ}(E'/Q) ⊆ {1, -1, 5, -5},
```

this proves

```text
Sel^{φ}(E'/Q) = {1, 5}.
```

So

```text
#Sel^{φ}(E'/Q) = 2.
```

## 6. From Selmer groups to the two descent quotients

The exact sequences give injections

```text
E(Q) / φ̂(E'(Q))  ↪ Sel^{φ̂}(E/Q),
E'(Q) / φ(E(Q))  ↪ Sel^{φ}(E'/Q).
```

Therefore

```text
#(E(Q) / φ̂(E'(Q))) ≤ 2,
#(E'(Q) / φ(E(Q))) ≤ 2.
```

But each quotient has at least two elements, because the rational kernel point gives a nontrivial descent class:

```text
O, (0,0) ∈ E(Q)  map to 1, -1 in Q*/Q*²;
O, (0,0) ∈ E'(Q) map to 1,  5 in Q*/Q*².
```

Hence

```text
#(E(Q) / φ̂(E'(Q))) = 2,
#(E'(Q) / φ(E(Q))) = 2.
```

Equivalently, the Ш-parts in the two isogeny exact sequences are zero:

```text
Ш(E'/Q)[φ̂] = 0,
Ш(E/Q)[φ]  = 0,
```

though this vanishing is not needed for the rank calculation.

Formal Lean lemma shape:

```lean
-- Schematic.
theorem quotient_card_eq_two_of_selmer_eq_pair
    (hSel : Sel_hat_E = {1, -1})
    (hKernelClass : alpha_E T = -1) :
    Nat.card (E_Q_mod_dual_image) = 2 := by
  -- injection into Selmer gives `≤ 2`
  -- the two classes `1` and `-1` in the image give `≥ 2`
  admit
```

Do the analogous theorem for `E'` with `{1,5}`.

## 7. The isogeny product exact sequence

Let

```text
A = E(Q),
B = E'(Q),
ψ = φ̂.
```

The compositions satisfy

```text
ψ ∘ φ = [2] on A,
φ ∘ ψ = [2] on B.
```

There is an exact sequence

```text
0
→ B[ψ] / φ(A[2])
→ B / φ(A)
→ A / 2A
→ A / ψ(B)
→ 0.
```

The maps are explicit:

```text
B[ψ] / φ(A[2]) → B / φ(A)
  is induced by inclusion B[ψ] ⊂ B,

B / φ(A) → A / 2A
  sends the class of Q ∈ B to the class of ψ(Q) ∈ A,

A / 2A → A / ψ(B)
  is the natural quotient map.
```

Exactness check:

* The map `B / φ(A) → A / 2A` is well-defined because

```text
ψ(φ(P)) = 2P.
```

* Its kernel consists of classes `Q mod φ(A)` with `ψ(Q) ∈ 2A = ψ(φ(A))`. Thus `Q - φ(P) ∈ B[ψ]`, giving the kernel term `B[ψ]/φ(A[2])`.

* Its cokernel is `A/ψ(B)` because `2A = ψ(φ(A)) ⊆ ψ(B)`.

For our curve,

```text
B[ψ] = E'(Q)[φ̂] = {O,T'}           has cardinal 2,
A[2] = E(Q)[2] = {O,T} = ker φ,
φ(A[2]) = {O}.
```

Therefore

```text
#(B[ψ] / φ(A[2])) = 2.
```

Taking cardinalities in the exact sequence gives

```text
#(A / 2A)
  = #(B / φ(A)) * #(A / ψ(B)) / #(B[ψ] / φ(A[2]))
  = 2 * 2 / 2
  = 2.
```

So

```text
#(E(Q) / 2E(Q)) = 2.
```

Formal Lean theorem shape:

```lean
-- Schematic group-theory theorem, independent of elliptic curves.
theorem card_mod_two_of_isogeny_quotients
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (ψ : B →+ A)
    (hψφ : ψ.comp φ = AddMonoidHom.mulLeft 2) -- replace by actual API
    (hφψ : φ.comp ψ = AddMonoidHom.mulLeft 2)
    -- plus finite quotient hypotheses and kernel-card hypotheses
    : Nat.card (A ⧸ AddSubgroup.map (AddMonoidHom.mulLeft 2) ⊤) = 2 := by
  -- instantiate the exact sequence above and take cardinalities
  admit
```

In practice it may be easier to prove the exact sequence directly for your concrete quotient definitions rather than introduce a maximally general theorem.

## 8. From `#E(Q)/2E(Q) = 2` to rank zero

Mordell-Weil says `E(Q)` is a finitely generated abelian group. For any finitely generated abelian group `A`,

```text
#(A / 2A) = 2^rank(A) * #A[2].
```

For our curve,

```text
#E(Q)[2] = 2.
```

Thus

```text
#(E(Q) / 2E(Q)) = 2^rank(E/Q) * 2.
```

But the isogeny calculation gave

```text
#(E(Q) / 2E(Q)) = 2.
```

Therefore

```text
2^rank(E/Q) * 2 = 2,
```

hence

```text
2^rank(E/Q) = 1,
```

and so

```text
rank(E/Q) = 0.
```

Formal Lean theorem shape:

```lean
-- Schematic; use the rank definition already present in the project.
theorem rank_eq_zero_of_mod_two_card_eq_two_and_two_torsion_card_eq_two
    (A : Type*) [AddCommGroup A]
    [Module ℤ A] [Module.Finite ℤ A]
    (hmod2 : Nat.card (A ⧸ twoMultipleSubgroup A) = 2)
    (htwo : Nat.card {a : A // (2 : ℕ) • a = 0} = 2) :
    moduleRankOverZ A = 0 := by
  -- Use structure theorem / `A ≃ ℤ^r × finite torsion`.
  -- Then `#A/2A = 2^r * #A[2]`.
  admit
```

Again, no `admit` in the final Lean proof; this is the formal target to isolate.

## 9. Minimal list of Lean facts to formalize

Here is the clean dependency graph.

### Curve/isogeny facts

```text
E(Q)[2] = {O, (0,0)}
E'(Q)[φ̂] = {O, (0,0)}
φ(E(Q)[2]) = {O}
φ̂ ∘ φ = [2]
φ ∘ φ̂ = [2]
```

### Descent-map facts

```text
ker α_E  = φ̂(E'(Q))
ker α_E' = φ(E(Q))
α_E(O) = 1
α_E((0,0)) = -1
α_E'(O) = 1
α_E'((0,0)) = 5
```

### Candidate-reduction facts

```text
Sel^{φ̂}(E/Q)  ⊆ {1, -1, 5, -5}
Sel^{φ}(E'/Q) ⊆ {1, -1, 5, -5}
```

These include the support-at-bad-primes argument and the local checks eliminating classes involving `2`.

### Local obstruction facts

```text
C_E(5)(Q_5) = ∅
C_E'(-1)(Q_2) = ∅
```

Your exhaustive computations supply these after the p-adic clearing-denominators lemma:

```text
no primitive solution mod 125 ⇒ no Q_5 solution,
no primitive solution mod 16  ⇒ no Q_2 solution.
```

### Selmer conclusions

```text
Sel^{φ̂}(E/Q)  = {1, -1}
Sel^{φ}(E'/Q) = {1, 5}
```

### Quotient-card conclusions

```text
#(E(Q)  / φ̂(E'(Q))) = 2
#(E'(Q) / φ(E(Q)))  = 2
```

### Rank conclusion

```text
#(E(Q)/2E(Q)) = 2
#E(Q)[2] = 2
#(E(Q)/2E(Q)) = 2^rank(E/Q) * #E(Q)[2]
-----------------------------------------------
rank(E/Q) = 0
```

## 10. Common pitfall

Do not conclude

```text
Sel^{φ̂}(E/Q) = {1}
or
Sel^{φ}(E'/Q) = {1}
```

from the local obstructions. That would contradict the rational kernel points. The correct conclusions are

```text
Sel^{φ̂}(E/Q)  = {1, -1}
Sel^{φ}(E'/Q) = {1, 5}.
```

The obstruction at `d = 5` removes the extra generator in the first Selmer group. The obstruction at `d' = -1` removes the extra generator in the second Selmer group. The forced rational-kernel classes remain.

If your Lean development labels the two homogeneous-space families oppositely, swap the names `φ` and `φ̂` in the display above. The cardinal calculation is invariant: the two Selmer groups must have cardinal `2` and `2`, so the product formula gives `#E(Q)/2E(Q)=2`, hence rank zero.
