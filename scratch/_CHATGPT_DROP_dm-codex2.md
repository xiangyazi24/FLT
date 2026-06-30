# Q2571 same-orientation step for Euler square pairs

Target family: `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`.

Connector note: the requested target Lean path was not fetchable through the GitHub contents API on `main` or `scratch` during this drop, so the statements below are deliberately self-contained and use only `Mathlib`-level `Int`/`Nat` formulations. They should be pasted into the local namespace/file and renamed to match the existing `EulerSquarePair` API.

## 1. Same-orientation proof

Let

```text
X  = U^2 - V^2,
Y  = 4*U'^2 - V'^2.
```

With the parity convention `U` even and `V` odd,

```text
U = 2u, V = 2v+1
X = 4u^2 - (2v+1)^2
  = 4*(u^2 - v^2 - v) - 1.
```

So `X` is `-1 mod 4`, equivalently `3 mod 4`.  Similarly, for the second triple, if `V'` is odd,

```text
Y = 4*U'^2 - (2v'+1)^2
  = 4*(U'^2 - v'^2 - v') - 1,
```

so `Y` is also `-1 mod 4`.  Notice that the evenness of `U'` is part of the Pythagorean parametrization route, but is not needed for this particular congruence because of the leading factor `4`.

Now assume the signed equations are

```text
D = X or -D = X,
D = Y or -D = Y.
```

The mixed choices are impossible.  For example, if `X = D` and `Y = -D`, then for some integers `m,n`,

```text
D  = 4m - 1,
-D = 4n - 1.
```

Adding gives `0 = 4*(m+n) - 2`, i.e. `2 = 4*(m+n)`, impossible.  The other mixed case is the same.  Therefore either both expressions equal `D`, or both equal `-D`.

This is a **mod 4** proof.  Do not use mod 8 for the same-orientation step: `4*U'^2 - V'^2` is always `7 mod 8` when `V'` is odd, but `U^2 - V^2` is `3 mod 8` or `7 mod 8` depending on `U/2`.  A mod-8 proof would introduce a false extra divisibility convention on `U`.

The positivity and oddness of `D` are still important upstream: they are used to obtain the primitive Pythagorean parametrizations and the parity conventions.  But once the signed equations and parities are already present, the core sign-comparison lemma is even stronger and does not need `D > 0` or `Odd D`.

## 2. Lean-facing same-orientation lemmas over `Int`

These snippets avoid finite sign types.  They use signed equations of the form `D = expr` or `-D = expr`.

```lean
import Mathlib

namespace N12FourSquaresAP

lemma int_even_sq_sub_odd_sq_eq_four_mul_sub_one
    {U V : ℤ}
    (hU : ∃ u : ℤ, U = 2 * u)
    (hV : ∃ v : ℤ, V = 2 * v + 1) :
    ∃ m : ℤ, U ^ 2 - V ^ 2 = 4 * m - 1 := by
  rcases hU with ⟨u, rfl⟩
  rcases hV with ⟨v, rfl⟩
  refine ⟨u ^ 2 - v ^ 2 - v, ?_⟩
  ring

lemma int_four_mul_sq_sub_odd_sq_eq_four_mul_sub_one
    {U V : ℤ}
    (hV : ∃ v : ℤ, V = 2 * v + 1) :
    ∃ m : ℤ, 4 * U ^ 2 - V ^ 2 = 4 * m - 1 := by
  rcases hV with ⟨v, rfl⟩
  refine ⟨U ^ 2 - v ^ 2 - v, ?_⟩
  ring

lemma int_same_sign_of_four_mul_sub_one
    {D x y : ℤ}
    (hx4 : ∃ m : ℤ, x = 4 * m - 1)
    (hy4 : ∃ n : ℤ, y = 4 * n - 1)
    (hxD : x = D ∨ x = -D)
    (hyD : y = D ∨ y = -D) :
    (x = D ∧ y = D) ∨ (x = -D ∧ y = -D) := by
  rcases hx4 with ⟨m, hx4⟩
  rcases hy4 with ⟨n, hy4⟩
  rcases hxD with hxD | hxD
  · rcases hyD with hyD | hyD
    · exact Or.inl ⟨hxD, hyD⟩
    · exfalso
      subst x
      subst y
      omega
  · rcases hyD with hyD | hyD
    · exfalso
      subst x
      subst y
      omega
    · exact Or.inr ⟨hxD, hyD⟩

lemma int_same_orientation_of_pythagorean_signed_forms
    {D U V Up Vp : ℤ}
    (hUeven : ∃ u : ℤ, U = 2 * u)
    (hVodd : ∃ v : ℤ, V = 2 * v + 1)
    (hVpodd : ∃ v : ℤ, Vp = 2 * v + 1)
    (h1 : D = U ^ 2 - V ^ 2 ∨ -D = U ^ 2 - V ^ 2)
    (h2 : D = 4 * Up ^ 2 - Vp ^ 2 ∨ -D = 4 * Up ^ 2 - Vp ^ 2) :
    (D = U ^ 2 - V ^ 2 ∧ D = 4 * Up ^ 2 - Vp ^ 2) ∨
      (-D = U ^ 2 - V ^ 2 ∧ -D = 4 * Up ^ 2 - Vp ^ 2) := by
  have hx4 : ∃ m : ℤ, U ^ 2 - V ^ 2 = 4 * m - 1 :=
    int_even_sq_sub_odd_sq_eq_four_mul_sub_one
      (U := U) (V := V) hUeven hVodd
  have hy4 : ∃ n : ℤ, 4 * Up ^ 2 - Vp ^ 2 = 4 * n - 1 :=
    int_four_mul_sq_sub_odd_sq_eq_four_mul_sub_one
      (U := Up) (V := Vp) hVpodd
  have hxD : U ^ 2 - V ^ 2 = D ∨ U ^ 2 - V ^ 2 = -D := by
    rcases h1 with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm
  have hyD : 4 * Up ^ 2 - Vp ^ 2 = D ∨
      4 * Up ^ 2 - Vp ^ 2 = -D := by
    rcases h2 with h2 | h2
    · exact Or.inl h2.symm
    · exact Or.inr h2.symm
  have hs := int_same_sign_of_four_mul_sub_one
    (D := D) (x := U ^ 2 - V ^ 2) (y := 4 * Up ^ 2 - Vp ^ 2)
    hx4 hy4 hxD hyD
  rcases hs with hs | hs
  · rcases hs with ⟨hx, hy⟩
    exact Or.inl ⟨hx.symm, hy.symm⟩
  · rcases hs with ⟨hx, hy⟩
    exact Or.inr ⟨hx.symm, hy.symm⟩

lemma int_refinement_equation_of_same_orientation
    {D U V Up Vp a b c d : ℤ}
    (hU : U = 2 * a * b)
    (hV : V = c * d)
    (hUp : Up = 2 * a * c)
    (hVp : Vp = b * d)
    (hsame :
      (D = U ^ 2 - V ^ 2 ∧ D = 4 * Up ^ 2 - Vp ^ 2) ∨
        (-D = U ^ 2 - V ^ 2 ∧ -D = 4 * Up ^ 2 - Vp ^ 2)) :
    b ^ 2 * (4 * a ^ 2 + d ^ 2) =
      c ^ 2 * (16 * a ^ 2 + d ^ 2) := by
  have heq : U ^ 2 - V ^ 2 = 4 * Up ^ 2 - Vp ^ 2 := by
    rcases hsame with hsame | hsame
    · rw [← hsame.1, ← hsame.2]
    · rw [← hsame.1, ← hsame.2]
  subst U
  subst V
  subst Up
  subst Vp
  ring_nf at heq ⊢
  nlinarith [heq]

end N12FourSquaresAP
```

If the local file already has `Even U` and `Odd V` fields, make a thin wrapper that converts them into the explicit witnesses `∃ u, U = 2*u` and `∃ v, V = 2*v+1`.  I recommend keeping the core lemma above in the explicit-witness form because it avoids fighting Lean's `%` normalization and keeps the proof `ring`/`omega` only.

A repository-facing theorem can include `hDodd : Odd D` or `0 < D`; those hypotheses are harmless but not needed by the core sign lemma after the signed forms are established.

## 3. Convention audit

The stated parametrization is correct **only with signs**.

For `(2A)^2 + D^2 = C^2`, with the even Pythagorean parameter named `U` and the odd one named `V`, the odd leg is

```text
U^2 - V^2.
```

Because `U` is even and `V` is odd, this expression is `3 mod 4`.  Therefore:

* if `D ≡ 3 mod 4`, then `D = U^2 - V^2`;
* if `D ≡ 1 mod 4`, then `D = V^2 - U^2`, equivalently `-D = U^2 - V^2`.

So a convention that always writes `D = U^2 - V^2` is wrong unless one has separately fixed `D ≡ 3 mod 4` or chosen the parameter order to make that true.

For `(4A)^2 + D^2 = B^2`, the even leg is `4A = 2*(2U')*V'`, so the signed odd leg is

```text
(2U')^2 - V'^2 = 4*U'^2 - V'^2.
```

Thus the signed formula

```text
τ*D = 4*U'^2 - V'^2
```

is the right one.  If `D ≡ 1 mod 4`, the positive equation is instead

```text
D = V'^2 - 4*U'^2.
```

The same-orientation lemma says exactly that the first and second signed odd legs lie on the same side of `D`:

```text
D  = U^2 - V^2      and D  = 4*U'^2 - V'^2,
```

or

```text
-D = U^2 - V^2      and -D = 4*U'^2 - V'^2.
```

Equivalently, the absolute-value conventions open consistently.

Also note that the second formula is not `U'^2 - V'^2`; the factor `4` is essential because the even Pythagorean parameter is `2U'`.

## 4. Path from same orientation to the refinement equation

After same orientation, the two signed odd legs are equal:

```text
U^2 - V^2 = 4*U'^2 - V'^2.
```

The common refinement should be applied to the equality of products after dividing the even parameters by `2`:

```text
A = U*V = U'*V',
U  = 2X,
U' = 2X',

X*V = X'*V'.
```

With `gcd(X,V)=1` and `gcd(X',V')=1`, isolate a `Nat` factorization theorem of this shape:

```text
Nat.coprime_product_refinement:
  0 < X -> 0 < V -> 0 < X' -> 0 < V' ->
  Nat.Coprime X V -> Nat.Coprime X' V' ->
  X * V = X' * V' ->
  ∃ a b c d : ℕ,
    X = a*b ∧ V = c*d ∧ X' = a*c ∧ V' = b*d.
```

Then returning to the original even parameters gives

```text
U  = 2*a*b,
V  = c*d,
U' = 2*a*c,
V' = b*d.
```

Substitute these into the equal-oriented odd-leg equation:

```text
(2ab)^2 - (cd)^2 = 4*(2ac)^2 - (bd)^2.
```

Expanding and rearranging gives

```text
b^2*(4*a^2 + d^2) = c^2*(16*a^2 + d^2),
```

which is the `int_refinement_equation_of_same_orientation` lemma above.

For the final square extraction, isolate a second `Nat` residual if Mathlib does not already have the valuation version you want:

```text
Nat.eq_squares_of_coprime_cross_square_mul:
  Nat.Coprime b c ->
  Nat.Coprime X Y ->
  b^2 * X = c^2 * Y ->
  ∃ r s : ℕ, X = r^2 ∧ Y = s^2.
```

Use it with

```text
X = 4*a^2 + d^2,
Y = 16*a^2 + d^2.
```

The required coprimality `Nat.Coprime X Y` follows from

```text
gcd(4*a^2 + d^2, 16*a^2 + d^2) | 12*a^2
```

and also divides `d^2`; with `Nat.Coprime a d`, it divides `12`.  Since both `X` and `Y` are odd, the gcd is not divisible by `2`.  The only remaining possible prime is `3`, and mod `3` gives

```text
4*a^2 + d^2 ≡ a^2 + d^2,
16*a^2 + d^2 ≡ a^2 + d^2.
```

If `3` divided both, then `a^2 + d^2 ≡ 0 mod 3`.  This forces `3 | a` and `3 | d`, contradicting `Nat.Coprime a d`.  Hence the gcd is `1`.

Once the extraction gives

```text
4*a^2 + d^2  = r^2,
16*a^2 + d^2 = s^2,
```

the smaller Euler pair is `(A_new,D_new,B_new,C_new) = (a,d,s,r)`.  Positivity and `d` odd come from the positive refinement factors.  The parity `a` even follows from the square congruence: if `a` were odd and `d` is odd, then

```text
4*a^2 + d^2 ≡ 4 + 1 ≡ 5 mod 8,
```

not a square.  Finally, `A = 2*a*b*c*d`, with positive `b,c,d`, gives `a < A`, so this is the intended descent.
