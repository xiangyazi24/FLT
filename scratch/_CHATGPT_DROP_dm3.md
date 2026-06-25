# Q593 (dm3): separability of `preΨ' n`

## Bottom line

I would **not** try to prove separability of all `preΨ' n` by a raw strong induction on the EDS recurrence.  The recurrence is excellent for proving divisibility, gcd/common-root facts, and adjacent non-vanishing, but it is the wrong shape for a global no-double-root proof.

The clean proof is the tangent/étale proof:

> If `char K ∤ n`, then the differential of `[n]` is multiplication by `(n : K)`, hence nonzero.  Therefore `[n]` is unramified at every point.  A double root of the division polynomial would give a nonzero first-order deformation of an `n`-torsion point whose image under `[n]` has zero first-order local parameter.  This contradicts the tangent map formula `d[n] = n`.

In your current Lean ecosystem, the most direct implementation is probably the **dual-number/tangent bridge** version, not the full scheme-theoretic étale version.

---

## Answer to question 1: the even cofactor branch does not close from adjacent non-vanishing

Write, at a fixed `x`,

```text
Ψ(2m) = Ψ(m) * g

g = Ψ(m-1)^2 * Ψ(m+2) - Ψ(m-2) * Ψ(m+1)^2.
```

Assume `Ψ(m)(x) = 0`.  Your adjacent non-vanishing theorem gives

```text
Ψ(m-1)(x) ≠ 0,
Ψ(m+1)(x) ≠ 0.
```

But this alone says essentially nothing decisive about `Ψ(m-2)(x)` and `Ψ(m+2)(x)`.  In particular, adjacent non-vanishing only forbids zeros at distance `1`; it does not forbid zeros at distance `2`.

With a stronger Ward/gcd theorem you can say more.  If `x` has exact division-polynomial rank `r`, then morally

```text
Ψ(k)(x) = 0  iff  r ∣ k.
```

Thus, from `Ψ(m)(x)=0`, one gets `r ∣ m`; and

```text
Ψ(m+2)(x)=0 or Ψ(m-2)(x)=0
```

would force `r ∣ 2`.  So for a normalized `preΨ'` root corresponding to a non-2-torsion point, the terms `Ψ(m±2)(x)` should also be nonzero.  This is a **gcd/Ward** consequence, not an adjacent-nonzero consequence.

However, even after proving all four neighboring terms are nonzero, you still do **not** get `g(x) ≠ 0` formally.  The equation

```text
Ψ(m-1)(x)^2 * Ψ(m+2)(x)
  = Ψ(m-2)(x) * Ψ(m+1)(x)^2
```

is a cancellation relation among nonzero field elements.  Adjacent non-vanishing cannot rule it out.

What is true geometrically is this:

```text
Ψ(2m) = Ψ(m) * g
```

and near a point with `[m]P = O`, the map `[2m]` is `[2] ∘ [m]`.  If the zero of `Ψ(m)` is simple and `(2 : K) ≠ 0`, then composing with `[2]` does not increase its local multiplicity.  Therefore `g(x) ≠ 0`.  But this is already a tangent/unramified statement; it is not a consequence of the recurrence plus adjacent non-vanishing.

So the even branch

```text
Ψ(m)(x)=0, g(x)=0
```

is not where the induction should spend effort.  Proving `g(x)≠0` is basically proving that `[2]` has nonzero tangent at `O`.

The other even branch is even worse for descent:

```text
Ψ(m)(x) ≠ 0,
g(x)=0,
g'(x)=0.
```

A root in this branch corresponds geometrically to a point `P` such that `[m]P` is a nonzero 2-torsion point.  This is not a root of a smaller `Ψ(k)` in any simple way.  Separability here says that the pullback of the reduced 2-torsion divisor under `[m]` is reduced.  Again, this follows from `[m]` being unramified when `(m : K) ≠ 0`, not from induction on the smaller division polynomials.

---

## Odd recurrence: the cubic powers do not solve the exact-order case

For odd

```text
Ψ(2m+1)
```

the recurrence has terms involving powers like `Ψ(m)^3` and `Ψ(m+1)^3`.  These powers help in branches where the root is already a root of one of the smaller factors.  But a generic root of `Ψ(2m+1)` has exact order `2m+1`; it is not a root of any smaller `Ψ(k)`.  In that case the recurrence vanishing is produced by cancellation between two nonzero terms.

Differentiating the recurrence at such a cancellation point gives a large derivative identity, not a descent to a double root of a smaller division polynomial.  So the odd recurrence has the same structural problem: exact-order roots have nowhere to descend.

This is the main reason a strong induction on `n` is unnatural.  Roots of `Ψ(n)` are not usually inherited from smaller `Ψ(k)`; only roots whose order is a proper divisor of `n` descend.

---

## Answer to question 2: Ward/SOMOS is useful, but not sufficient for separability

The Ward determinant identity, or equivalently the EDS/SOMOS package, is very useful for proving facts of the following kind:

```text
common root of Ψ(a) and Ψ(b)
  ⇒ common root of Ψ(gcd a b),
```

and hence exact-rank statements such as

```text
Ψ(r)(x)=0 and r minimal
⇒ Ψ(k)(x)=0 iff r ∣ k.
```

This is exactly the right tool for strengthening `no_adjacent_preΨ_zero` to a full `gcd`/rank-of-apparition theorem.

But squarefreeness is a **multiplicity** statement, not just a common-zero statement.  Ward identities can tell you which indices vanish at `x`; they do not by themselves tell you the order of vanishing of `Ψ(n)` at `x`.

The algebraic theorem that would actually imply separability is a local valuation theorem:

```text
Let r be the exact rank of x.
Then ord_x Ψ(n) = 0 if r ∤ n.
If n = r * q and (q : K) ≠ 0, then
  ord_x Ψ(n) = ord_x Ψ(r).
```

Then one still needs

```text
ord_x Ψ(r) = 1.
```

But that last statement is exactly the tangent-map statement for `[r]` at the corresponding torsion point.  So even a polished Ward/SOMOS route ultimately wants the same local tangent input.

Therefore my recommendation is:

1. Use Ward/SOMOS for gcd/exact-rank/no-common-root lemmas.
2. Use the tangent/dual-number bridge for multiplicity-one/separability.
3. Do not try to make the raw recurrence carry the derivative proof globally.

---

## Answer to question 3: degree and leading coefficient help only after root counting

The degree and leading coefficient facts are useful, but not by themselves enough.

For odd `n`, the expected degree is

```text
(n^2 - 1) / 2,
```

matching the number of pairs `{P, -P}` with `P ∈ E[n]`, `P ≠ O`.

For even `n`, the normalized polynomial `preΨ' n = Ψ_n / Ψ_2` has expected degree

```text
(n^2 - 4) / 2,
```

matching the number of pairs `{P, -P}` with `P ∈ E[n] \ E[2]`.

Thus, if you already have:

```text
#E[n] = n^2,
```

and the root classification

```text
roots(preΨ' n)
  = x-coordinates of E[n] \ {O}          -- odd n
  = x-coordinates of E[n] \ E[2]         -- even n,
```

then the degree formula proves separability by counting distinct roots.

But proving `#E[n]=n^2` in characteristic prime to `n` is itself normally proved from the fact that `[n]` is separable/étale, i.e. from the same tangent statement.  So degree/leading coefficient is a good final wrapper if Mathlib already gives you the finite-kernel cardinality theorem, but it is not a shortcut around the tangent bridge.

The leading coefficient `n` or `n/2` is still important because it ensures the polynomial does not degenerate when `(n : K) ≠ 0`.  In characteristic dividing `n`, inseparability really can occur, and the leading term degenerates accordingly.

---

## Recommended Lean route: dual numbers plus the tangent bridge

This is the route I would implement.

### Step 0: use the right separability target

Work with the local no-double-root statement:

```lean
def IsDoubleRoot (f : K[X]) (x : K) : Prop :=
  f.eval x = 0 ∧ f.derivative.eval x = 0
```

Then prove

```lean
∀ x, ¬ IsDoubleRoot (preΨ' n) x
```

and convert to `Polynomial.Separable`/`Squarefree` using the existing polynomial API.

Over an algebraically closed field, this is usually the cleanest interface.

### Step 1: polynomial double root means dual-number vanishing

Prove the standard dual-number lemma:

```lean
lemma eval_dual_eq_zero_of_doubleRoot
    (f : K[X]) (x v : K)
    (h0 : f.eval x = 0)
    (h1 : f.derivative.eval x = 0) :
    Polynomial.eval₂
      (algebraMap K (TrivSqZeroExt K K))
      (TrivSqZeroExt.inl x + TrivSqZeroExt.inr v)
      f = 0 := by
  -- f(x + ε v) = f(x) + ε v f'(x)
  ...
```

You will also want the more precise expansion:

```text
f(x + ε v) = f(x) + ε * v * f'(x).
```

This lemma is pure polynomial arithmetic and should be reusable everywhere.

### Step 2: pick a nonzero first-order lift of a root point

Let `x` be a hypothetical double root of `preΨ' n`.  Since `K` is algebraically closed, choose a point `P` above `x` on the elliptic curve.

The root-classification lemma should give:

```text
[n]P = O.
```

Also, `P` is not a 2-torsion/ramification point for the normalized polynomial:

* if `n` is odd, a nonzero `n`-torsion point cannot be 2-torsion;
* if `n` is even, `preΨ' n = Ψ_n / Ψ_2` removes the 2-torsion factor, so its roots correspond to `E[n] \ E[2]`.

Therefore the `x`-map is unramified at `P`.  In affine coordinates this is the statement that

```text
F_Y(P) = 2*y(P) + a₁*x(P) + a₃ ≠ 0.
```

So you can construct a dual-number lift with nonzero tangent by setting

```text
xε = x(P) + ε,
yε = y(P) + ε * η,
```

where

```text
η = - F_X(P) / F_Y(P).
```

Then `Pε` lies on the curve over `K[ε]`, reduces to `P`, and has nonzero tangent.

In Lean, isolate this as a lemma:

```lean
lemma exists_dual_lift_nonzero_tangent_of_not_twoTorsion
    (P : W.Point K)
    (hP : ¬ IsTwoTorsion P) :
    ∃ Pε : W.Point (TrivSqZeroExt K K),
      reduce Pε = P ∧ tangentCoeff Pε ≠ 0 := by
  ...
```

The exact names will differ, but the content should be this.

### Step 3: double root forces the division-polynomial `Z` coordinate to vanish to first order

For odd `n`, `Ψ_n` is already a polynomial in `x`, so

```text
preΨ' n (xε) = 0
```

implies

```text
Ψ_n(Pε) = 0
```

in the dual-number ring.

For even `n`, use

```text
Ψ_n = Ψ_2 * preΨ' n.
```

Since `preΨ' n (xε)=0`, again

```text
Ψ_n(Pε)=0.
```

Equivalently, in the projective division-polynomial representative for `[n]Pε`, the relevant `ψ_n`/`Z` factor has zero infinitesimal part.

This is where your existing local-parameter coefficient computation should plug in.  The earlier atom has the shape:

```text
coeffε(t([n]Pε))
  = - φ_n(P) / ω_n(P) * snd(ψ_n(Pε)).
```

At a double root, the right side is `0`, because `snd(ψ_n(Pε)) = 0`.  Therefore

```text
coeffε(t([n]Pε)) = 0.
```

### Step 4: tangent bridge gives the contradiction

On the other hand, since `[n]P = O`, translate the deformation `Pε` back to the origin, or equivalently use the tangent map of `[n]` at `P`.  The tangent bridge says:

```text
coeffε(t([n]Pε)) = (n : K) * tangentCoeff(Pε).
```

The chosen lift has

```text
tangentCoeff(Pε) ≠ 0,
```

and the hypothesis `char K ∤ n` is exactly

```text
(n : K) ≠ 0.
```

Since `K` is a field,

```text
(n : K) * tangentCoeff(Pε) ≠ 0.
```

Contradiction.

So no double root exists.

This proves separability without any induction on `n`.

---

## Minimal theorem stack I would target

Here is the Lean-facing decomposition I would aim for.

### Pure polynomial/dual arithmetic

```lean
lemma polynomial_eval_dual
    (f : K[X]) (x v : K) :
    evalDual f (x + ε*v)
      = inl (f.eval x) + inr (v * f.derivative.eval x)
```

Then:

```lean
lemma eval_dual_zero_of_doubleRoot
    (h0 : f.eval x = 0)
    (h1 : f.derivative.eval x = 0) :
    evalDual f (x + ε*v) = 0
```

### Root classification

For roots of the normalized polynomial:

```lean
lemma prePsi'_root_iff_exists_nsmul_eq_zero_not_twoTorsion
    (x : K) :
    (preΨ' n).eval x = 0 ↔
      ∃ P : W.Point K,
        P.x = x ∧ n • P = O ∧ P ≠ O ∧ ¬ IsTwoTorsion P
```

The exact statement may need separate odd/even versions.

For odd `n`, the `¬ IsTwoTorsion P` part follows from `n • P = O`, `P ≠ O`, and `Nat.Coprime n 2`.

For even `n`, it is the point of using `preΨ' n = Ψ_n / Ψ_2`.

### Non-ramified `x` lift

```lean
lemma exists_dual_point_lift_x_direction
    (P : W.Point K) (h2 : ¬ IsTwoTorsion P) :
    ∃ Pε : W.Point (TrivSqZeroExt K K),
      reduce Pε = P ∧
      xCoord Pε = inl P.x + inr 1 ∧
      tangentCoeffAt P Pε ≠ 0
```

This is just implicit differentiation using `F_Y(P) ≠ 0`.

### Division-polynomial local parameter atom

Use/finish the atom of the form:

```lean
lemma localParameterCoeff_nsmul_of_divisionPolynomial
    (hψ0 : ψ_n P = 0)
    (hω : ω_n P ≠ 0)
    (hφ : φ_n P ≠ 0) :
    coeffε (t ([n] Pε))
      = - φ_n P / ω_n P * snd (ψ_n Pε)
```

Then double-root gives `snd (ψ_n Pε)=0`, hence output coefficient is zero.

### Tangent bridge

```lean
lemma tangentCoeff_nsmul
    (Pε : W.Point (TrivSqZeroExt K K))
    (hred : reduce Pε = P)
    (hnP : n • P = O) :
    coeffε (t ([n] Pε))
      = (n : K) * tangentCoeffAt P Pε
```

This is the formal group/tangent-map theorem.  Translation by `-P` reduces it to the already expected theorem at `O`.

### Final no-double-root theorem

```lean
lemma not_doubleRoot_preΨ'
    (hn : (n : K) ≠ 0)
    (x : K) :
    ¬ IsDoubleRoot (preΨ' n) x := by
  intro hdouble
  obtain ⟨P, hxP, hnP, hPO, hP2⟩ :=
    prePsi'_root_iff_exists_nsmul_eq_zero_not_twoTorsion.mp hdouble.1
  obtain ⟨Pε, hred, hxε, htangent_ne⟩ :=
    exists_dual_point_lift_x_direction P hP2

  have hψdual : ψ_n Pε = 0 := by
    -- from polynomial_eval_dual + hdouble.1 + hdouble.2,
    -- with the odd/even normalization bridge
    ...

  have hout_zero : coeffε (t ([n] Pε)) = 0 := by
    -- localParameterCoeff_nsmul_of_divisionPolynomial + hψdual
    ...

  have hout_n : coeffε (t ([n] Pε)) = (n : K) * tangentCoeffAt P Pε := by
    exact tangentCoeff_nsmul Pε hred hnP

  have hout_ne : coeffε (t ([n] Pε)) ≠ 0 := by
    rw [hout_n]
    exact mul_ne_zero hn htangent_ne

  exact hout_ne hout_zero
```

Then convert:

```lean
theorem preΨ'_separable
    (hn : (n : K) ≠ 0) :
    (preΨ' n).Separable := by
  -- over algebraically closed field, use no double roots
  ...
```

---

## Where the existing `Psi3_separable` proof fits

The `n=3` Bézout certificate is still useful as a sanity check and as a small-characteristic/base-case certificate, but it should not be the model for the general proof.

If you continue the recurrence induction route, every new `n` introduces cofactors whose roots correspond to preimages of lower torsion under multiplication maps.  Proving those cofactors squarefree is essentially proving that multiplication maps are unramified.  That is exactly the tangent bridge again.

So the scalable proof should make the tangent bridge explicit and then use it uniformly for all `n` with `(n : K) ≠ 0`.

---

## Warning about the `(4 : K) ≠ 0` hypothesis

Your theorem `no_adjacent_preΨ_zero` assumes `(4 : K) ≠ 0`.  That is fine if your whole development is restricted to characteristic not `2`.  But the natural separability theorem only assumes `char K ∤ n`.

For odd `n`, this allows characteristic `2`.  In that case `no_adjacent_preΨ_zero` is not available as stated, but the tangent/dual-number proof still works: the differential of `[n]` is multiplication by `(n : K)`, which is nonzero.

So another reason not to base the final proof on `no_adjacent_preΨ_zero` is that it may impose an unnecessary characteristic restriction for odd `n`.

---

## Practical recommendation

Use the recurrence/EDS machinery to prove:

```text
root classification, no adjacent roots, gcd/common-root lemmas.
```

Use the tangent bridge to prove:

```text
multiplicity one at every root.
```

That separation of responsibilities is the cleanest Lean architecture.  The recurrence route can explain where the roots are; the tangent route proves they are simple.
