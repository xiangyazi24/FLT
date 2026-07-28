# N13 balanced-representative seam

## Verified production layer

`FLT/Assumptions/MazurProof/SexticMumfordRepresentative.lean` contains no
curve-class enumeration.  It proves the following general statements for
every smooth monic sextic model.

1. `exists_integralRepresentative`

   Every element of `ConcretePic M O` has a representative whose finite
   component is an integral invertible ideal.  The proof lifts through the
   quotient and applies
   `FractionalIdeal.exists_eq_spanSingleton_mul`; the infinity coordinate
   is changed by the same principal oriented factor.

2. `ideal_exists_two_generator_smith_form`

   The affine coordinate ring is free of rank two over `K[X]`, using
   `AdjoinRoot.powerBasis'`.  Mathlib's PID structure theorem
   `Ideal.exists_smith_normal_form` therefore gives every nonzero integral
   ideal a two-element `K[X]`-basis.  This is a structural lattice theorem,
   not a class-number computation.

3. `idealContraction_ne_bot` and `contractionGenerator`

   For a nonzero ideal `J`, its contraction to `K[X]` is nonzero.  If
   `z` is a nonzero element of `J`, then

   ```text
   z * conjugate(z)
   ```

   is a nonzero polynomial element of `J`.  The normalized generator of
   this contraction is therefore a canonical monic polynomial `u`.
   `contractionGenerator_mumfordIdeal` verifies that this construction
   recovers the original `u` on an existing Mumford ideal.

4. `mumfordIdeal_eq_of_contraction_eq_span_of_ySub_mem`

   If the contraction of `J` is `(u)` and `Y-v` belongs to `J`, then

   ```text
   J = (u, Y-v).
   ```

   The proof writes every element uniquely as `p(X)+q(X)Y`, subtracts
   `q(X)(Y-v)`, and contracts the remaining polynomial.

5. `exists_semiMumford_of_primitive`

   Define `IdealIsPrimitive M J` by the existence of an element of `J`
   whose `Y`-coefficient is one.  Every nonzero primitive integral ideal
   has a `SemiMumford` presentation `(u,v,n)` with:

   ```text
   J = (u, Y-v),
   u monic,
   v % u = v,
   u divides f-v^2.
   ```

   The graph element is reduced modulo `u`; the curve divisibility follows
   by multiplying `(Y-v)(Y+v)` and contracting.

6. `classOf_surjective_of_integral_reduction`

   This is the strongest current no-escape interface:

   ```lean
   theorem classOf_surjective_of_integral_reduction
       (reduce :
         forall R : IntegralOrientedRep M,
           exists D : Mumford M,
             classOf M O D = R.picClass M O) :
       Function.Surjective (classOf M O)
   ```

   Thus Kummer construction may assume only `Function.Surjective classOf`;
   uniqueness and `NormalFormData` are unnecessary.

Targeted build:

```text
lake build FLT.Assumptions.MazurProof.SexticMumfordRepresentative
```

passes.  Axiom audit for the Smith, contraction, primitive Mumford,
integral-representative, and final surjectivity theorems reports only:

```text
propext, Classical.choice, Quot.sound
```

There is no `sorry`, custom `axiom`, `native_decide`, or finite
representative table in this layer.

## Mathlib API audit

Useful existing APIs:

- `FractionalIdeal.exists_eq_spanSingleton_mul`: denominator clearing;
- `QuotientGroup.mk'_surjective`: lift a Picard quotient class;
- `AdjoinRoot.powerBasis'`: the rank-two `K[X]` basis;
- `Ideal.exists_smith_normal_form`: finite free PID lattice structure;
- `Ideal.span_singleton_generator`: canonical principal contraction.

The searched Mathlib tree has no algebraic-curve divisor, projective
Picard, or Riemann--Roch theorem that can directly prove the genus-two
degree bound.  `ClassGroup.mk0_surjective` is a Dedekind-domain affine
class-group theorem; it neither carries the chosen infinity orientation
nor supplies an effective divisor of degree at most two.  The present
proof therefore works directly in `ConcretePic`.

## Phase I closed; remaining infinity phase

`SexticMumfordPrimitivePart` now constructs the coefficient-content ideal,
divides it by a colon ideal, and proves the exact factorization

```text
(content) * primitivePart = J.
```

The quotient is primitive and fractionally invertible.  Its oriented
representative subtracts the actual `ordPlus(content)` and is equal to the
original class.  Thus every oriented class enters semi-Mumford graph form.

`SexticMumfordStructuralReduction` then iterates the verified Cantor
complement by well-founded recursion on `natDegree u`.  Above degree three
the cofactor has smaller degree; at degree three the lift `v+u` cancels
the monic degree-six terms.  The result is:

```lean
theorem exists_lowDegreeSemiRepresentative
    (c : ConcretePic M O) :
    ∃ D : LowDegreeSemi M,
      semiMumfordClass M O D.toSemi = c
```

where `D.toSemi.u.natDegree ≤ 2`.  The full oriented class is preserved,
not only its affine ideal class.

The only remaining representative seam is Phase II: move `nInf` between
the two balanced walls while retaining `deg u≤2`.  For the actual N13
polynomial, the relevant cubic is

```text
s = X^3 + 2X^2 + X - 1,
f - s^2 = 4X(X+1).
```

The two adapted cubic lifts should give updates
`n ↦ n+d-3` and `n ↦ n+3-e`; these formulas must be derived from the
existing `ordPlus`/`ordMinus` definitions before implementing the second
well-founded recursion.  No stale polynomial from Q1649 is admissible.

## Fake-Kummer bypass

Phase II is no longer required for the N13 fake-Kummer map.  The new
`N13LowDegreeKummerHom` uses the surjectivity of
`exists_lowDegreeSemiRepresentative` directly.  For a low-degree
semirepresentative `D`, it constructs an auxiliary Mumford datum with the
same `u` and `v` and with `nInf=0`; `deg u≤2` makes this a valid balanced
datum.  This auxiliary object is used only by the already-proved
`u(θ)` evaluator.

Crucially, equality and addition are not tested using the auxiliary
balanced class.  They are tested in

```text
semiMumfordClass M O D.toSemi,
```

with the original integer `nInf`.  The quotient equality supplies the
finite principal-ideal relation, and that relation alone is passed to the
existing Kummer invariance theorem.  Hence the resulting homomorphism is
unconditional and preserves the full oriented semantics; infinity
balancing remains only a normal-form theorem.
