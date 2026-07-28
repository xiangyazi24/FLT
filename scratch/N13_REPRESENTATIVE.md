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

## Minimal remaining seam

The next algebraic lemma is primitive principal scaling:

```lean
forall R : IntegralOrientedRep M,
  exists R' : IntegralOrientedRep M,
    R'.picClass M O = R.picClass M O
    and IdealIsPrimitive M R'.ideal
```

The intended proof is Hermite/content reduction, not enumeration.  Take
the ideal of all `Y`-coefficients of elements of `R.ideal`.  Ideal
stability under multiplication by `Y` shows that the same content divides
the constant coefficients.  Divide by its principal generator.  The new
ideal is integral and contains an element with `Y`-coefficient one; the
principal oriented factor records the corresponding infinity shift.

After this lemma, `exists_semiMumford_of_primitive` supplies graph-form
data for every class.  The next step should be a pure Cantor descent; a
general Riemann--Roch library is not required.

```text
semi-Mumford graph form
  -> principal-equivalent balanced Mumford form
  with natDegree(u) + nInf <= 2.
```

For `D=(u,v,n)` and `d=natDegree(u)`:

- if `d>3`, put `V=v` and `w=(f-V^2)/u`; reducedness of `v` gives
  `degree(w) <= max(6-d,d-2) < d`;
- if `d=3`, put `V=v+u`.  Both `f` and `V^2` are monic of degree six, so
  their leading terms cancel and `degree((f-V^2)/u) <= 2`;
- `V` is congruent to `v` modulo `u`, so `(u,Y-V)=(u,Y-v)`;
- prove the structural ideal identity

  ```text
  I(u,V) * I(w,V) = (Y-V)
  ```

  using the existing Mumford Bezout identity

  ```text
  2V(Y-V) = (f-V^2) - (Y-V)^2.
  ```

Normalize `w`, reduce `V` modulo the new monic polynomial, and recurse on
its strictly smaller degree.  The principal factor `Y-V` and
`ordPlus(Y-V)` must update the oriented infinity coordinate at every step.
The final low-degree step must also choose the natural `nInf` satisfying
the balancing inequality.  These orientation equations, rather than a
class enumeration, are the remaining Cantor seam.
