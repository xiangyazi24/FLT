# N13 genus-two zeta API audit

## Verdict

At Mathlib commit `96fd0fff3b8837985ae21dd02e712cb5df72ec05`,
there is no ready API that takes the point counts of a genus-two curve over
`F_q` and `F_{q^2}`, constructs its Weil numerator, and identifies evaluation
at one with the cardinality of its Jacobian over `F_q`.

The repository likewise has no such bridge theorem.  Its existing N13 files
provide concrete curve/function-field/Mumford infrastructure, while
`scratch/X1_13_PointCount.lean` only counts affine points over `F_5` and
`F_7`.  `scratch/N13_FAKE2_TO_POINTS.md` already records the separate
geometric seam needed at `q=2`.

## What is available

* `Mathlib.AlgebraicGeometry.EllipticCurve.LFunction` defines
  `WeierstrassCurve.localPolynomial`.  Its good-reduction branch is the
  degree-two elliptic formula
  `1 - a*T + q*T^2`, using the cardinality of the affine Weierstrass point
  type.  It is not a genus-two or general-curve interface.
* `Mathlib.NumberTheory.FunctionField` provides abstract function fields and
  their rings of integers.
* `Mathlib.NumberTheory.ClassNumber.FunctionField` proves finiteness of the
  class group of that affine ring and defines `FunctionField.classNumber`.
  It does not supply a curve zeta function, a degree-zero Picard/Jacobian
  object, or a theorem expressing this class number from `N_1,N_2`.
* `Mathlib.AlgebraicGeometry.FunctionField` constructs the function field of
  an integral scheme, but contains no point-count/zeta/Jacobian bridge.
* The only algebraic-geometry `Jacobian` directory in this Mathlib checkout is
  `AlgebraicGeometry/EllipticCurve/Jacobian`; here “Jacobian” means
  projective coordinates for a Weierstrass cubic, not the Jacobian variety
  of a genus-two curve.

Searches over all Mathlib and repository Lean files for combinations of
`hyperelliptic`, `curve zeta`, `Weil polynomial`, `point count`,
`finite field`, `Jacobian cardinality`, and related names found no reusable
theorem of the required shape.  The only local-polynomial hit was the
elliptic `WeierstrassCurve.localPolynomial`.

## Structural arithmetic layer

`FLT/Assumptions/MazurProof/N13WeilTwo.lean` formalizes the elementary
Newton-identity layer on top of the proved `F₂` and `F₄` counts:

```text
N1 = q + 1 - s1
N2 = q^2 + 1 - (s1^2 - 2*s2).
```

For `q=2` and `N1=N2=6`, these equations uniquely give
`s1=-3` and `s2=5`.  The corresponding reciprocal polynomial is

```text
P(T)=1+3*T+5*T^2+6*T^3+4*T^4,
```

and the file proves `P(1)=19`.  It deliberately does not pretend that the
missing geometric zeta/Jacobian theorem is already formalized.

Validation command:

```text
lake build FLT.Assumptions.MazurProof.N13GoodModelTwo \
  FLT.Assumptions.MazurProof.N13WeilTwo
```
