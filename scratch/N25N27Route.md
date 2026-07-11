# Order 25 and 27 proof routes

Verified on 2026-07-10 against the repository, LMFDB modular-curve data, and
the cited literature.  This note records the corrected targets for the Lean
formalization.

## Order 27

`CyclicExclusion27.lean` currently describes the Fermat cubic as `X_0(27)`
and assumes that an order-27 point maps to a noncuspidal affine point.  That
description is incorrect: `X_0(27)` has one rational noncuspidal CM point.

The useful quotient is instead the intermediate level-27 curve with labels

* LMFDB `27.216.1-27.a.1.1`;
* Cummins--Pauli `27C1`;
* RSZB `27.216.1.1`.

Its Weierstrass model is

```text
y^2 + y = x^3.
```

It has genus one, analytic rank zero, and precisely the three rational cusp
points `infinity`, `(0,0)`, and `(0,-1)`.  The map from `X_1(27)` to this
curve has degree three.  Thus the existing Fermat-cubic rational-point
classification is reusable after correcting the modular interpretation.  The
remaining geometric seam is an explicit Tate-normal-form map from exact
order-27 data to a noncuspidal point of `27C1`.

For comparison, `X_0(27)` has LMFDB label `27.36.1.a.1`, model
`y^2 + y = x^3 - 7`, two rational cusps, and one rational CM point of
discriminant `-27`.  This explains why the direct `X_0(27)` argument fails.

## Order 25

The relevant Kubert intermediate quotient is

* LMFDB `25.150.4.f.1`;
* Cummins--Pauli `25G4`;
* RSZB `25.150.4.5`.

It is a genus-four rank-zero curve.  `X_1(25)` maps to it with degree two,
and it maps to `X_0(25)` with degree five.  Its canonical model in
projective coordinates `(x:y:z:w)` is the intersection

```text
y^2 - x*z + y*z - x*w + z*w = 0
x*y*z + x^2*w - x*y*w - x*z*w + y*z*w + z^2*w - z*w^2 = 0.
```

The five rational cusps in this model are

```text
(0:0:0:1), (0:-1:1:0), (1:1:0:1), (0:0:1:0), (1:0:0:0).
```

Kubert's 1976 proof uses this genus-four quotient and a Mazur--Tate-type
descent.  Expanding the raw Tate division condition is only the front end:
the formalization must still construct the map to this model and prove that
its rational points are exactly the five cusps (via the rank-zero Jacobian
and the relevant torsion/intersection computation, or an equivalent explicit
descent).

## References

* D. S. Kubert, *Universal Bounds on the Torsion of Elliptic Curves*, Proc.
  London Math. Soc. (3) 33 (1976), 193--237.
* M. A. Kenku, *On the Modular Curves X0(125), X1(25), X1(49)*, J. London
  Math. Soc. (2) 23 (1981), 415--427.
* LMFDB modular-curve records `27.36.1.a.1`, `27.216.1-27.a.1.1`,
  `27.648.13-27.i.1.2`, `25.150.4.f.1`, and `25.600.12-25.j.1.2`.
