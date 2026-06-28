# Q1937 (dm4): obstruction-curve data for Mazur N = 14 and N = 16

Data for axiom-discharge proofs analogous to `RationalPointsC20.lean`.

## Source anchors checked

Source: John Cremona `ecdata`, the Cremona/LMFDB elliptic-curve tables.

Relevant file-format facts from `docs/file-format.txt`:

- `AI` = reduced minimal Weierstrass coefficient vector `[a1,a2,a3,a4,a6]`.
- `R` = rank.
- `T` = torsion order.
- `TOR` = torsion structure.
- `LMFDB_LABEL` is the LMFDB label; in each isogeny class, LMFDB curve numbering is lexicographic by `[a1,a2,a3,a4,a6]`.

Concrete rows used:

```text
# docs/curves.1-1000.html
80 B 1  [0,-1,0,4,-4]    rank 0, torsion order 2
96 A 1  [0,1,0,-2,0]     rank 0, torsion order 4

# alllabels/alllabels.00000-09999
80 b 4 -> 80.b1
80 b 3 -> 80.b2
80 b 2 -> 80.b3
80 b 1 -> 80.b4

96 a 1 -> 96.b3
```

## N = 14

Obstruction curve:

```text
E14 : w^2 = u^3 + u^2 - 2*u = u*(u+2)*(u-1)
```

Reduced Weierstrass coefficients:

```text
[a1,a2,a3,a4,a6] = [0,1,0,-2,0]
```

Database identification:

```text
old Cremona label: 96a1
LMFDB label:       96.b3
rank:              0
torsion order:     4
```

Since the cubic splits over Q with roots `-2`, `0`, and `1`, the three nontrivial rational 2-torsion points are

```text
(-2,0), (0,0), (1,0).
```

Rank is 0 and torsion order is 4, so the full Mordell-Weil group is

```text
E14(Q) ~= Z/2Z x Z/2Z.
```

All rational points:

```text
O, (-2,0), (0,0), (1,0).
```

Projective form:

```text
[0:1:0], [-2:0:1], [0:0:1], [1:0:1].
```

Answer to rank question: yes, rank 0.

## N = 16

Obstruction curve:

```text
E16 : w^2 = u^3 - u^2 - u = u*(u^2-u-1)
```

Reduced Weierstrass coefficients:

```text
[a1,a2,a3,a4,a6] = [0,-1,0,-1,0]
```

The model `[0,-1,0,-1,0]` lies in the old Cremona `80b` isogeny class. Starting with the class representative

```text
E0 : y^2 = x^3 - x^2 + 4*x - 4    # [0,-1,0,4,-4], old 80b1
```

translate the rational 2-torsion point `x = 1` to the origin by `x = X + 1`:

```text
Y^2 = X^3 + 2*X^2 + 5*X.
```

For `Y^2 = X^3 + a*X^2 + b*X`, the standard 2-isogenous curve is

```text
Y^2 = X^3 - 2*a*X^2 + (a^2 - 4*b)*X.
```

With `a = 2`, `b = 5`, this is

```text
Y^2 = X^3 - 4*X^2 - 16*X.
```

Scaling `X = 4*u`, `Y = 8*w` gives exactly

```text
w^2 = u^3 - u^2 - u.
```

So `E16` is the old Cremona `80b2` curve, and `alllabels` maps it to

```text
LMFDB label: 80.b3
```

The class has rank 0; rank is preserved under rational isogeny. For torsion, good reductions give

```text
#E16(F_3) = 2
#E16(F_7) = 10
```

so rational torsion injects into both and has order dividing `gcd(2,10) = 2`. Since `(0,0)` is rational 2-torsion, the torsion subgroup is exactly `Z/2Z`.

Equivalently, the cubic has only one rational root, `u = 0`; the quadratic factor `u^2 - u - 1` has discriminant `5`, not a square in Q.

Therefore:

```text
LMFDB label: 80.b3
E16(Q) ~= Z/2Z
rank: 0
```

All rational points:

```text
O, (0,0).
```

Projective form:

```text
[0:1:0], [0:0:1].
```

Answer to rank question: yes, rank 0.
