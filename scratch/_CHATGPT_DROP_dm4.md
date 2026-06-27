# Q1246 (dm4): small-prime `mazur_cyclic_order_bound` via explicit `X_1(p)` computations

## Executive answer

Yes, but with one important correction.

* For `p = 11`, `X_1(11)` is genus `1`, so it is itself an elliptic curve over `Q`.  The Mordell-Weil computation is literally a computation of `X_1(11)(Q)` as an elliptic-curve group.
* For `p = 13`, `X_1(13)` has genus `2`, so `X_1(13)(Q)` is **not** a Mordell-Weil group.  The Mordell-Weil group you compute is the Jacobian `J_1(13)(Q)`, and then you use Chabauty/Mordell-Weil-sieve style methods to prove that the listed rational points on the curve are exhaustive.

So the right computational split is:

```text
no_order_11 : explicit rank-0 elliptic curve computation for X_1(11)
no_order_13 : explicit genus-2 model + rank-0 Jacobian + Chabauty computation
no_order_17/no_order_19/no_order_23 : possible, but not the same one-line MW computation;
                                   these are higher-genus rational-points problems
no_order_ge_N : remaining hard Mazur/modular-curve core
```

For Lean, this can reduce the axiom only if the computations are imported as certified finite data: model of `X_1(p)`, exhaustive rational point list, and proof that every listed rational point is a cusp.  The Sage/Magma run is good evidence and can produce the certificate, but the code itself is not a formal proof unless the certificate is formalized or trusted.

## Models to use

### `X_1(11)`

Use the standard elliptic model

```text
X_1(11) : y^2 + y = x^3 - x^2.
```

In Sage this is

```python
EllipticCurve(QQ, [0, -1, 1, 0, 0])
```

with Cremona label usually `11a3`.  It has rank `0` and torsion subgroup of order `5`.  Its rational points are

```text
O, (0,0), (0,-1), (1,0), (1,-1),
```

and these are exactly the cusps in this model.  Therefore there is no noncuspidal rational point on `X_1(11)`, hence no elliptic curve over `Q` with a rational point of exact order `11`.

### `X_1(13)`

Use the standard genus-2 model

```text
v^2 + (u^3 + u^2 + 1)v = u^2 + u.
```

After completing the square with

```text
Y = 2v + u^3 + u^2 + 1,
```

this becomes the hyperelliptic model

```text
C_13 : Y^2 = u^6 + 2u^5 + u^4 + 2u^3 + 6u^2 + 4u + 1.
```

The rational points are

```text
u = 0,  Y = ±1,
u = -1, Y = ±1,
∞_+, ∞_-.
```

In the original `(u,v)` model, the finite points are

```text
(0,0), (0,-1), (-1,0), (-1,-1),
```

plus the two points at infinity.  These six points are the cusps.  Thus there is no noncuspidal rational point on `X_1(13)`, hence no elliptic curve over `Q` with a rational point of exact order `13`.

## Sage code for `p = 11` and `p = 13`

The `p = 11` part is pure Sage.  The `p = 13` part uses Sage's Magma interface for the rigorous Chabauty computation.  A bounded pure-Sage search on the genus-2 curve is not enough, because bounded search does not prove that all rational points have been found.

Save this as, for example, `q1246_x1_11_13.sage`, and run it with Sage:

```python
from sage.all import *

try:
    from sage.interfaces.magma import magma
except Exception:
    magma = None


def _sort_points(points):
    return sorted(list(points), key=lambda P: str(P))


def check_x1_11():
    """
    X_1(11): y^2 + y = x^3 - x^2.

    This is an elliptic curve, so X_1(11)(Q) is its Mordell-Weil group.
    The rank is 0, so the rational points are exactly the torsion points.
    """
    E = EllipticCurve(QQ, [0, -1, 1, 0, 0])

    print("\n=== X_1(11) ===")
    print("model: y^2 + y = x^3 - x^2")
    print("a-invariants:", E.a_invariants())
    print("conductor:", E.conductor())
    try:
        print("Cremona label:", E.cremona_label())
    except Exception as err:
        print("Cremona label unavailable in this Sage install:", err)

    rank = E.rank()
    torsion = E.torsion_subgroup()
    points = set(E.torsion_points())

    cusps = {
        E([0, 1, 0]),   # point at infinity
        E([0, 0]),
        E([0, -1]),
        E([1, 0]),
        E([1, -1]),
    }

    print("rank:", rank)
    print("torsion subgroup:", torsion)
    print("#E(Q):", len(points))
    print("E(Q):", _sort_points(points))
    print("cusps:", _sort_points(cusps))

    assert E.conductor() == 11
    assert rank == 0
    assert len(points) == 5
    assert points == cusps

    print("verified: X_1(11)(Q) consists exactly of cusps")
    return E, points


def sage_model_x1_13():
    """
    Construct the completed-square hyperelliptic model of X_1(13) in Sage.

    This does not by itself prove that the displayed rational points are all
    rational points.  The rigorous all-points proof is done below through
    Magma's Chabauty routine.
    """
    R = PolynomialRing(QQ, "u")
    u = R.gen()
    f = u**6 + 2*u**5 + u**4 + 2*u**3 + 6*u**2 + 4*u + 1
    C = HyperellipticCurve(f)

    print("\n=== X_1(13), Sage model ===")
    print("completed-square model: Y^2 =", f)
    print("curve:", C)
    print("genus:", C.genus())
    assert C.genus() == 2
    return C


def check_x1_13_with_magma():
    """
    Rigorous X_1(13)(Q) computation via Sage's Magma interface.

    Magma computes the Mordell-Weil rank bounds for the Jacobian J of the
    genus-2 curve and then applies Chabauty to prove that the rational points
    listed are exhaustive.
    """
    if magma is None:
        raise RuntimeError(
            "Sage's Magma interface is unavailable.  "
            "For p = 13, a bounded Sage search is not a proof; use Magma/Chabauty."
        )

    magma_code = r'''
Qx<x> := PolynomialRing(Rationals());

// Completed-square hyperelliptic model of X_1(13):
//   Y^2 = x^6 + 2*x^5 + x^4 + 2*x^3 + 6*x^2 + 4*x + 1.
C := HyperellipticCurve(x^6 + 2*x^5 + x^4 + 2*x^3 + 6*x^2 + 4*x + 1);
J := Jacobian(C);

rlo, rhi := RankBounds(J);
assert rlo eq 0 and rhi eq 0;

T, phiT := TorsionSubgroup(J);

// Chabauty proves this is the complete set C(Q), not just a search result.
pts := Chabauty(C);

// The six cusps in the completed-square model.
// Affine finite cusps: x = 0, -1 and Y = ±1.
// Since deg(f) = 6 and the leading coefficient is 1, there are two Q-rational
// points at infinity, represented here as (1 : ±1 : 0).
cusps := {
    C![0, 1, 1],
    C![0, -1, 1],
    C![-1, 1, 1],
    C![-1, -1, 1],
    C![1, 1, 0],
    C![1, -1, 0]
};

assert #pts eq 6;
assert &and[ P in pts | P in cusps ];
assert &and[ P in cusps | P in pts ];

print "model C13: Y^2 = x^6 + 2*x^5 + x^4 + 2*x^3 + 6*x^2 + 4*x + 1";
print "genus =", Genus(C);
print "RankBounds(J_1(13)) =", rlo, rhi;
print "TorsionSubgroup(J_1(13)) =", T;
print "X_1(13)(Q) =", pts;
print "verified: X_1(13)(Q) consists exactly of the six cusps";
'''

    print("\n=== X_1(13), Magma Chabauty proof ===")
    print(magma.eval(magma_code))


def main():
    check_x1_11()
    sage_model_x1_13()
    check_x1_13_with_magma()


if __name__ == "__main__":
    main()
```

## Expected mathematical output

For `X_1(11)`, Sage should report:

```text
rank: 0
torsion subgroup: Z/5Z
E(Q) = {O, (0,0), (0,-1), (1,0), (1,-1)}
verified: X_1(11)(Q) consists exactly of cusps
```

For `X_1(13)`, Magma should report that the Jacobian rank bounds are `0, 0`, then `Chabauty(C)` returns exactly six points:

```text
(0 : 1 : 1), (0 : -1 : 1), (-1 : 1 : 1), (-1 : -1 : 1), (1 : 1 : 0), (1 : -1 : 0)
```

Those are exactly the six cusps in the completed-square model.

## How this fits the proposed Lean split

A good split would be:

```text
mazur_cyclic_order_bound
  = small-prime explicit modular-curve certificates
  + large-prime Mazur core
```

For `p = 11`, the certificate is small and elliptic-curve-shaped:

```text
X_1(11) ≅ E : y^2 + y = x^3 - x^2
rank E(Q) = 0
tors E(Q) = Z/5Z
E(Q) = five listed points
all five listed points are cusps
```

For `p = 13`, the certificate is genus-2-shaped:

```text
X_1(13) ≅ C : Y^2 = u^6 + 2u^5 + u^4 + 2u^3 + 6u^2 + 4u + 1
rank J(C)(Q) = 0
Chabauty/Mordell-Weil sieve certificate: C(Q) = six listed points
all six listed points are cusps
```

Then the moduli interpretation gives:

```text
noncuspidal point of X_1(p)(Q)
  ↔ elliptic curve over Q with a rational point of exact order p.
```

Since the rational points for `p = 11, 13` are all cusps, there is no rational point of exact order `11` or `13`.

## Caution for `p = 17, 19, 23`

The same philosophy is valid, but the computations stop being simple Mordell-Weil computations of a curve:

```text
genus X_1(p) = (p - 5)(p - 7) / 24  for prime p ≥ 5.
```

So:

```text
p = 11 : genus 1
p = 13 : genus 2
p = 17 : genus 5
p = 19 : genus 7
p = 23 : genus 12
```

For `p ≥ 17`, one needs explicit high-genus models, Jacobian decompositions/rank information, and rational-points methods such as Chabauty, Mordell-Weil sieve, quotient strategies, or precomputed LMFDB/literature certificates.  That can still be used to shrink the axiom, but it should be treated as separate certified rational-points input, not as a uniform easy Sage `MW group of X_1(p)` computation.
