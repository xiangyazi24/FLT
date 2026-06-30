# Q2378 (dm-codex1): finite S={2,3} full-2-cover certificate boundary for E1

Curve:

```text
E1 : Y^2 = X(X-1)(X+3) over Q.
```

For `Y != 0`, all three factors `X`, `X-1`, and `X+3` are nonzero.  Write their squareclasses using

```text
S23 = {±1, ±2, ±3, ±6}
```

as

```text
X     = d0 * (A/T)^2,
X - 1 = d1 * (B/T)^2,
X + 3 = d3 * (C/T)^2,
```

with `A B C T` nonzero rationals.  Clearing denominators gives the cover equations

```text
d0*A^2 - d1*B^2 = T^2
d3*C^2 - d0*A^2 = 3*T^2
```

and the product squareclass condition

```text
d0*d1*d3 = 1 in Q*/Q*^2.
```

The finite certificate boundary below avoids a full elliptic-curve group API.  It reduces the problem to:

1. a 64-triple squareclass enumeration;
2. real-sign obstructions for half of the triples;
3. finite primitive projective congruence obstructions for the same-sign triples except the four locally/rationally soluble covers;
4. four explicit descent residuals, two nonzero and two degenerate.

The final nonzero affine values are exactly

```text
X = -1,  Y = ±2,  triple (-1,-2,2)
X =  3,  Y = ±6,  triple ( 3, 2,6).
```

Together with `Y=0`, this gives

```text
(-3,0), (0,0), (1,0), (-1,±2), (3,±6).
```

---

## 1. Complete enumeration of product-one S23 triples

Use the canonical representatives in the order

```text
S23 = [1, 2, 3, 6, -1, -2, -3, -6].
```

The following table gives `d3 = rep(d0*d1)` in `Q*/Q*^2`.  Every product-one triple is exactly

```text
(d0, d1, table[d0,d1]).
```

| `d0 \ d1` | `1` | `2` | `3` | `6` | `-1` | `-2` | `-3` | `-6` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `1`  | `1`  | `2`  | `3`  | `6`  | `-1` | `-2` | `-3` | `-6` |
| `2`  | `2`  | `1`  | `6`  | `3`  | `-2` | `-1` | `-6` | `-3` |
| `3`  | `3`  | `6`  | `1`  | `2`  | `-3` | `-6` | `-1` | `-2` |
| `6`  | `6`  | `3`  | `2`  | `1`  | `-6` | `-3` | `-2` | `-1` |
| `-1` | `-1` | `-2` | `-3` | `-6` | `1`  | `2`  | `3`  | `6`  |
| `-2` | `-2` | `-1` | `-6` | `-3` | `2`  | `1`  | `6`  | `3`  |
| `-3` | `-3` | `-6` | `-1` | `-2` | `3`  | `6`  | `1`  | `2`  |
| `-6` | `-6` | `-3` | `-2` | `-1` | `6`  | `3`  | `2`  | `1`  |

The sign patterns with product squareclass one are only

```text
+++, +--, -+-, --+.
```

Only `+++` and `--+` are compatible with a real nonzero point on `Y^2 = X(X-1)(X+3)`:

```text
X > 1      gives signs +++
-3 < X < 0 gives signs --+
```

The other two sign patterns are immediate real obstructions:

```text
+-- : d0 > 0, d1 < 0, d3 < 0.
      Then X > 0 but X+3 < 0, contradiction.

-+- : d0 < 0, d1 > 0, d3 < 0.
      Then X < 0 but X-1 > 0, contradiction.
```

Thus 32 of the 64 triples are disposed of by signs alone:

```text
REAL_SIGN_OBSTRUCTED =
  { (d0,d1,rep(d0*d1)) | d0 > 0, d1 < 0 }
  ∪
  { (d0,d1,rep(d0*d1)) | d0 < 0, d1 > 0 }.
```

The remaining same-sign triples are the following 32.

```text
+++ triples:
(1,1,1),   (1,2,2),   (1,3,3),   (1,6,6),
(2,1,2),   (2,2,1),   (2,3,6),   (2,6,3),
(3,1,3),   (3,2,6),   (3,3,1),   (3,6,2),
(6,1,6),   (6,2,3),   (6,3,2),   (6,6,1).

--+ triples:
(-1,-1,1), (-1,-2,2), (-1,-3,3), (-1,-6,6),
(-2,-1,2), (-2,-2,1), (-2,-3,6), (-2,-6,3),
(-3,-1,3), (-3,-2,6), (-3,-3,1), (-3,-6,2),
(-6,-1,6), (-6,-2,3), (-6,-3,2), (-6,-6,1).
```

Among these, four covers are not to be killed by local congruence; they are the genuine descent boundary:

```text
( 1, 1,1)    degenerate torsion cover, X = 1 only
(-3,-1,3)    degenerate torsion cover, X = 0 or X = -3 only
(-1,-2,2)    nonzero cover, X = -1 only
( 3, 2,6)    nonzero cover, X = 3 only
```

All same-sign triples except these four should be killed by finite primitive projective congruence.  Explicitly, the finite-congruence candidates are:

```text
FINITE_CONGRUENCE_CANDIDATES_PLUS =
[(1,2,2), (1,3,3), (1,6,6),
 (2,1,2), (2,2,1), (2,3,6), (2,6,3),
 (3,1,3), (3,3,1), (3,6,2),
 (6,1,6), (6,2,3), (6,3,2), (6,6,1)]

FINITE_CONGRUENCE_CANDIDATES_MINUS =
[(-1,-1,1), (-1,-3,3), (-1,-6,6),
 (-2,-1,2), (-2,-2,1), (-2,-3,6), (-2,-6,3),
 (-3,-2,6), (-3,-3,1), (-3,-6,2),
 (-6,-1,6), (-6,-2,3), (-6,-3,2), (-6,-6,1)]
```

---

## 2. Lean-checkable local obstruction shape

For a finite modulus `m = p^k`, use the primitive projective residue obstruction:

```text
No primitive residue class (A,B,C,T) mod m satisfies
  d0*A^2 - d1*B^2 = T^2
  d3*C^2 - d0*A^2 = 3*T^2
and at least one of A,B,C,T is not divisible by p.
```

This is stronger and safer than an affine `T != 0 mod p` check.  If a primitive integer solution existed, its reduction modulo `p^k` would be primitive in this sense.  Therefore absence of a primitive projective residue modulo `p^k` gives a valid local obstruction.

A Lean-side finite certificate can be encoded as a decidable statement over `Fin m` / `ZMod m`:

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace FLT.Mazur.N12.LocalCover

/-- `x : Fin m` represents a residue not divisible by the base prime `p`. -/
def residueUnitAtPrime (p m : Nat) (x : Fin m) : Prop :=
  x.val % p ≠ 0

/-- Primitive projective residue modulo `m = p^k`. -/
def primitiveResidue4 (p m : Nat) (A B C T : Fin m) : Prop :=
  residueUnitAtPrime p m A ∨
  residueUnitAtPrime p m B ∨
  residueUnitAtPrime p m C ∨
  residueUnitAtPrime p m T

/-- The two cover equations modulo `m`. -/
def coverResidue
    (m : Nat) [NeZero m]
    (d0 d1 d3 : Int) (A B C T : Fin m) : Prop :=
  let a : ZMod m := A
  let b : ZMod m := B
  let c : ZMod m := C
  let t : ZMod m := T
  ((d0 : ZMod m) * a^2 - (d1 : ZMod m) * b^2 = t^2) ∧
  ((d3 : ZMod m) * c^2 - (d0 : ZMod m) * a^2 = (3 : ZMod m) * t^2)

/-- Certificate proposition for one local obstruction. -/
def noPrimitiveCoverResidue
    (p m : Nat) [NeZero m]
    (d0 d1 d3 : Int) : Prop :=
  ∀ A B C T : Fin m,
    primitiveResidue4 p m A B C T →
      ¬ coverResidue m d0 d1 d3 A B C T

-- Each concrete certificate produced by the script below should become a theorem of this form,
-- closed by `native_decide` or by expanding the finite cases.
--
-- example shape:
-- theorem noPrimitiveCoverResidue_1_2_2_mod8 :
--     noPrimitiveCoverResidue 2 8 1 2 2 := by
--   native_decide

end FLT.Mazur.N12.LocalCover
```

The Python/Sage script in Section 4 emits, for every finite-congruence candidate, the first found primitive projective modulus.  That output is the table to port into Lean.

---

## 3. Genuine descent residuals beyond finite congruence

The following four covers are intentionally not killed by finite local congruence.  They have rational projective points: two are the final nonzero points, and two are degenerate torsion covers.  The exact residual theorem boundary should classify rational solutions of these four covers.

A convenient rational interface is:

```lean
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

namespace FLT.Mazur.N12.CoverDescent

/-- Rational full-2-cover equations for fixed squareclass representatives. -/
def CoverQ (d0 d1 d3 : Int) (A B C T : Rat) : Prop :=
  ((d0 : Rat) * A^2 - (d1 : Rat) * B^2 = T^2) ∧
  ((d3 : Rat) * C^2 - (d0 : Rat) * A^2 = (3 : Rat) * T^2)

/-- The positive nonzero cover gives only X = 3. -/
axiom coverQ_3_2_6_classifies
    {A B C T : Rat}
    (hT : T ≠ 0)
    (h : CoverQ 3 2 6 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2

/-- The negative nonzero cover gives only X = -1. -/
axiom coverQ_neg1_neg2_2_classifies
    {A B C T : Rat}
    (hT : T ≠ 0)
    (h : CoverQ (-1) (-2) 2 A B C T) :
    A^2 = T^2 ∧ B^2 = T^2 ∧ C^2 = T^2

/-- The identity/torsion cover is degenerate: only X = 1, so B = 0. -/
axiom coverQ_1_1_1_degenerate
    {A B C T : Rat}
    (hT : T ≠ 0)
    (h : CoverQ 1 1 1 A B C T) :
    B = 0 ∧ A^2 = T^2 ∧ C^2 = (4 : Rat) * T^2

/-- The other torsion cover is degenerate: only X = 0 or X = -3. -/
axiom coverQ_neg3_neg1_3_degenerate
    {A B C T : Rat}
    (hT : T ≠ 0)
    (h : CoverQ (-3) (-1) 3 A B C T) :
    (A = 0 ∧ B^2 = T^2 ∧ C^2 = T^2) ∨
    (C = 0 ∧ A^2 = T^2 ∧ B^2 = (4 : Rat) * T^2)

end FLT.Mazur.N12.CoverDescent
```

How these residuals close the rational-point theorem:

```text
Given Y != 0, the squareclass extraction has A,B,C,T all nonzero.

(1,1,1)      residual forces B = 0, contradiction.
(-3,-1,3)    residual forces A = 0 or C = 0, contradiction.
(-1,-2,2)    residual forces A^2 = B^2 = C^2 = T^2, hence X = -1 and Y^2 = 4.
(3,2,6)      residual forces A^2 = B^2 = C^2 = T^2, hence X = 3 and Y^2 = 36.
```

Thus the only nonzero `Y` affine points are `(-1,±2)` and `(3,±6)`.  The `Y = 0` branch is the direct cubic-root check `X ∈ {-3,0,1}`.

If desired, the four residuals can later be proved by elementary simultaneous-Pythagorean/infinite-descent quartic arguments rather than by an elliptic-curve group API.  The important formal boundary is that no other squareclass triple reaches this descent layer.

---

## 4. Python/Sage script: enumerate triples and search finite local obstructions

This is a standard Python 3 script; it also runs unchanged under Sage's Python.  It does not use Sage-specific elliptic-curve functionality.  Its purpose is to produce the Lean-portable local certificate table.

Save as, for example:

```text
scripts/e1_s23_cover_cert.py
```

Run:

```text
python3 scripts/e1_s23_cover_cert.py
python3 scripts/e1_s23_cover_cert.py --json
```

Expected behavior:

```text
* 64 product-one triples are enumerated.
* 32 are reported as REAL_SIGN.
* 4 are reported as DESCENT_RESIDUAL.
* every other same-sign triple is reported as MOD p^k with no primitive projective residue.
* if any extra same-sign triple is not obstructed by the searched moduli, the script exits nonzero and prints UNRESOLVED.
```

```python
#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from functools import lru_cache

S23 = [1, 2, 3, 6, -1, -2, -3, -6]

# Squareclass vectors: sign, v2 parity, v3 parity.
VEC = {
    1:  (0, 0, 0),
    2:  (0, 1, 0),
    3:  (0, 0, 1),
    6:  (0, 1, 1),
    -1: (1, 0, 0),
    -2: (1, 1, 0),
    -3: (1, 0, 1),
    -6: (1, 1, 1),
}
REP = {v: k for k, v in VEC.items()}

DESCENT_RESIDUALS = {
    (1, 1, 1): "degenerate torsion cover: X=1 only",
    (-3, -1, 3): "degenerate torsion cover: X=0 or X=-3 only",
    (-1, -2, 2): "nonzero cover: X=-1 only",
    (3, 2, 6): "nonzero cover: X=3 only",
}

# Small prime powers.  The search is intentionally primitive-projective, not affine T=1.
# Extend this list if experimenting; the script fails closed if anything remains unresolved.
DEFAULT_MODULI = [
    (2, 1, 2), (2, 2, 4), (2, 3, 8), (2, 4, 16), (2, 5, 32),
    (3, 1, 3), (3, 2, 9), (3, 3, 27), (3, 4, 81),
    (5, 1, 5), (5, 2, 25),
    (7, 1, 7), (7, 2, 49),
    (11, 1, 11), (13, 1, 13), (17, 1, 17), (19, 1, 19),
    (23, 1, 23), (29, 1, 29), (31, 1, 31), (37, 1, 37),
    (41, 1, 41), (43, 1, 43), (47, 1, 47),
]


def rep_mul(a: int, b: int) -> int:
    """Canonical S23 representative of the product squareclass a*b."""
    va = VEC[a]
    vb = VEC[b]
    return REP[(va[0] ^ vb[0], va[1] ^ vb[1], va[2] ^ vb[2])]


def product_one_triples() -> list[tuple[int, int, int]]:
    triples = [(d0, d1, rep_mul(d0, d1)) for d0 in S23 for d1 in S23]
    assert len(triples) == 64
    assert len(set(triples)) == 64
    # Product-one check in vector form.
    for d0, d1, d3 in triples:
        z = rep_mul(rep_mul(d0, d1), d3)
        assert z == 1, (d0, d1, d3, z)
    return triples


def real_sign_obstructed(d: tuple[int, int, int]) -> bool:
    d0, d1, d3 = d
    # Product-one signs are +++, +--, -+-, --+.
    # Only +++ and --+ occur for real points with Y^2 >= 0 and Y != 0.
    return (d0 > 0 and d1 < 0 and d3 < 0) or (d0 < 0 and d1 > 0 and d3 < 0)


@lru_cache(maxsize=None)
def square_residue_has_unit(m: int, p: int) -> dict[int, bool]:
    """Map square residue r mod m to whether r has a representative x^2 with p ∤ x."""
    out: dict[int, bool] = {}
    for x in range(m):
        r = (x * x) % m
        out[r] = out.get(r, False) or (x % p != 0)
    return out


def has_primitive_projective_solution_mod(
    d: tuple[int, int, int], *, p: int, m: int
) -> bool:
    """Search primitive projective solutions modulo m=p^k.

    Variables enter only through square residues.  A primitive residue means at least
    one of A,B,C,T has a representative not divisible by p.
    """
    d0, d1, d3 = d
    sq_unit = square_residue_has_unit(m, p)
    sqs = list(sq_unit.keys())
    sqset = set(sqs)

    # Equation 1 determines T^2 from A^2 and B^2:
    #   T^2 = d0*A^2 - d1*B^2.
    # Equation 2 is then checked against C^2:
    #   d3*C^2 - d0*A^2 = 3*T^2.
    for a2 in sqs:
        a_unit = sq_unit[a2]
        for b2 in sqs:
            t2 = (d0 * a2 - d1 * b2) % m
            if t2 not in sqset:
                continue
            rhs = (d0 * a2 + 3 * t2) % m
            for c2 in sqs:
                if (d3 * c2 - rhs) % m != 0:
                    continue
                primitive = a_unit or sq_unit[b2] or sq_unit[c2] or sq_unit[t2]
                if primitive:
                    return True
    return False


def first_local_obstruction(
    d: tuple[int, int, int], moduli: list[tuple[int, int, int]]
) -> tuple[int, int, int] | None:
    """Return the first (p,k,m) for which no primitive projective solution exists."""
    for p, k, m in moduli:
        if not has_primitive_projective_solution_mod(d, p=p, m=m):
            return (p, k, m)
    return None


def classify_triple(d: tuple[int, int, int], moduli: list[tuple[int, int, int]]) -> dict:
    if d in DESCENT_RESIDUALS:
        return {"triple": d, "kind": "DESCENT_RESIDUAL", "detail": DESCENT_RESIDUALS[d]}
    if real_sign_obstructed(d):
        return {"triple": d, "kind": "REAL_SIGN", "detail": "incompatible signs for X,X-1,X+3"}
    cert = first_local_obstruction(d, moduli)
    if cert is None:
        return {"triple": d, "kind": "UNRESOLVED", "detail": "extend moduli or promote to descent residual"}
    p, k, m = cert
    return {"triple": d, "kind": "MOD", "p": p, "k": k, "m": m,
            "detail": f"no primitive projective solution modulo {m}={p}^{k}"}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true", help="emit JSON records")
    parser.add_argument("--same-sign-only", action="store_true", help="omit real-sign-obstructed triples")
    args = parser.parse_args()

    triples = product_one_triples()
    records = [classify_triple(d, DEFAULT_MODULI) for d in triples]
    if args.same_sign_only:
        records = [r for r in records if r["kind"] != "REAL_SIGN"]

    unresolved = [r for r in records if r["kind"] == "UNRESOLVED"]

    if args.json:
        print(json.dumps(records, indent=2, sort_keys=True))
    else:
        for r in records:
            d = tuple(r["triple"])
            if r["kind"] == "MOD":
                print(f"{d}: MOD m={r['m']} p={r['p']} k={r['k']} -- {r['detail']}")
            else:
                print(f"{d}: {r['kind']} -- {r['detail']}")

        counts = {}
        for r in records:
            counts[r["kind"]] = counts.get(r["kind"], 0) + 1
        print("COUNTS", counts)

    if unresolved:
        raise SystemExit(f"UNRESOLVED triples: {[tuple(r['triple']) for r in unresolved]}")


if __name__ == "__main__":
    main()
```

---

## 5. Assembly plan for `E1AffineRationalPoints`

Use the following proof split.

### Step A: `Y = 0`

Direct ring/root check:

```text
Y = 0 -> X(X-1)(X+3)=0 -> X ∈ {-3,0,1}.
```

This gives

```text
(-3,0), (0,0), (1,0).
```

### Step B: `Y != 0`, squareclass extraction

Show there exist `d0 d1 d3 ∈ S23` and nonzero `A B C T : Q` satisfying the two cover equations and product-one.  This is the only place where the S-unit support `{2,3}` enters.

### Step C: enumerate the triple

Use the 8-by-8 table above, or a Lean finite enumeration over `S23`:

```text
for d0 in S23:
  for d1 in S23:
    d3 = rep(d0*d1)
```

### Step D: eliminate impossible triples

1. If signs are `+--` or `-+-`, use the real sign contradiction.
2. If the triple is one of the 28 finite-congruence candidates, use the corresponding `noPrimitiveCoverResidue p m d0 d1 d3` theorem emitted by the script.
3. If the triple is one of the four descent residuals, invoke the exact residual theorem from Section 3.

### Step E: conclude the nonzero branch

The degenerate residual covers contradict `A,B,C != 0`; the nondegenerate residual covers give

```text
X = -1 or X = 3.
```

Then evaluate the curve equation:

```text
X = -1 -> Y^2 = 4  -> Y = ±2
X =  3 -> Y^2 = 36 -> Y = ±6
```

This completes the finite-cover certificate boundary for the hard theorem.
