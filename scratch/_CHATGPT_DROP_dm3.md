# Q1195 (dm3): realistic path to a 0-axiom proof of `|E(ℚ)_tors| ≤ 16`

## Bottom line

You cannot prove the bound

```text
|E(ℚ)_tors| ≤ 16
```

from the current A-line infrastructure unless you prove, or import, a cyclic large-order exclusion such as

```lean
no_rational_point_of_order_ge_17 :
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ},
    17 ≤ n → ¬ HasRationalPointOfOrder E n
```

or an equivalent theorem.

The reason is simple: Route 4B controls only the **first invariant factor**.  It proves that the rational torsion group cannot contain full rational `m`-torsion for `m ≥ 3`, so in invariant-factor notation

```text
E(ℚ)_tors ≃ Z/m × Z/n,   m ∣ n,
```

it gives

```text
m ≤ 2.
```

But it gives no bound at all on the cyclic factor `n`.  The real Lie group `E(ℝ)` contains cyclic finite subgroups of arbitrarily large order, so real topology cannot bound `n`.

Therefore the current infrastructure proves no finite uniform bound on `|E(ℚ)_tors|`.  The tightest uniform bound obtainable from it is: **no finite bound**.

## Correction to the proposed `m = 2` argument

The statement

```text
for m = 2, n can be at most 8 because n = 10,12,14,16 are excluded
```

is false without an additional large cyclic-order theorem.

The four proved exclusions

```text
no_Z2_cross_Z10
no_Z2_cross_Z12
no_Z2_cross_Z14
no_Z2_cross_Z16
```

rule out torsion groups containing

```text
Z/2 × Z/10,
Z/2 × Z/12,
Z/2 × Z/14,
Z/2 × Z/16.
```

They do **not** rule out, purely group-theoretically,

```text
Z/2 × Z/18,
Z/2 × Z/22,
Z/2 × Z/26,
Z/2 × Z/34,
Z/2 × Z/38,
...
```

For example, `Z/2 × Z/18` contains no `Z/2 × Z/10`, no `Z/2 × Z/12`, no `Z/2 × Z/14`, and no `Z/2 × Z/16`.  It also has no odd `(Z/p)^2`, no `(Z/2)^3`, and its 2-torsion has exactly four elements.

So the existing noncyclic exclusions do not force `n ≤ 8`.  They force only certain divisibility obstructions on `n`.

## Why no finite bound follows from the current lemmas

For every large integer `N`, the abstract cyclic group

```text
Z/N
```

satisfies all the group-theoretic consequences of the current A-line lemmas:

* invariant factors are `Z/1 × Z/N`;
* it has no full `(Z/m)^2` subgroup for `m ≥ 2`;
* it has no odd `(Z/p)^2` subgroup;
* it has no `(Z/2)^3` subgroup;
* it has no subgroup `Z/2 × Z/10`, `Z/2 × Z/12`, `Z/2 × Z/14`, or `Z/2 × Z/16`;
* its 2-torsion has cardinality at most `2`, hence at most `4`.

Thus any proof using only those lemmas would also prove a false statement about the model `Z/N` for arbitrarily large `N`.  The missing ingredient must be a theorem that forbids cyclic rational points of large exact order.

There is also an unbounded noncyclic family surviving the current restrictions:

```text
Z/2 × Z/(2q)
```

for primes `q ≥ 11`.  These groups have order `4q`, are compatible with `m = 2`, have 2-torsion of size `4`, and avoid the four listed `Z/2 × Z/k` obstructions as long as `2q` is not divisible by `10`, `12`, `14`, or `16`.

So even after Route 4B, there is no uniform finite bound without cyclic-order input.

## What is actually enough for `|T| ≤ 16`?

Assume these ingredients:

1. invariant factors:

   ```text
   E(ℚ)_tors ≃ Z/m × Z/n,   m ∣ n;
   ```

2. Route 4B:

   ```text
   m ≤ 2;
   ```

3. cyclic large-order exclusion:

   ```text
   no rational point of exact order n for n ≥ 17;
   ```

4. the four rank-two exclusions:

   ```text
   no_Z2_cross_Z10,
   no_Z2_cross_Z12,
   no_Z2_cross_Z14,
   no_Z2_cross_Z16.
   ```

Then the proof of `|T| ≤ 16` is short.

### Case `m = 1`

Then torsion is cyclic:

```text
T ≃ Z/n.
```

If `17 ≤ n`, then `T` has a rational point of exact order `n`, contradicting `no_rational_point_of_order_ge_17`.  Hence

```text
n ≤ 16,
```

so

```text
|T| = n ≤ 16.
```

### Case `m = 2`

Since `m ∣ n`, `n` is even.  If `17 ≤ n`, then the second factor gives a rational point of exact order `n`, again contradicting `no_rational_point_of_order_ge_17`.  Hence

```text
n ≤ 16.
```

The even values `n ≤ 16` are

```text
2, 4, 6, 8, 10, 12, 14, 16.
```

The last four are excluded by the existing rank-two lemmas.  Therefore

```text
n ≤ 8,
```

and

```text
|T| = 2n ≤ 16.
```

This is the precise place where the four `no_Z2_cross_Zk` theorems are useful: **after** `no_rational_point_of_order_ge_17` has reduced the second invariant factor to `n ≤ 16`.

## Lean wiring shape once the missing cyclic theorem exists

The final bound theorem should be just arithmetic and dispatching.  The exact names below are schematic, but the dependencies are the right ones.

```lean
import Mathlib
import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.RealTorsionBound

noncomputable section

open scoped WeierstrassCurve.Affine

namespace FLT.MazurProof

/-- Schematic: cyclic large-order exclusion.  This is the real missing Mazur input. -/
-- theorem no_rational_point_of_order_ge_17
--     (E : WeierstrassCurve ℚ) [E.IsElliptic] {n : ℕ}
--     (hn : 17 ≤ n) :
--     ¬ HasRationalPointOfOrder E n := by
--   ...

/-- Schematic final shape of the bound proof. -/
theorem rational_torsion_card_le_sixteen_wiring
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    True := by
  /-
  Real proof outline:

  1. Obtain invariant-factor data:

       T ≃+ ZMod m × ZMod n,  hmn : m ∣ n.

  2. From Route 4B, prove `m ≤ 2` because `ZMod m × ZMod n`
     contains full rational `m`-torsion whenever `m ∣ n`.

  3. Split `m = 1` or `m = 2`.

     * `m = 1`:
         if `17 ≤ n`, use the element `(0, 1)` in `ZMod n`, transported back to torsion,
         to get `HasRationalPointOfOrder E n`, contradiction.
         Hence `n ≤ 16`, so cardinality is at most 16.

     * `m = 2`:
         `2 ∣ n`, so `n` is even.
         if `17 ≤ n`, again get a point of order `n`, contradiction.
         Hence `n ≤ 16`.
         By evenness, `n ∈ {2,4,6,8,10,12,14,16}`.
         Exclude `10,12,14,16` using the four `no_Z2_cross_Zk` theorems.
         Hence `n ≤ 8`, so `2 * n ≤ 16`.
  -/
  trivial

end FLT.MazurProof
```

The proof is conceptually small, but it absolutely depends on `no_rational_point_of_order_ge_17` or an equivalent cyclic-order theorem.

## Can we avoid `no_rational_point_of_order_ge_17`?

No, not if the target is a uniform bound.

A finite uniform bound on torsion immediately implies a cyclic large-order exclusion.  Indeed, if you prove

```text
|E(ℚ)_tors| ≤ 16,
```

then a rational point of exact order `n ≥ 17` is impossible because the cyclic subgroup generated by that point has cardinality `n`, so it already has more than `16` elements.

Thus:

```text
|E(ℚ)_tors| ≤ 16
  ⇒ no_rational_point_of_order_ge_17.
```

So any proof of the bound contains, at least implicitly, a proof of the large cyclic-order exclusion.  You can rename or repackage it, but you cannot avoid it.

## Most realistic 0-axiom route

The most realistic path is **not** to formalize the full positive classification of Mazur's theorem.  It is to formalize the negative pieces needed for the bound:

```text
A. invariant-factor decomposition of rational torsion;
B. Route 4B: first invariant factor `m ≤ 2`;
C. no `Z/2 × Z/10`, `Z/2 × Z/12`, `Z/2 × Z/14`, `Z/2 × Z/16`;
D. no rational point of exact order `n ≥ 17`.
```

Pieces A, B, and C are much smaller than full Mazur.  Piece D is the hard cyclic tail.  It is weaker than the full classification because it does not need to prove which small cyclic groups occur and it does not need to classify all small exceptional cases.  But it is still a major Mazur theorem.

A practical decomposition of D is:

```text
D1. order-divisor lemma:
    point of order n and d ∣ n ⇒ point of order d;

D2. arithmetic reduction:
    if n ≥ 17, then either n has a prime divisor p ≥ 11,
    or n has one of the critical composite divisors
      14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49;

D3. prime tail:
    no rational point of prime order p for p ≥ 11;

D4. finite composite certificates:
    no rational point of exact order
      14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49.
```

D1 and D2 are elementary Lean work.  D4 can be attacked with explicit Tate/Kubert normal forms and per-level rational-point certificates.  D3 is the real Mazur prime-level theorem; it is the largest remaining block.

## What bound can we prove right now without Mazur?

No finite bound.

What the current infrastructure can prove is closer to this structural statement:

```text
E(ℚ)_tors has invariant factors Z/m × Z/n with m ≤ 2,
and if m = 2 then n is not divisible by 10, 12, 14, or 16.
```

That statement still permits groups of arbitrarily large order, such as

```text
Z/N
```

and

```text
Z/2 × Z/(2q)
```

for primes `q ≥ 11`.

So there is no meaningful finite `SOME_BOUND` obtainable from the current lemmas alone.  To get any uniform finite bound, one must add a theorem that restricts the cyclic factor `n`; to get the sharp bound `16`, one essentially needs the cyclic large-order exclusion `no_rational_point_of_order_ge_17` plus the already-proved rank-two exclusions.
