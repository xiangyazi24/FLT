# Q1157 (dm3): 7-smooth `n ≥ 17`, `n ≤ 100`, and what the current A-line lemmas actually exclude

## Executive answer

The 7-smooth integers `n` with `17 ≤ n ≤ 100` are:

```text
18, 20, 21, 24, 25, 27, 28, 30,
32, 35, 36, 40, 42, 45, 48, 49,
50, 54, 56, 60, 63, 64, 70, 72,
75, 80, 81, 84, 90, 96, 98, 100.
```

Using only the listed existing proved infrastructure, **none of these exact orders can be excluded**.

The reason is uniform and important:

```text
A point of exact order n only forces a cyclic subgroup Cₙ.
```

All listed A-line results are rank/two-invariant-factor obstructions.  They rule out some noncyclic torsion shapes, such as `Z/2 × Z/10`, `Z/2 × Z/12`, `Z/2 × Z/14`, `Z/2 × Z/16`, `(Z/p)^2` for odd `p`, and `(Z/2)^3`.  But a cyclic group `Z/n` contains none of those forbidden noncyclic subgroups.

For every `n` in the list, the abstract cyclic group

```text
Z/n
```

satisfies all the group-theoretic consequences of the listed proved results:

* invariant factors are `Z/1 × Z/n`;
* it has a point of exact order `n`;
* it does not contain `Z/2 × Z/10`, `Z/2 × Z/12`, `Z/2 × Z/14`, or `Z/2 × Z/16`;
* it does not contain `(Z/p)^2` for any odd prime `p`;
* it does not contain `(Z/2)^3`;
* its 2-torsion has size `1` if `n` is odd and `2` if `n` is even, hence certainly at most `4`.

Therefore the current proved infrastructure can at best reduce many cases to the remaining cyclic case.  It cannot prove `¬ HasRationalPointOfOrder E n` for any of the 7-smooth `n ≥ 17` without an additional cyclic-order exclusion theorem.

## The complete list

```lean
import Mathlib

noncomputable section

namespace FLT.MazurALine

/-- The 7-smooth integers `n` with `17 ≤ n ≤ 100`. -/
def sevenSmooth_ge17_le100 : List ℕ :=
  [18, 20, 21, 24, 25, 27, 28, 30,
   32, 35, 36, 40, 42, 45, 48, 49,
   50, 54, 56, 60, 63, 64, 70, 72,
   75, 80, 81, 84, 90, 96, 98, 100]

/-- Cyclic exact-order obstructions that would cover the 7-smooth window by divisibility. -/
def neededCyclicDivisorsForSevenSmoothWindow : List ℕ :=
  [14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49]

end FLT.MazurALine
```

The second list is not currently available from the stated infrastructure.  It is the kind of cyclic Mazur input that would actually close the 7-smooth window.

## Why the suggested `n = 18` argument does not work

Suppose `P` has exact order `18`.

Then:

```text
2P  has order 9,
9P  has order 2.
```

But these points lie in the same cyclic subgroup `⟨P⟩ ≃ Z/18`.  They do **not** produce an independent `3`-torsion direction, so they do not give `(Z/3)^2`.  They also do not produce one of the forbidden groups `Z/2 × Z/10`, `Z/2 × Z/12`, `Z/2 × Z/14`, or `Z/2 × Z/16`.

In fact, even the noncyclic abstract group

```text
Z/2 × Z/18
```

survives all the listed obstructions: its 2-torsion has size `4`, it has no odd `(Z/p)^2`, and the second factor has no element of order `10`, `12`, `14`, or `16`.

So the current infrastructure does not exclude order `18`.

## Why the suggested `n = 20` argument also does not finish

Suppose `P` has exact order `20`.

If the full torsion group has invariant factors

```text
E(ℚ)_tors ≃ Z/a × Z/b,   a ∣ b,
```

and `20 ∣ b`, then the listed results can rule out many noncyclic possibilities:

* if an odd prime divides `a`, then `(Z/p)^2` embeds in torsion, contradicting `no_odd_prime_square_in_torsion`;
* if `2 ∣ a`, then `Z/2 × Z/10` embeds, contradicting `no_Z2_cross_Z10`.

Thus the current infrastructure can force the first invariant factor to be `a = 1` in the order-`20` case.  But that only says the torsion is cyclic in this branch.  It does **not** rule out

```text
E(ℚ)_tors ≃ Z/20.
```

So the current infrastructure does not exclude order `20` either.  What is missing is a cyclic theorem:

```lean
-- schematic name
no_rational_point_of_order_20 :
  ¬ HasRationalPointOfOrder E 20
```

## Complete case table

In the table below, “cyclic witness” means the abstract group `Z/n`, which satisfies all listed group-theoretic restrictions while still having an element of exact order `n`.  Therefore the current infrastructure cannot prove a contradiction for that row.

The last column gives a cyclic exact-order divisor that would be enough to kill the row, using the elementary fact that a point of order `n` gives a point of order `d` whenever `d ∣ n`.

| `n` | factorization | What the current listed lemmas do | Missing cyclic divisor theorem that would kill it |
|---:|---|---|---|
| 18 | `2 · 3^2` | Not excluded.  Cyclic witness `Z/18`; even `Z/2 × Z/18` also survives. | no exact order `18` |
| 20 | `2^2 · 5` | Noncyclic first factor is ruled out, but cyclic witness `Z/20` survives. | no exact order `20` |
| 21 | `3 · 7` | Noncyclic first factor is ruled out, but cyclic witness `Z/21` survives. | no exact order `21` |
| 24 | `2^3 · 3` | Noncyclic first factor is ruled out by `Z/2 × Z/12`, but cyclic witness `Z/24` survives. | no exact order `24` |
| 25 | `5^2` | Noncyclic first factor is ruled out, but cyclic witness `Z/25` survives.  `no_odd_prime_square_in_torsion` does not ban cyclic `5^2`. | no exact order `25` |
| 27 | `3^3` | Not excluded.  Cyclic witness `Z/27`; `Z/2 × Z/54` also survives the listed obstructions. | no exact order `27` |
| 28 | `2^2 · 7` | Noncyclic first factor is ruled out by `Z/2 × Z/14`, but cyclic witness `Z/28` survives. | no exact order `14` |
| 30 | `2 · 3 · 5` | Noncyclic first factor is ruled out by `Z/2 × Z/10`, but cyclic witness `Z/30` survives. | no exact order `15` or `30` |
| 32 | `2^5` | Noncyclic first factor with enough 2-power is ruled out by `Z/2 × Z/16`, but cyclic witness `Z/32` survives. | no exact order `16` |
| 35 | `5 · 7` | Noncyclic first factor is ruled out, but cyclic witness `Z/35` survives. | no exact order `35` |
| 36 | `2^2 · 3^2` | Noncyclic first factor is ruled out by `Z/2 × Z/12`, but cyclic witness `Z/36` survives. | no exact order `18` |
| 40 | `2^3 · 5` | Noncyclic first factor is ruled out by `Z/2 × Z/10`, but cyclic witness `Z/40` survives. | no exact order `20` |
| 42 | `2 · 3 · 7` | Noncyclic first factor is ruled out by `Z/2 × Z/14`, but cyclic witness `Z/42` survives. | no exact order `14` or `21` |
| 45 | `3^2 · 5` | Noncyclic first factor is ruled out, but cyclic witness `Z/45` survives. | no exact order `15` |
| 48 | `2^4 · 3` | Noncyclic first factor is ruled out by `Z/2 × Z/12` or `Z/2 × Z/16`, but cyclic witness `Z/48` survives. | no exact order `16` or `24` |
| 49 | `7^2` | Noncyclic first factor is ruled out, but cyclic witness `Z/49` survives.  `no_odd_prime_square_in_torsion` does not ban cyclic `7^2`. | no exact order `49` |
| 50 | `2 · 5^2` | Noncyclic first factor is ruled out by `Z/2 × Z/10`, but cyclic witness `Z/50` survives. | no exact order `25` |
| 54 | `2 · 3^3` | Not excluded.  Cyclic witness `Z/54`; even `Z/2 × Z/54` also survives. | no exact order `18` or `27` |
| 56 | `2^3 · 7` | Noncyclic first factor is ruled out by `Z/2 × Z/14`, but cyclic witness `Z/56` survives. | no exact order `14` |
| 60 | `2^2 · 3 · 5` | Noncyclic first factor is ruled out by `Z/2 × Z/10` or `Z/2 × Z/12`, but cyclic witness `Z/60` survives. | no exact order `15`, `20`, or `24` |
| 63 | `3^2 · 7` | Noncyclic first factor is ruled out, but cyclic witness `Z/63` survives. | no exact order `21` |
| 64 | `2^6` | Noncyclic first factor is ruled out by `Z/2 × Z/16`, but cyclic witness `Z/64` survives. | no exact order `16` |
| 70 | `2 · 5 · 7` | Noncyclic first factor is ruled out by `Z/2 × Z/10` or `Z/2 × Z/14`, but cyclic witness `Z/70` survives. | no exact order `14` or `35` |
| 72 | `2^3 · 3^2` | Noncyclic first factor is ruled out by `Z/2 × Z/12`, but cyclic witness `Z/72` survives. | no exact order `18` or `24` |
| 75 | `3 · 5^2` | Noncyclic first factor is ruled out, but cyclic witness `Z/75` survives. | no exact order `15` or `25` |
| 80 | `2^4 · 5` | Noncyclic first factor is ruled out by `Z/2 × Z/10` or `Z/2 × Z/16`, but cyclic witness `Z/80` survives. | no exact order `16` or `20` |
| 81 | `3^4` | Not excluded.  Cyclic witness `Z/81`; `Z/2 × Z/162` also survives the listed obstructions. | no exact order `27` |
| 84 | `2^2 · 3 · 7` | Noncyclic first factor is ruled out by `Z/2 × Z/12` or `Z/2 × Z/14`, but cyclic witness `Z/84` survives. | no exact order `14`, `21`, or `24` |
| 90 | `2 · 3^2 · 5` | Noncyclic first factor is ruled out by `Z/2 × Z/10`, but cyclic witness `Z/90` survives. | no exact order `15` or `18` |
| 96 | `2^5 · 3` | Noncyclic first factor is ruled out by `Z/2 × Z/12` or `Z/2 × Z/16`, but cyclic witness `Z/96` survives. | no exact order `16` or `24` |
| 98 | `2 · 7^2` | Noncyclic first factor is ruled out by `Z/2 × Z/14`, but cyclic witness `Z/98` survives. | no exact order `14` or `49` |
| 100 | `2^2 · 5^2` | Noncyclic first factor is ruled out by `Z/2 × Z/10`, but cyclic witness `Z/100` survives. | no exact order `20` or `25` |

## The actual group-theoretic obstruction pattern

Let the finite rational torsion group be written using the existing invariant-factor theorem as

```text
E(ℚ)_tors ≃ Z/a × Z/b,   a ∣ b.
```

If `E(ℚ)` has a point of exact order `n`, then `n ∣ b`.

The listed lemmas imply the following restrictions on `a`:

1. If an odd prime `p` divides `a`, then `(Z/p)^2` embeds in torsion, contradicting `no_odd_prime_square_in_torsion`.  Therefore `a` has no odd prime factor.
2. Thus `a` is a power of `2`.
3. If `2 ∣ a` and one of `10`, `12`, `14`, `16` divides `b`, then one of the forbidden groups

   ```text
   Z/2 × Z/10,
   Z/2 × Z/12,
   Z/2 × Z/14,
   Z/2 × Z/16
   ```

   embeds in torsion.

This explains why many rows in the table say that the noncyclic first factor is ruled out.  But the case `a = 1` always remains.  That is the cyclic case:

```text
E(ℚ)_tors ≃ Z/b.
```

A point of exact order `n` is perfectly compatible with this group-theoretic shape whenever `n ∣ b`.  None of the listed lemmas excludes this cyclic possibility.

## What additional theorem would actually close the 7-smooth window?

For the finite window `17 ≤ n ≤ 100`, prime factors at most `7`, it would be enough to add exact-order cyclic exclusions for:

```text
14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49.
```

Then every 7-smooth `n ≥ 17`, `n ≤ 100`, has one of these as a divisor.  The elementary order-divisor lemma would finish the rest:

```lean
import Mathlib

noncomputable section

namespace FLT.MazurALine

/-
Schematic only: use the actual project definition of `HasRationalPointOfOrder`.

If `P` has exact additive order `n` and `d ∣ n`, then `(n / d) • P`
has exact additive order `d`.
-/
-- theorem HasRationalPointOfOrder.of_dvd
--     (E : WeierstrassCurve ℚ) [E.IsElliptic]
--     {d n : ℕ} (hdpos : 0 < d) (hdn : d ∣ n)
--     (h : HasRationalPointOfOrder E n) :
--     HasRationalPointOfOrder E d := by
--   ... pure group theory using `addOrderOf_nsmul` ...

end FLT.MazurALine
```

That is the missing piece: not more rank-two exclusions, but cyclic exact-order exclusions.

## Bottom line for the A-line

The current infrastructure is useful, but it does **not** prove any of the desired exact-order exclusions for the 7-smooth `17..100` list.

It proves statements of the form:

```text
certain noncyclic torsion configurations cannot occur.
```

The target statement needs statements of the form:

```text
a cyclic point of exact order d cannot occur.
```

For this finite 7-smooth range, the cyclic divisors to attack are:

```text
14, 15, 16, 18, 20, 21, 24, 25, 27, 35, 49.
```

The listed `no_Z2_cross_Z14`, `no_Z2_cross_Z16`, etc. should not be confused with `no_rational_point_of_order_14` or `no_rational_point_of_order_16`; they are strictly weaker for the present purpose because they exclude only a second independent torsion direction.
