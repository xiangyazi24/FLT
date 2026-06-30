# Q2531 PrimitiveCenteredFourSqAP vs FLT-four route

## Verdict

There is no small direct algebraic substitution from the current
`PrimitiveCenteredFourSqAP` fields to Mathlib's `not_fermat_42` target.
The centered four-square AP gives two primitive Pythagorean triangles with the
same integer area `N`, and it gives identities of the form

```lean
q ^ 4 = (p*r) ^ 2 + (4*N) ^ 2
r ^ 4 = (q*s) ^ 2 + (4*N) ^ 2
```

but those are sums of two **squares** equal to a square, not sums of two
**fourth powers** equal to a square.  The pairwise gcd and oddness hypotheses do
not make `p*r`, `q*s`, or `4*N` squares.  Turning this data into a Fermat-4
contradiction is essentially the classical infinite descent/concordant-forms
argument, not a one-line bridge.

Mathlib's exposed theorem is exactly:

```lean
theorem not_fermat_42 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 2
```

so a direct FLT-four route would need an honest construction of nonzero
`a b : ℤ` and `c : ℤ` with `a^4 + b^4 = c^2`.  The natural identities below do
not supply such `a,b,c`.

## Pasteable algebra ledger

The following lemmas are the exact identities I would add around the current
`PrimitiveCenteredFourSqAP` structure.  They are useful for the descent route and
also show precisely why the naive FLT-four bridge stops short.

```lean
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

/-- The common square gap is `4*N`. -/
theorem primitiveCentered_gap_pq (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 2 - S.p ^ 2 = 4 * S.N := by
  nlinarith [S.hp, S.hq]

theorem primitiveCentered_gap_qr (S : PrimitiveCenteredFourSqAP) :
    S.r ^ 2 - S.q ^ 2 = 4 * S.N := by
  nlinarith [S.hq, S.hr]

theorem primitiveCentered_gap_rs (S : PrimitiveCenteredFourSqAP) :
    S.s ^ 2 - S.r ^ 2 = 4 * S.N := by
  nlinarith [S.hr, S.hs]

/-- The left three squares form a three-square AP: `p^2, q^2, r^2`. -/
theorem primitiveCentered_three_left (S : PrimitiveCenteredFourSqAP) :
    S.p ^ 2 + S.r ^ 2 = 2 * S.q ^ 2 := by
  nlinarith [S.hp, S.hq, S.hr]

/-- The right three squares form a three-square AP: `q^2, r^2, s^2`. -/
theorem primitiveCentered_three_right (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 2 + S.s ^ 2 = 2 * S.r ^ 2 := by
  nlinarith [S.hq, S.hr, S.hs]

/-- Endpoint symmetry of the centered AP. -/
theorem primitiveCentered_outer_inner_sum (S : PrimitiveCenteredFourSqAP) :
    S.p ^ 2 + S.s ^ 2 = S.q ^ 2 + S.r ^ 2 := by
  nlinarith [S.hp, S.hq, S.hr, S.hs]

/-- Pythagorean identity from the left three-square AP, without division by `2`. -/
theorem primitiveCentered_halfsum_left_num (S : PrimitiveCenteredFourSqAP) :
    (S.r - S.p) ^ 2 + (S.r + S.p) ^ 2 = (2 * S.q) ^ 2 := by
  have h := primitiveCentered_three_left S
  nlinarith

/-- Pythagorean identity from the right three-square AP, without division by `2`. -/
theorem primitiveCentered_halfsum_right_num (S : PrimitiveCenteredFourSqAP) :
    (S.s - S.q) ^ 2 + (S.s + S.q) ^ 2 = (2 * S.r) ^ 2 := by
  have h := primitiveCentered_three_right S
  nlinarith

/-- Numerator area identity for the left half-sum triangle. -/
theorem primitiveCentered_halfsum_left_area_num (S : PrimitiveCenteredFourSqAP) :
    (S.r - S.p) * (S.r + S.p) = 8 * S.N := by
  nlinarith [S.hp, S.hr]

/-- Numerator area identity for the right half-sum triangle. -/
theorem primitiveCentered_halfsum_right_area_num (S : PrimitiveCenteredFourSqAP) :
    (S.s - S.q) * (S.s + S.q) = 8 * S.N := by
  nlinarith [S.hq, S.hs]

/--
The tempting Fermat-shape identity.  This is only a Pythagorean triple
`(p*r, 4*N, q^2)`, not a `Fermat42` solution.
-/
theorem primitiveCentered_q4_pyth (S : PrimitiveCenteredFourSqAP) :
    S.q ^ 4 = (S.p * S.r) ^ 2 + (4 * S.N) ^ 2 := by
  have hpq : S.q ^ 2 = S.p ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_pq S]
  have hqr : S.r ^ 2 = S.q ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_qr S]
  calc
    S.q ^ 4 = (S.q ^ 2) ^ 2 := by ring
    _ = (S.p ^ 2 + 4 * S.N) ^ 2 := by rw [hpq]
    _ = S.p ^ 2 * (S.q ^ 2 + 4 * S.N) + (4 * S.N) ^ 2 := by
      rw [hpq]
      ring
    _ = S.p ^ 2 * S.r ^ 2 + (4 * S.N) ^ 2 := by rw [hqr]
    _ = (S.p * S.r) ^ 2 + (4 * S.N) ^ 2 := by ring

/-- Same tempting-but-insufficient identity on the right. -/
theorem primitiveCentered_r4_pyth (S : PrimitiveCenteredFourSqAP) :
    S.r ^ 4 = (S.q * S.s) ^ 2 + (4 * S.N) ^ 2 := by
  have hqr : S.r ^ 2 = S.q ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_qr S]
  have hrs : S.s ^ 2 = S.r ^ 2 + 4 * S.N := by
    nlinarith [primitiveCentered_gap_rs S]
  calc
    S.r ^ 4 = (S.r ^ 2) ^ 2 := by ring
    _ = (S.q ^ 2 + 4 * S.N) ^ 2 := by rw [hqr]
    _ = S.q ^ 2 * (S.r ^ 2 + 4 * S.N) + (4 * S.N) ^ 2 := by
      rw [hqr]
      ring
    _ = S.q ^ 2 * S.s ^ 2 + (4 * S.N) ^ 2 := by rw [hrs]
    _ = (S.q * S.s) ^ 2 + (4 * S.N) ^ 2 := by ring

end MazurProof.RationalPointsN12
```

## Why the direct `not_fermat_42` substitutions fail

The only obvious candidates are these two Pythagorean triples:

```lean
(p*r)^2 + (4*N)^2 = (q^2)^2
(q*s)^2 + (4*N)^2 = (r^2)^2
```

To feed Mathlib's `not_fermat_42`, one would need either

```lean
p*r = a^2      and      4*N = b^2
```

or

```lean
q*s = a^2      and      4*N = b^2
```

for some nonzero integers `a,b`.  The structure only gives pairwise coprimality
among `p,q,r,s` and oddness of the roots; it gives no squarehood of `p*r`,
`q*s`, or `N`.  In fact, the half-sum identities show the actual natural output
is a pair of primitive right triangles of area `N`:

```lean
A = (r - p) / 2,  B = (r + p) / 2,  A^2 + B^2 = q^2,  A*B = 2*N
C = (s - q) / 2,  D = (s + q) / 2,  C^2 + D^2 = r^2,  C*D = 2*N
```

This is the concordant-forms/infinite-descent configuration.  It is not a
square-area triangle unless an extra theorem proves `N` is a square, and such a
theorem is false in general for a single primitive Pythagorean triangle of area
`N`.

## Honest residual options

### Preferred residual, matching the file's current theorem

Keep the existing descent interface.  This is the mathematically honest next
frontier:

```lean
-- Already defined in the file:
-- def PrimitiveCenteredFourSqAPDescent : Prop :=
--   ∀ S : PrimitiveCenteredFourSqAP,
--     ∃ T : PrimitiveCenteredFourSqAP, T.N.natAbs < S.N.natAbs

-- Target to prove next:
-- theorem primitiveCenteredFourSqAP_descent : PrimitiveCenteredFourSqAPDescent := ...
```

Then the already checked theorem

```lean
-- theorem no_primitiveCenteredFourSqAP_of_descent
--     (hdesc : PrimitiveCenteredFourSqAPDescent) :
--     ¬ Nonempty PrimitiveCenteredFourSqAP := ...
```

is exactly the right final closure.

### FLT-four bridge residual, if you still want a `not_fermat_42` closure

This wrapper is compile-ready, but the bridge hypothesis is as hard as the
descent; it is not supplied by the elementary identities above.

```lean
import Mathlib.NumberTheory.FLT.Four

namespace MazurProof.RationalPointsN12

/-- A direct bridge strong enough to use Mathlib's `not_fermat_42`. -/
def PrimitiveCenteredFourSqAPToFermat42 : Prop :=
  ∀ S : PrimitiveCenteredFourSqAP,
    ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a ^ 4 + b ^ 4 = c ^ 2

/-- If such a bridge is proved, Mathlib FLT-four closes the AP contradiction. -/
theorem no_primitiveCenteredFourSqAP_of_fermat42_bridge
    (hbridge : PrimitiveCenteredFourSqAPToFermat42) :
    ¬ Nonempty PrimitiveCenteredFourSqAP := by
  rintro ⟨S⟩
  rcases hbridge S with ⟨a, b, c, ha, hb, hEq⟩
  exact (not_fermat_42 (a := a) (b := b) (c := c) ha hb) hEq

end MazurProof.RationalPointsN12
```

Do not treat `PrimitiveCenteredFourSqAPToFermat42` as a small algebra lemma unless
you have explicit formulas for `a,b,c` and proofs that the two summands are
fourth powers.  The centered AP data currently gives only the Pythagorean-square
identities above.
