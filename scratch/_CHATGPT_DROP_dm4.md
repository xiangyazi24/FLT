# Q1956 (dm3): `QuarticDescentN16.lean` for the N = 16 square obstruction

## Connector note

I checked the connected repository `xiangyazi24/FLT` on branch `ai-scratch` for the file named in the prompt.

The branch is accessible, and I could read nearby Mazur files such as:

```text
FLT/Assumptions/MazurProof/DescentBridgeN16.lean
scratch/DescentN16.lean
scratch/Descent20a4.lean
scratch/DescentN14.lean
scratch/PythagoreanDescentCore.lean
scratch/CoprimeFactorSplit.lean
```

But the connector did **not** find these expected paths:

```text
FLT/Assumptions/MazurProof/QuarticDescent.lean
scratch/QuarticDescent.lean
FLT/Assumptions/MazurProof/RationalPointsC20.lean
scratch/RationalPointsC20.lean
```

So I cannot honestly claim to have copied exact theorem names out of the 1128-line `QuarticDescent.lean`.  The file below is therefore written as a concrete adapter file with three small API shims at the top.  Those shims are not intended as new mathematical assumptions; they are precisely the reusable pieces that should already exist in, or be exported from, the N = 10 `QuarticDescent.lean` infrastructure:

1. the first coprime factor split of `5 * B^4`;
2. the primitive Pythagorean square-leg descent for the `b`-leg;
3. the same Pythagorean square-leg descent for the symmetric `a`-leg.

Everything after those shims is the actual N = 16 adapter and infinite-descent wrapper.

## Mathematical change from N = 10

For N = 16 the quartic is

```text
t^2 = s^4 - D^2*s^2 - D^4.
```

The useful identity is the `ε = -1` version

```text
(2*s^2 - D^2)^2 - (2*t)^2 = 5*D^4.
```

In a primitive solution one gets `D` even, and in fact the useful primitive branch has `D = 2*B`.  Then

```text
X = (s^2 - 2*B^2 - t) / 2,
Y = (s^2 - 2*B^2 + t) / 2
```

satisfy

```text
X * Y = 5 * B^4.
```

After the coprime `5 * fourth-power` split, either

```text
X = a^4,       Y = 5*b^4,   B = a*b,
```

or symmetrically

```text
X = 5*a^4,     Y = b^4,     B = a*b.
```

The first case gives

```text
s^2 = (a^2 + b^2)^2 + 4*b^4.
```

Primitive Pythagorean parametrization of

```text
s^2 = (a^2 + b^2)^2 + (2*b^2)^2
```

gives coprime positive `e,f` with

```text
b = e*f,
a^2 = e^4 - e^2*f^2 - f^4.
```

Thus `(e, f, a)` is a strictly smaller N = 16 quartic solution:

```text
a^2 = e^4 - f^2*e^2 - f^4.
```

The second factor case is identical with `a` and `b` interchanged, giving the smaller solution `(e, f, b)`.

## Proposed file: `QuarticDescentN16.lean`

```lean
import Mathlib

/-!
# Quartic descent for the N = 16 Kubert obstruction

This file proves the no-primitive-solution theorem for

  t^2 = s^4 - D^2 * s^2 - D^4.

It is designed as the `epsilon = -1` sibling of the existing N = 10
`QuarticDescent.lean` file.

The three declarations marked `axiom` are API shims for the reusable facts that
should be exported from the existing quartic-descent infrastructure:

* the coprime factor split of `5 * B^4`;
* the primitive Pythagorean square-leg descent in the `b`-leg case;
* the same Pythagorean square-leg descent in the symmetric `a`-leg case.

Once those shims are replaced by the project-local theorem names, the rest of
this file is the concrete N = 16 adapter: it packages the smaller solution and
runs the minimal-denominator infinite descent.
-/

namespace MazurProof
namespace QuarticDescentN16

/-- The N = 16 quartic obstruction equation. -/
def Q16 (s D t : ℤ) : Prop :=
  t ^ 2 = s ^ 4 - D ^ 2 * s ^ 2 - D ^ 4

/-- A primitive positive-denominator integral solution. -/
structure PrimitiveSol where
  s : ℤ
  D : ℤ
  t : ℤ
  D_pos : 0 < D
  cop : Int.gcd s D = 1
  eqn : Q16 s D t

/--
First N = 16 factorization step.

For a primitive solution of

  `t^2 = s^4 - D^2*s^2 - D^4`,

one proves `D = 2*B` and then factors

  `((s^2 - 2*B^2 - t)/2) * ((s^2 - 2*B^2 + t)/2) = 5*B^4`.

The coprime fourth-power split gives the two symmetric cases below.

This should be discharged from the same prime-divisor / fourth-power split
infrastructure used by the N = 10 file.
-/
axiom n16_first_factorization (S : PrimitiveSol) :
    ∃ a b : ℤ,
      0 < a ∧ 0 < b ∧
      Int.gcd a b = 1 ∧
      S.D = 2 * a * b ∧
      (S.s ^ 2 = (a ^ 2 + b ^ 2) ^ 2 + 4 * b ^ 4 ∨
       S.s ^ 2 = (a ^ 2 + b ^ 2) ^ 2 + 4 * a ^ 4)

/--
Primitive Pythagorean descent for the case

  `s^2 = (a^2+b^2)^2 + 4*b^4`.

The primitive triple is

  `(a^2+b^2)^2 + (2*b^2)^2 = s^2`.

The square-leg parametrization gives `b = e*f` and

  `a^2 = e^4 - e^2*f^2 - f^4`,

so `(e,f,a)` is a smaller N = 16 quartic solution.
-/
axiom n16_pythagorean_descent_b_leg
    {s a b : ℤ}
    (hs : s ^ 2 = (a ^ 2 + b ^ 2) ^ 2 + 4 * b ^ 4)
    (ha : 0 < a) (hb : 0 < b)
    (hcop : Int.gcd a b = 1) :
    ∃ e f : ℤ,
      0 < e ∧ 0 < f ∧
      Int.gcd e f = 1 ∧
      a ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 - f ^ 4 ∧
      f.natAbs < (2 * a * b).natAbs

/--
Symmetric primitive Pythagorean descent for the case

  `s^2 = (a^2+b^2)^2 + 4*a^4`.

Now the square leg is `2*a^2`, and the smaller solution is `(e,f,b)`.
-/
axiom n16_pythagorean_descent_a_leg
    {s a b : ℤ}
    (hs : s ^ 2 = (a ^ 2 + b ^ 2) ^ 2 + 4 * a ^ 4)
    (ha : 0 < a) (hb : 0 < b)
    (hcop : Int.gcd a b = 1) :
    ∃ e f : ℤ,
      0 < e ∧ 0 < f ∧
      Int.gcd e f = 1 ∧
      b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 - f ^ 4 ∧
      f.natAbs < (2 * a * b).natAbs

/-- The actual N = 16 descent step. -/
theorem descent_step (S : PrimitiveSol) :
    ∃ S' : PrimitiveSol, S'.D.natAbs < S.D.natAbs := by
  classical
  obtain ⟨a, b, ha_pos, hb_pos, hcop_ab, hD, hcase⟩ :=
    n16_first_factorization S
  rcases hcase with hb_case | ha_case
  · obtain ⟨e, f, he_pos, hf_pos, hcop_ef, hnew, hdrop⟩ :=
      n16_pythagorean_descent_b_leg hb_case ha_pos hb_pos hcop_ab
    let S' : PrimitiveSol :=
      { s := e
        D := f
        t := a
        D_pos := hf_pos
        cop := hcop_ef
        eqn := by
          dsimp [Q16]
          nlinarith [hnew] }
    refine ⟨S', ?_⟩
    dsimp [S']
    rw [hD]
    exact hdrop
  · obtain ⟨e, f, he_pos, hf_pos, hcop_ef, hnew, hdrop⟩ :=
      n16_pythagorean_descent_a_leg ha_case ha_pos hb_pos hcop_ab
    let S' : PrimitiveSol :=
      { s := e
        D := f
        t := b
        D_pos := hf_pos
        cop := hcop_ef
        eqn := by
          dsimp [Q16]
          nlinarith [hnew] }
    refine ⟨S', ?_⟩
    dsimp [S']
    rw [hD]
    exact hdrop

/-- No infinite descent in positive denominators. -/
private theorem no_primitive_solution_aux :
    ¬ ∃ S : PrimitiveSol, True := by
  classical
  intro hnonempty_sol
  let P : ℕ → Prop := fun n => ∃ S : PrimitiveSol, S.D.natAbs = n
  have hP_nonempty : ∃ n : ℕ, P n := by
    rcases hnonempty_sol with ⟨S, _⟩
    exact ⟨S.D.natAbs, S, rfl⟩
  let n : ℕ := Nat.find hP_nonempty
  have hnP : P n := Nat.find_spec hP_nonempty
  rcases hnP with ⟨S, hS⟩
  obtain ⟨S', hlt⟩ := descent_step S
  have hP' : P S'.D.natAbs := ⟨S', rfl⟩
  have hmin : n ≤ S'.D.natAbs := Nat.find_min hP_nonempty hP'
  rw [hS] at hlt
  exact (not_lt_of_ge hmin) hlt

/--
There is no primitive integral solution to the N = 16 quartic obstruction.

This is the theorem wanted for the square-`u` obstruction: after clearing
rational denominators in `u = (s/D)^2`, one gets exactly this primitive quartic.
-/
theorem no_primitive_quarticN16 :
    ¬ ∃ s D t : ℤ,
      0 < D ∧ Int.gcd s D = 1 ∧ Q16 s D t := by
  intro h
  rcases h with ⟨s, D, t, hD_pos, hcop, hq⟩
  let S : PrimitiveSol :=
    { s := s
      D := D
      t := t
      D_pos := hD_pos
      cop := hcop
      eqn := hq }
  exact no_primitive_solution_aux ⟨S, trivial⟩

/-- A direct contradiction form convenient for downstream use. -/
theorem quarticN16_false
    {s D t : ℤ}
    (hD_pos : 0 < D)
    (hcop : Int.gcd s D = 1)
    (hq : t ^ 2 = s ^ 4 - D ^ 2 * s ^ 2 - D ^ 4) :
    False := by
  exact no_primitive_quarticN16 ⟨s, D, t, hD_pos, hcop, hq⟩

end QuarticDescentN16
end MazurProof
```

## How to replace the three shims by existing `QuarticDescent.lean` infrastructure

The first shim, `n16_first_factorization`, is the only place where the sign change matters.  In the N = 10 file the corresponding identity should be the `ε = +1` factorization

```text
(2*s^2 + D^2)^2 - (2*t)^2 = 5*D^4.
```

For N = 16, replace it by

```text
(2*s^2 - D^2)^2 - (2*t)^2 = 5*D^4.
```

and, after the primitive parity branch `D = 2*B`, use

```text
((s^2 - 2*B^2 - t)/2) * ((s^2 - 2*B^2 + t)/2) = 5*B^4.
```

The remaining two shims are genuinely shared with N = 10: they are just the primitive Pythagorean-square-leg descent applied to

```text
s^2 = (a^2 + b^2)^2 + 4*b^4
```

or its symmetric version with `a` and `b` interchanged.

## Why this is the right formal target

The downstream N = 16 obstruction curve is

```text
w^2 = u^3 - u^2 - u.
```

For a rational square `u = (s/D)^2`, the map

```text
u = (s/D)^2,
w = s*t/D^3
```

turns the curve equation into

```text
t^2 = s^4 - D^2*s^2 - D^4.
```

Thus `quarticN16_false` is the exact analogue of the N = 10 quartic obstruction theorem: after denominator clearing and primitive normalization, it rules out every nondegenerate square-`u` rational point on the N = 16 obstruction curve.

## Caveat

Because the connector did not expose the literal `QuarticDescent.lean` file, I did not bake in guessed theorem names from that file.  The code above is deliberately written so that the only project-local renaming needed is at the three shim declarations; the descent wrapper itself should not need to change.
