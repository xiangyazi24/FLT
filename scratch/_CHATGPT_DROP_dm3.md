# Q1135 (dm3/dm2): set-builder membership goal for `fuelCounterSemantics.toWeak.traj`

I only received the short prompt `Q1135 (dm3): dm2`, but the relevant remembered `dm2/Q1135` context was a Lean goal of the form

```lean
⊢ fuelCounterSemantics.toWeak.traj w t ∈
    {y : Fin 2 → ℝ | sourceHalts (Int.toNat ⌊y 0 + 1 / 2⌋)}
```

The right move is to treat this as a definitional unfolding of set-builder membership.  Do **not** try to solve this by repeatedly rewriting with `Set.mem_setOf` or by applying `.mpr` and expecting a new mathematical subgoal.  For a set-builder, membership is definitionally the predicate:

```lean
x ∈ {y | P y}
```

is just

```lean
P x
```

So the clean proof step is `change` or `show ... from ...`.

## Drop-in proof pattern

In the proof where the goal is the set membership above, use:

```lean
import Mathlib

-- plus the project import that defines `fuelCounterSemantics` and `sourceHalts`

noncomputable section

-- Inside the relevant proof:
-- goal:
--   ⊢ fuelCounterSemantics.toWeak.traj w t ∈
--       {y : Fin 2 → ℝ | sourceHalts (Int.toNat ⌊y 0 + 1 / 2⌋)}

change sourceHalts
  (Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋)

-- Now prove this predicate directly.
```

If you already have the predicate as a hypothesis, for example

```lean
hhalt : sourceHalts
  (Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋)
```

then the whole proof is just:

```lean
import Mathlib

-- plus the project import that defines `fuelCounterSemantics` and `sourceHalts`

noncomputable section

-- Inside the relevant proof:

change sourceHalts
  (Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋)
exact hhalt
```

Often `exact hhalt` will work even before the `change`, because the goal is definitionally equal to the predicate.  But the `change` line makes the proof state explicit and avoids confusion.

## If you need to rewrite the rounded coordinate

If you know the rounded value is some natural number `n`, use the same `change` first, then rewrite.

```lean
import Mathlib

-- plus the project import that defines `fuelCounterSemantics` and `sourceHalts`

noncomputable section

-- Typical local hypotheses:
-- hcode : Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋ = n
-- hhalt : sourceHalts n

-- goal:
--   ⊢ fuelCounterSemantics.toWeak.traj w t ∈
--       {y : Fin 2 → ℝ | sourceHalts (Int.toNat ⌊y 0 + 1 / 2⌋)}

change sourceHalts
  (Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋)
rw [hcode]
exact hhalt
```

If instead you know the real-valued coordinate itself, for example

```lean
hcoord : (fuelCounterSemantics.toWeak.traj w t) 0 = x
hhalt : sourceHalts (Int.toNat ⌊x + (1 / 2 : ℝ)⌋)
```

then use:

```lean
import Mathlib

-- plus the project import that defines `fuelCounterSemantics` and `sourceHalts`

noncomputable section

change sourceHalts
  (Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋)
rw [hcoord]
exact hhalt
```

The explicit `(1 / 2 : ℝ)` annotation is worth keeping.  It prevents Lean from guessing a natural/integer/rational division in nearby rewrites.

## A tiny helper lemma, if you want one

You can also add a generic local helper to make the definitional equivalence named.  This lemma is not mathematically deep; its proof is `Iff.rfl`.

```lean
import Mathlib

noncomputable section

private lemma mem_halting_set_iff
    (sourceHalts : ℕ → Prop) (x : Fin 2 → ℝ) :
    x ∈ ({y : Fin 2 → ℝ |
        sourceHalts (Int.toNat ⌊y 0 + (1 / 2 : ℝ)⌋)} : Set (Fin 2 → ℝ)) ↔
      sourceHalts (Int.toNat ⌊x 0 + (1 / 2 : ℝ)⌋) :=
  Iff.rfl
```

Then one possible proof style is:

```lean
import Mathlib

-- plus the project import that defines `fuelCounterSemantics` and `sourceHalts`

noncomputable section

-- hhalt : sourceHalts
--   (Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋)

exact
  (mem_halting_set_iff sourceHalts
    (fuelCounterSemantics.toWeak.traj w t)).2 hhalt
```

But this helper is usually unnecessary.  I would prefer `change` in the actual proof because it makes the target readable and keeps the script shorter.

## Why `.mpr` looked like a no-op

A tactic like

```lean
apply Set.mem_setOf.mpr
```

or a proof term involving `.mpr` may appear not to advance the goal because the equivalence

```lean
x ∈ {y | P y} ↔ P x
```

is just reflexive at the kernel level.  Lean is not discovering a new theorem; it is unfolding the definition of membership in a set-builder.  Therefore the resulting goal is definitionally the same proposition, only displayed differently if Lean chooses to show it differently.

So the useful commands are:

```lean
change P x
```

or

```lean
show P x from h
```

or, when consuming an existing proof:

```lean
simpa only [Set.mem_setOf_eq] using h
```

For this particular goal, the most robust version is:

```lean
import Mathlib

-- plus the project import that defines `fuelCounterSemantics` and `sourceHalts`

noncomputable section

change sourceHalts
  (Int.toNat ⌊(fuelCounterSemantics.toWeak.traj w t) 0 + (1 / 2 : ℝ)⌋)
```

then continue with the hypotheses that identify the first coordinate of the trajectory or directly prove the `sourceHalts` predicate.
