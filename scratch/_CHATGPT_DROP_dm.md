# Q126 (dm): stopped/absorbing MGF tail above a ceiling

## Clean answer

Do **not** try to prove a uniform `r < 1` drift for

```text
Φ(c) = exp(s · U c)
```

on the whole window gate `G`. That statement is false below the ceiling: when `U c ≤ n`, the drop floor is unavailable and the best honest multiplicative drift for the raw exponential is `r = 1`.

The standard fix is to stop the potential at the ceiling. Use the survival set

```text
S := G ∩ {c | n < U c}
```

and the stopped/survival potential

```text
Φstop(c) := if n < U c then exp(s · U c) else 0.
```

Then the desired tail event is unchanged if

```text
θ := exp(s · (n+1)),   s > 0,
```

because `θ ≤ Φstop(c)` is equivalent to `n < U c`, i.e. `U c ≥ n+1` for `U : Config → ℕ`. Below the ceiling, `Φstop = 0`, so done states cannot contribute to the tail.

This gives a genuine uniform contraction on the original gate `G`:

* If `c ∈ G` and `n < U c`, apply the existing strict-drop/no-increase lemma:

  ```text
  ∫ exp(s · U c') dK(c,c') ≤ contractRate ρ s · exp(s · U c).
  ```

  Since `Φstop(c') ≤ exp(s · U c')`, this gives

  ```text
  ∫ Φstop dK(c) ≤ contractRate ρ s · Φstop(c).
  ```

* If `c ∈ G` and `U c ≤ n`, never-increase implies

  ```text
  K c {c' | n < U c'} = 0,
  ```

  because `{c' | n < U c'} ⊆ {c' | U c < U c'}`. Therefore `Φstop = 0` almost surely under `K c`, and

  ```text
  ∫ Φstop dK(c) = 0 = contractRate ρ s · Φstop(c).
  ```

So `gated_real_tail_anyr` can be applied on the **original gate `G`** with the stopped potential `Φstop` and

```text
r := contractRate ρ s < 1.
```

This is usually cleaner than changing the gate to `G ∩ {U > n}` if the existing lemma charges every gate exit as `killEscape`. If you make the gate `S = G ∩ {U > n}` and the lemma adds `P(exit S)` as an error term, then hitting the done set `{U ≤ n}` becomes an “escape” and the bound is polluted by a large, safe probability. That is the wrong accounting.

The right accounting is either:

1. keep the gate as `G` and use `Φstop`; or
2. use an Option/killed kernel for the survival set `S`, but send `{U ≤ n}` to a **safe absorbing cemetery with potential `0`**, not to the bad-escape term. Only exits from the original window gate `G` should be charged as `killEscape`.

## Absorbing/win-set interpretation

Let

```text
D := {c | U c ≤ n}.
```

Inside `G`, the set `D` is absorbing with respect to the tail event `{U ≥ n+1}`. More precisely, if `c ∈ G ∩ D`, then never-increase gives zero probability of jumping to `{U > n}` in one step. Iterating, as long as the chain remains in `G`, once it enters `D` it can never return to `{U > n}`. Thus `D` is a “win” or “done” set for the survival problem.

Consequently, the event

```text
{U(X_T) ≥ n+1}
```

is a survival event: it can occur only if the process has not yet hit `D` before time `T` and has not made a bad escape from `G`.

The resulting bound has the form

```text
P_c0[U(X_T) ≥ n+1]
  ≤ P_c0[bad escape from G before T]
    + (contractRate ρ s)^T · Φstop(c0) / exp(s · (n+1)).
```

If `c0 ∈ G` and `U c0 ≤ n`, then `Φstop(c0)=0`; the survival probability is zero except for whatever probability is charged by leaving the trusted gate `G`.

## Lean-oriented skeleton

The exact names for your kernel/tail lemmas will differ, but the shape should be this. The important point is that the drift lemma is proved for `stoppedPhi`, not for the raw exponential on all of `G`.

```lean
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace ContractingMGF

variable {Config : Type*} [MeasurableSpace Config]

/-- Done/win set: below the ceiling. -/
def doneSet (U : Config → ℕ) (n : ℕ) : Set Config :=
  {c | U c ≤ n}

/-- Survival set inside the original gate. -/
def surviveSet (G : Set Config) (U : Config → ℕ) (n : ℕ) : Set Config :=
  G ∩ {c | n < U c}

/-- Stopped exponential potential. It is zero once the process has reached the ceiling. -/
def stoppedPhi (U : Config → ℕ) (n : ℕ) (s : ℝ) (c : Config) : ℝ :=
  if n < U c then Real.exp (s * (U c : ℝ)) else 0

/-- The above-ceiling tail is exactly a Markov inequality event for the stopped potential. -/
lemma stoppedPhi_tail_iff
    (U : Config → ℕ) (n : ℕ) {s : ℝ} (hs : 0 < s) (c : Config) :
    Real.exp (s * ((n + 1 : ℕ) : ℝ)) ≤ stoppedPhi U n s c ↔ n < U c := by
  unfold stoppedPhi
  by_cases hc : n < U c
  · simp [hc]
    constructor
    · intro _
      exact hc
    · intro _
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.succ_le_iff.mp hc]
  · simp [hc]
    have hpos : 0 < Real.exp (s * ((n + 1 : ℕ) : ℝ)) := Real.exp_pos _
    constructor
    · intro h
      exact False.elim ((not_le_of_gt hpos) h)
    · intro h
      exact False.elim (hc h)

/-- Below the ceiling, never-increase makes the above-ceiling set null in one step.

This is the set-theoretic heart of the stopped-potential proof. The measure/integral
version is: if the integrand is `stoppedPhi`, then its integral is `0` from such a state. -/
lemma above_null_of_below_of_noincr
    {Kmeasure : Config → Set Config → ℝ≥0∞}
    {G : Set Config} {U : Config → ℕ} {n : ℕ} {c : Config}
    (hcG : c ∈ G) (hc_le : U c ≤ n)
    (hnoincr : Kmeasure c {c' | U c < U c'} = 0) :
    Kmeasure c {c' | n < U c'} = 0 := by
  -- Replace this schematic proof with the corresponding monotonicity lemma for your
  -- kernel/measure API, e.g. `measure_mono_null` or the kernel-specific wrapper.
  have hsubset : {c' : Config | n < U c'} ⊆ {c' : Config | U c < U c'} := by
    intro c' hc'
    exact lt_of_le_of_lt hc_le hc'
  -- schematic:
  -- exact measure_mono_null hsubset hnoincr
  sorry

/-- Schematic stopped drift. This is the lemma you want to feed to `gated_real_tail_anyr`.

For `U c > n`, it follows from the existing `expDrainPot_drift_contracting` and
`stoppedPhi ≤ exp(s·U)`. For `U c ≤ n`, it follows from
`above_null_of_below_of_noincr`, since the stopped potential is zero a.e. -/
lemma stoppedPhi_drift_contracting_schematic
    {K : Type*} -- replace by your Markov kernel type
    {G : Set Config} {U : Config → ℕ} {n : ℕ}
    {ρ s r : ℝ}
    (hr : r = contractRate ρ s) :
    True := by
  -- Intended proof structure:
  --
  -- intro c hcG
  -- unfold stoppedPhi
  -- by_cases habove : n < U c
  -- · -- use the strict-drop floor and never-increase hypotheses at `c`
  --   --   expDrainPot_drift_contracting ... :
  --   --     ∫ exp(s · U c') dK(c) ≤ r * exp(s · U c)
  --   -- then bound `stoppedPhi ≤ exp(s · U)` pointwise.
  --   exact ...
  -- · -- `U c ≤ n`; never-increase makes `{c' | n < U c'}` null,
  --   -- so `stoppedPhi` is zero a.e. and the integral is zero.
  --   exact ...
  trivial

/-- Final schematic use of the generic gated tail lemma.

Use the original gate `G`; do not charge the safe done set `{U ≤ n}` as `killEscape`. -/
theorem survival_tail_above_ceiling_schematic
    {G : Set Config} {U : Config → ℕ} {n T : ℕ} {s ρ : ℝ}
    (hs : 0 < s) (hρ : 0 < ρ) :
    True := by
  -- Let
  --   Φ := stoppedPhi U n s
  --   θ := Real.exp (s * ((n + 1 : ℕ) : ℝ))
  --   r := contractRate ρ s
  --
  -- Prove `hEdrift : ∀ x ∈ G, ∫ Φ dK(x) ≤ r * Φ x` by
  -- `stoppedPhi_drift_contracting`.
  --
  -- Apply:
  --   gated_real_tail_anyr K G Φ r θ T c₀ hEdrift ...
  --
  -- Then rewrite `{θ ≤ Φ}` using `stoppedPhi_tail_iff` to obtain
  -- `{c | n < U c}` = `{c | U c ≥ n+1}`.
  trivial

end ContractingMGF
```

## Option/killed-kernel formulation

The equivalent stopped-chain formulation is:

```text
from c ∈ G ∩ {U > n}: keep only transitions to G ∩ {U > n};
from c ∈ G ∩ {U ≤ n}: go to a safe absorbing state with potential 0;
from c ∉ G: go to a bad absorbing state, or charge this as `killEscape`.
```

If your existing Option kernel has only one cemetery state and the tail theorem adds the probability of reaching that state as `killEscape`, then do **not** use `G ∩ {U > n}` as the gate directly: it will count safe hits of `{U ≤ n}` as errors. Either keep the original gate and use `stoppedPhi`, or split the cemetery into safe and bad exits.
