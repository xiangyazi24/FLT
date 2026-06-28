# Q2121 dm1: `WeilPairingInterface.lean` left/right nondegeneracy

Date: 2026-06-28.

I read:

```text
FLT/Assumptions/MazurProof/WeilPairingInterface.lean
```

on branch `ai-scratch`.  The file is now visible.  The current structure is:

```lean
structure WeilPairingData (m : ℕ) (T K : Type*)
    [AddCommGroup T] [Module (ZMod m) T] [Field K] where
  pairing : T → T → rootsOfUnity m K
  pairing_zero_left : ∀ Q : T, pairing 0 Q = 1
  pairing_zero_right : ∀ P : T, pairing P 0 = 1
  pairing_add_left : ∀ (P₁ P₂ Q : T),
    pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q
  pairing_add_right : ∀ (P Q₁ Q₂ : T),
    pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂
  alternating : ∀ P : T, pairing P P = 1
  nondegenerate :
    ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
```

The two sorries are currently:

```lean
theorem left_nondegenerate (w : WeilPairingData m T K) (P : T)
    (h : ∀ Q : T, w.pairing P Q = 1) : P = 0 := by
  sorry

theorem right_nondegenerate (w : WeilPairingData m T K) (Q : T)
    (h : ∀ P : T, w.pairing P Q = 1) : Q = 0 := by
  sorry
```

## Verdict

No: these theorems cannot be proved from the current fields.

The field currently named `nondegenerate` is only existential:

```lean
∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
```

This says there is one hyperbolic pair with primitive value.  It does not say the radical of the pairing is zero on all of `T`.

A counterexample pattern is:

```text
T = H ⊕ R
```

where `H` is a two-dimensional symplectic module with a primitive pairing value, and `R` is a nonzero radical summand.  Define the pairing to ignore `R`.  Then there exist `P,Q` in `H` with primitive pairing value, but every nonzero `r ∈ R` satisfies

```text
e(r, a) = 1 for all a
e(a, r) = 1 for all a
```

so the stated `left_nondegenerate` and `right_nondegenerate` are false.

Therefore there is no exact Lean proof replacing those sorries unless the interface is strengthened.

## Correct minimal fix

Add true kernel-triviality as fields of `WeilPairingData`:

```lean
structure WeilPairingData (m : ℕ) (T K : Type*)
    [AddCommGroup T] [Module (ZMod m) T] [Field K] where
  pairing : T → T → rootsOfUnity m K
  pairing_zero_left : ∀ Q : T, pairing 0 Q = 1
  pairing_zero_right : ∀ P : T, pairing P 0 = 1
  pairing_add_left : ∀ (P₁ P₂ Q : T),
    pairing (P₁ + P₂) Q = pairing P₁ Q * pairing P₂ Q
  pairing_add_right : ∀ (P Q₁ Q₂ : T),
    pairing P (Q₁ + Q₂) = pairing P Q₁ * pairing P Q₂
  alternating : ∀ P : T, pairing P P = 1
  nondegenerate :
    ∃ P Q : T, IsPrimitiveRoot (rootVal (pairing P Q)) m
  left_kernel_trivial :
    ∀ P : T, (∀ Q : T, pairing P Q = 1) → P = 0
  right_kernel_trivial :
    ∀ Q : T, (∀ P : T, pairing P Q = 1) → Q = 0
```

Then replace the two sorries by the exact proofs:

```lean
/-- Left nondegeneracy: `(∀ Q, e(P,Q) = 1) → P = 0`. -/
theorem left_nondegenerate (w : WeilPairingData m T K) (P : T)
    (h : ∀ Q : T, w.pairing P Q = 1) : P = 0 := by
  exact w.left_kernel_trivial P h

/-- Right nondegeneracy: `(∀ P, e(P,Q) = 1) → Q = 0`. -/
theorem right_nondegenerate (w : WeilPairingData m T K) (Q : T)
    (h : ∀ P : T, w.pairing P Q = 1) : Q = 0 := by
  exact w.right_kernel_trivial Q h
```

## Alternative fix: weaken the theorem

If you do not want to add global nondegeneracy fields, the current existential field only supports a weaker statement: there exists a pair with primitive pairing value.  Under `1 < m`, that chosen value is nontrivial, so the chosen left and right arguments are not in the corresponding kernels.  That is much weaker than `∀ P, kernel(P) → P=0`.

The correct weak theorem shape is something like:

```lean
theorem exists_not_left_kernel (w : WeilPairingData m T K) (hm : 1 < m) :
    ∃ P : T, ¬ ∀ Q : T, w.pairing P Q = 1 := by
  obtain ⟨P, Q, hprim⟩ := w.nondegenerate
  refine ⟨P, ?_⟩
  intro hker
  have hval : rootVal (w.pairing P Q) = 1 := by
    -- follows from hker Q after coercing rootsOfUnity to K
    simpa [rootVal] using congrArg rootVal (hker Q)
  exact hprim.ne_one hm hval
```

The exact last line may need adaptation to the pinned `IsPrimitiveRoot.ne_one` lemma name.  But this theorem still does not imply the current `left_nondegenerate` theorem.

## Bridge sorry

The remaining `weil_interface_bridge` sorry is genuinely hard: it must construct actual Galois-equivariant Weil-pairing data from elliptic-curve torsion and then apply `primitive_root_in_base`.

## Bottom line

Do not replace the current `left_nondegenerate` / `right_nondegenerate` sorries with fake proofs.  The current statements are not derivable from the current structure fields.  The minimal correct source change is to add `left_kernel_trivial` and `right_kernel_trivial` to `WeilPairingData`, then the two theorem proofs are one-line projections from those fields.
