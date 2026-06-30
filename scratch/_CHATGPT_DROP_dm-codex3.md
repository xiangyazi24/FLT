# Q2532 checked AP wrapper

Place this at the end of `FLT/Assumptions/MazurProof/N12FourSquaresAP.lean`, after the seven checked local lemmas listed in the prompt.

```lean
theorem arbitraryAPToPrimitiveCentered_checked : ArbitraryAPToPrimitiveCentered := by
  exact arbitraryAPToPrimitiveCentered_of_weak
    (arbitraryAPToWeakPrimitiveCentered_of_dag
      rootGCD4Division
      weakPrimitiveAPParity
      weakPrimitiveAPPairwise
      positivePrimitiveAP_to_centered_weak)
    (weakPrimitiveCenteredToStrong_of_local_lemmas
      weakPrimitiveAPParity
      weakPrimitiveAPPairwise)
```

If Lean reports an arity mismatch, first check the wrapper signatures locally:

```lean
#check arbitraryAPToWeakPrimitiveCentered_of_dag
#check weakPrimitiveCenteredToStrong_of_local_lemmas
#check arbitraryAPToPrimitiveCentered_of_weak
```

Keep this theorem local in `N12FourSquaresAP.lean` for now. Use it to replace residual assumptions in `RationalPointsN12.lean`, `KubertBridgeN12.lean`, or other N12 cover files only after confirming the import is acyclic; then import `N12FourSquaresAP` and pass `arbitraryAPToPrimitiveCentered_checked` where an `ArbitraryAPToPrimitiveCentered` hypothesis is currently requested.
