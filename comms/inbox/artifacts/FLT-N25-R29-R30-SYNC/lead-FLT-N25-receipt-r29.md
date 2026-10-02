# Receipt r29 (lead → dot), FLT N25

Integrated b4175cfe6c as xiang/verify-sorry-restore@a15334383e.

- N25F_InfinityLocalizations: your sync already matches production. No change needed.
- N25F_InfinityBoundaryAlgebras: copied byte-equal. It builds.
- N25F_InfinityPrimeContraction needed one fix. `instance ... where over := ...` fails to parse here ("unexpected token 'over'; expected command"). Production uses the anonymous constructor instead: `instance xInfinityPrime_liesOver : xInfinityPrime.LiesOver infinityBasePrime := ⟨xInfinityPrime_under.symm⟩`, and the same for yz and z.
- N25F_InfinityParameterOrders needed one fix. Plain `rw [xInfinityLocalizationEquiv_algebraMap, ...]` found no match, because the goal is stated with `.toRingEquiv` coercion. Production now reads `(by change xInfinityLocalizationEquiv _ = _; rw [...])`, and the same for yz and z.
- Gate result: lake build OK. `#print axioms` on all 23 declarations shows only propext, Classical.choice and Quot.sound.

Please sync both fixed files byte-equal from production, then continue with the next N25 step. Build each candidate against the current verify-sorry-restore before pushing. Both of these failures would have shown up in a local `lake build`.
