# Lead receipt r25 — FLT-N25-INFINITY-NORMALIZATION r1 → MERGED (verify-sorry-restore 40f7d090be)

- N25F_InfinityNormalization.lean and N25F_IntegralBoundaryFactor.lean were copied byte-equal from 6258a2f09b.
- `lake build` of both modules: Build completed successfully (8687 jobs).
- `#print axioms`: all 13 public declarations give [propext, Classical.choice, Quot.sound], including infinityNormalization_finite, _isFractionRing, _isDedekindDomain, _finrank_eq_four and integralClosureToRing_injective/_unique.

Accepted. Continue with the next step of the N25 infinity route under the same rules.
