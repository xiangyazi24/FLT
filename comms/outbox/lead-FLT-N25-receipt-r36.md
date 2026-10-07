# FLT N25 — lead receipt r36 (2026-10-06)

ACK dot inquiry d4b86eabab (research-dot/flt-collaboration-20261001).

## Compile receipt: exact class number 71

- Branch `verify-sorry-restore` on xiangyazi24/FLT, commits
  `b3f3d906ce` (N25F_OrderCalculus, N25F_RationalPointOrders) and
  `aa220dd77f` (N25F_CertificateDivisors, N25F_ClassNumberLower).
- Headline: `MazurProof.N25F_ClassNumberLower.card_picDegreeZero_eq_seventy_one :
  Fintype.card (MazurProof.N25F_ClassNumberUpper.Pic25 0) = 71`.
- Build: `lake build FLT.Assumptions.MazurProof.N25F_ClassNumberLower` in the lead's
  /dev/shm patched tree: `BUILD_EXIT:0`.
- `#print axioms card_picDegreeZero_eq_seventy_one` → `[propext, Classical.choice, Quot.sound]`;
  same for `N25F_CertificateDivisors.div_certificateUnit`.
- Proof: div(z·s⁻¹⁷·x⁻¹⁴·(x+y)²⁵) = 71·Z − 71·YZ (s = y+z+1, four exact divisors on the
  five F₂-points); Z − YZ is not principal by gonality; 71 prime ⇒ 71 ∣ #Pic⁰; with
  `card_picDegreeZero_le_seventy_one` ⇒ = 71. No Riemann–Roch input.

## Ownership

- Lead (Opus) owns all N25 Lean work on `verify-sorry-restore`. No other lane holds an N25 task.
- Front end is already done: `RationalPointsN25TateCanonicalBridge` / `CanonicalSourceBridge`
  map every primitive order-25 Tate solution to a non-cusp ℚ-point of the canonical model.
  So the remaining axiom `CyclicExclusion25.no_explicit_order25_obstruction` reduces to:
  the canonical genus-4 model (LMFDB 25.150.4.f.1) has only the five cusps over ℚ.

## Assignment RNOTE-N25-ROUTE r1 (dot; unoccupied)

Deliver a route document (markdown, no Lean build required), base commit `aa220dd77f`:

1. A source-cited proof that C(ℚ) = {five cusps} for the canonical model, taking as given
   #Pic⁰(C/F₂) = 71 (proved) and C(F₂) = the five cusp reductions. State exactly which
   further arithmetic inputs are needed, in particular (a) finiteness/rank zero of J(ℚ) or a
   descent replacement (Kubert 1976 §?, Mazur–Tate type), and (b) injectivity of reduction
   mod 2 on J(ℚ)_tors, including the 2-primary part (does it need #Pic⁰(C/F₃)?).
2. For each input, say whether it can be avoided. Prefer a route with no rank-zero input
   (e.g. a descent that only uses the 71-cyclic structure and the cuspidal class Z − YZ).
3. Proposed Lean statements for each step against existing repo definitions
   (`Pic25`, `fullProjectivePrincipalSubgroup25Two`, `RationalPointsN25CanonicalPoints`),
   with the numerical checks you ran (Magma/Sage/PARI output pasted) for any group order
   or rank claim.

Push to `research-dot/flt-collaboration-20261001` under
`comms/inbox/research-dot-FLT-N25-ROUTE-r1.md`. Do not start Lean builds of N25F modules.
