TASK_ID: FLT-N25-ROUTE-DELIVER-20261030
REVISION_ID: 1
LEAD: Claude (FLT/Mazur controller, on Xiang's instruction of 2026-10-30)
PURPOSE: Reopen RNOTE-N25-ROUTE r1 (assigned in lead receipt r36) and deliver what exists, so Xiang can decide whether to resume order 25.
SOURCE_BASE_SHA: ec88cc6179136943cd82916b6f2e911aa4a07a25 (branch verify-sorry-restore)
INPUT_MANIFEST: comms/outbox/research-dot-FLT-N25-ROUTE-DELIVER-20261030-input.json
PRIOR_DOT_RESULT: a11846c1 on research-dot/flt-collaboration-20261001 — comms/inbox/research-dot-FLT-N25-ROUTE-r1-status-only-20261007.md ("local literature and source review exists, ... not delivered or committed").
SUPERSEDES: none. This reopens r36's RNOTE-N25-ROUTE r1; receipt r37 (campaign closed) is lifted for this one task only.

## Context

Order 13 is now Proved on Prove2Me (MazurCampaign.no_order_thirteen). In the community mission
`full_mazur_torsion_theorem`, only two open leaves remain: `MazurCampaign.no_order_twenty_five`
and `MazurCampaign.no_prime_ge_twenty_three`. Nobody on the platform has started order 25.
In our fork the only remaining order-25 axiom is
`CyclicExclusion25.no_explicit_order25_obstruction`, which reduces (front end proved) to:
the canonical genus-4 model C (LMFDB 25.150.4.f.1) has only the five cusps over ℚ.
Proved inputs: #Pic⁰(C/F₂) = 71 (`N25F_ClassNumberLower.card_picDegreeZero_eq_seventy_one`),
Abel–Jacobi injectivity over F₂ for points of degree ≤ 2 (`N25F_AbelJacobi.pointDiffClass_ne_zero`).

## REQUESTED_WORK

0. ACK first: commit a one-line ACK file before anything else.
1. Deliver now, as is, whatever you have for RNOTE-N25-ROUTE r1: the route review, literature notes,
   any addenda, any computations (Magma/Sage/PARI output), and any Lean drafts. Label each piece
   with its status (draft / checked / uncompiled). Do not polish before delivering; a partial
   document now is better than a complete one later.
2. Then, if you can, complete the r36 items:
   (a) a source-cited proof that C(ℚ) = {five cusps}, taking the F₂ facts above as given;
   (b) for each further arithmetic input (rank zero / finiteness of J(ℚ) or a descent replacement;
       injectivity of reduction on J(ℚ)_tors, including the 2-primary part; need for #Pic⁰(C/F₃)),
       whether it can be avoided, and the cheapest formalizable replacement;
   (c) an estimate of what is missing in Lean, as a list of statements against existing repo
       definitions (`Pic25`, `RationalPointsN25CanonicalPoints`, ...), with sizes.
3. Your judgement in one paragraph: is order 25 within reach, and by which route.

## ACCEPTANCE

- Markdown is fine; no Lean build is required. Lean drafts stay LEAN_UNCOMPILED unless you
  compiled them, and must not use sorry / admit / axiom / native_decide.
- Every group-order or rank claim cites a source or pastes the computation.

## OUTPUT_SCOPE

Branch `research-dot/flt-collaboration-20261001`, paths:
- `comms/inbox/research-dot-FLT-N25-ROUTE-DELIVER-20261030-ack.md` (ACK)
- `comms/inbox/research-dot-FLT-N25-ROUTE-r1.md` (the route document, as r36 asked)
- `research/dot/n25-route/` for any attachments or drafts.
