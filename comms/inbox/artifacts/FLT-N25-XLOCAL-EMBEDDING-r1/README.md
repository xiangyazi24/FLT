# Actual X-boundary local-ring embedding into the W function field

`N25F_XLocalFractionEmbedding.lean` extends the genuine coordinate-rigid
X-chart map through localization at the existing `xPrime`. Every denominator
outside that prime is nonzero, and chart injectivity sends it to a nonzero
field element. The universal localization lift is injective and maps the
actual `xWGerm` precisely to `1 / algebraMap W (FractionRing W) qx`.

The four public declarations are `xLocalToFraction`,
`xLocalToFraction_algebraMap`, `xLocalToFraction_injective`, and
`xLocalToFraction_xWGerm`, all in `MazurProof.N25F_XLocalFractionEmbedding`.
No new production premise, axiom, sorry, admit, or native_decide is present.
The actual source `XLocalRing` and `xWGerm` are used unchanged.

The candidate depends on the previous map, X/W equivalence, and coordinate
map injectivity candidates. It does not depend on the separate DVR candidate.
It proves a local-ring embedding and a coordinate identity, not a normalized
field valuation or projective product formula.

## Checks

The generic localization argument passed separately in 5.564 seconds. The
complete exact-source harness passed in 31.441 seconds, exit 0, 2509768 KiB
peak child RSS, one CPU/thread, 3072 MiB cap, 60-second timeout, using Lean
4.31.0-rc2 and Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
All four public declarations print only standard propext, Classical.choice,
and Quot.sound axioms. Existing style warnings are retained in the log.

The harness contains the complete previously checked injectivity assembly,
then 12 additional verbatim source declarations defining the actual X
point-prime, localization, and germ. Thus 63 accepted source declarations
are reproduced in total. The accepted W Dedekind structure is represented
by an ordinary harness parameter, as in the injectivity check. All carrier,
prime, localization, quotient, and coordinate definitions are exact.
Production imports supply the accepted structure and add no premise.

Full FLT import compilation was NOT RUN; the supplied
`ActualXLocalFractionCheck.lean` is for lead acceptance. Full integration
and axiom acceptance remain with the lead.

## Reproduction

The checked full harness is included. `make_check.py` reconstructs it from
the previously delivered `XChartInjectiveCheck.lean`, the production
candidate, and the exact XLocal source. All original-source URLs and hashes
are in `source-inputs.json`; the previous harness lives at dot commit
00be9496255202155d8748f60621edbaec072d36 under
`comms/inbox/artifacts/FLT-N25-XCHART-INJECTIVE-r1/`. Scripts preserve their
original local paths, which may be adjusted for a different checkout.
`validation.json` records hashes and resource evidence. The initially failed
generic check is retained; it only required explicitly including the
injectivity section hypothesis, and the second generic check passed.
