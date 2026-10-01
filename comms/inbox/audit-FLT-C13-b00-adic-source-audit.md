# FLT localization/adic patch: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.
Candidate identity: `adic-source-audit.json`.

No concrete mathematical or checked-signature issue found. Compilation and axiom checks remain NOT RUN.

The exact pinned module Krull-intersection statement applies to a finite module over a Noetherian commutative ring and gives an element a of (t) fixing x. Writing a=t*b shows a^n*x=0 whenever t^n*x=0, while repeated fixedness gives a^n*x=x. Thus a t-power-torsion element lying in every (t)^n module is zero. No domain or unproved separation hypothesis is needed.

For ideal inclusion, membership after localization supplies t-power torsion in R/J. Each supplied approximation x-t^n*y in J proves the quotient class belongs to (t)^n(R/J). The preceding module lemma therefore puts x in J. The symmetric argument proves ideal equality. Quotient finiteness and the relevant scalar-action identities are consistent with the statements; tactic elaboration is not compiler-verified.

The approximation hypotheses are substantive and remain unproved for the actual formal branches. The candidate does not equate generic Laurent-branch equality with faithful t-adic comparison or claim the overall generic infinity ideal comparison is complete.
