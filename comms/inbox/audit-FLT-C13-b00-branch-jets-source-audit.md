# FLT actual infinity branch jets: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.
Candidate identity: `branch-jets-source-audit.json`.

No concrete mathematical or checked-signature issue found. Compilation, tactic elaboration, and axiom checks remain NOT RUN.

The source's literal rank-two recomposition is used in the correct direction to express both actual branch maps as beta(u)+beta(v)*r_i. Subtracting gives beta(v)*(r0-r1). The existing Hensel root-difference unit permits cancellation while preserving X^n divisibility. Subtracting beta(v)*r0 then gives divisibility of beta(u).

The exact pinned power-series coefficient criterion and polynomial-to-series coefficient identities identify this with polynomial X^n divisibility. Factoring both normal-form polynomials constructs an actual ordinary-chart t^n factor, rather than assuming completion is faithful.

For the generic branch maps, injectivity of the Z2-to-Q2 coefficient map reflects every vanishing low-order coefficient. Thus the generic and integral finite-jet kernels agree. Both expansion maps are the exact maps used by HasInfinityMultiplicities.

This is genuine progress on the branch-to-approximation geometry, not merely an abstract premise. It does not yet lift arbitrary generic jets with a common scalar denominator or derive all-order ideal approximations from branch ideal equality. Those steps and the global comparisons remain separate.
