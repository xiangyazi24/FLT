# Local FLT continuation: exact affine ideal and total boundary cost

UNPUBLISHED. GitHub publication remains blocked after the earlier user-cancelled call.
No GitHub write was attempted for this continuation. Published collaboration head
remains 20f43b99f3a906637e369439c0eab2e78ed1d1b0; the previous eight-audit
boundary package is also unpublished.

Four new checked declarations:
- N25F_EffectiveAffineIdeal.exists_ideal_with_exact_counts
- N25F_EffectiveAffineIdeal.ideal_eq_of_exact_counts
- N25F_EffectiveAffineIdeal.exists_ideal_for_nonpositive_divisor
- N25F_TotalBoundaryCost.finrank_le_sub_three_boundaries

The ideal proof constructs the actual fractional prime product, proves it is
integral, recovers a nonzero Ideal R, and identifies every order exactly. Its
membership theorem includes the zero function correctly. No ideal-existence
certificate or dimension bound is assumed. This handles arbitrary finite
signed affine divisors with nonpositive coefficients, not just numerical cases.

The total-boundary theorem sequentially imposes three actual-type section
filtrations and proves dim L(D) <= dim L(D-aX-bYZ-cZ)+a+b+c. Its family
check includes the predecessor's real section definitions and proofs; existing
principal laws and the three binary cancellation facts are explicit family
inputs. These have named actual producers in the production candidate chain.

PASS total-01: 34.289s including compiler-slot wait, peak RSS 2,946,580 KiB.
PASS ideal-02: 4.245s, peak RSS 2,811,820 KiB. All four audits list only
propext, Classical.choice, Quot.sound, no sorryAx. Checked source hashes are
verified in validation.json. The initial ideal-01 failure was namespace/
implicit-parameter elaboration, and is not success evidence.

Exact existing FLT Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05;
shared compiler gate, one CPU/thread, 3072 MiB cap, 60-second active timeout.
No downloads or full build. Generic complete ideal module is kernel checked;
named full FLT imports, including TotalBoundaryCost and
ShiftedAffineIdeal.UNCOMPILED, were NOT RUN.

The actual W-chart adapter supplies the checked construction with the genuine
principal-shifted divisor and actual affine-point/height-one-prime equivalence.
It is source only, explicitly uncompiled. Next missing assembly: identify the
weighted ideal quotient dimension with the affine complement degree, identify
the affine-condition kernel with the appropriate section space, and combine
all three boundary costs to obtain L(D') and the general lower bound.
Picard finiteness and high-degree effectiveness remain open.
