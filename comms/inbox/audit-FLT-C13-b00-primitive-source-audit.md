# FLT primitive vertical presentation: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.
Candidate: `N13PrimitiveVerticalPresentation.lean`; exact snapshot in `primitive-source-audit.json`.

No concrete mathematical, type-signature, or normalization-identity issue found by source review. Compilation, tactic success, and axiom checks are NOT RUN.

The nontrivial codomain forces the reduction kernel to be proper. The exact pinned Krull-intersection theorem applies to a proper ideal in a Noetherian domain, so a nonzero z fails divisibility by some p-power. The first failing exponent is positive; its predecessor divides z. If the remaining factor reduced to zero, membership in the principal kernel would yield one more p-factor, contradicting minimality. This supplies actual witnesses and does not assume primitive factorization. The reasoning also handles p=0: a nonzero z has exponent zero.

The fraction theorem starts from the fraction-ring surjectivity interface with a nonzero denominator. Nonzero f forces the numerator nonzero. Separate factorizations x=p^n*a and y=p^m*b preserve the exact identity as p^m*f*b=p^n*a. Both primitive reductions are proved nonzero; no vertical power is silently discarded or assigned the wrong side.

The theorem is generic. It still requires Noetherian chart instances when applied, and supplies neither a shared two-chart primitive presentation nor a global chooser/comparison theorem. Those remain separate obligations.

## Concrete chart extension audit

The final 144-line snapshot adds affine and infinity chart factorization and a common-field fraction corollary. A missing local affine-to-rational Algebra instance was identified and added to match the pinned FractionalHull source setup. The Noetherian inference path is the standard PadicInt discrete valuation ring, polynomial ring, and AdjoinRoot quotient chain; it has not been compiler-tested. Kernel identities reduce to `(2)` by algebra-map simplification.
