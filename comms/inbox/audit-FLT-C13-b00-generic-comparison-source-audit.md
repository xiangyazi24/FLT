# FLT actual ideal approximation and generic comparison: independent audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.
Files: `N13InfinityIdealApproximation.lean` (170 lines) and `N13GenericInfinityComparison.lean` (89 lines). Exact identities: `generic-comparison-source-audit.json`.

No concrete mathematical, namespace, or checked-signature issue found. Compilation, tactic elaboration, typeclass inference, and axiom checks remain NOT RUN.

## Checks

- The finite-jet pair ring and its quotient maps use the actual generic branch maps. Its kernel is the previously proved literal t-power divisibility condition.
- `scaledIdeal` is a genuine ideal. Addition multiplies two nonzero scalars and combines witnesses as d*x+c*y. Closure under arbitrary jet-pair multiplication uses the actual simultaneous scaled jet lift, with the product scalar c*d and witness y*x. No unproved jet-map surjectivity is assumed.
- The exact pinned `Ideal.ideal_prod_eq` justifies decomposition of an ideal in a product ring. Consequently mapping a source ideal under a pair of ring maps generates the product of its two projected image ideals. This is not a claim that the pair ring map is surjective.
- Branch ideal equality therefore puts the jet of x in the image ideal of J. Membership in `scaledIdeal` supplies an actual z in J and one nonzero scalar c. The actual branch-kernel theorem turns equality of jets into c*x-z=t^n*y, producing the requested scaled approximation with the correct sign.
- At the exact Mathlib pin, localization membership gives x in I, denominator s, and z*map(s)=map(x). The candidate multiplies by the additional c and cancels only the explicit unit map(c)*map(s) in the vertical localization. No integral scalar cancellation is used.
- The resulting unscaled generic approximations supply both hypotheses of the reviewed adic patch, yielding generic ideal equality from actual branch ideal equalities and equality away from t.

The approximation predicates are now derived rather than assumed. The remaining task is to establish those branch and overlap equalities for the desired concrete cleared line comparison, then apply integral descent and assemble global chooser compatibility/B03. This audit does not certify those later obligations.

## Integral descent extension

The comparison file now has 127 lines. Its new integral equality theorem assumes invertibility and nonzero reductions of both ordinary infinity ideals. Equality after vertical localization supplies a denominator q=map(r), with r a nonzero Z2 scalar. The reviewed scalar-saturation theorem cancels this denominator in the target ideal. Applying both inclusions yields literal integral ideal equality. No new unit assumption on r is made. Source review found no concrete issue in this extension.
