# FLT invertible reduction saturation: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Candidate: `N13InvertibleReductionSaturation.lean`, 324 lines. Exact snapshot identity: `saturation-source-audit.json`.

## Result

No concrete mathematical, namespace, or checked-signature issue found. Compilation, tactic success, and transitive axiom checks are NOT RUN. All 64 files in the updated source inventory independently match their pinned Git blob identities. Four added chart sources were also independently fetched through the connector at the exact pin and byte-compared.

## Argument checks

1. The general assumptions are sufficient. The domain-valued reduction cancels a chosen nonzero reduced section of the invertible ideal. Kernel `(p)` converts the resulting zero reduction to actual divisibility by `p`.
2. For inverse-ideal section `z`, both `c = z*p*x` and `d = z*a` lie in the base ring. The equation `p*d*x = a*c` forces `c = p*e`; cancellation of nonzero `p` in the fraction field gives `z*x = e`. Multiplying the inverse-ideal containment back by the invertible ideal returns `x` to the original ideal. No Picard equality, additivity, or desired saturation conclusion is assumed.
3. Power saturation follows by induction. The exact pinned Mathlib `PadicInt.unitCoeff_spec` has the unit-times-uniformizer-power form used by the scalar saturation proof.
4. The localization equality descent uses the exact pinned Mathlib membership characterization `exists m in powers p, m*x in I`, then power saturation. The constructor and powers-extraction pattern agrees with existing pinned source.
5. Principal multiples remain invertible when their generators are nonzero. Their reduced ideal products remain nonzero because the reduction ring is a domain. Consequently the denominator-cleared equality theorem correctly specializes the localization descent result.
6. In the Data application, the infinity ideal is invertible by its line structure, the special infinity coordinate ring is a domain, and reduction has kernel `(2)`. Every special point ideal contains a nonzero horizontal polynomial; therefore every degree-two special-divisor infinity ideal is nonzero. The literal `special_infinity` equality transfers this to the reduced Data ideal. These are real source premises, not a compatibility assumption.

## Scope

The new conclusion establishes infinity scalar saturation for every Data and proves integral ideal equality from a specified generic equation with nonzero-reduction presentations. It neither determines the independently stored infinity mark nor constructs those presentations globally. Shared primitive principal presentations, compatible generic equations on both charts, global chooser point compatibility, and B03 remain separate obligations.
