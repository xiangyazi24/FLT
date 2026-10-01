# FLT actual integral tensor-comparison stack: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.
Five files, 838 lines; exact identities are in `tensor-stack-source-audit.json`.

## Result and verification limits

No concrete unresolved mathematical, source-signature, orientation, or direct circular-assumption issue found. Compilation, tactic elaboration, typeclass inference, and transitive axiom checks are NOT RUN. This is not kernel acceptance.

All 89 files in the refreshed pinned source inventory were independently rechecked for byte count, SHA-256, and Git blob identity. Earlier mismatches in SexticMumford and IntegralFractionalHull were exactly one extra trailing newline; the author corrected both to pinned bytes before this final snapshot.

## Per-file checks

### N13OverlapBranchCompatibility

The ordinary/formal and rational-affine diagrams compose in the correct order. Positive and negative overlap maps restrict to the actual named affine Laurent maps and infinity power-series inclusions. Injectivity is derived from faithful affine restriction and localization, then transferred through the ordinary overlap equivalence and infinity-to-overlap injection. The localization witness orientation is correct. Applying either branch map to the original cross-product preserves exactly the same numerator and denominator.

### N13PrincipalBranchIdeals

Nonzero power-series order agrees with Laurent order under inclusion. Division by X to the finite order produces a unit, so an order equation proves the principal power-ideal equation. Powers of two have Laurent order zero. The scaled primitive presentation and exact overlap cross-product yield ord(c)=ord(f)+ord(d) on both branches without changing the rational function. The positive orientation gives the positive multiplicity balance; the previously audited norm/degree identity gives the negative balance with the correct sign. Both final principal-ideal equations have c times the left tensor and d times the right tensor. The final simplification patterns match these orientations.

### N13PrimitiveAffineComparison

Powers of two contribute unit ideals only over the rational generic affine ring. The generic scalar-cleared equation therefore follows from the actual principal multiplier. Primitive principal ideals have nonzero reductions and are invertible; the established saturation theorem and tensor-product saturation make both cleared integral ideals saturated. Localization membership then descends both inclusions. No integral nonunit is cancelled without saturation.

### N13IntegralPrincipalComparison

The affine equality maps to the ordinary overlap using the line's actual gluing equations. The same-fraction cross-product converts it into the infinity-cleared overlap equation by cancellation of a nonzero principal ideal in the domain overlap. Mapping onward gives the generic-away equality. Nonzero primitive reductions preserve invertibility and nonzero special reductions of the cleared infinity ideals, allowing the reviewed generic/integral comparison theorem to supply their full integral equality.

### N13MarkedTensorComparison

The oriented quotient equality extracts a multiplier with left tensor times principal(f) equal to the right tensor, plus the corresponding positive-order equation. The two shifts by -1 cancel on each side. Raw certificates identify the affine graph ideals. The proof constructs one primitive a/b presentation, transports that same fraction to c/d, derives both branch equations, proves both integral ideal equations, and fills every IntegralComparison field. No integral comparison, point compatibility, or special-code additive law is an assumption.

## Scope boundary

The main theorem is a genuine source-level construction of integral tensor comparisons for data carrying the actual effective/raw/saturation/branch certificates. Global rational-class choice, required calibrations, rational-point compatibility, the special-code bridge, and all compiler/axiom checks remain separate work.
