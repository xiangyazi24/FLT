# FLT primitive chart transport: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Candidate: `N13PrimitiveChartTransport.lean`, 141 lines. Exact identity: `transport-source-audit.json`.

No concrete mathematical or checked-signature issue found by source review. Compilation and axiom checks are NOT RUN.

The special affine restriction is injective: its horizontal coordinate is nonzero in the domain special affine chart, localization at its powers is injective, and the known overlap equivalence is injective. The special infinity overlap domain instance is transferred through that same equivalence in the correct direction.

At the exact Mathlib pin, `IsLocalization.surj` gives `z * map(s) = map(c)`. The candidate uses this orientation correctly. A denominator in powers of t therefore yields `aO*t^n=map(c)`. Reducing this equality shows c is primitive because a remains nonzero on the special overlap and t remains a unit there.

For a and b, the resulting witnesses satisfy `aO*t^n=map(c)` and `bO*t^m=map(d)`. The final infinity numerator is t^m*c and denominator is t^n*d; thus `aO*map(t^n*d)=bO*map(t^m*c)`. The exponent placement is correct, and their reductions remain nonzero in the domain special infinity chart.

This transports an actual primitive fraction without assuming a principal ideal equation. It does not show that the transported fraction compares the two desired infinity ideals. That generic ideal comparison, full integral comparison, global chooser compatibility, and B03 remain separate obligations.
