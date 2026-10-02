# Actual Z-chart injectivity and function-field equivalence

Two production candidates are supplied:

1. N25F_ZChartFractionInjective.lean proves qz_pow_ne_one and actual
   zChartToFraction_injective. A noninjective map from the dimension-one,
   finite-type F2 chart to a field has finite image. Hence 1/qz would have
   finite positive order. Pulling qz^n=1 back through the faithful polynomial
   coefficient algebra and evaluating X at zero gives the contradiction.
2. N25F_ZChartFractionEquiv.lean extends that actual map to fraction fields,
   proves the range contains qz, qx and qy, and then all of W by quotient
   polynomial induction. Fraction representation gives surjectivity and the
   coordinate-rigid algebra equivalence. The IsFractionRing theorem uses an
   explicit letI algebra induced by zChartToFraction, avoiding any competing
   global scalar action.

No new production hypothesis, substitute carrier, custom axiom, sorry,
admit, or native_decide appears. Passed source predecessors remain unchanged.

## Checks

The injectivity source assembly includes the earlier exact Z-map harness,
the complete Z/W equivalence proof body, and the complete new injectivity
body. The two coordinate definitions already included in the Z-map fixture
are not duplicated; their original exact definitions are used. The first
check exposed only two leftover doc comments in that extraction; removing
the comments did not change any production source. The corrected check-02
passed in 30.584 seconds, 2553612 KiB RSS, and emitted ZChartInjectiveCheck.olean.
Both new public results printed only standard propext/Classical.choice/Quot.sound.

The field-equivalence harness imports that exact checked module and checks
the new production body with the accepted W torsion-free and Dedekind
instances as ordinary parameters. Its first check passed in 18.858 seconds,
2469712 KiB RSS, with all eleven public results standard-three only, and
emitted ZChartFractionEquivCheck.olean.

Both runs used Lean 4.31.0-rc2, Mathlib96fd0fff3b8837985ae21dd02e712cb5df72ec05,
one CPU/thread, a 3072 MiB memory cap, 60-second timeout, and the shared
serialization gate. Production imports supply the parameterized accepted
instances. Full FLT import compilation is NOT RUN; the ActualZFieldCheck
file is the lead validation request. No local full-project acceptance is claimed.

## Reproduction and dependencies

Predecessor source is at dot commit ec7da3d29290b8c56a9cc80b8081694abb2674c2
(Z map) and 6999499b1155d42c8ac17876012b3625d1a59b1e (Z/W equivalence), pinned
against accepted FLT f0eb8381677bc483bddd93826871845030dd5c0e.

The reconstruction scripts retain their original local paths, which can be
adjusted. Source snapshots come from the existing exact-pin source manifest;
they are not duplicated. The Z-map fixture has 83 copied declarations from
14 accepted files plus predecessor coordinates. The checked production
proofs extend those exact objects without a proxy.

The injection run's -R/-o command is in its receipt. For the field check,
set LEAN_PATH to the directory containing ZChartInjectiveCheck.olean.
validation.json records all input/output hashes. Binary .olean files are
not committed; rebuild them with the exact bounded command when needed.
The field module also depends on its injection .olean, so include both
directories in LEAN_PATH for future imports.

The actual Z-boundary localization/DVR and normalized order remain next.
The actual YZ-overlap unit alone does not prove a local-chart equivalence.
The full boundary coefficient triple, product formula, and N25 exclusion
remain open; the lead owns full import checks and integration.
