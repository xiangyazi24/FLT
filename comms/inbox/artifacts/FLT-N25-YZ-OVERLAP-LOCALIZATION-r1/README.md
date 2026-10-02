# Actual Y/Z overlap localization map

N25F_YZOverlapLocalization.lean extends the preceding actual ZChartRing map
into YZLocalRing to Localization.Away zY, using the proved unit image of Y/Z.
It proves the algebraMap restriction and the exact inverse-coordinate formula:
the image of Away.invSelf zY is the existing actual germ Z/Y.

The production file adds no premise, axiom, sorry or admission. It is only a
canonical one-sided localization map; it does not claim the full affine
Y/Z overlap equivalence or a local-ring isomorphism.

## Verification

The generic commutative-algebra proof passed in 7.587 seconds, exit 0,
2451940 KiB peak child RSS, one CPU/thread, 3072 MiB and 60-second bounds,
shared flock gate. All three new public declarations print only propext,
Classical.choice, Quot.sound. The prior generic map proof is included
unchanged. Only inherited fixture/style warnings remain. The initial failed
check needed the explicit unit argument to a standard inverse lemma; both
logs are retained and only generic-02 is acceptance evidence.

As in the predecessor packet, the target is parameterized by a commutative
Y-chart algebra L with unit image of Z/Y. This is GENERIC feedback. The
actual YZLocalRing specialization and full FLT imports are NOT RUN and
await the provided ActualYZOverlapLocalizationCheck.lean. The production
statement itself uses the existing local ring and its actual unit theorem.

Lean 4.31.0-rc2 / Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.
Production predecessor: 295b9a6e6fbc0cae9e2fb60a8423dc9b48eccb9c.
Fixture import paths and hashes are recorded in validation.json. Both
predecessor Z .olean directories are required in LEAN_PATH when reproducing.
The script preserves original paths, and no earlier source was modified.

An unconditional equivalence between the actual two affine overlap
localizations is being proved separately. The YZ local DVR/field order and
projective product formula remain open; integration remains lead-owned.
