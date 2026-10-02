# Actual YZ-local overlap map; generic algebra feedback

`N25F_YZOverlapMap.lean` constructs the actual Z-chart algebra map into the
existing YZLocalRing. It normalizes the universal Y-chart point using the
unit whose value is the previously proved germ Z/Y. Homogeneity preserves
both canonical equations, so quotient evaluation supplies the map.

The exact images are:
- zX ↦ inverse(Z/Y unit) × image(X/Y)
- zY ↦ inverse(Z/Y unit)
- zW ↦ inverse(Z/Y unit) × yzWGerm

The image of zY is proved to be a unit. No field/domain assumption on the
target local ring is needed for this construction. No production premise,
custom axiom, sorry, admit or native_decide is added. The module uses the
existing Y/Z chart quotients and existing YZLocalRing, with its previously
supplied actual unit candidate.

## Verification distinction

The actual YZLocalRing specialization and full FLT imports have NOT RUN.
The passed check is stronger in a different direction: it validates the
complete coordinate-normalization/quotient-map argument for any commutative
Y-chart algebra L in which the image of yZ is a unit. The fixture explicitly
supplies that unit condition as a Fact, replaces local germs by their exact
algebraMap expressions, and instantiates only the target type parameter.
This is generic algebra feedback, not a claimed check of the actual point
or of its earlier unit specialization.

The actual YChartRing, yZ and yzW definitions are copied verbatim from the
accepted source. The Z chart and canonical equations come from the checked
emitted predecessor module. The complete production proof body is otherwise
retained, with explicit L arguments added where the generic context requires
them. Definition names in rw steps remain un-applied names.

The corrected generic check passed: exit 0, 5.215 seconds, 2445992 KiB RSS,
one CPU/thread, 3072 MiB cap, 60-second timeout, shared flock gate. Eight
printed public declarations use only propext, Classical.choice and Quot.sound.
Four fixture/style warnings remain. The initial failed extraction/rewriting
diagnostics are retained and excluded from acceptance evidence.
Lean 4.31.0-rc2; Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05.

## Source synchronization

The original fixture source baseline is f0eb8381677bc483bddd93826871845030dd5c0e.
Source has now advanced to 1eab90d583a58211846c1b69e24e5ed73a59ce4d, adding only
our byte-equal XChartFractionMap. A verified compare establishes that these
Y/Z source definitions did not change. The observed commit reports the leaf
build/axiom pass; the formal next dispatch receipt is still awaited.

Required candidate predecessors: N25F_ZChartWChartEquiv at 6999499b1155d42c8ac17876012b3625d1a59b1e,
and N25F_YZLocalZUnit at ec7da3d29290b8c56a9cc80b8081694abb2674c2.
The tested fixture imports emitted ZChartFractionEquivCheck, whose source
and binary provenance were delivered at 0e8b444e8295b7247f00008ff54869736e78ca98;
that extra fixture import is not a new production dependency.

Use both predecessor .olean directories in LEAN_PATH when reproducing the
bounded check; the included script retains original paths for provenance.
ActualYZOverlapMapCheck.lean is the required real-import validation request.
This map is not yet a local-ring isomorphism. The remaining YZ-local DVR,
shared-field order, full coefficient triple and product formula stay open.
