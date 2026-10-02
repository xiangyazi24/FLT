# Actual YZ-boundary overlap unit: small source candidate

`N25F_YZLocalZUnit.lean` names the genuine Z/Y germ in the existing YZLocalRing
and proves it is a unit. It uses the public actual coordinate yZ and the
existing theorem yzPointEval_yZ = 1. Thus yZ is outside yzPrime and its image
is invertible in Localization.AtPrime yzPrime. No replacement local ring,
new hypothesis, or chart-equivalence assumption is introduced.

The 29-line production specialization is source-reviewed against exact
accepted FLT f0eb8381677bc483bddd93826871845030dd5c0e. Its full imports have
NOT RUN locally. The exact generic localization/kernel argument passed
Lean 4.31.0-rc2 / Mathlib 96fd0fff in 2.312 seconds, 2127632 KiB RSS, one CPU/thread,
3072 MiB and 60-second limits, with standard-three axioms only. This is generic
feedback, not a claimed compilation of the actual specialization.

The initial generic check required an explicit kernel-primality instance;
the actual specialization already obtains this from the accepted maximality
theorem. Both diagnostic logs are retained. The actual full-import validation
request is `ActualYZLocalZUnitCheck.lean`.

This unit is a concrete prerequisite for transporting the existing YZ local
ring across the Y/Z chart overlap. The overlap isomorphism, YZ DVR and shared
field valuation remain unproved. Source URLs/hashes and exact check metadata
are supplied; no prior source or candidate was changed.
