# FLT simultaneous actual branch-jet lifting: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`.
Exact candidate identity: `jet-lift-source-audit.json`.

No concrete mathematical, namespace, or checked-signature issue found. Compilation and axiom checks remain NOT RUN.

The actual root-difference unit is mapped to the generic power-series ring. Its inverse yields v=(r-s)/(r0-r1), u=r-v*r0, with u+v*r0=r and u+v*r1=s. The sign agrees with the named positive/negative roots.

The exact pinned `IsLocalization.surj₂` returns one common denominator with p*map(d)=map(a) and q*map(d)=map(b). Its polynomial specialization matches the existing pinned source construction. Extracting the constant-polynomial denominator gives one nonzero c in Z2 for both truncated interpolation polynomials.

The constructed ordinary element z=base(p)+base(q)*vClass therefore has branch expansions equal to the interpolated truncations multiplied by C(c). The difference from each requested scaled branch series is a sum of truncation errors, multiplied by the corresponding root and C(c). These operations preserve divisibility by X^n. This proves simultaneous arbitrary finite-jet lifting on the actual chart maps, without assuming a density or surjectivity claim.

The witness c is nonzero, not asserted to be a unit in Z2. Later arguments must retain this scalar or cancel it only where justified. Ideal-membership approximations and generic infinity ideal comparison still need to be derived from this lift and the previously proved branch kernel.
