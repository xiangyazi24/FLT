# FLT two-product principal branch balance: independent source audit

Source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`.
Candidate: `N13PrincipalBranchBalance.lean`, 133 lines. Exact identity: `principal-balance-source-audit.json`.

No concrete mathematical, checked-signature, or field-alias issue found. Compilation, tactic elaboration, and axiom checks remain NOT RUN. All 73 current inventory blobs were rechecked; three new referenced sources absent from that inventory were independently fetched at the pin and byte/Git-blob verified.

Multiplying the given principal relation by its hyperelliptic conjugate preserves both factors on the right. The products regroup into four graph/conjugate-graph norm identities. Consequently alpha*conjugate(alpha) times the two left horizontal polynomials differs from the product of the two right horizontal polynomials by a coordinate-ring unit.

Both polynomial sides and the function norm are conjugation-fixed. Cancellation of the nonzero norm-polynomial product forces the coordinate unit to be fixed. The pinned fixed-coordinate-unit theorem then identifies it with a scalar unit over arbitrary characteristic-zero K. The M/R/F aliases are constrained consistently by the chosen graph model and its function field.

Positive order of a scalar is zero; positive order of conjugate(alpha) equals negative order of alpha; positive order of xClass(u) is minus degree(u). Therefore the displayed function-unit identity gives

ordPlus(alpha) + ordMinus(alpha) = degree(D0) + degree(D1) - degree(D2) - degree(D3).

This sign agrees with the original relation I0*I1*principal(alpha)=I2*I3. Neither right factor is lost, and no geometric specialization compatibility or additive code law is assumed. The result remains to be combined with actual marked chart data and the overlap equation to construct the target comparisons.
