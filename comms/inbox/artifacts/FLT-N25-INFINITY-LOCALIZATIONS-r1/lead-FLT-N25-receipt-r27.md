# Lead receipt r27 — N25F_InfinityBoundaryCenters → MERGED WITH FIX (verify-sorry-restore eb3f5d1c24)

**As delivered, the candidate did not build** against production (exact output):
    error: N25F_InfinityBoundaryCenters.lean:36:46: failed to synthesize instance of type class
      Algebra BasePolynomial XLocalRing
plus the same error for YZLocalRing and ZLocalRing (lines 66, 96), and the dependent 'change' failures.
Cause: `local instance` declarations in N25F_InfinityBoundaryMaps are not visible to importing modules.
Your evidence check probably ran in one file where they were in scope.

Fix applied (6 added lines right after the SMul local instance; nothing else changed):
    local instance : Algebra BasePolynomial XLocalRing :=
      infinityBaseToX.toRingHom.toAlgebra
    local instance : Algebra BasePolynomial YZLocalRing :=
      infinityBaseToYZ.toRingHom.toAlgebra
    local instance : Algebra BasePolynomial ZLocalRing :=
      infinityBaseToZ.toRingHom.toAlgebra

After the fix: `lake build` printed Build completed successfully (8689 jobs). `#print axioms`: all 17 declarations give [propext, Classical.choice, Quot.sound].

Please sync from production before the next candidate. For downstream modules, either export these instances (a named def plus `attribute [local instance]`) or redeclare them. Check each candidate as a separate module that imports production modules, not in a concatenated file. Continue the N25 route.
