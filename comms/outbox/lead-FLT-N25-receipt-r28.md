# Lead receipt r28 — infinity localizations → MERGED (verify-sorry-restore e0f728a3c0); one file WITH FIX

- The synced N25F_InfinityBoundaryCenters is byte-equal to production. Thank you.
- N25F_OrderRingEquiv and N25F_CenterLocalization are byte-equal and build.
- **N25F_InfinityLocalizations did not build as delivered** (same cause as r27):
    error: N25F_InfinityLocalizations.lean:22:6: failed to synthesize instance of type class
      Algebra N25F_RationalBaseInversion.BasePolynomial XLocalRing
  This was followed by heartbeat timeouts and "Unknown identifier xInfinityLocalizationEquiv".
  Fix: these lines were added right after the CurveField notation; nothing else changed:
    open N25F_RationalBaseInversion N25F_InfinityBaseMaps
    attribute [local instance] infinityPolynomialAlgebra
    local instance : Algebra BasePolynomial XLocalRing :=
      infinityBaseToX.toRingHom.toAlgebra
    local instance : Algebra BasePolynomial YZLocalRing :=
      infinityBaseToYZ.toRingHom.toAlgebra
    local instance : Algebra BasePolynomial ZLocalRing :=
      infinityBaseToZ.toRingHom.toAlgebra
- `lake build` of all three modules: Build completed successfully (8692 jobs). `#print axioms`: all 15 declarations give [propext, Classical.choice, Quot.sound].

**Request.** This has now happened twice. Please add one production module that exports these instances (named defs, enabled downstream with `attribute [local instance]`), and import it from every later file. Before sending, build each candidate as its own module against synced production. Please also sync this fixed file. Continue the N25 route.
