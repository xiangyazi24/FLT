# Review checklist

- Actual carrier: `W` is the existing `N25F_NonBoundaryPrincipalDivisor.W`, definitionally the canonical `ChartQuotient 3`
- Actual norm: `Algebra.norm (Polynomial (ZMod 2))` uses the existing normalization's `rzAlgebraW`; the candidate does not construct or replace that algebra
- No new theorem premises: only the actual element `a` and its nonzero proof
- Scalar compatibility is proved locally by uniqueness of ring homomorphisms out of `ZMod 2`
- The basis is produced inside the proof using the finite/torsion-free module structure over the polynomial PID; the basis index is finite by Mathlib's existing instance
- The candidate is a genuine quotient-dimension/norm-degree identity, not a reindexing or an assumed weighted-degree formula
- Accepted quotient-finiteness helper is imported and untouched
- No new axioms, `sorry`, `admit`, or `native_decide` occur in the candidate source
- The generic compiler audit and actual-project audit are separate: only the generic audit is performed by this task
- The weighted affine principal-divisor formula, boundary valuation comparison, and N25 axiom elimination remain unproved by this artifact

First generic attempt exposed a missing binary-field import. The final source explicitly imports `Mathlib.Algebra.Field.ZMod` and supplies `(F := ZMod 2)` to the norm theorem. Earlier failed-check logs are retained for transparency; only `GENERIC_CHECK.log` and its recorded exit status in `MANIFEST.json` describe the final source.
