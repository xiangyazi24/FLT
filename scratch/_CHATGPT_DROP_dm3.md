# Q2113 dm3

I attempted to read `FLT/Assumptions/MazurProof/MillerFunction.lean` on branch `ai-scratch`, but the GitHub connector returned `404 Not Found`; repo search also found no hits for `MillerFunction`, `evalAtPoint`, `verticalFunction`, or `lineFunction`.

Because the source file is not visible through the connector, I could not verify an exact patch against the local definitions.  The main conclusion is: evaluation is total on `W.CoordinateRing`, but not total on `W.FunctionField` without a regularity/non-pole hypothesis.  The O-case simp lemmas for `verticalFunction_zero` and `lineFunction_zero_left/right` should close by `rfl` or `simp [verticalFunction, lineFunction]` if those functions pattern-match on `0` and return `1`.

The true Weil-pairing properties, including additivity, self-pairing, power order, and nondegeneracy, are hard theorem seams unless the file stores them as fields of an abstract structure.
