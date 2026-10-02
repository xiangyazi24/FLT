# N13 small-function certificate source repair

Base: b07243d72093bec5686e15b1208cb50d000f3e8d (the mathematics dependencies are unchanged from c200807b37eacfbeac530c86968a8f39094119e2).
Input source: branch commit 4109ba77745784c1a9f8c4c7b304df4124bf5ac4.

## Result and verification boundary

The repaired file is `candidate/FLT/Assumptions/MazurProof/N13SpecialSmallFunctionCertificate.lean` relative to the enclosing endpoint package. It keeps every public definition body and both public theorem statements literally unchanged. All additional declarations are private proof helpers or certificate rows. No theorem hypothesis or target was weakened.

- Standalone exact GF(2) arithmetic: PASS, all 128 coefficient pairs
- Explicit integer-polynomial halving identities used by the generated proof: PASS during generation
- Public source values and statements: PASS, byte-for-byte declaration comparison
- Enumeration coverage: PASS, 128 row lemmas and 128 dispatch leaves
- Lean compilation: NOT RUN, reserved for lead
- Kernel theorem checks and axiom audit: NOT RUN, reserved for lead
- No project/build/cache/Lean executable was run
- No remote write was made

These checks are source and mathematical checks, not a claim that Lean has accepted the file.

## The repair

1. Added the required noncomputable section without changing any definition value.
2. Moved resource options to ordinary commands before declarations, so no doc comment is attached to a `set_option` command.
3. Replaced the first theorem's polynomial-divisibility decision with six explicit division witnesses.
4. Replaced the second theorem's blanket decision over polynomial divisibility with a full, explicit finite proof split:
   - 69 coefficient pairs have valid jets and zero weighted code
   - 58 nonzero norms have a monic nonconstant obstruction factor coprime to X and X - 1
   - the sole zero norm is a=b=0, excluded because it cannot divide the nonzero target
5. Added a proved `List.findIdx_eq` bridge: first-nonzero-coefficient certificates imply the original `jetOrder` value. Neither the public `jetOrder` definition nor its semantic meaning changed.

## Six residual cofactors

The two x=0 residuals equal X^9 * (X + X^5).
The two x=1 residuals and two infinity residuals equal X^9 * (1 + X^2 + X^3 + X^7).

The identities are proved from `(2 : K[X]) = 0` by `linear_combination`, with explicit integer-polynomial multipliers. For every identity L=R, the generator expands L-R over Z, checks that each coefficient is even, and emits the polynomial (L-R)/2 multiplying that characteristic-two equality. This avoids trusting an external polynomial arithmetic result inside Lean: the emitted identities are independently checked by Lean's ordinary ring proof machinery when the lead compiles them.

## Unsupported norms

For each of the 58 nonzero unsupported norms N, the file supplies N=f*q. There are 17 distinct factors f (binary coefficient codes, coefficient of X^i is bit i):

11, 21, 37, 59, 61, 67, 69, 73, 81, 91, 103, 109, 117, 261, 273, 321, 341

Each has positive degree and is monic. Its explicit Bezout identities are

f + u*X = 1
f + v*(X-1) = 1

Consequently f is coprime to X^16*(X-1)^16. If N divided that target, f would divide it and therefore be a unit. A monic unit is 1, contradicting the checked positive-degree coefficient. Irreducibility of f is neither asserted nor needed.

## Supported rows

Each of the 69 rows supplies explicit normal forms for all six jet polynomials and a vector of six first-nonzero indices. Coefficient equalities and inequalities are discharged after splitting only the finite index types. The original `jetOrder` values follow from the bridge. The largest supported order is 7, safely below 9. The weighted code is checked in ZMod 19.

The remaining ordinary `decide` calls are only:
- scalar/natural finite facts, such as six concrete indices being less than nine
- concrete arithmetic in ZMod 19
- the two-element scalar case split
- the unchanged public `jetOrder` definition's scalar coefficient predicate

No polynomial divisibility or existential polynomial search is passed to `decide`.

## Reproduction

Run `python certificate_math.py` for the standalone bit-polynomial check and JSON table. Run `python generate_candidate.py` in this directory to create `REGENERATED_N13SpecialSmallFunctionCertificate.lean` from the included unchanged input plus the table. Then run `python independent_certificate_audit.py` and `python independent_source_literal_audit.py` for the separate arithmetic and generated-literal checks. The accepted Lean overlay is in `FLT/Assumptions/MazurProof/N13SpecialSmallFunctionCertificate.lean` at the repository root. Neither script invokes Lean, a project runner, a build, or a cache tool.

The JSON table `certificate_math.json` records every norm, six jets, order vector, weighted code, and the obstruction factor/cofactor/Bezout data for each unsupported nonzero row.

The remaining local-order/geometric comparison theorems are outside this file's scope. No claim is made here that the FLT endpoint is completed merely by repairing this certificate.
