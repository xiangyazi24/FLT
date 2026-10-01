# B03 special geometry: independent source review

Reviewed the three 507-line uncompiled candidates at source pin 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5. No concrete mathematical or inspected API defect found. Hashes are in source-audit.json. No compilation, tactic execution, typeclass synthesis, or kernel axiom check was run.

## Infinity branch jets

The maps reduce the actual integral Hensel branches to characteristic two. The roots have constant terms 0 and 1, and their difference is a unit because it is the image of the known integral difference unit. Thus this argument never divides by the characteristic-two scalar 2. Rank-two normal forms and subtraction recover divisibility of each polynomial coefficient from vanishing of both branch jets, and the polynomial X-power coefficient criterion reconstructs literal t^n divisibility. The four point-ideal identities have the correct own-branch order one and other-branch unit ideal. They agree with the actual infinity-point ideal generators in the pinned source.

## Factor pair from arbitrary special comparison

Each finite rational point contributes X or X−1; each infinity point contributes 1. The polynomial lies in its chart ideal, remains monic, and has degree bounded by the divisor degree. From aNum I=aDen J the proof produces z in J and w in I with aNum*uI=aDen*z and aDen*uJ=aNum*w. Cancellation is legitimate in the actual special affine domain and uses both nonzero comparison functions. The resulting zw=uI*uJ has degree at most eight. The exact pinned Mathlib Ideal.mem_span_singleton_mul witness has equality y*z=x, matching both final symmetric equations and the internal cancellation rewrite.

## Characteristic-two affine norm

Conjugation is y↦−h−y for y²+hy−rhs=0, so the norm is p²−pqh−q²rhs. The displayed multiplication identity, involutivity, nonvanishing, multiplicativity, and norm(xClass P)=P² agree. This is the good characteristic-two coordinate ring. It does not use the invalid completed-square operation at 2. The degree bound under deg p≤4, deg q≤1 uses deg h=3 and deg rhs=5, giving degrees at most 8,8,7. Exact pinned natDegree_pow_le/mul_le/sub_le parameter names and inequality directions match the candidate.

Taking the norm of the actual factor pair gives a polynomial X^i(X−1)^j with i+j≤16 and proves divisibility of norm z. The exponent arithmetic retains the square and both tensor polynomials. This is a consequence of the actual comparison, without enumerating guessed principal functions.

## Remaining scope

The factor-pair module so far uses the affine ideal equation, not the infinity equation or common-overlap condition. Therefore no two-infinity pole bound on z,w has yet been obtained. The norm degree lemma has explicit coefficient-degree hypotheses; these have not been derived for the comparison factors. The finite Abel-code compatibility theorem and B03 additivity remain open. These candidates do not assume or claim either conclusion.
