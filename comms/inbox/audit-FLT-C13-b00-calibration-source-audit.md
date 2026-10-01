# FLT calibrated chooser: independent source audit

Reviewed the frozen 15:41 snapshot at source pin `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`. No concrete mathematical or inspected source-signature defect found in the three final modules. This is an uncompiled source review: elaboration, tactic execution, typeclass synthesis, and `#print axioms` were not run. The JSON receipt records exact file hashes.

## Exact endpoint and named points

`N13CalibratedChooser.globalExistenceTarget` proves the existing `N13CoherentChooserSpecification.GlobalExistenceTarget` definition without parameters or added premises. It constructs the original Chooser, integral tensor comparisons for every P,Q, and the literal prescribed values at 0,T,−T. Certified contains only an effective SemiMumford witness, literal raw equality, affine saturation, and actual two-branch multiplicities; neither comparison nor additivity is a field.

The three case values are certified and have the correct generic classes. The disjointness checks compare the balanced representatives with nInf 1,0,2. The inverse-infinity certificate uses caSemi with u=X(X+1), v=1, nInf=−1, hence raw mark −2 and actual branch multiplicities (0,0). It does not confuse this SemiMumford datum with the balanced caMumford of nInf=0 and raw mark −1. The pair-line map uses the pinned split-ideal theorem in its actual product-to-graph direction; goodY/pointY cancel in both factors.

The named positive infinity has multiplicities (2,0), negative infinity (1,1), and anchored affine points (1,0). The anchor simplification only uses the infinityIdeal projection of tensorPow at one, so its extra tensor-with-one disappears by ideal multiplication. It does not require an unproved equality of whole chart-line structures. The rational-point dispatcher has exactly the same norm dichotomy, good-model conversion, integral lift, and negative-valuation proof as the pinned source. Proof irrelevance accommodates the reconstructed curve and valuation proofs.

Point compatibility follows from certified generic equality and the previously reviewed full integral comparison. Tensor comparison uses classes P+Q and 0 and `map_add/map_zero`, retaining the original comparison orientation. The piecewise chooser's three branches are made disjoint before proving the calibration equations.

## Surjectivity-only existence delta

`N13EffectiveDataCompatibility.exists_certified_realization` now obtains D directly from `N13MumfordInfinityBalance.classOf_surjective P`, maps that same D to Q₂, and applies the repaired marked-data construction. Its final rewrite is coefficient-extension class compatibility followed by hD. No `normalizedMumford`, `NormalFormData`, uniqueness, or injectivity is needed in this declaration.

## Injectivity dependency trace

The invoked theorem is `N13SmallMumfordRigidity.classOf_injective`, not the generic theorem with a NormalFormData premise. Its chain is:

1. `eq_of_class_eq` extracts a principal multiplier using `SexticMumford.classOf_eq_iff` from SexticOrientedPic. This is the literal QuotientGroup relation with its two projections; it is not the separately flagged `n13_class_eq_iff`.
2. `principal_is_constant` obtains integral factors z=αu₁ and w=α⁻¹u₂, with zw=u₁u₂ and membership in the opposite graph ideals, from SexticMumfordPrincipalNumerator.
3. Orientation gives ord₊α=nInf₂−nInf₁. For balanced Mumford, nInf is natural and degree(u)+nInf≤2. Thus both factors have positive order at least −2. Their product polynomial has degree at most four.
4. `N13FactorRigidity.factor_pair_coeffY_eq_zero` uses the actual negative branch: a nonzero Y coefficient and positive order ≥−2 force negative order ≤−3. Both factors cannot have such Y parts because their product has negative order ≥−4. If one Y coefficient vanishes, the rank-two multiplication coefficient forces the other to vanish.
5. Its key branch-minimum theorem in N13BranchLeading proves min ord(p+qY),ord(p−qY)=−max(deg p,deg q+3) by Laurent valuation and invertibility of 2. It uses actual injective branch maps, not a principal comparison/coherence assumption.
6. Polynomial contraction shows z=u₂c,w=u₁d with cd=1. SexticMumfordPrincipalScale cross-multiplies the ideal equality and contracts it to recover u₁=u₂. Polynomial units are constants, so α is a constant unit.
7. `principal_between_balanced_of_constant` cancels its trivial principal ideal and order; SexticMumfordRecover recovers u,v by the ideal kernel and monic/remainder conditions and then the natural infinity index.

The natural/nonnegative balanced hypothesis is essential at step 3. No conclusion of this uniqueness theorem was transferred to arbitrary raw/SemiMumford data with negative nInf. The instance `instNormalFormData` is constructed afterward from this injectivity and structural surjectivity, and is not assumed by the injectivity proof.

## Source provenance and limitations

The complete project import closure of N13SmallMumfordRigidity contains 32 files. All are materialized and scanned with nested Lean comments removed; none contains a `sorry`, `admit`, `axiom`, `native_decide`, `n13_class_eq_iff`, or `exactSpreadLine` token. This includes structural-reduction sources imported for surjectivity. Closure edges and exact local SHA256/Git-blob hashes are in calibration-import-closure.json. Newly retrieved exact-pin sources and GitHub blob receipts are in calibration-pinned-reference. Existing source inventory bytes were rechecked against its recorded pin/blob hashes. Import scanning is supplementary evidence, not a kernel proof-dependency or axiom check.

The prior reviewed comparison stack remains uncompiled as well. These findings support source-level endpoint acceptance only, not a claim that Lean has accepted the endpoint or that B03 additivity is proved.
