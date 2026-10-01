# B03 exact endpoint and specialization: independent source audit

Reviewed the five final modules, 532 lines, following the frozen14-module source review. Exact SHA256 hashes are in endpoint-delta-audit.json. No concrete mathematical or inspected source-signature defect found. All previous14 file hashes remain unchanged. All98 currently inventoried pinned source files rehash to their recorded Git blobs and SHA256 values at commit887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.

This is source-level acceptance only. No Lean invocation, elaboration, typeclass/tactic execution, ordinary-decide certificate evaluation, or kernel axiom check was performed.

## Finite local maps and literal point ideals

N13SpecialFiniteBranchFaithfulness proves the two finite branch maps are faithful by multiplying conjugate branches to obtain the translated polynomial norm. Translation X↦X+a is injective because composition with X−a recovers the original polynomial. Thus nonzero comparison numerators and denominators remain nonzero at each formal branch, as required before applying Laurent order multiplication.

N13SpecialFinitePointOrders maps the actual point ideal generators to X+a−xP and yBranch−yP. At the same point the first generator is X and the second is divisible by X, so the mapped ideal is exactly (X). At another horizontal coordinate, the first generator has nonzero constant term; on the other sheet at the same coordinate, the second does. Hence every other point has unit ideal. Infinity points are absent from the affine chart. The symmetric-square/tensor extensions multiply the actual ideals and add actual multiplicities.

The code weights agree with the pinned curvePointEquiv and pointCode definitions: finite coordinates(x,y)=(0,0),(0,1),(1,0),(1,1) have weights1,−1,7,−7; infinity v=0,1 have weights8,−8. No sheet is silently swapped. In particular the named rational cusp at x=−1 has the separately documented good-model sheet reversal, retained by the pinned cusp-code theorem.

## Exact original B03 bridge

The affine comparison yields ord(aNum)+leftCount=ord(aDen)+rightCount at each finite branch. The same cross-product aNum*uLeft=aDen*z yields ord(z)+leftCount=rightCount+ord(uLeft). Subtracting the two sheets cancels the identical polynomial contribution. At infinity, the full ordinary-overlap cross-product transports that same fraction; comparison and polynomial order give ord(z)+leftCount+deg(uLeft)=rightCount. The degree term again cancels between the two sheets.

The three sheet-difference equations, with coefficients1,7,8, give weightedLocalCode(z)=code(right)−code(left). The numerator supplied by exists_certified_numerator is precisely the same z with the same cross-product, nonzero proof, six actual jet certificates, and zero weighted code. Thus degreeFourCode_eq_of_comparison has exactly the original four divisors and original SpecialComparison as inputs; no degree bound, support assumption, local-order certificate, code-compatibility axiom, or additivity premise was added. The final equality direction is correct: zero=right−left implies left=right.

## Constructed specialization and classifier

Tensoring a special comparison by one common divisor retains all four comparison functions and its overlap equation. The degree-four theorem then cancels the common divisor code to prove the degree-two comparison result.

N13CalibratedChooser.chooser_tensor_comparisons supplies actual integral comparisons. IntegralComparison.reduce preserves their nonzero reductions and maps both ideal equations and the same overlap fraction. The pinned restrict_tensor_data/restrict_data identities expose the literal special divisors of the same chosen Data. The code balance is therefore proved, not supplied. Subtracting the code of choose0 constructs specialCode and its zero/additive laws, hence specialization:G→+ZMod19.

Point compatibility uses the constructed chooser's actual integral point comparison. After reduction the degree-two result identifies the divisor codes; the independently proved finite picCode_injective identifies the special set-valued classes. The pinned rational-point Data's special_eq gives actual proper reduction. The positive infinity calibration supplies the same anchor at zero. Recentring turns code(P+anchor)−code(2anchor) into pointCode(P)−pointCode(anchor), with no mismatch of degree-two versus degree-zero normalization.

The classifier is defined with kernel=specialization.ker and classify(P)=choose(P).toSpecialPic. Its exactness proof in both directions is algebraic cancellation of the common anchor code plus picCode injectivity. CompatibleReduction supplies exactly the original fields using the actual proper reduction map and its cusp theorem. No classifier-exactness or point-compatibility premise is assumed.

The negative infinity cusp maps to−8−8=3 mod19. For any r, the witness(13*r).val•T maps to r since13*3=1 mod19. This proves surjectivity of the actual constructed specialization. It does not prove separatedness of its kernel or the final rational-point classification.

## Dependency boundary

The19 B03 candidate files contain no uncommented sorry/admit/axiom/native_decide/sorryAx or flagged exactSpreadLine/n13_class_eq_iff/N13SpecializationGroupHom references. The new endpoint uses the prior reviewed concrete chooser/comparison construction and the new finite-jet geometry. The source picCode_injective derives from finite separation of the21 degree-two divisors under the explicit AbelRel, not from assumed general principal compatibility; the latter is supplied by the new B03 proof. The pinned reduction/tensor identities and named cusp-code checks were inspected directly. Standard imported libraries and all tactics still require eventual kernel validation; token/declaration review is not an axiom audit.
