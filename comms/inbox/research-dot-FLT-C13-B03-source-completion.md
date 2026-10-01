# FLT-C13 B03: exact degree-four bridge and additive specialization source candidates

Source: xiangyazi24/FLT @ 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5
Output branch: research-dot/flt-collaboration-20261001
Status: local source candidates; own-branch commit/push authorized. Compilation, ordinary-decide execution, and axiom checks NOT RUN. Lead owns all builds and acceptance.

## Exact results supplied

1. `MazurProof.N13SpecialDegreeFourCode.degreeFourCode_eq_of_comparison` has precisely the requested four degree-two divisors and their original `SpecialComparison` as inputs. It concludes equality of their degree-four code sums. No code-compatibility hypothesis is added.
2. `MazurProof.N13ConstructedSpecialization.specialization : G →+ ZMod 19` uses the constructed calibrated chooser. `specialCode_add` proves the requested recentered additivity.
3. `specialization_rationalAbel` identifies the constructed map on every rational curve point with its actual proper reduction, recentered at the positive-infinity anchor.

These are uncompiled source candidates, not accepted kernel proofs. The first fourteen B03 modules have independent source reviews with no concrete unresolved issue; the last finite-local-ideal/degree-four/specialization/classifier delta also passed independent source review with no concrete defect found. The ordinary `decide` certificates have not been run in Lean. No `native_decide`, new axiom, sorry, or statement weakening is used.

## Why the finite calculation now applies to arbitrary comparison witnesses

The original comparison allows arbitrary affine/infinity numerators and denominators. The proof does not assume they belong to a finite list.

- For each actual rational-point divisor, construct its monic fibre polynomial q. Its affine ideal contains q; its degree is the number of finite points, counted with multiplicity.
- The affine comparison extracts nonzero regular functions z,w with exact equations aNum*qLeft=aDen*z, aDen*qRight=aNum*w, and z*w=qLeft*qRight. Both q's are supported over x=0 and x=1 and have degree at most four.
- Construct the actual characteristic-two infinity Hensel maps and affine Laurent maps. Their difference is h(x), not twice a square root. Use the actual ordinary overlap to preserve the same fraction on both sheets.
- The input infinity ideal equation and overlap fraction give ord(z)=right infinity count−left infinity count−degree(qLeft). Finite degree plus both left infinity counts equals four, so both infinity pole orders are bounded by four.
- From the two actual pole bounds, prove z=p+q*y with deg(p)≤4 and deg(q)≤1. The conjugation norm is nonzero and divides x^i(x−1)^j with i+j≤16.
- Encode p and q by their actual five and two F2 coefficients. This gives 128 coefficient pairs, one of which is zero and is excluded by norm support. No guessed bounded-function premise is used.

## Finite certificate and actual local orders

Six explicit degree-eight polynomials satisfy the two finite-point equations at x=0 and x=1 and the infinity equation modulo X^9, on both sheets. A unit difference-factor proof identifies these jets with the actual Hensel roots.

`N13SpecialSmallFunctionCertificate.supported_small_function_certificate` uses ordinary kernel `decide` to state that every supported pair has a first nonzero coefficient below nine on all six jets, all preceding coefficients vanish, and its weighted code is zero. The weights are (1,−1,7,−7,8,−8). An independent Python cross-check confirms 69 supported pairs and maximum first-nonzero jet index seven; that check is planning/source evidence only, not Lean acceptance.

The reciprocal identity t^4*z = Abar+Bbar*v makes the actual infinity orders equal to the last two jet orders minus four. Those identical shifts cancel between weights +8 and −8. A coefficient/order lemma proves that a certified nonzero nine-jet determines the actual Laurent order.

Finally, the actual finite and infinity point-ideal images give the six divisor multiplicities. The same cleared numerator gives weightedLocalCode(z)=right code−left code. The finite certificate makes its left side zero and proves the exact requested degree-four implication.

## Additive assembly

Reduce the already constructed integral tensor comparisons. The degree-four bridge gives u(P)+u(Q)=u(P+Q)+u(0). Recenter by u(0) to construct an additive map. Tensoring a single comparison with a common divisor and cancelling its code proves equality for degree-two comparisons, hence compatibility with every named rational-point realization.

No proof uses `exactSpreadLine`, the flagged raw-to-special coherence shortcut, or `N13SpecializationGroupHom.J₂` based on the bad characteristic-two sextic.

## Lead acceptance

Compile all new modules in dependency order, then run the supplied check/axiom harness. The potentially expensive finite `decide` statements are explicit and isolated; their elaboration/reduction performance is unmeasured. If a tactic fails, repair its implementation without changing the theorem or substituting the finite code condition as an assumption.

GlobalExistenceTarget and B03 now both have complete source candidates. Full C13/project completion still requires compiler and axiom acceptance plus any remaining downstream kernel/classifier/endgame obligations; this report does not assert those are finished.
