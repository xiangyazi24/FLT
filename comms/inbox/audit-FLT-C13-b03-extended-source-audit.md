# B03 geometry and six-jet source audit

Reviewed 14 modules through N13SpecialSixJetOrders, with the exact post-rename hashes in extended-source-audit.json. No concrete mathematical or inspected API defect found after the author renamed the bare `include` helper to `includeSeries` throughout the dependent files. The bare name was flagged as a Lean command-keyword/parser hazard; no parser run was performed. Review remains source-only and uncompiled, including the ordinary-decide certificates.

## Discharging the two-infinity bounds

N13SpecialLaurentBranches uses the actual good characteristic-two equation, with x=t⁻¹ and y=t⁻³r. Multiplying its equation by t⁶ gives exactly r²+(1+t²+t³)r−(t+t²)=0. The two ordinate branches have difference h(x), using 2=0 rather than dividing by2. Hence their difference on p+qy is qh(x). The Laurent lower-order inequality and degree(h)=3 give deg(q)+3≤d; subtracting the ordinate term then bounds deg(p)≤d. evalPoly_order and evalPoly_ne_zero in the pinned N13BranchNorm explicitly omit CharZero and are applicable here.

The affine norm proves each Laurent branch is faithful. Actual overlap localization transports that faithfulness to the infinity chart; no injectivity of completion is assumed. The localization witness is used with the correct z*map(s)=map(a) orientation and a genuine unit denominator. The pinned ordinary-overlap diagrams preserve exactly the same aNum/aDen=iNum/iDen fraction.

Literal mapped infinity ideals give order1 at their own point, order0 at the other infinity, and order0 for finite points. Finite-degree plus both infinity counts equals4 for each tensor of degree-two divisors. Mapping the infinity principal equation gives ord(iNum)+leftCount=ord(iDen)+rightCount. Combining the overlap fraction and aNum*uLeft=aDen*z gives ord(z)=rightCount−leftCount−deg(uLeft), which is at least−4. This establishes the formerly open pole-bound premise from the original SpecialComparison, with no added hypothesis. The same cleared numerator therefore has deg(p)≤4, deg(q)≤1 and the supported nonzero norm already reviewed.

## Finite certificates and actual branches

The finite space is the 32-by-4 coefficient arrays, including the zero pair before the norm-divisibility premise excludes it. The certificate checks the six approximate root equations mod X⁹, all first-nonzero coefficient assertions, and the weighted code. Ordinary `decide` is used; its execution and resource adequacy remain untested. No independent numeric/exhaustive run was performed in this audit.

RootJetAgreement is an algebraic Hensel uniqueness argument: subtract the exact and approximate quadratic equations; the factor r+s+H has constant1 in characteristic two and is a unit. Dividing only by this unit proves equality of jets. FiniteBranchJets constructs the actual two roots over each finite x=0,1 via the same IsAdicComplete/HenselianRing pattern used by the pinned integral infinity source. Its coordinate substitution x=X+a and the four displayed jet assignments agree with the equations and constant terms.

JetOrder proves genuine Laurent order from a coefficient below precision9 that is nonzero and the vanishing of every lower coefficient. Thus the finite List.findIdx definition is not trusted to imply any unproved order law. CertifiedNumerator encodes all degree-bounded polynomials exactly by their coefficients and extends the supported norm divisibility to X¹⁶(X−1)¹⁶. This weakens only the sufficient finite-certificate filter, not the arbitrary-comparison theorem.

SixJetOrders transports these certificates to all six actual local expansions of the same numerator. The exact reciprocal identity t⁴(p(t⁻¹)+q(t⁻¹)t⁻³r)=A(t)+B(t)r has A=Σaᵢt^(4−i), B=b₀t+b₁. Accordingly each infinity order is its jet order minus4. The two shifts cancel in the weighted code because the infinity weights are+8 and−8. The finite branch weights and signs are consistently 1,−1,7,−7 in the new weightedLocalCode definition.

## Exact API checks and limits

At Mathlib pin96fd0fff3b8837985ae21dd02e712cb5df72ec05, inspected HahnSeries.le_order_iff_forall, order_le_of_coeff_ne_zero, coeff_eq_zero_of_lt_order, order_pow, ofPowerSeries_apply_coeff, ofPowerSeries_X, and the Laurent PowerSeries.coeff_coe formula. Their hypotheses, coefficient casts, and directions match the inspected uses. Henselian root construction matches the exact existing source pattern. No claim is made that simplifier/tactic scripts or typeclass inference have run successfully.

The present endpoint proves zero weighted local code for the certified numerator. The remaining B03 work is to relate all finite local ideal multiplicities to the input comparison, cancel the cleared polynomial contribution, and identify these weighted codes with the original finite Abel-code compatibility theorem. The arbitrary principal-code comparison and final additivity endpoint are not yet claimed by these14 modules. The earlier three-file audit's open pole-bound issue is now discharged at source level; its finite-code endpoint remains open.
