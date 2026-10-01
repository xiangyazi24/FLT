# Independent source review: FLT-C13-KERNEL K1

## Verdict and scope

The corrected five-module, 513-line K1 chain passes independent mathematical
and source/API-shape review. One concrete cancellation-API error was found and
corrected by the author. No remaining concrete bounded-claim defect was found.
This review preserves **UNCOMPILED / NOT RUN** status: no Lean command, build,
ordinary-decide evaluation, kernel check, or emitted-axiom check was run.

The exact endpoint is
`N13ConstructedMappedSpecialFamily.mappedSpecialFamily : MappedSpecialFamily Kernel`,
where `Kernel` is definitionally the actual constructed `specialization.ker`.
It has no mapped-special, near-base, kernel-separatedness, or K2 premise.

No remote write or producer-file edit was made by the auditor. Source retrieval
used read-only GitHub actions for exact pinned Mathlib files. The newly arriving
`N13CenteredHermiteFirstOrder.lean` is outside this review; K2 remains separate.

## Frozen/revised candidate identities

All files are under `FLT/Assumptions/MazurProof/` in the candidate directory.

- `N13KernelBaseDivisor.lean`: 3,542 bytes, 88 lines,
  `7cb59949e46450341438fec3caa7b1d3981e0320f80bb051a77a5acea35cbd1f`
- `N13KernelInfinityMultiplicity.lean`: 6,426 bytes, 139 lines,
  `fd68334a68946192e6e7a9e3495ffd53c6bc66e46c542aa58e330722bb66e5fd`
- `N13KernelGraphContraction.lean`: 4,715 bytes, 98 lines,
  `c98542116f277997576f09dbf007685d45c1cb80c21e641ec474d60aedab2455`
- `N13KernelBasePic.lean`: 6,051 bytes, 134 lines,
  `2237b399608bcfc2e5a43b71afa28caaa05ed4a71a53679ecaab02026644521b`
- `N13ConstructedMappedSpecialFamily.lean`: 2,497 bytes, 54 lines,
  `f20ca03307778ebfae0969a9868947c41a774308f98de88406b653bc86bc1ef0`

No `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` token occurs
outside comments in these five modules. Absence of these tokens is not an
emitted-axiom claim for their dependencies.

## Source/API provenance

- Repository source pin: `887d29cd9eb9b60a6e5ec438ff919a74ccda41e5`
- Mathlib pin: `96fd0fff3b8837985ae21dd02e712cb5df72ec05`
- Supplied Lean toolchain: `v4.31.0-rc2`; no executable was invoked
- Existing 41-module constructed-chooser dependency packet: delivered at
  `2561ea7c66fb30c15416934a7ae513127cb387e1`, still uncompiled dependencies
  for purposes of this source review

Independently recomputed byte counts and SHA-256 identities match all 107
original source captures, all 41 Lean dependency candidates, all five kernel
input captures, and all nine extra kernel captures. Recorded Git blob identities
also match wherever supplied. The audit deliberately checks the 41 scientific
Lean artifacts rather than treating later mutable communications as frozen
source; two appended communication documents differ from an earlier delivery
manifest, while all 41 Lean files match it.

See `SOURCE_AND_CANDIDATE_IDENTITIES.json`. `MATHLIB_SOURCE_IDENTITIES.json`
records six independently fetched exact-pin source files with provider/local
Git blob checks, byte counts, and SHA-256. No current-main API was substituted.

## Concrete correction found and rechecked

The original `chosen_translated_code` proof ended with
`sub_right_injective ht` for an equality of shape `A - 16 = 8 - 16`.
Pinned Mathlib `Algebra/Group/Basic.lean:688–699` gives the additive counterparts:

```
sub_left_injective  : Function.Injective (fun a => a - b)
sub_right_injective : Function.Injective (fun a => b - a)
```

The author changed the last step to `sub_left_injective ht`. This is the exact
required cancellation; the repository's existing
`N13TwoAdicAbelChartPic.centeredPic_injective` uses the same API shape.
Original BaseDivisor hash was
`de7b8d3ed7384e9718448550a4da7bf3179c36de8526534f502fafee01710f94`;
the corrected hash is listed above. The other four K1 files are unchanged.

## 1. Actual kernel, C+B, code8, and literal divisor equality

`Kernel := N13ConstructedSpecialization.specialization.ker` uses the actual
additive specialization built from the calibrated chooser. It is not an
arbitrary subgroup or a subgroup assumed to have the desired representatives.

The translated divisor uses the correct two cusps:

- `zeroPlus` is C, good special coordinates `(0,0)`, code1
- `negOneMinus` is B, good special coordinates `(1,0)`, code7
- Their divisor has code8
- `negOnePlus` would instead be the other sheet A and give code13; that
  inverse-infinity datum is not substituted here

`chosen_zero_specialClass`, passed through `picCode`, identifies the chosen
zero divisor's code with the doubled positive anchor, code16. Cusp compatibility
therefore gives `specialization baseTranslate = 8 - 16`. For `z` in the actual
kernel, additivity and `z.property` force the translated chosen divisor's code
to be8 after cancellation.

The literal-divisor step is valid, not just a class equality: the exact source
`divisorCode_eq_iff_abelRel` returns either divisor equality or two canonical
divisors. Every canonical divisor has code0. Code8 is nonzero in ZMod19, so the
canonical alternative is excluded. `IsCanonical` is membership in the range
of `canonicalDivisor`, hence its witness equality is `canonicalDivisor b = D`;
the candidate's `rw [← hb]` has the correct orientation.

## 2. Infinity multiplicities from actual branch constants

The proof does not read geometric multiplicities off an unrelated integer
field. It uses the actual integral infinity ideal and both actual generic
branch expansions carried by `HasInfinityMultiplicities`.

The plus/minus constant-reduction identities follow from the existing
rank-two normal forms, coefficientwise reduction, and exact branch constants:

- integral plus root constant0, special plus root constant0
- integral minus root constant−1, special minus root constant1 in characteristic2

The reduction coefficient theorems in `N13IntegralInfinityReduction` are tagged
`[simp]`, and the cited `reducePoly`, polynomial/power-series coefficient maps,
and `ZMod.neg_eq_self_mod_two` match the proposed simplification.

For the literal special divisor C+B, the C factor on the infinity chart is
the unit ideal and the B factor is `(t-1,v)`. Therefore `t-1` belongs to the
reduced infinity ideal. If a generic branch ideal were `(X^n)` with `n>0`, every
element of the integral ideal would have generic constant coefficient zero.
Injectivity of `ℤ₂ → ℚ₂` then forces its integral constant to vanish, so the
entire reduced ideal lies in the kernel of the special branch constant map.
But the constant of `t-1` is−1, a contradiction. This argument applies to both
branches and proves both actual multiplicities are zero.

Pinned APIs checked:

- `PowerSeries.X_pow_dvd_iff`, `PowerSeries/Basic.lean:490–493`, gives all
  coefficients below n equal to zero, including coefficient0 when n>0
- `IsFractionRing.injective`, `Localization/FractionRing.lean:137–138`, is
  injectivity of the actual algebraMap
- The actual source `powerMap` is coefficientwise map of the actual `coeffMap`

The `Certified D` witness supplies effective-chamber inequalities and the
actual multiplicities of that same semirepresentative E. Its two cast
identities yield `E.nInf = -1` and `E.u.natDegree = 2` without truncation.
Thus the actual effective raw mark is−2 before balancing.

## 3. Literal affine graph and saturated descent

The affine ideals of C and B are `(X,Y)` and `(X-1,Y)` over F2. Their horizontal
polynomials are coprime, with Bezout coefficients1 and−1. The exact
`graphIdeal_mul_of_coprime` API therefore identifies their product with
`(X(X-1),Y) = (X²+X,Y)`, which is the actual `specialIdeal` required by the
existing adapter.

The saturation step retains the necessary hypothesis
`AffineVerticallySaturated D.charts` supplied by `choose_certified`. It does
not claim contraction/extension equality for an arbitrary integral lattice.
Pinned `IsLocalization.algebraMap_mem_map_algebraMap_iff` takes the vertical
multiplicative set first and returns precisely `∃ q ∈ M, q*a ∈ I`.
The source defines M as the image of nonzero integral scalars, so a witness
q can be pulled back to a nonzero scalar r and cancelled by saturation.
The reverse containment is ordinary `Ideal.mem_map_of_mem`.

The same `genericRaw` equality projects to equality of ideal units, then of
fractional ideals. `coe_genericIdealUnit` and `coe_mumfordIdealUnit` expose the
literal ideals, and `FractionalIdeal.coeIdeal_injective` gives the affine ideal
equality. No choice of a different spread or unstated normal-form coherence is
used. Combining this exact contraction with `D.special_affine` and the literal
special-divisor theorem proves the required mapped contraction equation.

## 4. Both +1 twists and the actual basePic

The existing definitions are crucial:

- `semiMumfordRaw E` has mark `E.nInf - 1`
- `balancedGraph E hd` keeps the same u,v and sets nInf0, so its raw mark is−1
- The certified finite effective graph has nInf−1 and raw mark−2

Consequently `balancedGraph_class` multiplies the actual raw pair by
`(1, ofAdd 1)` and adds exactly `infinityShift` in the quotient. Its first
component is unchanged because the ideal depends on u,v, not the marking.

For the actual adapter basePair, the smooth good-model points are `(0,0)` and
`(-1,0)`. Completing the square gives sextic ordinates1 and−1, so these are
exactly C and B. The base u is `X(X+1)`. Its completed graph is
`h(X)=X³+X+1`; modulo u this is `2X+1`, since

```
h(X) - (2X+1) = X³-X = X(X+1)(X-1)
```

`basePair_graphIdeal` uses the exact existing reduced-completed-graph transport
and this divisibility. The secant through `(0,1)` and `(-1,-1)` is exactly
`2X+1`. Existing `pointIdeal_mul_eq_secantGraph` therefore identifies the
product of the two actual mapped cusp ideals with the actual basePair ideal.

Each mapped affine cusp has nInf0/raw mark−1. Their raw product has mark−2;
again multiplication by `(1, ofAdd 1)` gives the actual basePair's mark−1.
Hence `basePic = picMapRatToQ₂ baseTranslate + infinityShift`. The proof uses
the correct rational-to-Q2 `mapCoeffs` fields and the exact
`picMapRatToQ₂_classOf` theorem, with its orientation reversed for cusp classes.
It does not replace basePic with an unbalanced sum or silently drop the shift.

## 5. Endpoint assembly and noncircularity

For each actual kernel element z, choose the already constructed certified
datum for `z + baseTranslate`. Its finite semirepresentative E supplies the
balanced Mumford graph. The two required fields are then:

1. class equality: chooser generic equality plus the finite-graph +1 shift,
   followed by the independently proved basePic equality and associativity
2. mapped-contraction equality: the same datum's saturation, raw graph equality,
   and literal special divisor C+B

The resulting `Nonempty (MappedSpecialRepresentative (subgroupToPic Kernel z))`
is chosen pointwise with `Classical.choice`, producing exactly the existing
`MappedSpecialFamily Kernel`. Its `toNearBaseFamily` and `realize` methods are
the existing Hensel recovery consumers. No additional global choice coherence
is required for K1, and none is asserted for the distinct K2 first-jet problem.

No theorem in the five-file chain derives separatedness or final rational-point
classification without K2. The imported adapter's separate
`FirstJetDoublingCompatibility` premise remains intact. The base chooser and
41 dependent candidates must still pass the lead's compilation and axiom
checks before this source-level construction can be reported as accepted.
