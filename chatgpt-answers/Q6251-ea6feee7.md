ANSWER Q6251 ea6feee7

## Source-state qualification

I cannot honestly certify repository-local declarations at the requested SHA b240303dc824bf0b3291a8d954ecc9c4cdcfbb9f from the connected GitHub source: that commit is not resolvable in the connected xiangyazi24/FLT repository (nor in the public ImperialCollegeLondon/FLT endpoint available to the connector). The connected ai-scratch branch currently resolves to 69ef7a53b6027e9b6f6ce84e98bbc2a962de193f (2026-08-21). In that connected snapshot, RationalPointsN25QuotientTwoRelativeDifferentials.lean and the declaration canonicalRelativeDifferentialsIsoCurvePullback are not present. I therefore treat the stated local theorem

```javascript
canonicalRelativeDifferentialsIsoCurvePullback
```

as a newer local premise, not as a connector-certified declaration, and audit the exact downstream APIs against the newest connected FLT source plus its pinned Mathlib.

The connected branch pins Mathlib to

```plain text
96fd0fff3b8837985ae21dd02e712cb5df72ec05
```

(lake-manifest.json; Lean input revision is in the 4.31.0-rc2 line). All declarations below marked PINNED: yes were located at that Mathlib SHA or in the connected FLT source. Declarations marked current only are useful reference implementations but are not available at this pin.

## Bottom line

After the local isomorphism

```javascript
Ω_(C/F₂) ≅ curvePullbackTwist (-1)
```

the next useful bridge is not a general Cartier-divisor/Picard/Riemann–Roch formalization. At this pin there is no turnkey scheme-level Cartier divisor, zero divisor of a line-bundle section, geometric complete-linear-system, Riemann–Roch, or dualizing-sheaf package that connects to the project’s custom ClosedPointGrading/Divisor layer.

The shortest endpoint-moving route is N25-specific:

1. identify the hyperplane coordinate section with the relevant local section of curvePullbackTwist (-1) using the project’s actual transition convention;

1. identify its quotient in the three relevant curve local rings/stalks with the already-proved local Artin quotients;

1. compute lengths 2, 1, 3 using existing pinned length APIs;

1. package those multiplicities as the already-defined hyperplaneSectionDivisor and hyperplaneSectionClass;

1. use canonicalRelativeDifferentialsIsoCurvePullback to certify that this explicit degree-six class is the class represented by the differential/canonical line bundle.

The genuinely missing seam is therefore a stalk/principal-open quotient comparison, not a missing length theory and not a missing abstract Picard quotient.

## 1. What the project’s divisor/Picard layer actually provides

### FLT/Assumptions/MazurProof/CurveZetaEffectiveDivisors.lean

The project uses a Frobenius-orbit grading, not scheme points:

```javascript
structure ClosedPointGrading where
  Closed : ℕ → Type*
  finite_closed : ∀ d, Finite (Closed d)
  empty_degree_zero : IsEmpty (Closed 0)

abbrev ClosedPointGrading.Atom := Σ d : ℕ, C.Closed d

def atomDegree (x : C.Atom) : ℕ := x.1

abbrev EffDiv := C.Atom →₀ ℕ

def divDegree (D : C.EffDiv) : ℕ :=
  D.sum fun x m => m * C.atomDegree x

def EffDivOfDegree (n : ℕ) :=
  {D : C.EffDiv // C.divDegree D = n}
```

This matters: even a generic scheme-theoretic order-of-vanishing theorem would still need a map from scheme closed points/codimension-one points into these custom atoms.

### FLT/Assumptions/MazurProof/CurveDivisorPicard.lean

Import:

```javascript
import FLT.Assumptions.MazurProof.CurveZetaEffectiveDivisors
```

Core declarations present in the connected source:

```javascript
abbrev Divisor := C.Atom →₀ ℤ

def divisorDegree : C.Divisor →+ ℤ

noncomputable def effectiveToDivisor : C.EffDiv →+ C.Divisor

theorem divisorDegree_effectiveToDivisor (D : C.EffDiv) :
  C.divisorDegree (C.effectiveToDivisor D) = (C.divDegree D : ℤ)

abbrev DivisorClass (Principal : AddSubgroup C.Divisor) :=
  C.Divisor ⧸ Principal

noncomputable def classOf (Principal : AddSubgroup C.Divisor) :
  C.Divisor →+ C.DivisorClass Principal

noncomputable def classDegree
  (Principal : AddSubgroup C.Divisor)
  (hPrincipal : Principal ≤ C.divisorDegree.ker) :
  C.DivisorClass Principal →+ ℤ

def PicDegree
  (Principal : AddSubgroup C.Divisor)
  (hPrincipal : Principal ≤ C.divisorDegree.ker)
  (n : ℤ) :=
  {c : C.DivisorClass Principal //
    C.classDegree Principal hPrincipal c = n}
```

It also contains the purely algebraic residual equivalence

```javascript
residualDegreeFourTwo
  (canonical : C.DivisorClass Principal)
  (hcanonical : C.classDegree Principal hPrincipal canonical = 6) :
  C.PicDegree Principal hPrincipal 4 ≃
    C.PicDegree Principal hPrincipal 2
```

Important limitation: Principal and hPrincipal are inputs. The file does not construct principal divisors from rational functions or prove degree zero of principal divisors for a proper curve. Also, residualDegreeFourTwo accepts any class of degree six; it contains no canonicality theorem.

## 2. Existing API for rational functions and local orders

### 2a. Function field: PINNED: yes

File:

```javascript
Mathlib/AlgebraicGeometry/FunctionField.lean
```

at Mathlib 96fd0fff....

Usable declarations:

```javascript
noncomputable abbrev Scheme.functionField
  [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)

noncomputable abbrev Scheme.germToFunctionField
  [IrreducibleSpace X]
  (U : X.Opens) [Nonempty U] : Γ(X, U) ⟶ X.functionField

theorem Scheme.germToFunctionField_injective
  [IsIntegral X]
  (U : X.Opens) [Nonempty U] :
  Function.Injective (X.germToFunctionField U)

theorem functionField_isFractionRing_of_isAffineOpen
  [IsIntegral X]
  (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
  IsFractionRing Γ(X, U) X.functionField

instance [IsIntegral X] (x : X) :
  IsFractionRing (X.presheaf.stalk x) X.functionField

instance [IsIntegral X] {x : X} :
  IsDomain (X.presheaf.stalk x)
```

This is enough to regard the function field as the fraction field of a local stalk, but not enough by itself to produce a global divisor.

### 2b. Ring-level order of vanishing: PINNED: yes

File:

```javascript
Mathlib/RingTheory/OrderOfVanishing/Basic.lean
```

Usable declarations include:

```javascript
noncomputable def Ring.ord (x : R) : ℕ∞ :=
  Module.length R (R ⧸ Ideal.span {x})

noncomputable def Ring.ordFrac
  [IsNoetherianRing R]
  [Ring.KrullDimLE 1 R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] :
  K →*₀ ℤᵐ⁰

lemma Ring.ordFrac_eq_ord {x : R} (hx : x ≠ 0) : ...
lemma Ring.ordFrac_eq_div (a b : nonZeroDivisors R) : ...
```

Additional ring-level lemmas live in

```javascript
Mathlib/RingTheory/OrderOfVanishing/Noetherian.lean
```

including the additive/multiplicative behavior of Ring.ordFrac under the one-dimensional Noetherian hypotheses.

For Noetherian stalks, pinned Mathlib has

```javascript
Mathlib/AlgebraicGeometry/Noetherian.lean
```

with an instance of the form

```javascript
instance [IsLocallyNoetherian X] {x : X} :
  IsNoetherianRing (X.presheaf.stalk x)
```

### 2c. Scheme-level Scheme.ord: NOT PINNED

A newer Mathlib has

```javascript
Mathlib/AlgebraicGeometry/OrderOfVanishing.lean
```

with a wrapper approximately

```javascript
noncomputable def AlgebraicGeometry.Scheme.ordHom
  [IsIntegral X] [IsLocallyNoetherian X]
  (z : X) (hz : coheight z = 1) :
  X.functionField →*₀ ℤᵐ⁰ :=
  Ring.ordFrac (X.presheaf.stalk z)

noncomputable def Scheme.ord
  (f : X.functionField) (z : X) : ℤ := ...
```

and lemmas such as Scheme.ord_mul, Scheme.ord_of_isUnit, etc. I verified that this file is absent at the pinned SHA 96fd0fff.... It is therefore a reference for a possible backport, not an API available to this campaign without changing dependencies.

### Consequence for (a)

At the pin, the following chain exists:

```plain text
scheme function field
  -> stalk is a fraction-ring source
  -> ring-level ordFrac
```

but the following do not exist as turnkey pinned APIs:

```plain text
rational function
  -> finitely supported divisor on scheme points
  -> custom ClosedPointGrading.Divisor
  -> proof principal divisor has total degree zero on a proper curve.
```

Thus a general Principal : AddSubgroup C.Divisor construction would still require nontrivial global geometry (finite support/product formula plus identification of custom atoms). It is not the shortest N25 bridge.

## 3. Cartier divisors / line-bundle section zero divisors

### Status: no turnkey pinned API found

Searches of the pinned Mathlib source found no usable scheme package named CartierDivisor, no line-bundle-section-to-zero-divisor construction, and no scheme Picard group tied to invertible sheaves.

Mathlib/RingTheory/PicardGroup.lean does exist at the pin, but it is the Picard group of a ring via invertible modules. Its main objects are Module.Invertible and ring-class-group/Picard comparisons such as ClassGroup.equivPic. The file itself records the sheaf connection on Spec R as unfinished/TODO infrastructure. Therefore

```javascript
ClassGroup.equivPic
```

is not a legal replacement for the missing scheme line-bundle/Cartier-divisor bridge here.

### Project-specific substitute already present

The N25 files have explicit gluing data for twisting sheaves. In

```javascript
FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoTwistingSheafGluing.lean
```

there are declarations such as

```javascript
coordinateLocalPushforwardBaseChangeIso
coordinateRestrictLeftIso
coordinateRestrictRightIso
coordinateDescentIso (d : ℤ) (i j : Fin 4)
```

plus overlap/cocycle lemmas. This is much closer to the local theorem canonicalRelativeDifferentialsIsoCurvePullback than the ring Picard API is.

But one sign/convention check is essential: because the local theorem uses curvePullbackTwist (-1), do not infer from the notation alone that the hyperplane coordinate is the desired section. The project transition map for exponent d = -1 must be matched explicitly to the section transition. A convention reversal here would identify the dual line bundle.

## 4. Complete linear systems and Riemann–Roch

### Mathlib: no pinned turnkey Riemann–Roch API found

No usable declaration named RiemannRoch or geometric complete-linear-system construction was found at the pinned Mathlib SHA.

### Repo consumer: CurveZetaMiddleRiemannRoch.lean

Imports:

```javascript
import FLT.Assumptions.MazurProof.CurveZetaClassNumber
import FLT.Assumptions.MazurProof.CurveDivisorPicard
```

The file is an abstract consumer of RR/fibre data, not a proof of it. Its central theorem has the shape

```javascript
theorem effective_card_middle_degree
  {PicHigh PicLow EffectiveHigh EffectiveLow : Type*}
  [Fintype PicHigh] [Finite EffectiveHigh] [Finite EffectiveLow]
  (classHigh : EffectiveHigh → PicHigh)
  (classLow : EffectiveLow → PicLow)
  (residual : PicHigh ≃ PicLow)
  (rankHigh : PicHigh → ℕ)
  (rankLow : PicLow → ℕ)
  (q : ℕ)
  (hHighFiber : ∀ c,
    Nat.card {D : EffectiveHigh // classHigh D = c} =
      linearSystemCard q (rankHigh c))
  (hLowFiber : ∀ c,
    Nat.card {D : EffectiveLow // classLow D = c} =
      linearSystemCard q (rankLow c))
  (hRR : ∀ c,
    rankHigh c = rankLow (residual c) + 1) :
  Nat.card EffectiveHigh = Fintype.card PicHigh + q * Nat.card EffectiveLow
```

The concrete wrapper

```javascript
effective_card_genus_four_divisorPicard
```

similarly takes as hypotheses:

- the degree-six class;

- rank functions in degrees four and two;

- complete-linear-system fibre cardinality formulas;

- the Riemann–Roch rank relation.

So this file cannot be used to manufacture those hypotheses.

CurveZetaClassNumber.lean likewise supplies combinatorial lemmas such as

```javascript
def linearSystemCard (q r : ℕ) : ℕ := ...
linearSystemCard_recurrence
card_eq_card_mul_fiber
rr_fiber_numeratorCoeff_eq_zero
rr_fiber_eval
```

but its RR-shaped statements consume an RR/fibre hypothesis; they are not geometric RR.

### Consequence for (c)

There is no shortcut from canonicalRelativeDifferentialsIsoCurvePullback directly to effective_card_genus_four_divisorPicard. The missing complete-linear-system/rank semantics remain a later layer. First certify the actual canonical class in the project’s divisor quotient.

## 5. Dualizing/canonical sheaf

### Pinned Mathlib status

No usable pinned declaration/package for a scheme canonicalSheaf, dualizingSheaf, complete-intersection adjunction, or a canonical-divisor constructor was found.

### Project status

FLT/Assumptions/MazurProof/RationalPointsN25QuotientTwoCanonicalDivisor.lean explicitly constructs a degree-six hyperplane candidate but deliberately stops before asserting canonicality. The source notes that the missing classical geometry is adjunction for the smooth (2,3) complete intersection.

The important local development you report changes this dependency: if

```javascript
canonicalRelativeDifferentialsIsoCurvePullback
```

really gives the scheme-relative differential sheaf globally and then identifies it with curvePullbackTwist (-1), a separate full complete-intersection adjunction theorem may no longer be the shortest route. What is still missing is the semantic bridge

```plain text
this invertible/differential sheaf
  -> this explicit divisor class in the custom DivisorClass quotient.
```

That is strictly smaller than building a general dualizing-sheaf theory.

## 6. Existing N25 hyperplane certificate to reuse

RationalPointsN25QuotientTwoCanonicalDivisor.lean already defines the three degree-one atoms and

```javascript
noncomputable def hyperplaneSectionDivisor :
  frobeniusOrbitGrading25TwoLE4.EffDiv :=
  Finsupp.single (degreeOneAtom hyperplanePointW) 2 +
  Finsupp.single (degreeOneAtom hyperplanePointZ) 1 +
  Finsupp.single (degreeOneAtom hyperplanePointYZ) 3

theorem hyperplaneSectionDivisor_degree :
  frobeniusOrbitGrading25TwoLE4.divDegree
    hyperplaneSectionDivisor = 6

noncomputable def hyperplaneSectionEffectiveDegreeSix :
  frobeniusOrbitGrading25TwoLE4.EffDivOfDegree 6
```

and, for arbitrary Principal and hPrincipal, a class

```javascript
noncomputable def hyperplaneSectionClass ... :
  frobeniusOrbitGrading25TwoLE4.DivisorClass Principal

theorem hyperplaneSectionClass_degree ... :
  frobeniusOrbitGrading25TwoLE4.classDegree
    Principal hPrincipal (hyperplaneSectionClass ...) = 6
```

The coefficients 2,1,3 are not merely guessed: the local-intersection files already prove exact local quotient normal forms.

### RationalPointsN25QuotientTwoHyperplaneArtin.lean

Present declarations include

```javascript
abbrev DoubleArtin :=
  AdjoinRoot ((X : (ZMod 2)[X]) ^ 2)

abbrev TripleArtin :=
  AdjoinRoot ((X : (ZMod 2)[X]) ^ 3)

theorem doubleArtin_finrank :
  Module.finrank (ZMod 2) DoubleArtin = 2

theorem tripleArtin_finrank :
  Module.finrank (ZMod 2) TripleArtin = 3
```

and ideal normal forms reducing the W and YZ local intersections to square/cube nilpotent quotients.

### RationalPointsN25QuotientTwoHyperplaneArtinKernel.lean

This supplies the exact kernel/equivalence layer, including declarations of the form

```javascript
doubleNormalQuotientAlgEquiv
tripleNormalQuotientAlgEquiv
doubleEvaluation_ker
tripleEvaluation_ker
```

### RationalPointsN25QuotientTwoHyperplaneArtinLocal.lean

This already proves localization/quotient equivalences, in particular

```javascript
noncomputable def doubleLocalizedChartQuotientEquiv :
  (Localization.Away wChartDenominator ⧸
    Ideal.map
      (algebraMap BinaryAffinePlane
        (Localization.Away wChartDenominator))
      (Ideal.span {wChartQuadricPolynomial, wChartCubicPolynomial}))
    ≃+* DoubleArtin
```

and the triple analogue. It also proves

```javascript
theorem awayLift_ker ... :
  RingHom.ker (Localization.awayLift f r hr) =
    Ideal.map (algebraMap R (Localization.Away r)) (RingHom.ker f)
```

plus the specialized localized evaluation kernels/surjectivity.

These are exactly the inputs to exploit next.

## 7. Pinned length/quotient APIs: enough to finish multiplicities

### Mathlib/RingTheory/Length.lean — PINNED: yes

Useful exact declarations:

```javascript
theorem Module.length_eq_of_surjective
  {S : Type*} [CommRing S] [Algebra S R] [Module S M]
  [IsScalarTower S R M]
  (h : Function.Surjective (algebraMap S R)) :
  Module.length S M = Module.length R M

lemma Module.length_eq_finrank
  (K M : Type*) [DivisionRing K]
  [AddCommGroup M] [Module K M] [Module.Finite K M] :
  Module.length K M = Module.finrank K M
```

### Mathlib/RingTheory/LocalRing/Length.lean — PINNED: yes

Imports at the pin include Mathlib.RingTheory.Length and the local-ring residue-field infrastructure. The central theorem is exactly

```javascript
theorem IsLocalRing.length_restrictScalars
  (A B M : Type*) ... :
  Module.length A M =
    Module.length B M *
      Module.length (ResidueField A) (ResidueField B)
```

under [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M].

Thus there is no reason to invent a new general theorem saying “intersection multiplicity equals vector-space dimension.” The pinned library already has the length machinery.

### Mathlib/RingTheory/Ideal/Quotient/Operations.lean — PINNED: yes

Useful exact names include

```javascript
RingHom.quotientKerEquivOfSurjective
Ideal.ker_quotient_lift
Ideal.mem_quotient_iff_mem_sup
```

Together with the project’s awayLift_ker, these are sufficient for the quotient/localization algebraic transport.

## 8. Smallest missing theorem-sized commutative-algebra node

The smallest useful compile target, using only objects already present in the connected source, is to package the already-known quotient equivalences as length statements.

Close pseudotype for W:

```javascript
theorem doubleLocalizedChartQuotient_length :
  Module.length
    (Localization.Away wChartDenominator)
    (Localization.Away wChartDenominator ⧸
      Ideal.map
        (algebraMap BinaryAffinePlane
          (Localization.Away wChartDenominator))
        (Ideal.span
          {wChartQuadricPolynomial, wChartCubicPolynomial})) = 2 := by
  -- transport through doubleLocalizedChartQuotientEquiv
  -- reduce self-length of DoubleArtin to F₂-dimension
  -- use doubleArtin_finrank
```

and analogously

```javascript
theorem tripleLocalizedChartQuotient_length :
  Module.length
    (Localization.Away yzChartDenominator)
    (Localization.Away yzChartDenominator ⧸
      Ideal.map
        (algebraMap BinaryAffinePlane
          (Localization.Away yzChartDenominator))
        (Ideal.span
          {yzChartQuadricPolynomial, yzChartCubicPolynomial})) = 3
```

with the exact denominator/ring names adjusted to those already used by the triple localized equivalence.

For the reduced Z point, prove the corresponding local quotient is isomorphic to ZMod 2, yielding length one.

These lemmas should be provable from existing APIs; they are not a new theory. If local-ring/residue-field instances for DoubleArtin/TripleArtin do not synthesize automatically, prove only the tiny concrete instances/facts needed for these two Artin rings rather than generalizing.

### The actual geometric seam after those length lemmas

The theorem that materially connects to the endpoint is the stalk comparison. Since the local-only RelativeDifferentials file is unavailable through the connector, the exact curve-stalk type/name cannot be certified here; the correct shape is:

```javascript
-- close pseudotype; use the project's actual curve/stalk names
noncomputable def wHyperplaneStalkQuotientEquiv :
  ((C.presheaf.stalk pW) ⧸ Ideal.span {x_at_pW}) ≃+* DoubleArtin

noncomputable def yzHyperplaneStalkQuotientEquiv :
  ((C.presheaf.stalk pYZ) ⧸ Ideal.span {x_at_pYZ}) ≃+* TripleArtin

noncomputable def zHyperplaneStalkQuotientEquiv :
  ((C.presheaf.stalk pZ) ⧸ Ideal.span {x_at_pZ}) ≃+* ZMod 2
```

The proof should pass through the already-localized chart quotients and the stalk map; no new divisor abstraction is needed.

Then the local orders are literally lengths by the pinned definition

```javascript
Ring.ord x = Module.length R (R ⧸ Ideal.span {x}).
```

This yields the multiplicity certificate 2,1,3.

## 9. Minimal divisor-class bridge that composes with current ClosedPointGrading/Divisor/PicDegree

Do not introduce a fictitious existing zeroDivisor API. Instead add one N25-specific theorem whose conclusion is already in the project’s concrete divisor language. Close pseudotype:

```javascript
theorem hyperplane_section_orders :
  hyperplaneOrder hyperplanePointW = 2 ∧
  hyperplaneOrder hyperplanePointZ = 1 ∧
  hyperplaneOrder hyperplanePointYZ = 3
```

where hyperplaneOrder is a tiny local helper defined via the relevant stalk quotient length, followed by

```javascript
theorem hyperplane_section_divisor_certificate :
  -- the divisor extracted from these three supported local orders
  hyperplaneDivisor =
    frobeniusOrbitGrading25TwoLE4.effectiveToDivisor
      hyperplaneSectionDivisor
```

If introducing hyperplaneDivisor is undesirable, state the theorem directly as the three coefficient equalities plus vanishing off the three supported atoms. That avoids pretending a general Cartier divisor formalization exists.

Finally, after checking the curvePullbackTwist (-1) transition orientation, add the semantic theorem tying the local-only differential sheaf to the already-existing class:

```javascript
-- close pseudotype: exact sheaf/class names depend on the local b240 source
 theorem canonicalRelativeDifferentials_class_eq_hyperplane
  (Principal : AddSubgroup frobeniusOrbitGrading25TwoLE4.Divisor)
  (hPrincipal : Principal ≤
    frobeniusOrbitGrading25TwoLE4.divisorDegree.ker) :
  classRepresentedBy
      canonicalRelativeDifferentials
      Principal =
    hyperplaneSectionClass Principal hPrincipal
```

Here classRepresentedBy is not claimed to exist. The preferred implementation is N25-specific and should be defined only after the local quotient/transition certificate, so its soundness is transparent. If a general sheaf-to-divisor-class map is later desired, this theorem becomes its first concrete test case.

Once this is proved, the existing

```javascript
hyperplaneSectionClass_degree ... = 6
```

supplies the canonical degree-six input needed downstream without weakening the goal.

## 10. Circularity audit

Reject the following apparent shortcuts:

1. “Degree six implies canonical.” False. hyperplaneSectionClass_degree = 6 proves only degree; there can be many degree-six classes.

1. Use residualDegreeFourTwo to justify canonicality. Circular. That equivalence is algebraic translation by any supplied degree-six class. It does not know the class is canonical.

1. Use effective_card_genus_four_divisorPicard to obtain RR. Circular. The theorem takes the complete-linear-system fibre formulas and RR rank relation as hypotheses.

1. Use CurveZetaClassNumber RR-looking formulas to prove the missing RR input. Same issue: they consume the geometric fibre/RR statement.

1. Use ClassGroup.equivPic as scheme Picard. Invalid at this pin. It is ring Picard/invertible-module infrastructure; the invertible-sheaf connection is not implemented there.

1. Use current Scheme.ord without a dependency change. Invalid for this audit. The scheme wrapper exists in newer Mathlib but not at pinned 96fd0fff....

1. Assume principal divisors have degree zero because local ordFrac exists. Incomplete. One still needs finite support/product formula on the proper curve and the identification with the project’s custom closed-point atoms.

1. Assume curvePullbackTwist (-1) has the standard sign convention. Unsafe. Check the actual coordinateDescentIso (-1) transition against the hyperplane section. Otherwise one can accidentally identify the dual line bundle.

1. Treat the local Ω-isomorphism as automatically a divisor-class equality. There is no existing sheaf-to-custom-DivisorClass API. The local intersection/stalk bridge is exactly what must still be proved.

## 11. Recommended implementation order

1. In or next to RationalPointsN25QuotientTwoHyperplaneArtinLocal.lean, prove the W/YZ localized quotient length lemmas and the reduced Z length-one lemma using doubleLocalizedChartQuotientEquiv, tripleLocalizedChartQuotientEquiv, Module.length_eq_finrank, and the pinned local-ring length API.

1. Prove the three stalk quotient equivalences from the actual curve charts to DoubleArtin, ZMod 2, TripleArtin. Reuse awayLift_ker, RingHom.quotientKerEquivOfSurjective, and the existing localized evaluation kernels instead of normalizing the equations again.

1. Prove a direct N25 hyperplane multiplicity theorem 2,1,3 and identify it with hyperplaneSectionDivisor. This is the first theorem that genuinely connects scheme-local algebra to ClosedPointGrading.

1. In the newer local differential file, prove the section-transition compatibility for curvePullbackTwist (-1) and use canonicalRelativeDifferentialsIsoCurvePullback to identify the explicit hyperplane divisor class as the class of the differential sheaf.

1. Only after that should hyperplaneSectionClass be supplied as the canonical argument to residualDegreeFourTwo / the genus-four RR consumer.

1. The later independent obligations remain: construct/validate the true principal-divisor subgroup and degree-zero theorem; then formalize enough complete-linear-system/rank semantics to discharge hFourFiber, hTwoFiber, and hRR. Those are not eliminated by the differential calculation.

## Verdict

The strongest reusable APIs actually present at the pin are one layer below algebraic-curve divisor geometry: function fields, stalks as fraction-ring sources, one-dimensional ring orders/lengths, localization/quotient algebra, and the project’s explicit twist-gluing and Artin local calculations. There is no hidden pinned Cartier/RR/dualizing API that turns canonicalRelativeDifferentialsIsoCurvePullback directly into a canonical divisor class.

So the next concrete bridge should be the hyperplane section stalk-length certificate and its identification with hyperplaneSectionDivisor, followed immediately by the transition-compatible identification of that class with the local relative-differentials sheaf. This uses the newly proved global Ω-isomorphism, consumes the strongest existing N25 local algebra, and avoids both circular RR reasoning and a large detour through a general-purpose divisor/sheaf formalization.