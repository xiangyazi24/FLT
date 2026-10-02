# General projective product formula: complete source candidate

TASK_ID: FLT-N25-PROJECTIVE-PRODUCT-FORMULA
REVISION: 1
TYPE: RESULT
STATUS: GENERAL-PRODUCT-FORMULA-SOURCE-COMPLETE; NAMED-PRODUCTION-GATE-PENDING
REPO: xiangyazi24/FLT
SOURCE_BRANCH: verify-sorry-restore
SOURCE_COMMIT: 51bbb4f191ad0d3753b87123635c100a638ae580
DISPATCH_COMMIT: 9700ca106515f04411193844fbb347d40d86e481
OUTPUT_BRANCH: research-dot/flt-collaboration-20261001
DEPENDS_ON_RESULTS: 6a4110a03ca7bee2db5fb2e506eb75edd3643ce0,
  b6bae08bf96ddbd1fe1c81db4705ec2524a5ac83,
  fc653e9e48c5e2c66c3d315652b59f2b741bc85c,
  06f02da731842a497c13bf2d4a5b4189b8bea3e9
SUPERSEDES: none; closes the norm/valuation route at source-candidate level

## Exact endpoint

Candidate N25F_ProjectiveProductFormula.lean proves the unweakened statement

    theorem projectivePrincipalDivisor_degree_eq_zero
        (f : Additive (FractionRing N25F_NonBoundaryPrincipalDivisor.W)ˣ) :
      fullClosedPointGrading25Two.divisorDegree (projectivePrincipalDivisor f) = 0

It uses the existing actual divisor, grading, W-chart function field and all
three existing signed boundary coefficients. There is no product-formula,
norm/order compatibility or regularity hypothesis on f. A preceding theorem
handles every nonzero regular W-chart function; an exact fraction argument
extends it to all nonzero functions by the additive divisor-degree homomorphism.

## Five modules, eight public declarations

1. N25F_NormBaseTwist proves the norm transformation under an explicitly
   precomposed base action. Both Algebra structures appear in its statement.
2. N25F_InfinityAffineNormComparison defines the genuine affine field norm
   and proves that the reciprocal norm of the same function is baseInversion.symm
   applied to that affine norm. This is the actual coordinate change.
3. N25F_BaseInversionOrder proves the actual inverse base variable has a
   simple pole at (T), then proves the order of every inverted nonzero base
   polynomial is minus its degree. Its local parameter generates the actual
   maximal ideal, so the proof derives order one from irreducibility; it
   does not assume a valuation normalization.
4. N25F_AffineNormPolynomial identifies the actual affine field norm of a
   regular W-chart function with its existing polynomial-base norm, using
   the exact scalar towers and integral-norm restriction theorem.
5. N25F_ProjectiveProductFormula combines those identities with the delivered
   three-boundary norm-order sum and the accepted affine norm-degree formula.
   For a regular function, boundary degree is minus the polynomial norm degree
   and affine degree is plus that same degree. A nonzero fraction a/b then
   has degree zero by additivity, with nonzero numerator/denominator proved.

No accepted source is modified and no new assumption is added to the actual
endpoint. The private polynomial-at-a-pole argument uses the same already
proved valuation calculation as the accepted polynomial-boundary module.

## Check ledger

All passing files still match their recorded SHA-256 values after the final
generator run. No passing check was repeated merely for delivery.

PASS: exact generic norm-twist declaration, twist-02, exit 0, 30.813 seconds
wrapper elapsed, peak RSS 2,385,308 KiB, standard-three.

PASS: actual fixed-field norm comparison, actual-comparison-01, exit 0,
16.119 seconds, peak RSS 2,514,584 KiB. All three audits standard-three.

PASS: actual binary rational-base inversion/order calculation, base-order-05,
exit 0, 8.566 seconds, peak RSS 2,903,636 KiB. Both audits standard-three.
This check imports the unchanged emitted accepted base-inversion module and
reproduces only the accepted (T) ideal definition and maximality instance.

PASS: actual affine field norm/polynomial norm identification,
affine-polynomial-01, exit 0, 12.244 seconds, peak RSS 2,711,316 KiB,
standard-three. The fixture uses the actual W and fixed-field carrier with
the accepted finite/torsion-free/Dedekind/rank facts exposed as parameters.

PASS: the exact generic fraction-extension proof from the production source,
fraction-extension-02, exit 0, 2.805 seconds, peak RSS 1,925,500 KiB,
standard-three.

PASS: final product-formula assembly on the actual W-chart field carrier,
product-family-01, exit 0, 47.367 seconds, peak RSS 2,961,832 KiB. Both final
theorem audits are exactly [propext, Classical.choice, Quot.sound], with no
warnings or sorryAx. SHA-256:
01912e7af2e2c70de61b7cae859a2813514f5fa431f1cb8068c4858a562097bc.

The final family imports/reproduces the actual norm and base-inversion proofs.
It exposes the named divisor maps, degree split, affine quotient-degree and
norm-dimension facts, and the separately proved boundary norm-order identity
as explicit inputs. The production proof closes them with their exact names.
Thus the checked implication is distinct from the full named FLT endpoint.
Neither the degree-zero target nor an opaque product formula is a family input.

FAILED attempts are recorded separately in validation.json: initial generic
twist over a merely noncommutative target, local quotient-length API attempts,
and the initial fraction-coercion simplification. They are not PASS evidence.
The final base-order proof uses the actual uniformizer/irreducibility theorem;
the final fraction proof explicitly simplifies the unit quotient.

NOT RUN locally: the five full named FLT modules and their eight production
audits. ActualProjectiveProductFormulaCheck.lean lists all eight. The latest
retrieved dispatch remains r34, so the four preceding packets and this packet
remain pending full named acceptance. Family checks do not establish that
the final named endpoint compiles in the full project.

Pins: Lean 4.31.0-rc2 / 5e44d5f905127c78a2da7a015fe7a47840c95eb1;
Mathlib 96fd0fff3b8837985ae21dd02e712cb5df72ec05. One gate acquisition per
check, one CPU/thread, 3,072 MiB Lean cap, 60 active seconds. Wrapper times
may include shared-lock waiting. No broad build was run.

Seven relevant accepted source files were read at the full source pin;
the base inversion, function-field and normalization sources independently
match the local production bytes. Blob identities are attached.

## Scope of the result

This is a complete proof-source candidate for the general projective product
formula with bounded standard-only validation of its pieces and assembly.
Integration and the named kernel/dependency audit remain the lead's gate.
The result does not yet remove the explicit order-25 obstruction axiom,
prove N25, or close Mazur. The last fresh root closure still has no sorryAx
and exactly three custom axioms. The next research step is to identify and
wire the precise downstream degree-zero requirement without changing the
actual divisor or weakening its target.

Manifest: comms/inbox/research-dot-FLT-N25-PROJECTIVE-PRODUCT-FORMULA-r1-manifest.json
