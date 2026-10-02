# Integral boundary factor helper

Checked with the pinned Lean 4.31.0-rc2 / Mathlib environment. Production source:
`N25F_IntegralBoundaryFactor.lean`
SHA-256: `4272b28a1097eabc81fc7b6485baa8b029c7da0e0bca553049f11dcfdf5887a7`

Namespace: `MazurProof.N25F_IntegralBoundaryFactor`.

For `[CommRing A] [CommRing R] [Field K] [Algebra A R] [Algebra A K]
[Algebra R K] [IsScalarTower A R K] [IsFractionRing R K]
[IsIntegrallyClosed R]`, constructs

`integralClosureToRing : integralClosure A K →ₐ[A] R`.

Construction uses `x.property.tower_top (A := R)` and
`IsIntegrallyClosed.isIntegral_iff.mp` to choose a preimage in R, then
`IsFractionRing.injective R K` to prove the algebra-homomorphism laws.
No factorization, localization isomorphism, product formula, finite degree,
or separability hypothesis occurs.

Theorem API:
- `exists_preimage`
- `algebraMap_integralClosureToRing` (simp)
- `toAlgHom_comp_integralClosureToRing`: exact A-AlgHom equality with
  `(integralClosure A K).val`
- `integralClosureToRing_injective`
- `integralClosureToRing_unique`

Validation:
- `check-02.log`: production source elaborates, exit 0, no diagnostics
- `IntegralBoundaryFactorCheck.lean`: byte copy of production source plus
  six `#print axioms` commands
- `axioms.log`: exit 0; all six declarations use only
  `propext`, `Classical.choice`, `Quot.sound`
- Each check used one shared `with-compiler-slot` wrapping one `check-lean`

## Actual reciprocal-base specialization advice

Use the identical reciprocal A-action on K that defines the parent's actual
normalization carrier. With A = Polynomial (ZMod 2), take R successively to
XLocalRing, YZLocalRing, ZLocalRing.

Set local A→R Algebra from `infinityBaseToX/YZ/Z.toRingHom.toAlgebra`; set
local R→K Algebra from `x/yz/zLocalToFraction.toRingHom.toAlgebra`.
The corresponding already-proved fraction-field instances are:
- `N25F_XBoundaryOrder.xLocalToFraction_isFractionRing`
- `N25F_YZLocalFractionEmbedding.yzLocalToFraction_isFractionRing`
- `N25F_ZBoundaryOrder.zLocalToFraction_isFractionRing`

Obtain the compatible tower by `IsScalarTower.of_algebraMap_eq`: on each p,
the desired equality is exactly the symmetric pointwise consequence of
`x/yz/zLocalToFraction_comp_infinityBase`. Infer integrally closedness from
the accepted DVR instances. Apply the helper and its simp factorization.

This advice does not constitute an actual specialized compilation. In the
actual modules, explicitly align Module/SMul instances with the chosen local
Algebra structures before synthesizing the tower, exactly as required by the
existing reciprocal-field action implementation. The helper was checked in
coherent abstract typeclass context and does not introduce an extra
compatibility hypothesis beyond the necessary tower.
