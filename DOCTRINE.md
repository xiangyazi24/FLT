# Automode Doctrine: Complete Mazur `|E(ℚ)ₜₒᵣₛ| ≤ 16`

## Goal

Replace every custom axiom reachable from `MazurProof.mazur_torsion_bound` so
its rebuilt `#print axioms` output contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Source-rebuilt state (2026-08-12)

The endpoint has no reachable `sorryAx` and depends on exactly four custom
axioms:

1. `CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
2. `CyclicExclusion25.no_explicit_order25_obstruction`
3. `CyclicExclusion49.no_raw_order49_tate_obstruction`
4. `no_prime_order_ge_23`

Orders 17 and 19 are now proved by direct quotient and rational-point
classifications.  The Vélu two-isogeny quotient for orders 20 and 24 is also
proved.  The two tracked `sorry`s in `KubertBridgeN16.lean` are outside the
endpoint import closure.

## Ranked avenues

### (a) N25 finite-field and Jacobian reduction route

Current active route.  The primitive Tate obstruction already maps to the
checked canonical genus-four quotient and avoids all five rational cusps.
The complete executable field tables and projective counts over
`F_2,F_4,F_8,F_16` are certified as `5,5,20,29`.  Four chartwise Bézout
identities exclude the explicit complete-intersection singularity predicate
over every characteristic-two field.  Newton's identities and genus-four
reciprocity give the exact candidate Weil numerator, with value `71` at one.
At three, the semantic `F₃,F₉,F₂₇,F₈₁` point types have certified counts
`5,5,20,89`.  Locally finite closed points now construct finite
fixed-degree effective divisors, a marked-divisor equivalence proves the
Euler recurrence, and middle-degree Riemann--Roch reduces the local order
`71` to geometric Picard data.  Arithmetic Frobenius on the canonical curve
over `F_(3^12)` and fixed-subfield descent now prove all four required
point-orbit classifications through degree four.  This finite common field
is used only for those degrees, not as a model of closed points of arbitrary
degree.  In characteristic two, the full degreewise carrier is now built
instead from exact-period Frobenius orbits over `F_(2^d)` for every positive
degree `d`.  Coherent field embeddings preserve least periods and descend to
orbit-class equivalences, so this full grading agrees structurally with the
former common-field grading through degrees one to four and inherits the
verified semantic point-count bridge.  The binary class-number consumer now
runs on this full grading.  The remaining local seam is therefore to identify
these orbit-defined closed points with scheme points, construct the global
principal-divisor/Picard and complete-linear-system interfaces, prove the
geometric Riemann--Roch input, and build the analogous full carrier in
characteristic three before obtaining both local Picard cardinalities.
The global seam needs rational rank zero and two good reductions: reduction
at two alone does not exclude two-primary torsion.
The leading candidates use either the degree-two map from `X_1(25)` or its
level-25 newform factor.  The corrected primary source has now been verified:
`J_1(25)(Q)` has rank zero and is cyclic of order `227555`; the exact
four-conjugate newform polynomial at three is also kernel-checked and has
value `71` at one.  The pure two-prime cardinal-divisibility endgame is proved
as well, including the kernel-range formula that derives each local bound
from a finite reduction map with primary kernel.  These bounds also prove
that doubling is injective; consequently a degree-two Jacobian pullback is
injective once its norm-pullback composite is identified with `[2]`.  Neither
route is counted at the endpoint until the required specialization,
closed-point/Picard, pullback/norm, and Abel--Jacobi infrastructure is
formalized.  Closing these seams forces every rational
canonical point to be a cusp, contradicting the proved noncuspidality of the
primitive Tate image.

The characteristic-two function-field foundation is now explicit.  The
`w = 1` canonical complete intersection projects to a monic plane sextic
over `F₂[z]`; specialization at `z = 1` and a certified quartic
irreducibility argument prove that its coordinate ring is a domain.  The
division-free elimination identities construct both directions of the
projection after inverting `D = xz + x + z`, with inverse coordinate
`y = (x²+xz+z²+z)/D`.  The resulting equivalence
`P[D⁻¹] ≃ C_w[D⁻¹]` is source-built and clean-3 audited.

The whole canonical chart is now proved integral.  In the separated
presentation `F₂[z][x]`, the denominator `D=(z+1)x+z` is prime and the
numerator `N=x²+zx+z²+z` is nonzero modulo `(D)`.  A reusable elementary
quotient-swap lemma turns regularity of `N` modulo `D` into regularity of
`D` modulo the monic quadric and cubic equations.  Explicit variable,
quotient, and tower equivalences transport this statement back to the
canonical `w=1` chart.  Thus localization at `D` is injective; the already
integral plane principal open proves `IsDomain C_w`.  This removes the
possible hidden `D`-torsion or boundary component and makes the explicit
principal-open equivalence a sound foundation for the common function
field.

The affine Dedekind-domain divisor layer is now explicit: fractional ideals
map to finitely supported height-one-prime divisors, the map is multiplicative
and injective on nonzero ideals, and nonzero rational functions define an
additive principal-divisor map into this affine carrier.  Canonical normalized
points now evaluate on their pivot chart quotient; evaluation is Frobenius
equivariant, its kernel is Frobenius invariant, and exact-period orbit classes
descend to primes in the product of the four chart rings.  The kernel quotient
is canonically the finite coordinate-generated subring of the ambient finite
field and hence is itself a field.  The coordinate field degree is now proved
equal to the point's exact Frobenius period, so every full degree-`d` closed
point has residue cardinality exactly `2^d`, and its descended product-ring
prime is maximal.  This is not yet the projective curve divisor theory:
nonzeroness/height one of the selected chart kernel, chart overlap
identification, points at infinity, and the projective product formula remain.
Mathlib currently has no turnkey
curve-divisor/product-formula API, so the comparison must be built from the
available commutative-algebra interfaces.

The ambient Koszul-to-curve seam is closed.  Vertical-open Beck--Chevalley
base change now permits arbitrary horizontal morphisms, so it applies to the
closed curve immersion.  On each standard chart the explicit equation
quotient sheaf is identified with the direct image of the affine curve chart,
and the quotient projection is identified with the structure-module map.
Affine Koszul exactness therefore gives exactness of the geometric right
complex locally; restriction--stalk descent gives global exactness.  The
categorical Koszul quotient and `i_* O_C` are consequently two cokernels of
the same differential, and the canonical comparison has a verified `IsIso`
instance.

This result is infrastructure, not a discharge of the N25 endpoint axiom.
The ambient Koszul construction has also been shifted uniformly: for every
integer debt `d`, the global sequence
`O(-(d+5)) → O(-(d+2)) ⊕ O(-(d+3)) → O(-d) → i_* i^* O(-d)`
is now verified exact.  Pullback Beck--Chevalley is derived structurally by
iterated mates, and the adjunction unit is compared chartwise with the affine
closed-immersion structure map.  Restriction--stalk descent and cokernel
uniqueness then identify the former categorical quotient `Q_d` with
`i_* i^* O(-d)` for every `d`.  In particular `Q_{-1}` is the actual
hyperplane twist on the curve.  This closes the shifted terminal comparison;
it does not yet reduce the four endpoint axioms.

The local restriction of that ambient twist is now identified with the
curve-side Čech model.  The graded quotient maps every degree-one coordinate
ratio, including arbitrary integral powers, to the corresponding curve
ratio.  For an arbitrary affine map `Spec S → Spec R`, the canonical
comparison `g^* O_{Spec R} ≅ O_{Spec S}` is proved natural with respect to
rank-one unit scalars.  Consequently the ambient and curve overlap
transitions commute after pullback, and every standard chart has a canonical
isomorphism from the actual restricted ambient twist to the local curve
twist.  These chart maps now lift through the existing Čech equalizer.  Their
two overlap projections agree by the verified Beck--Chevalley unit laws,
including the congruence between the named right restriction and its
composite presentation.  The lift is an isomorphism because its restriction
to every standard chart is an isomorphism, checked on stalks.  Thus the actual
pullback of the ambient hyperplane twist is globally identified with the
effective curve-side twist; `[MZ-N25-CECH-COMPARE]` is closed without changing
the four endpoint axioms.

The transition-theoretic part of adjunction is now global.  The composite of
the ambient canonical exponent `4` with the inverse conormal-determinant
exponent `-5` defines its own Čech equalizer.  Its first gluing arrow is proved
equal to the exponent `-1` arrow, so this transition-defined line is globally
isomorphic both to the effective `O_C(1)` twist and to the pullback of the
ambient hyperplane twist.  This is `[MZ-N25-ADJUNCTION-DESCENT]`; it does not
claim that a dualizing sheaf has been constructed.  The remaining adjunction
seam is to construct the canonical/dualizing object and prove that its local
trivializations carry exactly this verified composite transition.

The first half of that remaining seam is now concrete.  On every ordinary
affine curve chart, the two equation gradients have a unimodular cross product:
the three components are exactly the selected Jacobian minors, up to the
alternating middle sign, and the existing smoothness certificate makes them
generate the unit ideal.  Dot product with this cross product therefore has
kernel equal to the span of the two relation gradients.  Comparing that
functional with the presentation cotangent sequence constructs an explicit
linear equivalence `Ω¹_{B/k} ≃ B` and a singleton basis for the actual Kähler
differentials.  This is `[MZ-N25-AFFINE-CANONICAL]`.  Those equivalences have
now also been transported across the proved algebra equivalences to the actual
degree-zero homogeneous coordinate rings of all four projective charts.  The
transported coordinate functionals are proved to be exactly the affine
Jacobian residues followed by the chart equivalences; this is
`[MZ-N25-CHART-CANONICAL]`.  Both chart coordinates have now been localized
to every ordered overlap through the actual homogeneous chart projections.
Their change of basis is an explicit unit
`coordinateOverlapResidueUnit`; this is
`[MZ-N25-OVERLAP-LOCALIZATION]`.  The affine localization parameter is now
identified with the homogeneous coordinate ratio, and its residue is the
corresponding localized ambient Jacobian minor.  Each ambient minor is proved
homogeneous of degree three; complementary chart omissions select the same
minor, so its two chart expressions differ by the cube of the coordinate
ratio.  The Leibniz identity for inverse ratios then reduces this cube to the
single ratio factor predicted by adjunction on the differential of the chart
ratio.  The equality now extends to all three affine-coordinate differentials:
for the two non-ratio coordinates, the weighted Euler minor syzygy supplies
the missing relation without cancelling any individual minor.  A Bezout
combination of the three differentials has first residue one, and its second
residue is the inverse coordinate ratio.  The full transition unit is
therefore the established exponent `-1` coordinate-ratio unit on every
ordered overlap, including self-overlaps.  This closes
`[MZ-N25-RESIDUE-UNIT]`.  Affine tilde has now been applied to the actual
Kähler modules on every chart and ordered overlap.  The residue equivalences
give actual module-sheaf trivializations, and their ordered-overlap change is
proved equal, as a sheaf isomorphism, to the existing exponent `-1` twist
transition.  Thus the local differential and effective `O_C(1)` descent data
have a fixed common orientation; this is `[MZ-N25-AFFINE-TILDE]`.

The ordered-overlap restriction maps are now canonical rather than
frame-defined.  Restriction of affine tilde along each principal open is
constructed from the localized top-section universal property and formally
étale base change.  Its action on localization generators is the functorial
map on Kähler differentials.  A separate calculation shows that these
canonical isomorphisms equal the residue-frame presentations on both overlap
legs.  Consequently the actual Kähler Čech arrows use canonical restriction
maps, while the residue frames only prove their comparison with the exponent
`-1` twist diagram.  The resulting Čech equalizer is globally isomorphic to
the effective `O_C(1)` twist and the pulled-back ambient hyperplane twist;
this is `[MZ-N25-CANONICAL-CECH]`.  This does not yet identify the equalizer
with the sheafification of the scheme-relative Kähler presheaf or with a
dualizing sheaf.

The next ranked canonical-geometry attacks are:

1. use the completed same-site relative Kähler comparison in divisor theory.
   The constant-base
   morphism, its objectwise relative differential presheaf, its associated
   module sheaf, and the sheafification unit are now explicit.  On every
   standard chart the transported base map is proved to be the canonical
   binary-field algebra map, and both canonical overlap restrictions are
   proved to carry universal differentials to universal differentials.
   Generic product and equalizer constructors now assemble any compatible
   family of chart-valued same-site derivations into a derivation valued in
   the actual canonical Kähler Čech equalizer.  The comparison is transported
   through the non-definitional product and equalizer preservation
   isomorphisms of the sheaf-forgetful functor, and both projection formulas
   are proved.  A generic affine construction now extends the universal
   Kähler derivation from principal opens to the full small Zariski site and
   packages precomposition along a commutative square of ring maps.  It gives
   all four pushed-forward chart derivations and, independently, the sixteen
   direct ordered-overlap derivations.  The sectionwise formula for
   `pushforwardRestrictionHom` is now proved for arbitrary named composites:
   extension by zero first restricts sections, applies the coefficient map,
   and transports across the chosen equality of composite immersions.  A
   generic theorem proves that a
   full-site affine derivation is determined by its top component, using
   localization extensionality on basic opens and sheaf locality.  Both chart
   derivations have now been transported through their open-immersion section
   isomorphisms and canonical Kähler base changes.  Localization extensionality
   identifies both transported derivations with the direct overlap derivation
   on the full site, including the dependent transport attached to the named
   right composite.  Hence the four chart derivations satisfy the two Čech
   arrows, descend to the global Kähler equalizer, and transpose through the
   universal and sheafification adjunctions to a canonical comparison map.
   Its composite with every Čech chart projection is the corresponding
   universal affine chart comparison.  Literal Čech evaluation is now proved
   equal to `globalKaehlerDifferentialLocalIso`, so restriction of the global
   comparison is equivalent to the single chart-local comparison.  On an
   arbitrary affine spectrum, the objectwise relative-differential comparison
   with tilde is explicitly identified on every principal open; local
   injectivity and surjectivity then prove that its sheafification is an
   isomorphism.  For the N25 charts, the adjunct of the named local comparison
   is proved to be exactly the universal morphism represented by the extended
   affine derivation.  The global sheafification's universal derivation has
   now also been transported through each chart's open-immersion section
   isomorphism, and its universal transpose defines a morphism from the affine
   objectwise relative differential presheaf to the restricted global sheaf;
   its formula on universal differentials is proved.  Section-ring transport
   is bijective on every open, and the restricted sheafification unit is
   locally injective and locally surjective.  Sheafification uniqueness now
   gives an explicit isomorphism between the restricted global sheaf and the
   affine sheafification on every chart.  The canonical local comparison is
   proved equal to this isomorphism followed by the affine tilde comparison,
   so all four local comparisons are isomorphisms.  The open-cover criterion
   then proves that `canonicalRelativeDifferentialsToGlobalKaehler` is an
   isomorphism.  Composing with the existing Čech-to-twist isomorphism gives
   the named `canonicalRelativeDifferentialsIsoCurvePullback`, identifying the
   scheme-relative differential sheaf with the effective curve hyperplane
   twist and closing `[MZ-N25-RELATIVE-DIFFERENTIAL-GLOBAL]`.
   It does not construct a dualizing sheaf or discharge the N25 endpoint.
   The line-bundle identification is now consumed by projectivization-based
   complete-linear-system interfaces, but their geometric section-space
   realizations remain to be supplied;
2. extend the new affine Dedekind principal-divisor map to the projective
   curve: identify chart height-one primes with the full degreewise
   Frobenius closed points, add the missing points at infinity, prove the
   product formula/degree-zero theorem, and feed that subgroup into the
   full-grading Picard and middle-degree Riemann--Roch consumer.

### (b) N13 concrete specialization and separatedness — ACTIVE

**Status:** the remaining `n13_class_eq_iff` in `N13DischargeWiring.lean`
is false as typed.  `N13SpreadLineCounterexample` constructs two spread lines
with the same generic class modulo `⊥` and distinct special classes.  The
counterexample uses the positive-infinity line and the negative-infinity line
whose independent generic orientation is reset to zero; both have saturated
affine geometry, so affine saturation cannot repair the statement.
`TrivialKernelFamily` still proves `CanonicalMappedSpecialFamily` and
`NSeparated ⊥ 2` without `class_eq_iff`, and first-jet doubling compatibility
is also proved without it.

**Attack plan:**
1. Remove the impossible all-`SpreadLine` interface from the endpoint route.
   Either restrict it to a coherent subtype tying `infinityOrder` to the
   actual infinity-chart factor, or use only the canonical `exactSpreadLine`
   chooser.
2. Prove specialization compatibility for the coherent/canonical carrier;
   affine contraction alone is insufficient because the two infinity sheets
   have the same affine ideal.
3. Prove the resulting specialization map injective, using its certified
   19-element source and target only after surjectivity or a concrete
   representative table is connected.
4. Feed that injectivity into the existing pointwise-reflection endpoint and
   the already proved trivial-kernel separatedness.

**Key infrastructure gap:** a specialization carrier whose generic infinity
orientation is realized by its actual two-chart geometry.

### (c) N49 explicit rational-point obstruction

The front-end Tate reduction is proved.  The terminal condition is the honest
rational-point classification of the relevant modular quotient plus a
universal Tate-to-modular map excluding its cusps; fixed-fibre computations
alone are insufficient.

### (d) Uniform primes `p ≥ 23`

Build the formal-immersion/Eisenstein-ideal argument only from explicit
source-faithful interfaces.  This remains the broadest single axiom.

## Fallbacks and terminal conditions

- If an avenue stalls, change the mathematical attack vector while retaining
  the same theorem; do not weaken the goal or replace it by a new axiom.
- Every banked node must compile in scope, pass the bypass scan, and have a
  clean-3 axiom audit.
- The run terminates only when all four remaining boxes in
  `MAZUR_CHECKLIST.md` are discharged and the rebuilt endpoint axiom audit is
  clean-3.
