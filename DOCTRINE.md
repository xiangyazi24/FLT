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
degree.  The remaining local seam is therefore to package smooth proper
genus-four special fibres, identify the orbit-defined effective divisors
with their actual geometric divisors, construct the Picard/Riemann--Roch
interfaces, repeat the orbit construction in characteristic two, and obtain
both local Picard cardinalities.
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

The next missing layer is divisor theory on that integral chart: height-one
valuations, principal divisors, and the bridge to class-indexed
Riemann--Roch fibres.  Mathlib currently has no turnkey
curve-divisor/product-formula API, so this must be built from the available
commutative-algebra interfaces.

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

The next ranked canonical-geometry attacks are:

1. build the missing height-one valuation/principal-divisor layer on the
   proved integral chart, including the common-function-field interface
   needed by the class-indexed middle-degree Riemann--Roch consumer;
2. connect the proved conormal basis and shifted ambient Koszul
   resolution to the determinant/adjunction identification
   `ω_C ≅ O_C(1)`.

### (b) N13 concrete specialization and separatedness

The low-degree spread algebra, complete rational Picard spread existence,
vertical saturation of every constructor, certified exact-spread choice, and
the final cusp endgame are proved.  The endpoint now has exactly two explicit
providers: `class_eq_iff` for concrete rational spread lines and first-jet
doubling compatibility for the canonical recovered representatives.

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
