# Mazur torsion bound: exact discharge ledger

Goal: prove `MazurProof.mazur_torsion_bound_ncard` with no custom axioms and
no reachable `sorryAx`.

Last source rebuild and `#print axioms` audit: 2026-08-10.

## Current endpoint

The main numerical theorem and its cyclic-order input compile from source:

- `MazurProof.mazur_cyclic_order_bound_assembled`
- `MazurProof.rational_torsion_finite`
- `MazurProof.mazur_torsion_bound`
- `MazurProof.mazur_torsion_bound_ncard`

Their reachable custom-axiom ledger has exactly four entries:

1. `MazurProof.CyclicExclusion13.C13Sextic_affine_x_is_cuspidal`
   in `CyclicExclusion13.lean`;
2. `MazurProof.CyclicExclusion25.no_explicit_order25_obstruction`
   in `CyclicExclusion25.lean`;
3. `MazurProof.CyclicExclusion49.no_raw_order49_tate_obstruction`
   in `CyclicExclusion49.lean`;
4. `MazurProof.no_prime_order_ge_23`
   in `CyclicOrderAssembly.lean`.

Apart from these four declarations, the audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  It reports no reachable `sorryAx`.

## Newly discharged: orders seventeen and nineteen

`CyclicExclusion17.no_F17_rational_solution` is now a theorem, not an axiom.
The source proof in `TateOrder17Quotient.lean`:

1. normalizes the exact Tate residual `F₁₇(b,c)`;
2. proves all exceptional denominator factors nonzero by explicit polynomial
   identities;
3. maps the normalized point through three checked degree-two formulas to the
   integral `X₀(17)` model;
4. uses the completed four-point classification of
   `X017RationalPoints.lean`;
5. excludes the two remaining affine fibres by a monic quartic with no root
   modulo three and by the nonsquareness of seventeen in `ℚ`.

The theorem
`MazurProof.TateOrder17Quotient.no_F17_rational_solution` depends only on the
three standard logical axioms above.

`CyclicExclusion19.no_F19_rational_solution` is also now a theorem.  The
source proof:

1. completes both rational-flex degree-three isogeny descents on the
   good-reduction model;
2. combines weak three-descent with three-adic formal entry and separatedness
   to prove that every good-model rational point is killed by three;
3. classifies every affine good-model point by its first coordinate;
4. transports the classification through the scaled dual, short, and minimal
   quotient models; and
5. applies the checked algebraic Tate-to-diamond quotient identities to
   exclude every nondegenerate zero of `F₁₉`.

`MazurProof.XDelta19RationalPoints.no_F19_rational_solution` and the public
cyclic exclusion depend only on the three standard logical axioms above.

## Order-twenty-five foundation

The local source tree now contains a checked canonical model for the
genus-four quotient `25.150.4.f.1`.  The N25 files prove:

1. the exact quadric-cubic equations, the five rational cusp vectors, and
   elimination to a plane sextic away from the boundary;
2. an explicit order-five automorphism preserving the model, together with
   its basic homogeneous invariants;
3. exhaustive projective classifications over `𝔽₂` and `𝔽₄`, showing that
   the quadratic extension introduces no new class; and
4. the actual multiples `2P`, `3P`, `4P`, and `7P` of the Tate origin,
   exact order 25 on the primitive locus, and complete Tate
   re-normalizations at `2P` and `7P`, with all denominator factors proved
   nonzero and all five Weierstrass coefficients checked; and
5. Sutherland's raw and optimized affine `X₁(25)` equations, the exact
   `F25=c¹⁰(b-c)¹⁵ Fraw` pullback, the universal raw-to-optimized polynomial
   identity, and the nonvanishing of both optimization denominators on every
   primitive Tate solution; and
6. the official degree-eleven LMFDB plane model for `X_{\pm1}(25)` together
   with an explicit degree-six map to the stored canonical quotient, whose
   quadric and cubic pullbacks are literal multiples of the source equation;
   and
7. a direct degree-nine adjoint map from the checked Sutherland optimized
   source to the stored canonical quotient.  Its quadric and cubic pullbacks
   are again literal multiples of Sutherland's equation, and its composition
   with the primitive Tate map is kernel-checked; exact resultant certificates
   prove that its homogeneous vector is nonzero and avoids all five canonical
   cusp classes; and
8. complete ordinary-kernel field-table certificates for the cubic and
   quartic binary models, together with projective counts
   `#C(𝔽₂),...,#C(𝔽₁₆) = 5,5,20,29`; and
9. four characteristic-two chartwise Bézout identities excluding the
   explicit complete-intersection singularity predicate over every field,
   plus the exact Newton/reciprocity calculation `P₂(1)=71` and the exact
   four-conjugate level-25 polynomial calculation `P₃(1)=71`; and
10. the pure arithmetic two-prime lemma combining local cardinal bounds
    `2^a·71` and `3^b·71` into divisibility by `71`; and
11. the finite-group specialization bookkeeping: the kernel-range order
    formula, each local bound from a primary kernel and target order, and the
    combined conclusion that two maps with kernel orders `2^a` and `3^b` and
    target orders `71` force the source order to divide `71`; and
12. the degree-two pullback endgame: divisibility of the source order by `71`
    makes doubling injective, so a pullback whose norm composite is `[2]` is
    injective.  A combined theorem derives this directly from the two
    reduction maps without circularly assuming pullback injectivity; and
13. the generic divisor-count class-number theorem: actual finite effective
    divisor types and Riemann--Roch Picard-fibre cardinalities imply formal
    zeta rationality and `P(1)=#Pic^0`; and
14. the structural closed-point layer: locally finite positive-degree closed
    points give finite fixed-degree effective-divisor types, a marked-divisor
    equivalence proves the Euler recurrence, and summed middle-degree
    Riemann--Roch gives `A₄=3A₂+#Pic⁰`.  Arithmetic Frobenius on the canonical
    curve over `𝔽_(3^12)` now constructs the four point-orbit classification
    equivalences by fixed-subfield descent, so the N25 consumer derives
    `#Pic⁰(F₃)=71` from only the remaining geometric Picard/Riemann--Roch
    interfaces, with no Euler recurrence or orbit-classification hypothesis.
    The same coherent construction now works in characteristic two.  Semantic
    field wrappers identify the certified `F4`, `F8`, and `F16` tables with the
    actual field-valued curve equations; Frobenius over `𝔽_(2^12)` realizes
    all four extension-point types and derives `A₂=15`, `A₄=101`, and the
    conditional conclusion `#Pic⁰(F₂)=71` from the same geometric interfaces;
    and
15. the actual divisor-class quotient layer: signed closed-point divisors,
    their integer degree, quotient by a degree-zero principal subgroup, and
    literal `Pic^n` fibres.  The binary `x=0` hyperplane section is now the
    explicit degree-six divisor
    `2[0:0:0:1]+[0:0:1:0]+3[0:1:1:0]`, and the final binary consumer fixes
    both this residual class and an explicit degree-one base class.  Its two
    nonreduced local factors now have exact ideal normal forms
    `(y^2,z)` and `(a+b+a*b,b^3)` on the required principal opens, together
    with surjective maps to the dimension-two and dimension-three Artin
    targets and extensions across those localizations.  Explicit two-sided
    quotient-algebra equivalences now prove both affine exact kernels.  The
    principal-open layer maps the actual chart equations to the normal ideals
    and proves that each resulting ideal is exactly the kernel of its
    localized Artin evaluation.  Thus both local quotient-ring presentations
    are fully packaged; and
16. the affine-cone conormal layer for the binary canonical model: an actual
    homogeneous coordinate quotient `F_2[x,y,z,w]/(Q,C)`, compatibility of
    the degree-two and degree-three universal polynomials and their
    differentials with the stored curve equations and Jacobian rows, and the
    exact conormal sequence
    `I/I² → B⊗Ω_A → Ω_B → 0` specialized to this quotient;
    and
17. the regular-sequence layer for the same equations: an explicit
    `F_2[x,z,w][y]` tower equivalence, a free rank-two quadric quotient, the
    exact multiplication matrix of the cubic class, a nonzero determinant
    certificate, and the final theorem that `[Q,C]` is a
    `RingTheory.Sequence.IsRegular` sequence in `F_2[x,y,z,w]`; and
18. the explicit ungraded Koszul resolution: the maps
    `r ↦ (Cr,-Qr)` and `(a,b) ↦ Qa+Cb`, injectivity on the left,
    exactness at both middle terms, and surjectivity onto the coordinate-ring
    quotient.  Every syzygy is proved to be the standard Koszul syzygy using
    regularity, not a coefficient table or dimension argument; and
19. the shifted resolution in every homogeneous degree: explicit pieces
    `S(-debt)_n`, degree-preserving restrictions of both Koszul maps, a
    homogeneous-component cancellation theorem forcing each witness into
    degree `n-5`, and exactness of
    `0 → S(-5)_n → S(-2)_n ⊕ S(-3)_n → S_n → A_n^{pres} → 0`; and
20. the literal quotient degree pieces: homogeneity of `(Q,C)`, structural
    extraction of the degree-`n` part of every ideal relation, equality of the
    restricted quotient kernel with the Koszul range, and the resulting
    canonical linear equivalence `A_n^{pres} ≃ (S/(Q,C))_n`.

These theorems compile and depend only on the three standard logical axioms.
They do not yet discharge N25.  The model-identification seam is now closed
directly, without needing a Sutherland-to-LMFDB plane transformation.  The
remaining input is a global rational-point or formal-immersion argument over
`ℚ` proving that every rational canonical point is a cusp.  On the active
Jacobian route this expands into explicit missing bridges: scheme-level smooth
proper genus-four reduction, identification of the degree-at-most-four
closed-point effective divisors with actual geometric divisors, the
actual principal-divisor subgroups, adjunction/canonicality for the chosen
degree-six residual classes (with the homogeneous regular-sequence premise
and its degreewise shifted Koszul exactness and literal quotient-piece
identification now proved), the degree-two and
degree-four complete-linear-system fibres, and the Riemann--Roch rank theorem
needed to instantiate the proved class-number formula on both the
characteristic-two and characteristic-three fibres, a second good-reduction
bound controlling
two-primary torsion, rational rank
zero together with the geometric construction and primary-kernel proof for
the reduction maps, construction of the Jacobian pullback and norm maps with
their degree-two composition identity, and the final Abel--Jacobi point
classification.  The proposed ambient `J₁(25)` and level-25 newform routes
are not counted at the endpoint.  The corrected primary source now verifies
the ambient rank-zero and cyclic-order statement, and Lean checks the exact
newform conjugate polynomial at three.  The direct curve route no longer
needs a modular quotient/newform identification for its local cardinality;
the missing work is the geometric divisor/Picard/Riemann--Roch and
good-reduction infrastructure connecting the stored canonical curve to the
proved arithmetic interfaces.

## Declarations present in the tree but not reachable from the endpoint

These custom axioms remain in older or alternative routes, but the rebuilt
main theorem does not depend on them:

- `CyclicOrderReduction.mazur_prime_torsion_bound`;
- `OrderReduction.mazur_cyclic_order_bound`;
- `TorsionFinite.mordell_weil_fg`.

The two tracked proof placeholders in `KubertBridgeN16.lean` are likewise not
reachable from the current endpoint.  They must not be counted as completed
work, but they are not part of the four-entry endpoint ledger.

## Next discharge order

The four remaining assumptions are independent named arithmetic inputs.
The finite cases should be attacked before the uniform tail:

1. finish the rational-point classification on the order-thirteen sextic;
2. close the explicit order-twenty-five obstruction;
3. close the raw order-forty-nine Tate obstruction;
4. formalize the uniform prime-order exclusion for `p ≥ 23`.

Any future count must come from a fresh source rebuild of every changed
downstream module followed by `#print axioms`; stale `.olean` files can retain
already removed axiom dependencies.
