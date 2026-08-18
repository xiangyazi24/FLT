## Run 2026-08-18 (N49 + N13 axiom closure, ChatGPT-as-workhorse)

- doctrine version: four endpoint axioms; N49/N13 focus
- approval: automode 继续推动
- starting avenue: (c) N49 explicit rational-point obstruction + (b) N13 wiring
- ChatGPT: saturate all 6 tabs with N49/N13/p≥23 research
- banked: RationalPointsN49.lean (preΨ'_7 factorization, 0 sorry)
- end: <fill in>
- final result: <fill in>

## Run 2026-08-10 (N25 characteristic-three Frobenius orbit classification)

- doctrine version: four endpoint axioms; N25 finite-field/Jacobian route
- approval: continuing autonomous Mazur proof work
- starting avenue: replace the four semantic point-orbit equivalence inputs
  in the characteristic-three class-number calculation by actual arithmetic
  Frobenius and fixed-subfield descent
- result:
  - constructed exact-period orbit classes and the structural equivalence
    between fixed points of an iterate and degree-indexed ghost slots
  - proved normalized canonical N25 points commute with field embeddings
  - embedded `F₃,F₉,F₂₇,F₈₁` into `F_(3^12)` and identified each image with
    the roots of `X^(3^d)-X` using the polynomial root bound
  - descended Frobenius-fixed projective coordinates chart by chart and
    obtained all four curve-point/orbit equivalences without using point
    cardinalities
  - removed the orbit-classification parameter from the concrete theorem
    deriving `#Pic⁰(F₃)=71`
- semantic boundary: the common field realizes every orbit through degree
  four only; it does not model closed points of arbitrary degree
- axiom audit: the new Frobenius, descent, orbit, and class-number declarations
  depend only on `propext`, `Classical.choice`, and `Quot.sound`
- remaining N25 local seam: actual geometric divisor/Picard/Riemann--Roch
  realization in characteristic three and the analogous construction in
  characteristic two

## Run 2026-08-09 23:35 (N25 marked-divisor Euler recurrence)

- doctrine version: `773f882e9c`
- approval: automode continuation; no tmux names may be changed
- starting avenue: replace the remaining N25 Euler-recurrence hypothesis by
  an explicit finite marked-divisor double count
- completed:
  - constructed locally finite positive-degree closed points and proved
    fixed-degree effective divisors finite by bounded support and multiplicity
  - proved the marked-divisor removal/reinsertion equivalence and the exact
    ghost convolution `n A_n = ∑_(k=1)^n N_k A_(n-k)`
  - proved cutoff-independence of ghost slots and discharged the reusable
    `SatisfiesEulerRecurrence` interface
  - proved the summed middle-degree identity `A₄=3A₂+#Pic⁰`
  - added the N25 consumer deriving `#Pic⁰(F₃)=71` from four semantic
    point-orbit equivalences plus the geometric Picard/Riemann--Roch data
- verification: scoped Lake target builds pass; all audited declarations
  depend only on `propext`, `Classical.choice`, and `Quot.sound`; bypass scan
  is empty
- end: clean bounded milestone; campaign continues
- final result: the Euler recurrence is no longer an N25 hypothesis; the
  remaining local geometric seams are closed-point/Frobenius-orbit
  classification and Picard/Riemann--Roch instantiation

## Run 2026-08-09 (N25 finite-field and Jacobian reduction route)

- doctrine version: `9fc18f1c64`
- approval msg_id: unavailable in the Codex conversation
- starting avenue: (a), certify the good `F_2` fibre and its first four point
  counts, then use the resulting Weil data in the Jacobian reduction argument
- comment discipline: every substantive Lean declaration receives an English
  mathematical docstring recording meaning, conventions, proof idea, and role
- end: banked complete `F_8`/`F_16` field tables and point counts
  `5,5,20,29`; four chartwise characteristic-two Bézout smoothness
  certificates; the Newton polynomial with `P₂(1)=71`; and the exact
  four-conjugate level-25 polynomial with `P₃(1)=71`; the abstract two-prime
  cardinal lemma now combines the future local bounds into divisibility by
  `71`; and the finite-group kernel-range layer derives those bounds from
  reduction maps with primary kernels; the resulting odd order then makes a
  degree-two pullback injective from the identity `norm ∘ pullback = [2]`
- source audit: corrected *Sporadic cubic torsion* v2, Theorems 3.1 and 4.13,
  Corollary 4.14, and Table 2 verify externally that `J₁(25)(ℚ)` has rank zero
  and is cyclic of order `227555`; the authors' computation repository was
  pinned at `f0c6cf41e156d9d96bebd6b639e1f71208f04b6c`
- final result: all new Lean terminal theorems pass scoped checks and depend
  only on `propext`, `Classical.choice`, and `Quot.sound`; N25 remains an
  endpoint axiom because the smooth-curve zeta/Jacobian, modular quotient or
  newform, geometric construction and primary-kernel control of the
  good-reduction maps, geometric Jacobian pullback/norm construction, and
  Abel--Jacobi bridges are absent

## Run 2026-08-09 (N25 direct canonical adjoint bridge)

- Confirmed the local `sage` micromamba environment contains Sage 10.9 and
  Singular 4.4.1; the earlier project inventory that treated them as absent
  was stale.
- Computed the Gorenstein adjoint ideal of Sutherland's degree-twelve
  projective closure.  Its degree-nine component has dimension 12, as required
  by the source genus.
- Derived the diamond action `⟨7⟩` from five exact Tate doublings, verified the
  function-field involution, and computed dimensions `(4,8)` for its invariant
  and anti-invariant differential spaces.
- Matched the residual order-five action on the invariant four-space with the
  stored canonical action.  This produced four explicit degree-nine adjoint
  coordinates mapping directly to `25.150.4.f.1`.
- Added `RationalPointsN25CanonicalSourceBridge.lean`.  Literal `ring`
  certificates prove that both target equations pull back to multiples of
  Sutherland's source equation, and
  `tateCanonicalCoordinates25_onCanonical` composes this map with the existing
  primitive Tate-to-Sutherland bridge.
- Proved that the optimized Sutherland `y` coordinate is neither zero nor one
  on the primitive Tate locus.  The `y=1` case reduces to `r=s`, and the exact
  raw diagonal specialization is `r⁴(r-1)¹⁷`.
- Formalized a Bezout resultant for the first and fourth adjoint cores.  Its
  only residual factor is a monic degree-ten polynomial with no root modulo
  two, so those two canonical coordinates cannot vanish simultaneously when
  the optimized source coordinate is not one.  The Tate canonical quadruple
  is therefore formally nonzero.
- Formalized a second exact resultant between Sutherland's source equation and
  the third canonical coordinate.  Its fibre polynomial is
  `(y-1)¹² p₁₀(y)`, so the third coordinate is nonzero on the primitive Tate
  locus.
- Used the third coordinate to exclude cusp classes A, C, and E, and the
  first/fourth nonvanishing pair to exclude B and D.  The direct Tate
  canonical image is now formally noncuspidal.
- N25 remains an endpoint axiom.  The direct model-comparison and base-point
  seams, including canonical noncuspidality, are closed; only the global
  rational-point classification remains.
- Scoped checks pass, and all four terminal bridge theorems audit to exactly
  `propext`, `Classical.choice`, and `Quot.sound`.

## Run 2026-08-09 (N25 Sutherland source bridge)

- Added `RationalPointsN25SutherlandBridge.lean` with the published raw
  bidegree-`(10,15)` and optimized bidegree-`(8,8)` equations for `X₁(25)`.
- Proved the exact Tate-chart identity
  `F25(b,c)=c¹⁰(b-c)¹⁵ Fraw(b/c,c²/(b-c))` by a literal ring certificate.
- Verified Sutherland's universal raw-to-optimized map by a separate
  bihomogeneous polynomial identity.  Splitting the comparison into these two
  certificates avoids one much larger direct expansion.
- Proved the two optimization denominators are nonzero on every primitive
  Tate solution using the exact exceptional-divisor specializations
  `(s-1)²³` and `-s(s-1)²⁷`.
- The public theorem `tateToSutherland_on_plane` now maps the original
  `b≠0`, `F5≠0`, `F25=0` locus directly to the optimized source equation;
  it has no additional denominator assumptions.
- Scoped source compilation passed.  Axiom audits of the Tate-to-raw,
  raw-to-optimized, denominator, and public map theorems report exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- N25 remains an endpoint axiom.  The source-side gap is now narrowed from
  `F25` versus LMFDB to the birational comparison between Sutherland's checked
  bidegree-`(8,8)` equation and the LMFDB degree-eleven plane model.  After
  that, noncuspidality and the global canonical rational-point classification
  remain.

## Run 2026-08-09 (N25 LMFDB quotient bridge)

- approval: automode continuation; no tmux names may be changed
- starting avenue: close the target half of the Tate-to-canonical model
  comparison using the official `X_{\pm1}(25)` source model
- completed:
  - recorded the homogeneous degree-eleven LMFDB plane equation for
    `25.300.12.j.1` in source coordinates `[C:W:S]`
  - solved the published genus-twelve canonical quadrics on `S=1`, composed
    the published linear degree-two quotient, and homogenized the resulting
    four degree-six coordinates
  - proved exact pullback identities `Q(Φ)=-C F₁₁` and
    `K(Φ)=-W H₆ F₁₁`, hence every source-plane zero maps to the stored
    canonical complete intersection
- verification:
  - all 45 source canonical quadrics have zero remainder modulo the affine
    degree-eleven plane equation in an independent exact SymPy audit
  - scoped Lean compilation passes
  - the three new public theorems audit to exactly `propext`,
    `Classical.choice`, and `Quot.sound`
- next frontier: compute and certify the birational transformation from the
  Tate `F25(b,c)=0` model to the LMFDB degree-eleven source plane, then prove
  the canonical image is noncuspidal
- end: clean bounded milestone; campaign continues

## Run 2026-08-09 (N25 sevenfold normalization)

- approval: automode continuation; no tmux names may be changed
- starting avenue: complete the exact `7P` Tate normalization on the
  primitive order-25 locus
- completed:
  - proved the Tate origin has exact additive order 25 from `F25=0`,
    `b≠0`, and `F5≠0`
  - exposed the order-fourteen division evaluation and proved `G14≠0`
  - derived the tangent denominator, slope, translated coefficients, and
    explicit parameters `B₇,C₇` at the actual point `7P`
  - proved the remaining translated quadratic numerator `H7` is nonzero:
    otherwise the translated origin is killed by three, forcing `21P=0`
  - checked all five coefficients of the normalized Tate curve and verified
    the downstream denominator-free canonical bridge
- verification:
  - scoped source compilations pass
  - six new public endpoints audit to exactly `propext`,
    `Classical.choice`, and `Quot.sound`
- next frontier: derive the source involution/order relations or directly
  construct invariant plane numerators and their `F25` divisibility and
  nonvanishing certificates
- end: clean milestone; campaign continues

## Run 2026-08-05 (source-rebuilt Mazur audit and N17 classification layer)

- approval: automode continuation; ChatGPT tabs kept saturated through the
  shared `flt` bridge
- source-rebuilt correction:
  - endpoint has exactly six custom axioms and no reachable `sorryAx`
  - removed the stale seventh item `exists_rational_two_isogeny_quotient`;
    the Vélu quotient used by orders 20 and 24 is proved
  - confirmed the two tracked `KubertBridgeN16` `sorry`s are outside the
    endpoint import closure
- N13 audit:
  - Q3802 confirms that the finite 19-element special Abel set, quotient
    basis, graph/disk-pair recovery, relation-first classifier, separatedness
    adapter, and rational-point cusp tail are already proved
  - Q3805 isolates the weakest endpoint seam as pointwise reflection of
    rational Abel classes from equality of anchored special classes
  - the next low-degree construction is irreducible-quadratic special
    restriction on both charts; no new special Jacobian count is needed
- N17 verified milestones:
  - `42adc64469`: preserve `j` in exact-order-17 Tate normalization
  - `aefa1fdb8c`: explicit `X₀(17)` model, standard two-isogeny, and exact
    order-four point
  - `034571e123`: classify rational two-torsion and prove its cardinality is
    two
  - current working node: sharpen the abstract two-isogeny exact sequence;
    a zero left arrow embeds `G/2G` into the right quotient, and
    `|G/2G| ≤ |G[2]|` forces free rank zero
  - specialized Mathlib's height descent to representatives `{0,T}` modulo
    doubling; finite generation now needs only Northcott, the doubling lower
    bound, and one fixed-`T` translation estimate
  - connected `TwoCosetExhaustion` directly to the sumset cover required by
    that descent theorem; both bridge declarations compile and audit clean-3
  - proved the integral model has three affine points over both `𝔽₂` and
    `𝔽₃`, hence four projective points in each good fibre; the remaining
    torsion step is the absent rational-point reduction/injection API
  - `X017IsogenySequence.lean` transports the existing bundled Vélu maps to
    the two standard N17 models, proves dual-forward composition is doubling,
    and identifies the dual-kernel representative with the target point
    `(0,0)`; `(64,0)` instead maps back to the nonzero source kernel
  - Q3806 independently audited the exact-sequence layer: the left
    two-representative cover and the right quotient bound are separate
    arithmetic producers, and finite generation remains an independent
    height input
  - `X017Descent.lean` clears square denominators on the standard source and
    proves that every nonzero rational first coordinate has squareclass `1`
    or `17`; the positive quadratic factor removes negative classes
  - Q3809 identifies the target quotient as the first independent endpoint:
    its expected squareclass image is `{1,-1}`, with `(0,0)` as the
    nontrivial representative
  - `X017FirstCoset.lean` clears denominators on the standard target, excludes
    both provisional `±2` classes by three-stage two-adic parity descent, and
    proves that every nonzero rational target coordinate has squareclass
    `1` or `-1`
  - `StandardTwoIsogenyPreimages.lean` promotes the order-15 square-coordinate
    reconstruction to arbitrary standard two-isogeny coefficients
  - the target squareclass calculation and explicit preimages now prove the
    concrete cover `target = forwardHom(source) ∪
    (eta + forwardHom(source))`; consequently the concrete left
    exact-sequence arrow is zero and the right arrow is injective
  - `StandardTwoIsogenyDualHom.lean` bundles the explicit standard
    `dualPoint` formula by applying the already additive forward map to the
    dual curve and scaling the twice quotient back by `(x/4,y/8)`
  - the generic square-coordinate reconstruction is also proved for
    `dualPoint`; this removes the coordinate/bundled-map seam on the source
    quotient
  - Q3817 was rejected after source verification: it incorrectly treated
    `T=(17,136)` as two-torsion, assumed its vertical coordinate was zero,
    and confused membership in an isogeny image with membership in its kernel
  - `X017SecondCoset.lean` proves the correct translation identity for
    `P-T`, handles the visible exceptional points, and obtains the second
    concrete cover `source = dualHom(target) ∪ (T + dualHom(target))`
  - the right quotient has an explicit surjection from `Bool`, so
    `|E(ℚ)/2E(ℚ)| ≤ 2`; combining both isogeny covers further proves every
    source point is a double or `T` plus a double
  - removed the unnecessary import of `FLT.EllipticCurve.Torsion` from the
    proved rational projective-height development, keeping its Northcott and
    duplication theorems independent of unrelated torsion API sorries
  - `X017HeightDescent.lean` symmetrizes any nonnegative height over the four
    translates by an order-four point; the result is exactly invariant under
    translation by `T`, retains Northcott finiteness, and inherits a
    factor-two doubling bound from the base factor-four bound
  - `X017RankZero.lean` applies this to the rational projective `x`-height and
    exact `{0,T}` cover, proves finite generation, and then obtains free rank
    zero from `|E(ℚ)/2E(ℚ)| ≤ |E(ℚ)[2]| = 2`
  - `X017FourTorsion.lean` closes the algebraic classification tail:
    `2P=K` forces `(x(P)^2-289)^2=0`, hence `P=T` or `P=-T`; consequently
    every point killed by four is one of `0,K,T,-T`
  - `X017FormalTwoCore.lean` proves the explicit duplication formulas on the
    good integral model, the integral-or-formal valuation dichotomy, and that
    doubling a nonzero formal point raises its two-adic level by at least one
  - `X017FormalTwoReduction.lean` computes the mod-two residue dynamics of
    the integral model, proves that four times every rational point enters the
    formal kernel, and proves formal separatedness by strict level growth
  - `X017RationalPoints.lean` combines formal separatedness with the exact
    `{0,T}` cover: four times every rational point is divisible by every
    power of two and hence vanishes; the point group is exactly
    `⟨T⟩={0,K,T,-T}` and has cardinality four
- verification:
  - scoped compilations pass
  - the N17 two-torsion theorem, exact-sequence/rank declarations, and
    transported N17 isogeny identities, both source and target squareclass
    classifications, the generic square-coordinate preimage theorem, and the
    two concrete coset exhaustions and doubling quotient bound have clean-3
    axiom audits
  - the four-orbit height lemmas, concrete finite-generation instance, and
    N17 free-rank-zero theorem audit to exactly `propext`,
    `Classical.choice`, and `Quot.sound`
  - the conditional four-torsion classification has the same clean axiom
    audit
  - the two-adic formal core also audits to exactly Lean's standard
    quotient/classical axioms
  - the mod-two entry theorem, formal separatedness, uniform exponent-four
    theorem, four-point classification, cyclic-generation theorem, and exact
    cardinality theorem all force-compile from source and audit to exactly
    `propext`, `Classical.choice`, and `Quot.sound`
- N17 endpoint closure:
  - the level quotient, cusp and `j` control, model transport, and exact Tate
    fibre elimination are complete; the endpoint axiom audit no longer
    contains N17 or N19
- current N13 first-jet milestone:
  - exact centered-square and linearized-double polynomial identities are
    formalized without denominators
  - coefficients one and three of `P.u² - uBase * Q.u` modulo the moving
    coordinate ideal square imply literal doubling of the two disk
    coordinates
  - the resulting adapter constructs the existing
    `FirstJetDoublingCompatibility` structure by comparison with the proved
    transition-square jet
  - scoped builds pass, and the coordinate theorem, centered Picard doubling
    lemma, and adapter audit to exactly `propext`, `Classical.choice`, and
    `Quot.sound`
  - the remaining first-jet arithmetic input is exactly the two stated cross
    coefficients for the canonical recovered representatives of `z` and
    `2z`
  - proved vertical saturation of a product of saturated affine ideals when
    the first is invertible in the common function field, using inverse
    fractional-ideal cancellation
  - instantiated the product theorem for valuation-independent point lines;
    `pairLine` is vertically saturated for both split secants and coincident
    repeated-root tangents
  - the product theorem, tensor wrapper, point-line wrapper, and `pairLine`
    theorem pass scoped compilation and audit to exactly `propext`,
    `Classical.choice`, and `Quot.sound`
  - threaded those saturation certificates through every split, repeated,
    reciprocal, finite, rational degree-zero/one/two, and exact-spread chooser
  - the selected `exactSpreadLine` now exposes vertical saturation directly;
    the public N13 endpoint no longer accepts an external saturation provider
  - the strengthened chooser and endpoint declarations compile and audit to
    exactly `propext`, `Classical.choice`, and `Quot.sound`

## Run 2026-07-28 (N13 structural two-adic Abel chart)
- approval: `/automode`; stop requested at the next clean node
- proof policy: structural only; no finite tables, `native_decide`, giant
  certificates, replacement axioms, or `sorry`
- completed:
  - proved compatibility of the two infinity orders under field extension,
    including `ℚ → ℚ₂`, by preservation of Laurent order and uniqueness of
    the positive square root (`9b70a580cd`)
  - proved canonical Mumford normalization commutes with `ℚ → ℚ₂` and that
    rational oriented Picard base change is injective (`0e2befa7a2`)
  - constructed the balanced degree-two Mumford class of every pair in the
    two distinguished residue disks and proved the centred Abel chart
    `DiskPair → J(ℚ₂)` injective (`014e31f9a7`)
  - derived `pair_zero` and `pair_injective` automatically from Picard
    faithfulness; for a rational reduction kernel the remaining chart inputs
    are now only representative existence and regularity of transported
    addition (`91fdc242e5`)
  - recovered a unique `DiskPair` from every smooth integral Mumford graph
    reducing to `(X² + X, 0)`: Hensel lifting supplies the two roots and the
    curve equation identifies the two graph values; the original and
    recovered graph ideals coincide (`201ae724b1`)
  - proved that completion of the square sends those two graph ideals to the
    same sextic fractional ideal, hence the recovered pair carries exactly
    the original oriented and centred two-adic Picard class (`7954d95b0d`)
  - separated the genuine Abel differential from the graph-equation
    linearization: evaluation at `(0,0)` and `(-1,0)` has matrix
    `[[1,0],[-1,1]]`, determinant one, and an explicit integral linear
    inverse (`b1b350245d`)
  - formalized the module-theoretic Čech--Nakayama step: special-fibre
    surjectivity of a finite-target coboundary lifts integrally, and a
    cochain closed modulo the maximal ideal can be corrected to an actual
    cocycle without changing its reduction (`b1b350245d`)
  - computed the actual special-fibre two-chart Laurent Čech quotient:
    the affine and infinity images miss exactly `v t⁻²` and `v t⁻¹`;
    the two base-point principal parts have obstruction vectors `(1,0)`
    and `(1,1)`, so the connecting matrix is invertible and the twisted
    Čech `H¹` vanishes (`f24ae0b1dc`)
  - extracted the Laurent calculation over an arbitrary commutative ring
    and lifted the finite obstruction complex to `ℤ₂`; the integral
    principal-part columns are `(1,0)` and `(1,-1)`, with determinant
    `-1`, and reduce to the computed special-fibre matrix.  Consequently
    every finite integral coboundary with that residue is surjective, and
    every cochain closed modulo two has a kernel lift with unchanged
    reduction (`94e0fb8037`)
  - replaced the finite Laurent-polynomial proxy by the genuine formal
    overlap of Laurent series, including arbitrary power-series tails at
    infinity.  Its quotient still has exactly the two obstruction classes;
    the actual integral principal functions satisfy the cleared-denominator
    identities, induce the computed integral matrix, and make the formal
    twisted additive `H¹` vanish (`1dce55b62f`)
  - formalized multiplication in the actual quadratic formal curve algebra.
    For every invertible transition function reducing to `1`, the twisted
    principal connecting map reduces to the special N13 matrix, hence is
    surjective and admits the required kernel lift (`cefa49c23b`)
  - identified that pair algebra with the genuine quadratic
    `ℤ₂((t))`-algebra and constructed the actual restriction homomorphism
    from the integral affine coordinate ring by `x ↦ t⁻¹`,
    `y ↦ t⁻³v`.  Its normal-form coordinates respect multiplication, every
    actual affine function lands in the previously defined affine-section
    submodule, and a genuine overlap unit reducing to one canonically gives
    a `NearIdentityTransition` (`7713f611c7`)
  - constructed the genuine complete formal-infinity chart
    `ℤ₂[[t]][v]/(v²+(1+t²+t³)v-(t+t²))` and proved that its restriction
    image is exactly the full power-series `infinitySections` submodule
    (`98237bf9cf`)
  - proved the converse on the actual affine chart: every Laurent pair in
    `affineSections` is the restriction of an integral affine function.
    The proof reverses the finitely many nonpositive Laurent coefficients
    into polynomials in `x=t⁻¹`; for the `v` coefficient it first shifts by
    `t³`.  Thus both submodules in the formal Čech quotient are now exactly
    the images of the two genuine chart rings (`f636af395b`)
  - formed the genuine additive Čech coboundary from the actual affine and
    complete formal-infinity rings.  Its image is exactly the kernel of the
    two principal-part coefficients, and its additive cokernel is
    canonically equivalent to the rank-two obstruction group.  The
    Laurent-series calculation is therefore now an exact statement about
    the actual chart complex, not only its coefficient submodules
    (`f2e7c66f84`)
  - generalized the Čech--Nakayama correction from a finite overlap target
    to an arbitrary overlap with finite actual cokernel.  Vanishing of the
    residue cokernel now implies integral surjectivity and a kernel lift
    preserving reduction.  The source can therefore retain a nonprincipal
    affine invertible module (`891e1592c8`)
  - proved both genuine chart restrictions are `ℤ₂`-linear, upgraded the
    actual coboundary and cokernel to modules, and identified that cokernel
    linearly with `ℤ₂²`.  In particular the genuine untwisted Čech cokernel
    is finite, exactly the finiteness input used by the module-valued
    Nakayama theorem (`2d7b71c0ee`)
  - lifted the simple formal-infinity branch `v = 0` by X-adic Hensel,
    constructed its quadratic conjugate, and proved that the two roots
    differ by a unit.  The complete-chart polynomial now has a verified
    linear factorization over `ℤ₂[[X]]`; two-point evaluation/interpolation
    is therefore the remaining step to an explicit product decomposition
    of the infinity chart
  - completed that product decomposition: simultaneous evaluation on the
    two Hensel roots is injective by the unique normal form `a+bv` and
    surjective by explicit two-point interpolation.  Hence the actual
    complete formal-infinity chart is ring-equivalent to
    `ℤ₂[[X]] × ℤ₂[[X]]`, with a proved formula for the inverse
  - split the actual punctured formal overlap by the same method:
    its quadratic algebra is ring-equivalent to the product of its two
    Laurent-series branch rings.  The equivalence has an explicit
    interpolation inverse, and simultaneous branch evaluation commutes
    with restriction from the complete formal-infinity chart
  - combined the two rational Laurent expansions into a faithful algebra
    map from the N13 function field to the product of its infinity branches.
    Every affine fractional ideal, including an invertible nonprincipal
    one, now restricts canonically and injectively to that product; the
    construction is a ring homomorphism on fractional ideals and therefore
    also restricts their units, without choosing a global generator
  - identified the integral and rational infinity branches under
    `ℤ₂ → ℚ₂`.  Coefficient extension sends the X-adic Hensel root reducing
    to zero to the positive sextic Laurent root after the good-model
    coordinate change, and sends its conjugate to the negative root.  The
    proof uses the quadratic relation and constant-term uniqueness rather
    than coefficient expansion
  - proved the full affine restriction/base-change square commutes.  On
    `x`, this is naturality of polynomial evaluation at `t⁻¹`; on the good
    `y`, it is exactly the two branch identities above.  The unique
    rank-two normal form `p(x)+q(x)y` then extends the comparison to every
    integral affine function
  - proved that every nonzero affine fractional ideal becomes the full
    rank-one module after scalar extension to the product of the two
    Laurent branch fields.  A nonzero ideal section is nonzero in both
    branches by faithfulness, hence is a unit in their product; this proves
    local triviality without selecting a global affine generator
  - embedded `ℤ₂[[t]] × ℤ₂[[t]]` faithfully into the rational branch pair
    as an `ℤ₂`-algebra and defined its image as the complete integral branch
    lattice.  This embedding is proved equal to restriction
    `Power → Laurent` followed by coefficient extension, so the lattice is
    compatible with the formal/rational branch square
  - proved that the actual complete formal-infinity chart realizes exactly
    this integral branch lattice.  Restriction through the punctured formal
    overlap, Hensel branch splitting, and coefficient extension gives the
    same rational branch pair
  - placed the fixed base-divisor twist on the correct chart.  Since
    `(0,0)+(-1,0)` is supported on the affine chart, the infinity lattice is
    unchanged and the affine source is enlarged by its two genuine
    principal parts.  Combining these with the actual two-chart
    coboundary gives a surjective extended Čech map for every invertible
    overlap transition reducing to one; every near-closed cochain has an
    actual kernel lift with unchanged residue
  - extracted a finite integral affine lattice from every invertible
    rational affine fractional ideal without choosing a global generator.
    Its generators lie in the original ideal, rational scalar extension
    recovers that ideal exactly, and the lattice is nonzero and finitely
    generated.  After restriction to the two faithful Laurent branches,
    its scalar extension is the full branch pair: a nonzero lattice section
    is nonzero in both branch fields and hence is a unit in their product
  - packaged the corresponding branch-local trivialization without
    principalizing the affine ideal.  A nonzero affine-lattice section gives
    a unit only in the product of the two rational branch fields; multiplying
    the standard complete branch lattice by that unit produces its local
    lattice model.  This model is linearly equivalent to the standard
    lattice, independent of the local-basis choice up to linear equivalence,
    has full rational scalar span, contains the restricted chosen section,
    and is exactly the unit multiple of the image of the actual complete
    formal-infinity chart
  - constructed the formal transition attached to an already-integral
    near-base Mumford graph.  For every monic `u`, its restriction at
    `x=t⁻¹` factors as the Laurent pole monomial times the power-series
    reversal of `u`; the latter has constant coefficient one and is a unit.
    Coefficientwise reduction commutes with this restriction.  Hence for
    `u mod 2 = u₀ mod 2`, the ratio `u/u₀` is a genuine unit of the actual
    quadratic formal overlap whose reduction is one, and canonically gives
    `NearIdentityTransition`.  No Laurent-coefficient enumeration or
    denominator clearing is used
  - proved that the affine generic fibre is exactly the vertical
    localization of the integral good-model coordinate ring: after inverting
    nonzero `ℤ₂` scalars, the rank-two normal form clears the two polynomial
    denominators simultaneously.  Completion of the square transports this
    localization to the standard sextic coordinate ring.  Hence every
    generic-fibre ideal has a canonical contraction whose extension is
    exactly the original ideal; the contraction is nonzero when the original
    ideal is nonzero and is saturated by every nonzero vertical scalar.
    Every local oriented Picard class now has such a nonzero integral-model
    ideal whose generic fibre represents the class.  Invertibility of that
    contraction on the two-dimensional integral surface is deliberately not
    asserted
  - proved that the N13 function field is also the fraction field of the
    integral good-model ring and that vertical extension commutes with
    inverse fractional ideals.  The reverse inclusion uses Noetherian finite
    generation and one common vertical denominator for all generators.
    Therefore extension also commutes with the divisorial double inverse,
    and the divisorial hull of the contraction of every invertible generic
    ideal has exactly the original generic fibre.  This removes the
    reflexive-hull/localization compatibility gap without choosing an affine
    generator; local freeness of the hull on the integral surface remains a
    separate geometric step
  - proved that reduction of the integral good-model coordinate ring onto
    the special N13 fibre is surjective and computed its kernel exactly as
    the principal ideal generated by `2`.  The proof uses the rank-two normal
    form and polynomial coefficientwise reduction, not finite enumeration
    (`c0e1729e9e`)
  - defined the defect ideal `H * H⁻¹` and proved a generic--special fibre
    criterion: generic invertibility makes its vertical localization top,
    while top special reduction forces the integral defect ideal itself to
    be top by an explicit two-adic geometric-series argument
    (`a749bdd4f2`)
  - reduced the remaining special-fibre hypothesis to one concrete trace
    witness: an element of the defect ideal whose reduction is `1`.
    Generic invertibility plus this single witness is now a complete
    capstone for integral invertibility, with no regular-local or UFD
    infrastructure
  - proved the generalized Mumford inverse formula integrally over an
    arbitrary commutative base: the graph ideal `(u,Y-v)` times its
    hyperelliptic-conjugate graph ideal `(u,Y+h+v)` is the principal ideal
    `(u)`.  The proof uses only the curve equation and the smoothness Bézout
    identity, retains the `2v+h` term, and commutes with reduction; it does
    not use a characteristic-two shortcut
  - proved triple-inverse stability for nonzero fractional ideals and hence
    identified the inverse of the divisorial hull with the inverse of the
    original contracted ideal.  A finite dual frame for the contraction
    therefore transports directly to the hull, avoiding any
    reflexive-rank-one-to-locally-free theorem
  - formalized the finite dual-frame endpoint: finitely many primal and
    multiplier-inverse affine lifts, together with integral representatives
    of their products whose reductions sum to one, give the defect witness
    and make the divisorial hull invertible
  - proved the explicit special-fibre affine dual frame symbolically:
    `[u,cu,y]` lies in `(u,y)`,
    `[x³,(y+h)/u,c]` lies in its multiplier inverse, and the three
    evaluations sum to one.  Membership of `(y+h)/u` uses only
    `y(y+h)=u x³`; there is no finite computation
  - isolated generic two-chart trace-lifting lemmas, including a raw-lift
    variant which corrects one supplied cochain by a divisible coboundary
    and does not assert global reduction-surjectivity for a constrained
    complete chart
  - ruled out an overstrong route: the six displayed special affine factors
    cannot individually be compatible global proper-curve sections.  For
    example `u x³=x⁵+x⁴` has a pole at infinity.  The remaining theorem must
    lift these factors only in the affine lattice and multiplier inverse;
    proper Čech data supplies the integral specialization model, not six
    global sections
  - closed the pure rank-two quotient-algebra tail needed after geometric
    finiteness and flatness.  A literal basis `{1,x}` is converted to a
    power basis; monic division and power-basis linear independence prove
    that evaluation at `x` has kernel generated by the characteristic
    polynomial of multiplication by `x`.  The polynomial is monic of degree
    two, annihilates `x`, and every quotient element is linear in `x`.
    This step uses no domain, UFD, divisor, or N13-specific hypothesis and
    does not assume the missing no-escape theorem
  - formalized the algebraic finiteness endpoint in the explicit no-escape
    route.  If an affine algebra has normal form `P(x)+Q(x)y` and an ideal
    contains one monic relation in `x`, its quotient is finite over the
    base ring.  The proof is a surjection from two copies of the finite
    monic algebra `AdjoinRoot m`; it does not enumerate coefficients or
    choose a finite spanning bound
  - closed the fixed-curve algebra in the explicit no-escape route.  The
    hyperelliptic conjugate of `P(x)+Q(x)y` has norm
    `P²-hPQ-rQ²`, and this norm stays in the same affine ideal.  Polynomial
    reflection computes its coefficient of degree `2N` as the product of
    the two normalized infinity-branch constants, without expanding a
    coefficient convolution.  If both constants are units, scaling the norm
    gives a monic polynomial in the ideal, so the affine quotient is finite
  - isolated the generic branch-unit argument.  A power series reducing to
    one under a local coefficient homomorphism is a unit; multiplication by
    an invertible transition transfers this to the normalized affine
    branch restriction.  The remaining project-specific input is now only
    the genuine compatible Čech section, its componentwise reduction, and
    the normalized branch/glue identities
  - closed the finite-flat graph-recovery tail.  Over a local base, flatness
    and a residue-field basis literally given by `{1,x}` lift that same
    family to an integral basis and hence to a power basis.  If evaluation
    at the quotient class of `x` has principal kernel `(u)` and the quotient
    class of `y` is `v(x)`, polynomial normal form and ideal correspondence
    recover the original ambient ideal exactly as `(u(x), y-v(x))`.  This
    is a structural basis-lifting and kernel argument, not coefficient
    elimination
  - replaced the remaining no-escape certificate by an equal-two-fibre
    argument.  Vertical saturation makes every canonical contracted
    quotient torsion-free and hence flat over `ℤ₂`.  Ambient reduction
    descends to quotients with kernel generated by the quotient class of
    `2`, and the corresponding tensor special fibre is identified
    explicitly with the reduced quotient.  Abstractly, if `{e₀,e₁}` is a
    basis on both the generic and special fibres, every generic denominator
    is a unit times `2^n`; reduction forces both coefficients of a relation
    divisible by `2`, and torsion-freeness cancels one factor at a time.
    Thus no denominator can escape, and the same literal pair is already an
    integral basis.  This proof assumes neither module finiteness nor
    properness, Čech branch units, a valuation table, or a finite
    certificate
  - constructed the generic and fixed-special graph-quotient equivalences
    and transported the monic quadratic power bases to literal quotient
    bases `{1,x}`.  These are genuine algebra equivalences, not dimension
    counts or chosen quotient representatives
  - proved that the quotient of a canonical vertical contraction injects
    into its generic Mumford quotient and carries the integral classes of
    `1` and `x` to the two literal generic basis vectors
  - instantiated the abstract equal-two-fibre theorem for the canonical
    contraction.  Assuming only the remaining literal special-ideal
    equality, the integral quotient itself has basis `{1,x}` without any
    prior module-finiteness hypothesis
  - used multiplication by `x`, its characteristic polynomial, expression
    of `y` in the integral basis, and ideal correspondence to recover the
    canonical contraction exactly as a monic degree-two generalized
    Mumford graph.  Thus every algebraic step after the special-ideal
    equality is now compiled
- verification:
  - all touched endpoints compile by `lake env lean <file>`
  - axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`
- exact remaining N13 seam:
  1. prove that every rational Picard specialization-kernel class has a
     smooth integral Mumford representative reducing to `(X² + X, 0)`.
     Vertical localization and contraction are now closed: every generic
     ideal has a nonzero vertically saturated integral-model contraction
     with the correct generic fibre.  Its divisorial double inverse is now
     constructed and proved to retain exactly that generic fibre for every
     invertible generic ideal.  Its generic invertibility is enough: the
     generic--special defect criterion now reduces integral invertibility to
     constructing one element of `H * H⁻¹` whose special reduction is `1`.
     The special affine trace/evaluation certificate is now closed.  The
     equal-two-fibre theorem removes the separate infinity
     no-escape/properness certificate.  The remaining semantic input is to
     choose the generic degree-two Mumford quotient for a specialization
     kernel class and prove that the mapped contraction ideal on the special
     affine fibre is literally the fixed graph ideal `(X²+X,Y)` (or supply
     the equivalent quotient map carrying `{1,x}` to its fixed special
     basis).  The generic and fixed special quotients now have their literal
     degree-two bases, and a single application of
     `N13ConcreteGraphRecovery.exists_integral_graph` performs vertical
     no-escape, constructs the integral basis, and recovers the monic
     quadratic graph.  Hence this representative-level special-ideal
     equality is the sole remaining semantic theorem before graph recovery.
     Once such a `NearBaseMumford` representative exists, its integral
     near-identity transition, Hensel recovery, chart uniqueness, and Picard
     compatibility are all automatic.  The new `u/u₀` transition theorem is
     downstream of representative existence and must not be used
     circularly
  2. construct the genuine finite reduction classifier and prove its fibres
     are the cosets of its kernel
  3. prove the transported local group law has the required two-adic
     quadratic error (or replace it by an equally strong structural
     logarithm argument)
  The large proper two-chart infrastructure remains available, but it is no
  longer needed for denominator no-escape: equality of the two literal
  fibre bases supplies the shorter structural proof.  It must not be
  replaced by an unchecked claim that Picard specialization equality already
  gives literal equality of affine ideals; that ideal-level bridge is the
  next theorem.
- latest ChatGPT bridge audits Q2789, Q2790, Q2802, Q2820, Q2821, Q2837,
  and Q2840 have been harvested.  They confirm that the remaining statement
  is the literal special-ideal equality; restricted reduction exactness is
  only an equivalent reformulation.  The honest structural route is to
  construct the special effective degree-two divisor represented by the
  mapped contraction and use Abel rigidity to identify it with the fixed
  divisor.  Do not duplicate stale failed deliveries Q2313/Q2314 unless the
  corresponding tabs are confirmed dead

## Run 2026-07-12 (Complete Mazur proof — Layer 2 decomposition)
- doctrine version: 6 gaps initially → 8 axioms after decomposition (narrower scope each)
- approval: /automode from Xiang
- starting avenue: (a)→(b) Layer 2 dispatcher decomposition + N18 bridge (C)
- commits:
  077eebc6: dispatcher theorem + N18 bridge (C) — both green on uisai2
  83e50b4b: further decompose p≥17 into 17+19+≥23 — green on uisai2
- axiom check (fresh oleans): mazur_cyclic_order_bound_assembled depends on
  {propext, Classical.choice, Quot.sound, sorryAx} + 8 project axioms
- ChatGPT: 5+4 questions dispatched to SOL Pro flt1-5, all delivery-timed-out
  (tabs may still have answers in browser). Pre-existing designs Q4463-Q4560 used.
- Python verified: p=19 kernel poly k₁₉ (monic, irreducible, no root mod 2),
  X₀(17) noncuspidal points at (7,13)/(7,-21), X₀(19) at (5,9)/(5,-10)
- ChatGPT round 2: flt1,2,5 timed out (f=2); flt3,4 still running
- end: 2026-07-13 01:20 (clean pause — all independent work exhausted)
- final result: 5 commits, axiom surface decomposed from 1 monolithic to 8 targeted,
  kernelPoly19_no_rational_root sorry-free, N18 bridge (C) sorry-free
- next session priorities:
  (1) p=17 kernel poly: need Sage on uisai2 to compute isogeny kernel for
      the 17-isogeny corresponding to the noncuspidal X_0(17) points.
      The LMFDB shows curves with 17-isogenies exist (conductor 14450).
      Command: `E.isogenies_prime_degree(17)[0].kernel_polynomial()` in Sage.
  (2) close kernelPoly17_no_rational_root (same pattern as p=19 — monic+mod p)
  (3) KubertBridgeN16 sorry #2: birational map (b,c,eta) → (u,w) on w²=u³-u²-u
  (4) Vélu 2-isogeny for exists_rational_two_isogeny_quotient
  (5) p=13 genus-2 descent (biggest piece, needs Q4478 design)
  Note: ChatGPT flt tabs may still have answers in browser — check manually.

## Run 2026-07-08 (ChatGPT harvest mode)
- doctrine version: Close CyclicExclusion sorry's via ChatGPT harvest
- approval: /automode command
- starting avenue: (a) CyclicExclusion20 group-theory sorry's
- status update 07:40:
  CyclicExclusion20: 7→2 sorry (5 group-theory lemmas CLOSED). commit 0796e235.
  CyclicExclusion15: fixed false no_tate_order5_psi3_root_solution (was missing curve eq). commit 3b0e38e6.
  Total: 125→120 sorry, 27 axiom.
  ChatGPT: Q3905 (group theory) ✓ harvested; Q3907 (Kubert bridge) ✓ research harvested;
  Q3906 (Diophantine N18/N21) still processing; Q3915 (Z2×Z10 embedding) still processing.
- status update 08:00:
  CyclicExclusion15: fixed false `no_tate_order5_psi3_root_solution` (commit 3b0e38e6).
  ChatGPT Q3915 + Q3918 (Z2×Z10 embedding): structure correct (coprod + fin_cases),
  `eq_five_nsmul_of_order_two_mem_zmultiples` + `coprod_zmod_two_ten_injective` received,
  tactic details need debugging (ZMod↔ℤ conversion, simp lemmas).
  Q3906 (Diophantine) still running at ~29min extended thinking.
  Found CyclicExclusion15 no_tate_order5_psi3_root_solution FALSE (b=-2 x=-1 counterexample), fixed.
- status update 08:10:
  eq_five_nsmul_of_order_two_in_zmultiples: COMPILES (commit 6734e097).
  Key independence lemma for Z2×Z10 embedding.
  Q3906 (Diophantine) git-drop failed after 40min, re-dispatched.
  Total: 120 sorry, 27 axiom.
- status update 08:15:
  Q3921 (Diophantine N18) answered: X₁(18) is genus 2, proof needs Chabauty.
  F9=0 parametrizes as c=t²(t-1), b=t²(t-1)(t²-t+1), reducing to single
  curve G(t,X)=0 which is an affine model of X₁(18).
  no_obstruction18 and no_obstruction21 should remain as axioms (genus-2 Chabauty
  is beyond current Lean infra).
- status update 09:15:
  Z2×Z10 injective embedding COMPILES (commit fa82cf3b).
  RationalPointsN14 + DescentBridgeN14 wired (commit cef30929, needs remote build).
  ChatGPT Q3935: cyclic-14 Kubert bridge uses different curve (j-invariants differ).
  Prepared code closes 3 sorry + 1 axiom if remote build passes.

## Run 2026-07-08 14:00 (automode: clear remaining sorry)
- doctrine version: Clear remaining 12 MazurProof sorry's
- approval: /automode command
- starting avenue: (a) CyclicExclusion14/16 Kubert bridges
- status update 10:30:
  All avenues analyzed. All 12 sorry need substantial infrastructure.
  ChatGPT: Q3946 ✓ Q3947 ✓ Q3950 pending.
  Mathematical roadmap complete for all 12 sorry.
- end: 2026-07-08 10:30
- final result: THIS SESSION TOTAL: 7 sorry closed + 1 axiom discharged + 1 fix.
  12 remaining sorry classified. Codex dispatch pending per role-division.
  Mathematical research harvested: Kubert bridge (N14/N16), X₁(18) genus-2 analysis.
  ChatGPT: 5 questions dispatched, 4 answers harvested (1 git-drop fail → re-dispatched).
  Total: 125→120 sorry, 27 axiom.

## Run 2026-07-07 22:30
- doctrine version: Mazur axiom elimination (rewritten)
- approval: /automode command
- starting avenue: (a) arithmetic foundation + Phase 0 decomposition
- status update 2026-07-08 00:30:
  Phase 0 DONE (3 files, 0 sorry): TateNFDivision + CyclicOrderArithmetic + CyclicOrderAssembly.
  Monolithic axiom decomposed into 13 named sub-axioms.
  Scaffolding committed: CyclicExclusion{18,20,21,27} (4 new files, ~14 sorry total).
  ChatGPT channels active: flt1 = N14 scaffold, flt2 = N27 scaffold (may be stuck).
- end: 2026-07-08 01:30
- final result: Phase 0 DONE + all scaffolding + CyclicExclusion27 sorry CLOSED.
  9 commits, 12 new files. 1 monolithic axiom → 13 named sub-axioms.
  ChatGPT flt2 git-drop unstable (3+ consecutive failures).

## Run 2026-06-19 01:30
- doctrine version: DOCTRINE.md written this session
- approval: /automode command msg_id 11362 + 我睡了. 你自己执行
- starting avenue: (a) squareclass bypass
- workers: dm1 (b99vgar9x), dm2 (b0051ml2y), Codex (tmux)
- end: <pending>
- final result: <pending>

## Status update 2026-06-19 02:30
- ALL mathematical content proved (0 sorry in each piece file)
- Assembly compiles with 2 sorry (Rat API wiring only)
- 2 axioms in assembly are PROVED in separate files (Descent20a4, CoprimeSqDvd)
- Key breakthrough: p=-1 case doesn't need quartic — b⁴|(b²-1) gives b=1 directly
- Remaining: wire Rat.num/den API to connect rational u to integer descent chain

## Status update 2026-06-19 05:30
- rat_sq_int_implies_den_one: PROVED (15 lines, 0 sorry)
- CoprimeSqDvd: PROVED (28 lines, 0 sorry)  
- FourthPowerSplit: PROVED (76 lines, 0 sorry)
- Assembly skeleton: compiles, 1 sorry (u.den=1 wiring)
- p=1 case math DONE (w²<0), Lean cast issues remain (5 errors)
- p=-1 case math DONE (b⁴|(b²-1) → b=1), Lean wiring pending
- |p|≥2 case: axiomatized (num_abs_le_one). Needs valuation argument.
- Git-drop connector broken since ~midnight. ChatGPT answers not landing.
- Codex: stdin-not-a-terminal issue with nohup exec. Not usable.
- Avenue (a) partially successful: cover trick + coprime_sq_dvd bypass most complexity
- Remaining work: ~50 lines of Rat API cast plumbing to close the last sorry

## Status update 2026-06-19 21:35 (Opus 4.8)
- ObstructionComplete: 0 sorry, 4 axioms (3 now PROVEN separately):
  - int_solutions_20a4 ✓ (Descent20a4.lean)
  - coprime_sq_dvd ✓ (ChatGPT: q|b² ∧ b²|q → q=b²)
  - isSquare_of_isSquare_cube ✓ (ChatGPT: Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow)
  - num_abs_le_one ⬜ = the full quartic descent (= no_denominator_quartic)
- Descent chain gaps remaining:
  - ZPhiDescentOddFinal: 2 pythagorean axioms (left5/right5) — closeable via FourthPowerSplit+PythagoreanDescentTail (both proven)
  - CoprimeFactorSplit: 1 UFD axiom (coprime product = 4th power)
  - ZPhiDescentStep: 2 sorry (odd/even core wiring)
- Dispatched: ChatGPT pipe (left5), Codex (right5 + UFD axiom)
- KEY: FourthPowerSplit + PythagoreanDescentTail both 0-sorry → left5/right5 are pure assembly

## Run 2026-06-20 (automode)
- goal: close odd_core last sorry → discharge obstruction_curve_20a4
- starting avenue: (a) Codex session 019ee381
- approval: explicit /automode launch (do-not-ask)
- end: TBD

## Run 2026-06-20 RESULT
- obstruction_curve_20a4_points_degenerate DISCHARGED (theorem, 0 custom axiom).
- Chain: odd_core(b61d0ab) -> W1 DenominatorQuartic(d222a81) -> W2+W3 ObstructionComplete(141582b) -> W4 DescentBridge(5e6a0a2). left5 earlier d271fa6.
- #print axioms at every node = [propext, Classical.choice, Quot.sound].
- Caveat: scratch oleans not yet in lake globs; verified via lake env lean w/ prebuilt oleans.
- Next: fold scratch into build graph; remaining 11/12 Mazur axioms.

## Run 2026-06-20 RESULT #2
- obstruction_curve_N12_points_degenerate DISCHARGED (theorem, 0 custom axiom, #print verified).
- Crux was not_ljunggren_14 (z²=x⁴+14x²y²+y⁴ no nontrivial sol) — fresh Pellian descent (48y⁴), 1104 lines (a134637).
- + Lemma B (SquareStep014), Lemma A (FourSquaresAP), ObstructionN12 squareclass assembly (d9829b0).
- TWO Mazur axioms now discharged tonight: obstruction_curve_20a4 + obstruction_curve_N12.
- Remaining obstruction_curve family: N14, N16 (same shape as N12 — Ljunggren/Lemma A/B machinery is the template).

## Run 2026-06-20 RESULT #3
- obstruction_curve_N16_points_degenerate DISCHARGED (0 axiom, #print verified). Partial-2-torsion, mirrored 20a4 (DescentN16 + DenominatorQuarticN16 683-line quartic descent + reused ObstructionComplete/CoprimeSqDvd/IsSquareCube). commit dac126b.
- THREE obstruction_curve axioms discharged: 20a4, N12, N16. Remaining: N14 (full-2-torsion, torsion-only).

## Run 2026-06-20 RESULT #4 — obstruction_curve FAMILY COMPLETE
- obstruction_curve_N14_points_degenerate DISCHARGED (0 axiom, #print verified). Full-2-torsion, reused Lemma A/B (SquareStep014+FourSquaresAP), 1924-line case analysis. commit 1ac9661.
- ALL FOUR obstruction_curve axioms discharged tonight: 20a4, N12, N16, N14. #print clean each.
- Remaining Mazur axioms: Z2xZ10/12/14/16_gives_non_degenerate_*_point (group-theory side), + Axioms.lean trio (rational_torsion_two_invariant_factors, weil_pairing_primitive_root, no_rational_point_of_order_ge_17).

## Run 2026-06-20 RESULT #7 — N=12 CASE COMPLETE
- Z2xZ12_gives_non_degenerate_N12_point DISCHARGED (0 axiom, fresh-olean #print verified). Tate order-12 normalization (6P group law) + explicit 2-isogeny E_X(24a4)→E_N12 + R12/K12 branch + 5 non-degeneracy eliminations. commit 61df088.
- no_Z2_cross_Z12_from_descent now 0 custom axiom → COMPLETE N=12 case (both halves).
- TALLY: 7 axioms discharged (13→6). TWO complete cases: N=10 + N=12.
- Remaining 6: Z2xZ14/16 forward (genus 4/5 obstruction, our curves to restructure to the elliptic quotient), rational_torsion + weil_pairing (KEYSTONE: n-torsion + Weil pairing via FLT/EllipticCurve/Torsion.lean 10 sorries + Route C), mordell_weil_fg (Mordell-Weil thm), no_rational_point_of_order_ge_17 (Mazur core).
- NEXT: keystone (Torsion.lean).

## Run 2026-07-18 01:30 (automode: N25/N49 axiom attack)
- doctrine version: DOCTRINE.md (7 axioms, N18 ported, build in progress)
- approval: /automode 我睡觉你自主做
- starting avenue: (a) build verification + commit, then (b) N25/N49 per Fable oracle
- Fable oracle strategy (R1):
  * N49: X₀(49) = 49a1 elliptic curve, rank 0, MW = ℤ/2. 2-isogeny descent.
  * N25: Cyclic quintic cover, z⁵ = h(t) over ℚ(ζ₅), ℤ[ζ₅] PID arithmetic.
  * Step 0 CRITICAL: verify axioms are literally true FIRST (cusp check).
- ChatGPT: Q45-48 all connector-timed-out, waiting for git-drop
- end: <pending>
- final result: <pending>

## Run 2026-08-11 23:29 (automode: N25 Koszul comparison)

- doctrine hash: `d40ba62f830c145d68fdc2b7570a2f5f87cd00be57342f9cbc4035ca9191e513`
- approval: Xiang's explicit instruction to continue autonomously and use ChatGPT
- starting avenue: (a) vertical-open restriction/direct-image base change,
  followed by chartwise detection of the canonical comparison kernel
- fallback: direct affine-chart kernel vanishing through the proved quotient
  equivalences and affine tilde fully faithfulness
- ChatGPT bridge at launch: the `flt` group reported no registered channels;
  local proof work continues while bridge health is checked without changing
  any tmux session or window name
- terminal condition: construct and audit an `IsIso` instance for
  `ambientGlobalKoszulQuotientToCurve`, or record a verified Mathlib/API
  obstruction together with the next concrete attack vector
- result: the terminal condition is met.  A generic vertical-open
  Beck--Chevalley isomorphism and its structure-map naturality identify the
  restricted curve target on each affine chart.  The explicit equation
  quotient sheaf is identified with that target via affine global sections,
  the local geometric right Koszul complex is exact, and restriction--stalk
  descent proves global geometric exactness.  Cokernel uniqueness gives
  `ambientGlobalKoszulQuotientIsoCurve` and an `IsIso` instance for the
  canonical comparison.
- ChatGPT bridge remained unavailable because the `flt` group had no
  registered channels; no tmux names were changed and no unrelated channel
  was borrowed.
- verification: the 8596-job Lake target build and 4011-job repository-wide
  build passed.  Fresh axiom audits of the base-change theorem,
  quotient-target compatibility, local/global geometric exactness,
  comparison equality, and `IsIso` instance contain only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Run 2026-08-12 (automode: shifted N25 ambient Koszul resolution)

- approval: Xiang's explicit instruction to continue the Mazur proof and use
  ChatGPT where available
- ChatGPT bridge: the `flt` group still reports no registered channel; no
  tmux name was changed and no unrelated project channel was borrowed
- result: `RationalPointsN25QuotientTwoAmbientKoszulShifted.lean` constructs
  the normalized shifted quadric--cubic Koszul sequence for every integer
  debt `d` and proves exactness at both middle and terminal terms
- proof shape: direct Cech descent at debts `d+5`, `d+2`, `d+3`, and `d`;
  comparison with the affine regular-sequence complex on each coordinate
  chart; global descent through restriction and stalks; categorical cokernel
  at the terminal term
- verification: the 8597-job target build passed.  Fresh `#print axioms`
  checks for global multiplier commutativity, global left exactness, and
  global right exactness contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- next attack: specialize `d = -1` and identify its terminal quotient with
  `i_* O_C(1)`, then feed that effective hyperplane twist into the
  determinant/adjunction seam

## Run 2026-08-12 (automode: shifted N25 geometric quotient)

- approval: Xiang's explicit instruction to continue the Mazur proof and use
  ChatGPT to save local model usage
- ChatGPT bridge: the canonical script still reports no channel registered
  for the `flt` window; no tmux name was changed and no unrelated project
  channel was borrowed
- result: `RationalPointsN25QuotientTwoAmbientKoszulPullback.lean` identifies
  every categorical shifted quotient `Q_d` with the genuine geometric target
  `i_* i^* O(-d)`; in particular `Q_{-1} ≅ i_* i^* O(1)`
- proof shape: arbitrary-scheme pullback of the structure module; pullback
  Beck--Chevalley derived by iterated mates; chartwise conjugation of the
  global adjunction unit to the affine closed-immersion structure map; local
  Koszul exactness; restriction--stalk descent; sheaf-level epimorphism and
  cokernel uniqueness
- verification: the 8598-job target build passed, and fresh axiom audits of
  the generic pullback/base-change layer, global exactness, cokernel witness,
  quotient comparison, and final `IsIso` instance contain only `propext`,
  `Classical.choice`, and `Quot.sound`
- endpoint ledger: unchanged at four custom axioms; next attack is the
  determinant/adjunction identification `ω_C ≅ i^* O(1)`
- endpoint verification: a fresh 8775-job rebuild of `MazurEndpointAudit`
  reports exactly those four custom axioms and no `sorryAx`
