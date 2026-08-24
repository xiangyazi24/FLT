## Run 2026-08-19 — N13 class_eq_iff circularity break

- doctrine version: four endpoint axioms (DOCTRINE.md)
- starting avenue: (a) Direct CanonicalMappedSpecialFamily for ⊥ via baseLine saturation
- end: 2026-08-19
- final result:
  - 2 sorry → 1 sorry in N13DischargeWiring.lean
  - N13TrivialKernelFamily.lean: CanonicalMappedSpecialFamily ⊥ WITHOUT class_eq_iff (0 sorry)
  - FirstJetDoublingCompatibility PROVED (z=0, coord=0, trivial)
  - NSeparated ⊥ 2 PROVED (from family + FJDC)
  - REMAINING: class_eq_iff (well-definedness of specialization for ALL SpreadLines)
  - GAP ANALYSIS: affine ideal matching works via contraction retract for saturated Lines;
    infinity ideal matching via overlap_eq is unproved. Fork investigation confirmed no
    existing theorem connects toSpecialPic to toGenericPic for arbitrary Data objects.
  - Two commits: 4b16178 (family+FJDC), 7c8b2b0 (wiring FJDC elimination)

## Run 2026-08-18 17:00 (Newton polygon + wiring campaign)

- doctrine version: four endpoint axioms; N49/N13 focus
- starting avenue: N49 Newton polygon analysis + N13 wiring
- end: ongoing
- final result:
  - 7 commits on ai-scratch (dab52c1..60e3858)
  - N49: H_49 fully computed (3526 terms), 8/9 charts closed at p=2
  - N49: Q5293 confirms local approach BLOCKED (genuine Q₂ points exist)
  - N49: Q5294 identifies X_0(49)=49a1 route (genus 1, E(Q)=Z/2)
  - N13: h₁/h₃ gap trivially closed for kernel=⊥
  - N13: |J(F_5)|=19 computed (Jacobian isomorphism at p=5)
  - N13: N13DischargeWiring.lean builds (8836 jobs, 2 sorry)
  - N13: n13_affine_x_is_cuspidal matches axiom type
  - Remaining: class_eq_iff (J(Q)→J(F_2) injectivity)
  - ChatGPT: Q5293-Q5298 dispatched (3 answered, 3 pending)

## Run 2026-08-18 (N49 + N13 axiom closure, ChatGPT-as-workhorse)

- doctrine version: four endpoint axioms; N49/N13 focus
- approval: automode 继续推动
- starting avenue: (c) N49 explicit rational-point obstruction + (b) N13 wiring
- ChatGPT: saturate all 6 tabs with N49/N13/p≥23 research
- banked: RationalPointsN49.lean (preΨ'_7 factorization, 0 sorry)
- end: 2026-08-18 ~10:30
- final result:
  - 5 commits on ai-scratch (6a12efb..eefed37)
  - RationalPointsN49.lean: preΨ'_7(0) factorization (0 sorry)
  - RationalPointsN49Composition.lean: 7P composition framework (1 sorry)
  - N49_PROOF_PLAN.md: complete proof strategy with Newton polygon
  - FLT_MAZUR_STATUS.md: complete axiom inventory
  - 8 ChatGPT answers archived (Q5265-Q5284)
  - N49 proof path fully mapped: 6/9 bihomogeneous charts excluded,
    Newton polygon has 13 vertices, 11 valuation rays need iterated
    refinement (finite computation, delegable to Wolfram)
  - N13 wiring confirmed as most tractable axiom (Q5270)
  - p≥23 confirmed no shortcut (Q5269)
  - H_49(t,t) = -t^157 (diagonal is a pure monomial, excludes b=c)
  - H_49 mod 2 computed via Sage: 1603 terms, min total degree 98
  - Second-stage Newton analysis: degree-99 terms dominate after diagonal
    blow-up (Q5285 correction). Q5288 (corrected computation) pending.
  - RationalPointsN49Composition.lean: 7P coordinates + composition (1 sorry)
  - ChatGPT: 12 questions dispatched (Q5265-Q5288), 11 answers received

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

## Run 2026-08-20 00:37 CDT

- doctrine version: `249e693f40fb196f4ccffd84002152949059b328`
- approval msg_id: unavailable in the Codex conversation
- starting avenue: (a), continue the N25 canonical-geometry route from the
  verified shifted geometric quotient `Q_{-1} ≅ i_* i^* O(1)` to the
  adjunction identification `ω_C ≅ i^* O(1)` and its Riemann--Roch consumer
- ChatGPT role: use all live `flt*` channels as the design/API/feasibility
  workhorse; verify every returned theorem chain against the checked-out
  source and fresh Lake builds
- result: constructed an explicit integral plane-sextic model on the
  characteristic-two `w = 1` chart.  The nested polynomial is monic and
  irreducible (specialization to `x⁴+x+1`), so its `AdjoinRoot` coordinate
  ring is a domain with a fraction field.
- result: proved the exact characteristic-two elimination/reconstruction
  identities for `D=xz+x+z` and `N=x²+xz+z²+z`, constructed the forward
  plane-to-canonical chart map, and constructed the reverse map with
  `y=N/D` after localizing.
- result: proved both compositions and banked the ring equivalence
  `PlaneCoordinateRing[D⁻¹] ≃+* ChartQuotient(3)[D⁻¹]` in
  `RationalPointsN25QuotientTwoPlaneChartLocalization.lean`.
- ChatGPT: rolling Q5322--Q5393 campaign audited the adjunction/Riemann--Roch
  route, rejected several vacuous coordinate-transition and Hilbert-count
  shortcuts, supplied the reconstruction syzygy and the `D = 0` Gröbner
  certificate.  The syzygy and certificate were independently checked;
  several proposed Mathlib names were rejected against local source.  Q5393
  delivered only a 50-byte header and was not re-dispatched over the tab.
- verified next route: localizing alone does not prove the canonical chart is
  a domain.  The independently verified Gröbner basis
  `{x+z³+z², y²+yz, z⁴+z²+z}` makes the boundary quotient
  eight-dimensional; formalizing this finiteness is the next dense-open
  integrality step before function-field divisors.
- verification: target build of the new localization module passed (8586
  jobs), followed by a repository-wide 4011-job build.  Fresh axiom audits of
  irreducibility, elimination, both localized inverse identities, and the
  ring equivalence contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- end: 2026-08-20 (localized plane/canonical equivalence banked)
- final result: the N25 endpoint axiom remains, but the first honest integral
  function-field model and its explicit common principal open are now proved;
  no endpoint axiom was repackaged or weakened.

## Run 2026-08-20 (N25 plane-chart boundary finiteness)

- approval: Xiang's explicit instruction to continue the FLT project and use
  ChatGPT as the workhorse
- starting avenue: formalize the verified `D = 0` Gröbner certificate and
  make the boundary quotient finite over `F₂`
- result: added
  `RationalPointsN25QuotientTwoPlaneChartBoundary.lean`.  Three exact
  characteristic-two polynomial certificates prove
  `x+z³+z²=0`, `y²+yz=0`, and `z⁴+z²+z=0` in the boundary quotient.
- result: constructed a two-stage monic `AdjoinRoot` tower, first of degree
  four in `z` and then of degree two in `y`; explicit coordinate lifts prove
  that its algebra map to the boundary is surjective.  The resulting theorem
  `canonicalWChartBoundary_moduleFinite` proves
  `Module.Finite (ZMod 2) (ChartQuotient(3)/(D))` structurally.
- ChatGPT: Q5421 and Q5423 were read and independently audited.  Their useful
  parts guided the monic-tower organization and isolated the true next seam;
  invalid quotient-direction and specialization suggestions were discarded.
  Q5422 and Q5424 delivered only 248-byte and 344-byte Notion headers, so no
  mathematical or API claim was taken from them and neither question was
  silently re-dispatched.
- verification: strict single-file checking, the 8587-job target build, and
  the repository-wide 4011-job build passed.  Fresh axiom audits of all three
  elimination relations, tower surjectivity, and boundary finiteness contain
  only `propext`, `Classical.choice`, and `Quot.sound`; the bypass scan is
  clean.
- verified next route: boundary finiteness is not itself a proof that `D` is
  regular.  A local symbolic saturation check gives `(q,c):D∞=(q,c)`; the
  next bankable theorem is the source-level colon identity or an equivalent
  injectivity proof, followed by integrality of the whole canonical chart.
- final result: the N25 endpoint axiom remains unchanged; the finite-boundary
  prerequisite for the dense-open integrality argument is now formalized.

## Run 2026-08-20 (N25 canonical plane-chart integrality)

- approval: Xiang's explicit instruction to continue the FLT project and use
  ChatGPT as the workhorse
- starting avenue: replace the remaining colon/saturation seam by a direct
  source-level proof that the projection denominator is regular on the whole
  canonical `w = 1` chart
- result: added
  `RationalPointsN25QuotientTwoPlaneChartDomain.lean`.  In the separated ring
  `F₂[z][x]`, the linear denominator `D=(z+1)x+z` is prime and the monic
  numerator `N=x²+zx+z²+z` is nonzero modulo `(D)`.
- result: proved a reusable elementary quotient-swap lemma for regular
  elements.  Together with freeness of a monic `AdjoinRoot` extension, it
  proves `D` regular modulo the chart's quadric and cubic equations.
- result: explicit affine-variable, polynomial-tower, and double-quotient
  equivalences identify that presentation with `ChartQuotient 3` and carry
  its denominator to the intrinsic canonical denominator.  Consequently the
  canonical localization map is injective and `canonicalWChart_isDomain`
  proves `IsDomain (ChartQuotient 3)`.
- ChatGPT: Q5481 supplied the useful elementary quotient-swap organization;
  its quotient constructor details were corrected against the local Mathlib
  API and rebuilt.  Q5491 contained inaccurate signatures and was rejected.
  Q5483, Q5495, and Q5498 delivered only short headers or an uncompiled
  admission, so no claim from them was used.
- verification: the 8588-job module target and repository-wide 4011-job
  default build passed.  Fresh axiom audits of primality, numerator
  nonvanishing, quotient regularity, canonical denominator regularity,
  localization injectivity, and final chart integrality contain only
  `propext`, `Classical.choice`, and `Quot.sound`; the bypass scan and
  `git diff --check` are clean.
- final result: the possible hidden `D`-torsion/component is eliminated and
  the common principal-open model now connects integral domains.  The N25
  endpoint axiom remains unchanged; the next route is the height-one
  valuation/principal-divisor interface needed for Riemann--Roch.

## Run 2026-08-20 (N25 ambient twist restriction)

- approval: Xiang's explicit instruction to restore the current FLT proof
  campaign and keep all ChatGPT bridge tabs occupied
- repository recovery: verified `/home/xhuan5/repos/flt-ai` as the active Git
  worktree, preserved the local N13 and N25 edits, merged the three current
  N25 plane-chart commits from `xiang/ai-scratch`, and pushed merge commit
  `7133cc401b` without touching the unrelated untracked worktree files
- result: normalized both ambient and curve Čech evaluations around the
  forward equalizer map and proved that the degree-one coordinate ratio is
  preserved under graded base change
- result: proved affine structure-sheaf naturality for scalar automorphisms
  under arbitrary `Spec.map`, then used it to prove that the pulled-back
  ambient overlap transition equals the curve overlap transition
- result: banked `curvePullbackTwistOverlapIso` and
  `curvePullbackTwistChartIso`, identifying the actual ambient restriction
  with the curve-side rank-one twist model on every overlap and chart
- ChatGPT: Q5672--Q5704 were rolled across all live tabs.  Q5672 correctly
  supported the forward equalizer normalization; several later replies could
  not access the local worktree and were treated only as route audits, with
  every API claim checked locally.  Q5671 suffered connector timeout and was
  not re-dispatched over the still-running tab.
- verification: the 8603-job target build passed.  Fresh axiom audits of the
  affine generator naturality, pullback scalar naturality, ratio transition,
  and overlap compatibility contain only `propext`, `Classical.choice`, and
  `Quot.sound`; the bypass scan and `git diff --check` are clean.
- verified next route: construct the chartwise adjunction-unit map into
  `twistCechSource`, prove its two overlap projections agree using the new
  transition theorem, lift through `globalTwistModule`, and prove the lift is
  an isomorphism.
- final result: the N25 endpoint axiom remains unchanged; the local
  ambient-to-curve twist restriction seam is closed without `sorry`, new
  axioms, or `native_decide`.

## Run 2026-08-20 (N25 global ambient/curve twist comparison)

- approval: Xiang's explicit instruction to continue the autonomous Mazur
  campaign, use ChatGPT proactively, verify locally, build, audit, and commit
- starting avenue: lift the four chartwise ambient-to-curve twist maps through
  the curve Čech equalizer and prove that the global lift is an isomorphism
- result: added
  `RationalPointsN25QuotientTwoAmbientTwistGlobalComparison.lean`.  Reusable
  two-square Beck--Chevalley coherence lemmas identify the inverse base-change
  component with the restriction unit and handle the congruence between the
  named right overlap and its iterated-restriction presentation.
- result: both ordered overlap restrictions of every chart map are normalized
  to the ambient transition pair.  Their compatibility constructs
  `curvePullbackTwistToCechSource`, which lifts uniquely to
  `curvePullbackTwistToGlobalTwist` through the existing equalizer.
- result: the lift restricts on every standard chart to the verified local
  isomorphism.  Restriction--stalk compatibility and the four-chart cover prove
  `curvePullbackTwistToGlobalTwist_isIso`, yielding the packaged global
  isomorphism `curvePullbackTwistGlobalIso`.
- ChatGPT: Q5814 was dispatched through `ask-gpt.py` for an independent API and
  route audit.  All connectors timed out while the tab could still be running,
  so it was not re-dispatched and no mathematical or API claim from it was
  used.
- verification: strict single-file checking, the 8608-job module target, and
  the repository-wide 4011-job build passed.  Fresh axiom audits of the generic
  base-change congruence and unit laws, Čech compatibility, global `IsIso`, and
  packaged isomorphism contain only `propext`, `Classical.choice`, and
  `Quot.sound`; the bypass scan is clean.
- final result: `[MZ-N25-CECH-COMPARE]` is closed without `sorry`, new axioms,
  or `native_decide`.  The four endpoint axioms remain unchanged; the ready
  N25 frontier is the determinant/adjunction bridge `ω_C ≅ O_C(1)` followed by
  the explicit divisor and middle-degree Riemann--Roch interfaces.

## Run 2026-08-21 (N25 adjunction descent)

- doctrine version: `7274fc9b6d11efe825eef6851ae5f8cfe972dfde6798701cfd1a677f622c2e14`
- approval: Xiang's explicit instruction to continue the current task
  autonomously and keep using ChatGPT for hard mathematical and design work
- starting avenue: promote the proved chartwise `(2,3)` adjunction transition
  to a global Čech comparison tied to the effective curve twist
- result: added the generic theorem `ratioPowerTransition_trans`, proving that
  composition of rank-one transition functions adds integral exponents
- result: added
  `RationalPointsN25QuotientTwoAdjunctionDescent.lean`.  It identifies the
  existing ambient-canonical/inverse-conormal calculation with the exponent
  identity `4 + (-5) = -1`, lifts it through affine tilde, and constructs the
  resulting Čech arrow and equalizer.
- result: proved that the adjunction Čech arrow is literally
  `twistCechLeft (-1)`.  The transition-defined line is therefore globally
  isomorphic to `globalTwistModule (-1)`, to the actual pullback of the ambient
  hyperplane twist, and locally to the unit module on every standard chart.
- ChatGPT: Q5814 still has no git-drop and was not re-dispatched.  A new
  independent adjunction-design request through the canonical `ask-gpt.py`
  exited before dispatch because the current `flt` window has no configured
  channel; it produced no Q number or answer, and no claim from ChatGPT was
  used.
- verification: strict single-file checking, the 8609-job module target, and
  the repository-wide 4011-job build passed.  Fresh axiom audits of exponent
  composition, the transition identity, the Čech-arrow equality, both global
  isomorphisms, and the local trivialization contain only `propext`,
  `Classical.choice`, and `Quot.sound`; the bypass and whitespace scans are
  clean.  The source-rebuilt 8775-job endpoint audit still reports exactly the
  four established custom axioms and no `sorryAx`.
- end: `[MZ-N25-ADJUNCTION-DESCENT]` proved
- final result: the transition-function prerequisite for projective
  adjunction is closed without defining a dualizing sheaf to be `O_C(1)`.
  The remaining seam is to construct the canonical/dualizing object and prove
  that its local trivializations induce this verified descent datum.

## Run 2026-08-21 (N25 affine canonical differentials)

- doctrine version: `8b3a36ac87fa766acde538b13596aae63e3074269d021ae206eeaefb2edd8336`
- approval: Xiang's explicit instruction to continue the current task
  autonomously, use ChatGPT for hard mathematical and design questions, verify
  locally, and preserve the repository comment discipline
- starting avenue: construct an honest local canonical object from the smooth
  affine complete-intersection presentations, rather than naming the already
  known twist as a dualizing sheaf
- result: added the generic commutative-ring theorem
  `LinearMap.ker_crossProductFunctional`.  If two rows in `R^3` have a
  unimodular cross product, dot product with that vector is surjective and its
  kernel is exactly the span of the rows.  The proof uses the vector
  triple-product identities and requires no field or domain hypothesis.
- result: added
  `RationalPointsN25QuotientTwoAffineCanonicalDifferentials.lean`.  On every
  standard chart it identifies the cross-product components of the affine
  quadric and cubic gradients with the three selected Jacobians, including
  the alternating middle sign, and converts the existing unit-ideal
  smoothness certificate into an explicit Bézout vector.
- result: reindexed the actual presentation cotangent-space basis by the three
  non-pivot coordinates, proved that the two relation classes span the
  conormal module, and proved their differential coordinates are exactly the
  two Jacobian rows.  Exactness of the cotangent sequence then shows that the
  pulled-back residue functional and the projection to `Ω¹_{B/k}` have the
  same kernel.
- result: the first isomorphism theorem constructs
  `chartKaehlerDifferentialEquiv : Ω¹_{B/k} ≃ₗ[B] B`, characterizes its
  value on every ambient differential class, and supplies the singleton basis
  `chartKaehlerDifferentialBasis` for each ordinary affine curve chart.
- ChatGPT: dispatched Q5910 through the canonical `ask-gpt.py` bridge for an
  independent derivation of the residue-basis overlap power.  The request was
  accepted by `flt10` and remained `processing`; no authoritative git-drop was
  available during this run, it was not re-dispatched, and no ChatGPT claim
  was used in the proofs.
- verification: the strict single-file check and the 8585-job module target
  pass, as does the repository-wide 4011-job build.  Fresh axiom audits of the
  generic kernel theorem, Jacobian span and kernel identities, cotangent
  coordinate comparison, conormal spanning, common-kernel theorem, final
  Kähler equivalence, its computation rule, and the free-module theorem all
  report exactly `propext`, `Classical.choice`, and `Quot.sound`.  The bypass,
  long-line, whitespace, and comment scans are clean.  The source-rebuilt
  8775-job endpoint audit still reports exactly the four established custom
  axioms and no `sorryAx`.
- end: `[MZ-N25-AFFINE-CANONICAL]` proved
- final result: the four local canonical modules and residue bases now exist
  as actual Kähler differentials.  The remaining adjunction seam is the
  ordered-overlap base-change calculation proving their ratio is the already
  verified exponent `-1` transition.

## Run 2026-08-21 (N25 homogeneous chart canonical differentials)

- doctrine version: `8b3a36ac87fa766acde538b13596aae63e3074269d021ae206eeaefb2edd8336`
- approval: Xiang's instruction to continue the current task autonomously,
  retain ChatGPT as a mathematical workhorse, and verify every result locally
- starting avenue: remove the remaining distinction between the ordinary
  affine quotient presentations carrying the residue bases and the actual
  degree-zero homogeneous coordinate rings used by projective descent
- result: added `FLT/Mathlib/RingTheory/Kaehler/AlgEquiv.lean`.  A bijective
  algebra map is proved to induce a bijection on relative Kähler
  differentials by computing the kernel through the standard finitely
  supported presentation.  Algebra equivalences are then packaged as
  semilinear equivalences of their differential modules.
- result: added
  `RationalPointsN25QuotientTwoCanonicalDifferentialCharts.lean`.  The four
  existing affine-to-homogeneous ring equivalences are upgraded to algebra
  equivalences over `ZMod 2`, and the explicit rank-one Kähler equivalences
  are transported to the actual rings of the projective charts.
- result: proved that the transported coordinate functional applied to a
  transported affine differential is exactly the affine Jacobian residue
  coordinate mapped through the chart algebra equivalence.  This pins the
  actual singleton bases to the computed residues and rules out an unrelated
  choice of local generator.
- result: added `FLT/Mathlib/RingTheory/Kaehler/FormallyEtale.lean`, which
  base-changes a chosen Kähler coordinate through a formally étale algebra and
  computes its value on the image of a source differential.
- result: added
  `RationalPointsN25QuotientTwoCanonicalDifferentialOverlaps.lean`.  It
  explicitly casts the propositionally equal homogeneous denominators,
  factors both ordered-overlap projections through genuine `Away`
  localizations, and transports both actual chart residue coordinates to the
  same overlap Kähler module.
- result: the induced rank-one change of coordinate is multiplication by the
  explicit unit `coordinateOverlapResidueUnit`.  The remaining adjunction seam
  is therefore the equality of this unit with the established exponent `-1`
  coordinate-ratio unit.
- ChatGPT: Q5910 was checked again only through the configured git-drop
  branch.  No drop was present; the request was not re-sent and no unverified
  external claim entered the proof.
- verification: strict source checks for all four new modules pass, and their
  module targets produced `.olean` files.  Fresh axiom audits of the generic
  bijection, semilinear and formally étale transports, actual chart and
  overlap Kähler equivalences, coordinate comparisons, transition formula,
  and transition unit report exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- end: `[MZ-N25-CHART-CANONICAL]` and
  `[MZ-N25-OVERLAP-LOCALIZATION]` proved
- final result: only the explicit equality between the localized residue
  transition unit and the existing exponent `-1` adjunction unit remains.

## Run 2026-08-21 (N25 residue-minor overlap transition)

- doctrine version: `ae54d6386238edaa718564c9f3989c48395736ba95a36434e41f03fae67e6642`
- approval: Xiang's instruction to continue the current task autonomously,
  retain ChatGPT as the workhorse for hard design questions, and verify every
  proposed identity locally
- starting avenue: compute the actual overlap change of the localized
  Kähler-residue coordinates and reduce it to homogeneous Jacobian minors
- result: made the coordinate class definition reducibly identical to the
  graded quotient image.  This removes the proposition-only denominator cast
  and lets the actual projective chart ring map directly to the ordered
  localization without a redundant formally étale identity stage.
- result: proved that dehomogenizing and then rehomogenizing a homogeneous
  polynomial gives its canonical chart fraction, and identified every affine
  Jacobian cross component uniformly with the chart image of an ambient
  polynomial minor.
- result: proved every ambient Jacobian minor homogeneous of degree three.
  The two ways of omitting an ordered pair of chart pivots select the same
  complementary minor; the proof uses only injectivity of `Fin.succAbove`,
  the four-coordinate pigeonhole constraint, and symmetry of minors in
  characteristic two.
- result: proved the general homogeneous chart transition and specialized it
  to the selected Jacobian crosses.  Consequently the left residue of
  `d(X_j/X_i)` equals the cube of `X_j/X_i` times the right residue of
  `d(X_i/X_j)`.
- result: derived from the universal Leibniz rule that
  `d(X_j/X_i) = (X_j/X_i)^2 d(X_i/X_j)` in characteristic two.  Combining
  this with the cubic minor transition proves the predicted single-ratio
  relation between the two residue evaluations on `d(X_j/X_i)`.
- ChatGPT: Q5910 was checked only through its configured git-drop branch; no
  drop exists and it was not re-dispatched.  A separate cast/naturality design
  audit through canonical `ask-gpt.py` failed before dispatch because the
  current `flt` window has no configured channel, so it produced no Q number
  or answer and no external claim entered the proof.
- verification: strict codegen checks, the 8595-job overlap module target,
  and the repository-wide 4011-job build pass.  Fresh axiom audits of the
  homogeneous rehomogenization, minor homogeneity and complementary-pair
  identity, chart cross formula, generic and specialized overlap transitions,
  inverse-ratio differential formula, and final linear residue relation all
  report exactly `propext`, `Classical.choice`, and `Quot.sound`.  The bypass,
  long-line, whitespace, and comment scans are clean.  The source-rebuilt
  8775-job endpoint audit still reports exactly the four established custom
  axioms and no `sorryAx`.
- final result: the expected exponent `-1` has now been derived on the chart
  ratio differential itself.  The remaining unit identity requires extending
  this equality to a spanning differential family via the already proved
  unimodular Jacobian-cross certificate; no cancellation of a potentially
  vanishing individual minor is assumed.

## Run 2026-08-21 (N25 full residue transition unit)

- doctrine version: `ae54d6386238edaa718564c9f3989c48395736ba95a36434e41f03fae67e6642`
- approval: Xiang's instruction to continue the autonomous FLT campaign,
  keep ChatGPT occupied on hard design questions, verify locally, audit, and
  commit concrete progress
- starting avenue: extend the proved ratio-differential seam to a spanning
  family and identify the full localized Kähler-residue transition unit
- result: extracted the homogeneous Euler minor syzygy and proved its
  right-chart localization.  For four distinct ambient labels it expresses
  the pivot minor by the two remaining minors in characteristic two.
- result: proved the residue transition formula on every affine-coordinate
  differential.  The ratio coordinate uses the inverse-ratio derivative;
  each other coordinate uses Leibniz, the cubic homogeneous minor transition,
  and the Euler syzygy.  The proof never cancels a Jacobian minor.
- result: defined the overlap differential as the Bezout combination of all
  three coordinate differentials.  Its first residue is one by the existing
  unimodular Jacobian-cross certificate, while its second residue is exactly
  `X_i/X_j`.  Hence the transition scalar and transition unit are the inverse
  coordinate-ratio scalar and unit.
- result: normalized the self-overlap separately.  The two localized residue
  equivalences unfold to the same equivalence, so the self transition is the
  identity; the unit theorem now holds for every ordered chart pair.
- verification correction: Lake's cache initially replayed stale artifacts
  while the newly edited source still contained errors.  Strict source
  compilation exposed and fixed the `Fin 4` complement argument, missing
  namespace import, coordinate unfolding, characteristic-two Euler
  rearrangement, local `Algebra`/`SMul` instance diamonds, and self-overlap
  proof.  The four edited sources now pass strict checks.
- ChatGPT: Q5913 supplied an independent Euler-minor/Bezout architecture and
  correctly predicted the final exponent one; Q5918 independently checked
  the exact commutative-ring calculation and its single explicit use of
  `u*v=1`.  Both were used only as design audits and every identity was
  reconstructed in Lean.  Q5922, Q5924, and Q5927 seeded the next honest
  affine-tilde/Čech descent layer; all API claims remain subject to local grep
  and compilation.
- verification: strict source checks for the affine smoothness, affine
  canonical differential, homogeneous chart, and overlap files pass.  Fresh
  axiom audits of the complement-minor theorem, Euler-minor theorem, full
  generator transition, normalized second residue, and final unit identity
  report exactly `propext`, `Classical.choice`, and `Quot.sound`; the bypass
  and whitespace scans are clean.
- end: `[MZ-N25-RESIDUE-UNIT]` proved
- final result: the actual localized Kähler bases now carry exactly the
  previously verified exponent `-1` adjunction cocycle.  The next avenue is
  to apply affine tilde to these actual modules, compare the resulting Čech
  diagram with the existing twist diagram, and prove local effectiveness.

## Run 2026-08-21 (N25 actual Kähler affine tilde)

- doctrine version: `d8930d608ca93a5e70193bd64bdce8199c2312e55b1b72561ce71330965139b5`
- approval: Xiang's instruction to continue the autonomous FLT campaign,
  keep ChatGPT occupied on hard mathematical and design questions, verify
  locally, audit, and commit concrete progress
- starting avenue: lift the actual chart and overlap Kähler modules and their
  residue coordinates through affine tilde, while fixing the overlap
  orientation before constructing a Čech equalizer
- result: strengthened the residue-unit theorem to an equality of full linear
  equivalences.  The change from the first residue frame to the second is
  exactly `Away.ratioPowerTransition` at internal exponent `-1`, hence the
  geometric positive twist `O(1)` transition.
- result: defined the affine tilde sheaves of the actual Kähler modules on all
  four charts and every ordered pair overlap.  The chart residue and both
  ordered-overlap residues induce explicit isomorphisms to rank-one tilde
  modules and their unit sheaves via `LinearEquiv.toModuleIso`,
  `Functor.mapIso`, and `tildeSelf`.
- result: proved that affine tilde carries the full residue transition to the
  existing `coordinateOverlapTwistIso (-1)`.  The right residue tilde frame is
  the left residue tilde frame followed by this twist isomorphism, giving the
  exact commuting-square orientation required by the next Čech comparison.
- ChatGPT: Q5935 and Q5939 supplied independent audits of the covariant tilde
  API and the affine `Spec` construction; Q5936 and Q5938 identified the
  strongest useful overlap orientation certificate; Q5940 independently
  confirmed that no inverse isomorphism is needed and that internal exponent
  `-1` denotes geometric `O(1)`.  All usable claims were checked against the
  local source, and the proposed obsolete `chartTilde` route from Q5934 was
  rejected after local inspection.
- verification: strict source compilation of the modified overlap file and
  the new affine-tilde file passes.  The 8596-job module build passes.  Fresh
  axiom audits of the full linear transition, its affine-tilde image, the
  functorial frame factorization, and the final overlap frame theorem report
  exactly `propext`, `Classical.choice`, and `Quot.sound`; the bypass and
  whitespace scans are clean.
- end: `[MZ-N25-AFFINE-TILDE]` proved
- final result: the actual local Kähler sheaves and the effective `O_C(1)`
  twist now have identical ordered-overlap transition isomorphisms under the
  residue frames.  The next avenue is to assemble the actual Kähler Čech
  source, target, and restriction arrows and compare their equalizer with the
  existing twist equalizer.

## Run 2026-08-21 (N25 canonical Kähler Čech restrictions)

- doctrine version: `ce381aa6b94cef856ae1446ccf50c717e9d6f7c631f268e10343b26d8635edae`
- approval: Xiang's instruction to continue the autonomous FLT campaign,
  keep ChatGPT occupied on hard mathematical and design questions, verify
  locally, audit, record progress, and commit appropriate milestones
- starting avenue: replace the residue-frame-defined overlap restrictions in
  the actual Kähler Čech diagram by canonical localization and formally étale
  base-change isomorphisms
- result: added basis-free affine-tilde infrastructure.  Morphisms from a
  counit-recovered affine module sheaf are determined by normalized top
  sections, Away restriction top sections satisfy the localized-module
  universal property, and restriction framed by arbitrary source and target
  affine coordinates has an explicit generator formula.
- result: constructed canonical left and right restriction isomorphisms from
  the actual chart Kähler tilde sheaves to the actual overlap Kähler tilde
  sheaves.  Their normalized top-section maps send every chart differential
  to the functorial Kähler differential on the overlap.
- result: proved the explicit residue-frame restrictions have the same
  generator formula.  `IsBaseChange.algHom_ext` upgrades equality on the
  localization generators to equality on all top sections, and affine
  `fromTildeΓ` faithfulness upgrades this to equality of the full canonical
  and residue-frame sheaf isomorphisms on both overlap legs.
- result: proved restriction-frame transport is coherent under equality of
  named open immersions.  The public Čech restrictions now refer to the
  canonical isomorphisms; the former residue-frame definitions remain under
  explicit names and are used only through proved comparison theorems.
- result: rebuilt the existing Čech-arrow comparison and equalizer
  equivalences without changing their downstream interface.  The canonical
  Kähler Čech equalizer is therefore isomorphic to the effective `O_C(1)`
  twist, the adjunction transition line, and the pulled-back ambient
  hyperplane twist.  No claim that it is already a dualizing sheaf or the
  sheafification of the relative Kähler presheaf is made.
- ChatGPT: Q6039 supplied the useful performance boundary of separating the
  rank-one restriction calculation from the N25 specialization.  Q6040--Q6042
  independently audited the base-change extensionality, right-leg symmetry,
  and public-name refactor.  Connector-visible answers could not inspect the
  local commit, so all placeholder names and source-level assertions were
  discarded; the implemented lemmas were derived from local source and
  compiled before use.
- verification: strict source checks pass for every changed Lean file.  The
  8619-job canonical Čech module build and repository-wide 4011-job build
  pass.  Fresh axiom audits of the generic frame-coherence and generator
  lemmas, both canonical/frame Spec equalities, both named geometric
  equalities, both Čech-arrow comparisons, and the final global isomorphisms
  report exactly `propext`, `Classical.choice`, and `Quot.sound`.  Bypass and
  whitespace scans are clean.
- end: `[MZ-N25-CANONICAL-CECH]` proved
- final result: the global differential Čech object is now assembled from
  canonical Kähler restriction maps.  The next ranked seam is to compare it
  with the sheafification of the same-site relative Kähler presheaf.

## Run 2026-08-21 (N25 same-site relative differential foundation)

- doctrine version: `f190152f1f945b544e296d88c786643800c21802adb09c9e79578ae72105ed70`
- approval: Xiang's instruction to continue the autonomous FLT campaign,
  keep ChatGPT occupied on hard mathematical and design questions, verify
  locally, audit, record progress, and commit appropriate milestones
- starting avenue: construct the same-site relative Kähler presheaf and
  connect its chart and overlap evaluations to the canonical affine Kähler
  data
- result: added a generic constant-base natural transformation on the small
  Zariski site for any morphism `X ⟶ Spec K`.  Its naturality is proved at the
  stable `Scheme.Hom.appLE_map` boundary without unfolding the structure
  sheaf implementation.
- result: packaged the universal property of Mathlib's objectwise relative
  differential presheaf as an equivalence between module-presheaf morphisms
  and compatible relative derivations.
- result: instantiated the construction for the binary N25 canonical curve,
  named its relative differential presheaf, its associated module sheaf, and
  the canonical sheafification-unit morphism.  This resolves the former base
  category mismatch between the CommRingCat structure presheaf and the
  curve's RingCat module sheaf.
- result: composed the sheafification adjunction with the Kähler universal
  property.  Morphisms from the associated differential sheaf to any curve
  module sheaf now form an explicit equivalence with compatible same-site
  relative derivations, with a named inverse constructor and universal
  associated-sheaf derivation.
- result: on all four standard charts, transported the geometric base map
  through the open-immersion section isomorphism and `ΓSpecIso`, then proved
  it equals the affine `ZMod 2` algebra map by uniqueness of ring homomorphisms
  out of `ZMod 2`.
- result: specialized both canonical ordered-overlap restriction calculations
  to universal Kähler generators.  Each leg sends `d(x)` to the differential
  of the corresponding localized chart section, which is the exact local
  compatibility needed to build the Čech-valued derivation.
- result: extracted the stalk argument used by the earlier ambient-twist
  comparison into a universe-polymorphic theorem: a module-sheaf morphism
  whose restrictions are isomorphisms on every member of an open cover is
  globally an isomorphism.  The ambient-twist proof now applies this theorem
  directly, validating the generic interface on the N25 affine cover and
  removing its duplicated stalk construction.
- ChatGPT: Q6068--Q6070 and Q6072--Q6073 independently selected objectwise
  chart evaluation before global sheaf comparison.  Q6074 identified the
  useful `appLE_map` transparency boundary, Q6077 independently proposed the
  `ZMod 2` uniqueness proof, and Q6080 exposed the module-base and local
  naturality obligations.  Q6084 independently confirmed the final
  composition of the Kähler and sheafification Hom equivalences.  Several
  displayed snippets had reversed arrows, schematic names, or nonexistent
  convenience APIs; those were discarded, and every retained claim was
  reconstructed from the pinned local source.
- verification: strict source compilation passes for all new and refactored
  production files.  The generic relative-differential module's 2344-job
  build, the restriction-cover module's 2542-job build, and the N25 module's
  8621-job build pass.  Fresh axiom audits of the constant-base map, universal Hom
  equivalence, sheafification unit, chart base-map comparison, and both
  overlap generator formulas report exactly `propext`, `Classical.choice`,
  and `Quot.sound`.  The generic cover isomorphism criterion and the
  refactored ambient-twist application have the same clean-3 audit; bypass,
  long-line, whitespace, and comment scans are clean.
- end: `[MZ-N25-RELATIVE-DIFFERENTIAL-BASE]` proved
- final result: the intrinsic same-site relative differential object now
  exists in the same module-sheaf category as the canonical Čech equalizer,
  and its affine base maps and overlap generator restrictions match the
  already verified canonical Kähler data.  The next seam is the compatible
  derivation into the Čech equalizer and the local-isomorphism proof for its
  sheafified transpose.

## Run 2026-08-21 (N25 Čech-valued derivation descent)

- doctrine version: `a9c0fa47eaca65c9e076afca99cf410e5751fd75d2e80a4e90c590a643cea540`
- approval: Xiang's instruction to continue the autonomous FLT campaign,
  use ChatGPT as the workhorse for hard mathematical and design questions,
  verify locally, audit, record progress, and commit appropriate milestones
- starting avenue: assemble compatible chart-valued same-site derivations
  into the actual canonical Kähler Čech equalizer without assuming that the
  sheaf-forgetful functor preserves its chosen limits definitionally
- result: added generic product and equalizer constructors for compatible
  presheaf-valued relative derivations.  Both constructors are obtained from
  the objectwise Kähler universal property, and their projection formulas are
  proved as equalities of full derivations.
- result: made the preservation comparison explicit for the finite product of
  four pushed-forward chart Kähler sheaves.  A family of chart derivations now
  defines a derivation into the actual sheaf Čech source, and postcomposition
  with each sheaf projection recovers the corresponding family member.
- result: made the parallel-pair preservation comparison explicit for the
  canonical Čech equalizer.  Any family whose two overlap composites agree
  now descends to a derivation into `globalKaehlerDifferentialModule`, and
  postcomposition with the equalizer inclusion recovers the Čech-source
  derivation.
- source correction: the forgetful functor preserves the relevant limits but
  its preserved cone is not definitionally the chosen presheaf product or
  equalizer.  Direct rewriting was rejected; the production construction uses
  `PreservesProduct.iso` and `PreservesEqualizer.iso`, with the transparency
  workaround scoped only to the two projection proofs.
- ChatGPT: Q6102--Q6123 independently audited product/equalizer descent,
  sheafification direction, dense-basis isomorphism detection, and affine
  tilde localization.  The product/equalizer architecture and the exact
  `TopCat.Sheaf.isIso_iff_isIso_basis` boundary survived local verification.
  Claims that FLT lacked the canonical restriction wrapper, that derivation
  postcomposition was not definitional, or that basis data alone fed the
  sheafification Hom equivalence were disproved by local source and discarded.
- verification: strict source compilation passes for the generic relative
  differential file and the N25 specialization.  The targeted 8622-job build
  passes.  Fresh axiom audits of all four generic derivation declarations and
  all six N25 product/equalizer comparison and descent declarations report
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- end: `[MZ-N25-CECH-DERIVATION-DESCENT]` proved
- final result: no global Čech limit plumbing remains.  The next obligation is
  exactly the four full-open chart derivations and their overlap equality.
  Local source inspection identifies a concrete route: view the structure and
  tilde sheaves as fixed-base module sheaves, extend basic-open localization
  derivations with `restrictHomEquivHom`, and prove the derivation laws on the
  basic-open basis before pushing them to the canonical curve.

## Run 2026-08-21 (N25 full-site affine derivations)

- doctrine version: `64ee1a5d220465f7352b063f683b92d2d864d6c8a228c219d546899e9abdeb69`
- approval: Xiang's instruction to continue the autonomous FLT campaign,
  use ChatGPT as the workhorse for hard mathematical and design questions,
  verify locally, audit, record progress, and commit appropriate milestones
- starting avenue: construct the four chart derivations required by the
  canonical Kähler Čech descent theorem and isolate their overlap comparison
- result: added the affine universal Kähler derivation on the full small
  Zariski site.  Principal-open derivations are obtained by formally étale
  Kähler base change, their restriction naturality is proved by localization
  extensionality, and sheaf locality extends Leibniz and base-constant
  vanishing from the principal-open basis to arbitrary opens.
- result: added `ModuleCat.Derivation.precomp`, which transports a relative
  derivation through a commutative square of ring maps while restricting the
  target scalars.  This removes the expensive definitional expansion of the
  pushed-forward module action from the N25 chart construction.
- result: constructed all four `coordinateChartDerivation`s as genuine
  compatible same-site derivations into the pushed-forward affine Kähler
  sheaves.  The binary base-square equality on every open follows from
  uniqueness of ring homomorphisms out of `ZMod 2`; presheaf naturality is
  proved from scheme-map naturality and the affine derivation restriction law.
- result: constructed the sixteen `coordinateOverlapDerivation`s directly
  from the affine universal derivation on each ordered overlap.  These provide
  a fixed common target for proving that the left and right canonical Čech
  restrictions agree.
- source correction: a direct `simp` proof of the chart Leibniz and base laws
  exceeded the elaborator budget, and a proposed rewrite through a chart-image
  `appLE` used the wrong source open.  Both were rejected.  The compiled proof
  instead uses the generic precomposition square; no overlap equality or
  transpose is claimed yet.
- ChatGPT: Q6156, Q6158, Q6159, and Q6160 suggested the localization and
  generator architecture.  Local checking rejected several schematic API
  names and the one-line overlap extensionality shortcut.  Q6161--Q6163 were
  asked for the exact extension-by-zero component formula and overlap proof;
  Q6163 explicitly lacked checkout access and supplied no usable code.  The
  surviving architecture was reconstructed from the pinned local source and
  compiled declaration by declaration.
- verification: strict source checks pass for the generic affine differential
  file and the N25 specialization.  The targeted 8623-job N25 module build
  passes.  Fresh axiom audits of derivation precomposition, localization
  extensionality, the full-site affine derivation, both base-square packages,
  and the chart and overlap derivations report no axioms beyond `propext`,
  `Classical.choice`, and `Quot.sound`.
- end: `[MZ-N25-FULL-SITE-DERIVATIONS]` proved
- final result: the chart and direct-overlap derivation families now exist on
  arbitrary opens.  The next exact seam is to prove each canonical
  `pushforwardRestrictionHom` composite equals the corresponding direct
  overlap derivation, first by extracting its sectionwise transpose formula
  and then applying the already proved Kähler generator identities.

## Run 2026-08-21 (extension-by-zero section formula)

- doctrine version: `a06df5dfe4a8341212ec2dbb95a3246e72dce6d1066ceec681c7d969a1afc00c`
- starting avenue: expose the exact section map hidden inside
  `pushforwardRestrictionHomOfHom` so that the chart-to-overlap derivation
  comparison no longer unfolds an adjunction and two pushforward isomorphisms
- result: proved the generic named-composite formula.  On an open `W`, the
  extension-by-zero morphism restricts a source section along
  `k.image_preimage_le (f ⁻¹ᵁ W)` and then applies the supplied morphism on
  `k ⁻¹ᵁ f ⁻¹ᵁ W`; the pushforward-composition and congruence maps
  normalize away.
- N25 reduction: applying the formula to the first Čech leg reduces the
  desired derivation equality to the local statement that
  `coordinateKaehlerRestrictLeftIso` carries the restricted affine universal
  derivation to `coordinateOverlapDerivation`.  No global product,
  equalizer, or extension-by-zero plumbing remains in that component goal.
- ChatGPT: Q6167 was given the full local definition and asked for this exact
  formula, but its network capture contained only delivery metadata.  The
  proof was derived from the pinned component lemmas
  `restrictAdjunction_unit_app_app`, `pushforwardComp_hom_app_app`, and
  `pushforwardCongr_hom_app_app`, then verified locally.
- end: `[MZ-PUSHFORWARD-RESTRICTION-APP]` proved
- final result: the remaining N25 overlap seam is purely local affine Kähler
  naturality under the two chart localizations.

## Run 2026-08-21 (first transported overlap derivation)

- doctrine version: `a06df5dfe4a8341212ec2dbb95a3246e72dce6d1066ceec681c7d969a1afc00c`
- approval: Xiang's instruction to continue, finish the current local work,
  use ChatGPT as the mathematical workhorse, and stop at a clean opportunity
- starting avenue: package the first chart localization as a genuine
  full-site derivation on the ordered overlap, then reduce its equality with
  the intrinsic overlap derivation to affine global sections
- result: added `PresheafOfModules.Derivation'.ext_of_affine_top`.  Equality
  on top sections propagates to every principal open by localization
  extensionality and then to arbitrary opens by sheaf locality.
- result: proved both raw and normalized top-section formulas for the affine
  universal derivation.  These expose the ordinary Kähler differential under
  `StructureSheaf.toOpenₗ` and `tilde.isoTop`.
- result: constructed `coordinateOverlapLeftTransportedDerivation` on the
  full overlap site.  Its binary-base compatibility, Leibniz rule across the
  canonical Kähler base-change isomorphism, and restriction naturality are
  all proved without `sorry` or new axioms.
- exact residual: identify the transported derivation's normalized top
  component with `affineUniversalDerivation` using the existing localization
  generator theorem; affine-top extensionality then gives the first component
  equality, after which the right component is symmetric.
- ChatGPT: Q6161 and Q6162 still have no git-drop and were not re-sent.  A new
  independent design request through canonical `ask-gpt.py` failed before
  dispatch because the current `flt` window had no configured channel; it
  produced no Q number and no unverified claim entered the proof.
- verification: strict source checks pass for both changed Lean files; the
  8623-job N25 target and repository-wide 4011-job build pass.  Fresh axiom
  audits of affine-top extensionality, both top normalization formulas, base
  compatibility, transported naturality, and the transported derivation
  report exactly `propext`, `Classical.choice`, and `Quot.sound`.
- end: clean intermediate N25 checkpoint
- final result: the first overlap leg is now represented by two full-site
  derivations in the same affine target, with only their normalized top
  equality still open.

## Run 2026-08-22 (N25 Čech compatibility and canonical transpose)

- doctrine version: `ea8bb2c0ffecd2412e40d9ae534d2850f72dd96372318ef45af5e31611474b4e`
- approval: Xiang's instruction to continue autonomously from the latest
  verified checkpoint, use ChatGPT as the workhorse when available, verify
  locally, and continue past individual item boundaries
- starting avenue: close the normalized transported-derivation equality,
  prove both full extension-by-zero overlap comparisons, and feed them into
  the already constructed Čech derivation descent
- result: normalized top sections of both transported overlap derivations
  agree with the ordinary Kähler universal derivation on all localized chart
  generators.  Localization extensionality and affine-top extensionality then
  identify both full-site transported derivations with
  `affineUniversalDerivation` on every ordered overlap.
- result: proved the first chart extension-by-zero composite equals the direct
  overlap derivation on arbitrary ambient opens.  The proof reduces all
  section transports to `Scheme.Hom.appLE_appIso_inv`, rather than unfolding
  the structure sheaf or assuming a top-section formula on general opens.
- generic infrastructure: strengthened the extension-by-zero component
  formula to an arbitrary named composite.  Its last factor is the presheaf
  transport induced by the equality between the literal composite and its
  chosen name.  Also added identity postcomposition and product extensionality
  lemmas for relative derivations.
- result: proved the second chart extension-by-zero composite equals the same
  direct overlap derivation.  This closes the dependent right-composite seam:
  the proof explicitly transports between the literal and named preimage
  opens, applies naturality of the canonical Kähler comparison, and collapses
  the three affine restriction maps before using `appLE_appIso_inv`.
- result: the four chart derivations now satisfy the two canonical Čech
  arrows.  They descend to a derivation valued in
  `globalKaehlerDifferentialModule`, and the relative-differential universal
  property transposes it to the canonical morphism
  `canonicalRelativeDifferentialsToGlobalKaehler`.
- result: postcomposition of the descended derivation with every Čech chart
  projection recovers the corresponding affine universal derivation.  By
  naturality of the sheafification/Kähler Hom equivalence, the canonical
  morphism followed by each chart projection is exactly the named universal
  chart comparison.
- next exact seam: prove the four universal chart comparisons are isomorphisms
  after restriction to their standard charts, using localization of Kähler
  differentials on the principal-open basis.  A local probe further isolated
  the target-side obligation to the categorical identity between literal
  Čech evaluation and `globalKaehlerDifferentialLocalIso`.
- ChatGPT: the canonical bridge was queried again for an independent audit of
  the local-isomorphism route, but the `flt` window still had no configured
  channel and the request failed before dispatch.  No external claim was used.
- verification: direct source compilation passes for the generic pullback,
  generic relative-differential, and full N25 relative-differential files.
  Both left and right component theorems and the global compatibility theorem
  were separately developed in scratch files that compile with exit code
  zero.  Bypass and whitespace scans are clean.  The fresh axiom audit and
  repository build are recorded below once completed.
- end: `[MZ-N25-RELATIVE-CECH-COMPATIBILITY]` proved
- final result: the same-site relative differential sheaf now has a canonical
  morphism to the actual global Kähler Čech equalizer, with all four chart
  composites identified.  Only the local-isomorphism proof remains before
  the two sheaves are globally identified.

## Run 2026-08-22 (affine sheafification and N25 local reduction)

- doctrine version: `a64549f5adb5e19a4af71ab643c0b0cd52b9d8e9b233ab778063cfa02a3dae79`
- approval: Xiang's instruction to continue autonomously past the previous
  item boundary, keep ChatGPT as a workhorse, and verify every result locally
- starting avenue: close the target-side literal Čech evaluation and prove
  the chart-local comparison invertible from affine localization of Kähler
  differentials
- result: defined the literal chart evaluation of
  `globalKaehlerDifferentialModule` and proved it equals
  `globalKaehlerDifferentialLocalIso.hom`.  The proof maps the source
  equalizer/projection identity through restriction and cancels the local
  residue isomorphism using counit naturality.
- result: restriction of
  `canonicalRelativeDifferentialsToGlobalKaehler`, followed by the local Čech
  isomorphism, is exactly `canonicalRelativeDifferentialsToLocalChart`.
  Since the second factor is an isomorphism, invertibility of the restricted
  global comparison is now equivalent to invertibility of this one affine
  chart morphism.
- generic infrastructure: on `Spec R`, constructed the objectwise relative
  differential comparison with `KaehlerDifferential k R` tilde.  Formal
  étaleness and module localization give an explicit isomorphism on every
  principal open, and the comparison is proved equal to that isomorphism on
  universal differential generators.
- generic infrastructure: upgraded the principal-open calculation to an
  `IsIso` instance after sheafification.  The underlying presheaf morphism is
  locally injective and locally surjective because every point has a
  principal-open neighbourhood on which the component is bijective.
  `GrothendieckTopology.W_iff` and the sheafification adjunction then give the
  sheaf isomorphism.
- N25 compatibility: proved that the presheaf adjunct of every named chart
  comparison is exactly the universal descent of `coordinateChartDerivation`.
  Equivalently, composing the global sheafification unit with the chart
  comparison gives that objectwise universal morphism.  This fixes the
  compatibility condition required by the remaining restriction/locality
  comparison.
- exact residual: construct the source-side locality isomorphism between the
  restriction of `canonicalRelativeDifferentialsSheaf` to a standard chart
  and `affineRelativeDifferentialsSheaf` for its coordinate ring, and prove it
  intertwines the two universal derivations.  The new generic affine `IsIso`
  instance then proves all four local comparisons invertible, after which the
  existing coverwise criterion proves the global comparison invertible.
- ChatGPT: Q6168, Q6169, and Q6170 independently audited the literal local
  evaluation and categorical cancellation route.  Their source-equality plus
  restricted-functor mapping architecture was checked against the pinned
  checkout and compiled.  Three follow-up batches asking for the affine
  sheafification and restriction-locality APIs failed before dispatch because
  the `flt` bridge reported no ready channels; no unavailable answer was used.
- verification: direct source compilation passes for both the generic affine
  differential file and the full N25 relative-differential file.  The
  8623-job N25 target build and repository-wide 4011-job build pass.
  Whitespace and bypass scans are clean.  Fresh axiom audits of the affine
  presheaf comparison, its principal-open formula, its sheafified `IsIso`
  instance, literal Čech evaluation, the global and chart comparisons, both
  adjunct formulas, and the local reduction report exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- end: `[MZ-N25-AFFINE-SHEAFIFICATION]` proved
- final result: the target-side local Čech plumbing and the generic affine
  Kähler sheafification theorem are closed.  The remaining N25 local
  isomorphism seam is isolated to restriction compatibility of the source
  sheafification, with its required universal-derivation equation already
  proved.

## Run 2026-08-22 (restricted global derivation on N25 charts)

- doctrine version: `4877a8b8571fc2fff2ade0c23ff3d442d3699b7abed02ce848765d6588776936`
- starting avenue: continue immediately past the affine-sheafification
  milestone and construct the source-side chart restriction map needed by
  sheafification uniqueness
- result: proved that each chart's open-immersion section isomorphism carries
  its affine binary-base map to the global constant base map.  Transporting
  `canonicalRelativeDifferentialsSheafDerivation` through this isomorphism
  gives `coordinateChartRestrictedRelativeDerivation`, a derivation on the
  full small Zariski site of the affine chart with values in the restriction
  of the global relative differential sheaf.
- result: proved restriction naturality of the transported derivation on
  arbitrary chart opens.  Its universal transpose is the named morphism
  `coordinateChartRelativeDifferentialsToRestrictedSheaf` from affine
  objectwise relative differentials to the restricted global sheaf, and its
  action on every universal differential is explicit.
- exact residual: prove the named morphism locally injective and locally
  surjective.  It will then exhibit the restricted global sheaf as a
  sheafification of the affine presheaf, so the generic affine isomorphism and
  sheafification uniqueness identify the N25 chart-local comparison as an
  isomorphism.
- verification: the standalone construction probe and the complete N25
  source file compile.  The 8623-job N25 target build passes.  Fresh axiom
  audits of base compatibility, restriction naturality, the transported
  derivation, its universal transpose, and its generator formula report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- end: `[MZ-N25-RESTRICTED-RELATIVE-DERIVATION]` proved

## Run 2026-08-22 (N25 global relative differential comparison)

- doctrine version: `4877a8b8571fc2fff2ade0c23ff3d442d3699b7abed02ce848765d6588776936`
- starting avenue: prove the restricted global relative-differential unit
  locally bijective, identify it with affine sheafification, and close the
  chart-to-global isomorphism argument
- result: constructed the sectionwise Kähler transport induced by every
  chart section-ring isomorphism and proved it bijective on every open.  Its
  factorization through the restricted global sheafification unit proves the
  latter locally injective and locally surjective.
- result: sheafification uniqueness gives the explicit chart isomorphism
  `coordinateChartRestrictedRelativeDifferentialsSheafIso`.  Both inverse
  laws are proved from the two locally bijective universal properties.
- result: proved on universal differential generators that the canonical
  chart comparison equals this uniqueness isomorphism followed by the affine
  comparison to the tilde sheaf.  Hence every
  `canonicalRelativeDifferentialsToLocalChart` is an isomorphism.
- result: the four coordinate opens cover the canonical curve, so the
  existing coverwise criterion proves
  `canonicalRelativeDifferentialsToGlobalKaehler_isIso`.  The same-site
  relative differential sheaf is therefore globally identified with the
  canonical Kähler Čech object and, through the existing global Čech
  comparison, with the effective hyperplane twist.  The latter identification
  is exported directly as `canonicalRelativeDifferentialsIsoCurvePullback`.
- ChatGPT: Q6174--Q6203 supplied independent route and API audits.  The
  sheafification-uniqueness route was retained; suggestions that conflated
  the affine sheafification with its tilde target were corrected against the
  pinned source before formalization.
- verification: direct compilation of the complete N25 relative-differential
  file passes.  The 8623-job target build passes without a new unscoped-option
  warning.  Bypass and whitespace scans are clean.  Fresh axiom audits of the
  component bijectivity, restricted-unit factorization, chart sheafification
  isomorphism, counit calculation, local triangle, local factorization, and
  global `IsIso` instance report exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- end: `[MZ-N25-RELATIVE-DIFFERENTIAL-GLOBAL]` proved
- final result: the N25 scheme-relative differential sheaf is now the proved
  curve hyperplane twist.  The remaining endpoint work begins at the
  divisor/Picard/Riemann--Roch consumer, not at sheaf restriction or Čech
  compatibility.

## Run 2026-08-22 (N13 spread-line interface counterexample)

- doctrine version: `4877a8b8571fc2fff2ade0c23ff3d442d3699b7abed02ce848765d6588776936`
- starting avenue: audit the remaining unrestricted `n13_class_eq_iff` after
  closing the N25 relative-differential comparison
- result: formalized `negativeZeroData` by retaining the complete
  negative-infinity two-chart geometry and special divisor while resetting
  only its independently stored generic orientation to the identity Mumford
  representative.
- result: packaged positive- and negative-infinity spread lines with the same
  stored rational class `0`.  Their generic classes modulo the trivial kernel
  are equal, but their special classes are distinct by the existing anchored
  and canonical infinity-class computations.
- consequence: `exists_same_generic_bottom_distinct_special` formally refutes
  the all-`SpreadLine` reverse implication required by the current
  `n13_class_eq_iff`.  The next route must use a coherent spread subtype or
  the canonical exact-spread chooser; additional affine saturation cannot
  fix an infinity-chart mismatch.
- ChatGPT: Q6198 identified the candidate interface defect and explicit
  infinity-line construction.  Every theorem name and equality was checked
  against the local source, and the counterexample was independently
  elaborated and compiled.
- verification: direct source compilation, the 8807-job target build, and the
  repository-wide 4011-job build pass.  Fresh axiom audits of the affine-ideal
  equality, generic reorientation, special-class inequality, and existential
  counterexample report exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- end: `[MZ-N13-SPREADLINE-COUNTEREXAMPLE]` proved

## Run 2026-08-22 (N25 full binary closed points and divisor interfaces)

- doctrine version: `abc391991483845d125301317010784dc6e6a9de669f7e6ad54a36cdda5b439c`
- approval: Xiang's instruction to continue the autonomous FLT campaign,
  keep ChatGPT saturated on hard mathematical/design questions, verify every
  claim locally, and continue past individual item boundaries
- starting avenue: consume the completed binary differential-sheaf
  comparison at the divisor/Picard/Riemann--Roch frontier without treating
  the fixed common field as a global closed-point carrier
- result: `RationalPointsN25QuotientTwoFullClosedPoints.lean` constructs a
  locally finite closed-point grading in every degree from exact-period
  arithmetic-Frobenius orbits over `CommonField 2 d`.  Coherent embeddings
  into the degree-twelve field commute with Frobenius, preserve minimal
  periods, descend through the exact-orbit quotient, and give structural
  equivalences with the former common-field grading in degrees one through
  four.  The semantic point-count bridge is transported through bounded
  atoms and intrinsic ghost slots to the full grading.
- result: `RationalPointsN25QuotientTwoClosedPointChart.lean` defines the
  first-nonzero-coordinate pivot of a normalized projective point and proves
  it invariant under base change, Frobenius, and every Frobenius iterate.
  The pivot descends to positive-degree full closed-point orbits and defines
  the four canonical pivot strata needed for the point-to-chart-prime map.
- result: the binary middle-degree consumer now derives `#Pic^0 = 71` on the
  full degreewise grading.  `CurveZetaMiddleRiemannRoch.lean` also converts
  complete-linear-system/projectivization equivalences and finite section
  dimensions into the required fibre-cardinality formula, so a bare fibre
  count need not be assumed.
- result: `CurveDedekindDivisor.lean` packages Dedekind fractional-ideal
  factorization as affine height-one-prime divisors.  The divisor map is
  multiplicative and injective on nonzero fractional ideals, and principal
  fractional ideals give an additive map from `Kˣ`.  This remains explicitly
  affine: no points at infinity or projective product formula are claimed.
- result: `RationalPointsN25QuotientTwoHyperplaneArtinLocal.lean` adds the
  reduced `Z` quotient and proves the three explicit localized quotients have
  `F₂`-module lengths `2`, `1`, and `3`.  The new generic
  `CurveLocalIntersectionLength.lean` exposes the residue-field-length-one
  hypothesis required to convert a ground-field quotient length into a
  local-ring length; the present three results are not mislabeled as stalk
  intersection multiplicities.
- exact residual: construct `chartQuotientEval` on each canonical pivot,
  prove Frobenius invariance of its kernel, descend the kernel to a nonzero
  height-one chart prime, and prove its residue degree equals the orbit
  degree.  Then pull back `FractionalIdeal.count` to a finitely supported
  global principal-divisor coefficient map, add the boundary points, and
  prove the genuine projective degree-zero product formula.
- ChatGPT: Q6250 and Q6251 independently rejected the bounded common-field
  grading as a global divisor carrier and found no pinned turnkey projective
  divisor/Riemann--Roch API.  Q6256 audited the exact length transport.  Q6258
  supplied the degreewise field/orbit comparison architecture, which was
  corrected and compiled locally.  Q6264 identified the canonical pivot and
  point-to-chart-prime route; Q6265 isolated the AtPrime quotient and residue
  field factor needed before the Artin lengths become local orders.  Q6260
  failed all connectors and was not used.  All accepted API claims were
  checked against the pinned source before formalization.
- verification: direct strict compilation passes for the canonical-pivot,
  full closed-point, generic local-length, Artin-local, projectivization, and
  middle-Riemann--Roch modules.  The integrated 8608-job target build passes.
  Fresh axiom audits of Frobenius semiconjugacy, orbit-class equivalence, the
  full closed-point bridge, the full-grading `71` consumer, the affine
  principal-divisor map, and all three `F₂`-length theorems report exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- end: `[MZ-N25-FULL-CLOSED-POINTS]` and
  `[MZ-N25-AFFINE-DIVISOR-FIRST-ATOMS]` proved

## Run 2026-08-22 (N25 Frobenius closed points to affine chart primes)

- doctrine version: `abc391991483845d125301317010784dc6e6a9de669f7e6ad54a36cdda5b439c`
- starting avenue: continue the full binary closed-point milestone by
  constructing evaluation on the canonical pivot chart, proving Frobenius
  invariance of its kernel, and descending that kernel through exact-period
  orbit classes
- result: `RationalPointsN25QuotientTwoClosedPointEvaluation.lean` evaluates
  normalized homogeneous coordinates and the three affine chart variables,
  proves compatibility with dehomogenization, proves both canonical chart
  equations vanish, and descends evaluation through the explicit two-equation
  chart quotient.
- result: chart evaluation is equivariant under arithmetic Frobenius.  Its
  kernel and associated prime-spectrum point are invariant under every
  Frobenius iterate.  The quotient by the evaluation kernel is canonically
  equivalent to the coordinate-generated range in the ambient finite field;
  it is finite and is a field.
- result: `RationalPointsN25QuotientTwoClosedPointPrime.lean` uses the product
  of the four affine chart rings as a fixed target.  Each geometric point
  defines the product-ring prime coming from its canonical pivot factor.
  Frobenius invariance proves this prime constant on `SameExactOrbit`, so it
  descends to every positive-degree member of
  `fullClosedPointGrading25Two`.  The descended prime is proved to lie on the
  factor selected by `fullClosedPointPivot`.
- exact residual: prove the chart evaluation kernel nonzero and height one,
  and prove that its finite residue-field degree equals the point's least
  Frobenius period.  Then identify overlap primes and local orders, add the
  boundary points, and establish the projective degree-zero product formula.
- ChatGPT: Q6269 returned only a DOM refusal and supplied no mathematical
  content.  A new high-value request for the dependent orbit-to-chart-prime
  descent was attempted after the local kernel theorem, but every configured
  channel was still recovering; the bridge reported no ready channel.  The
  fixed chart-product construction was developed and verified locally.
- verification: strict direct compilation passes for both new modules.  The
  integrated 8815-job build, including the endpoint audit, passes.  The
  endpoint axiom list is unchanged.  Fresh axiom audits of quotient
  Frobenius equivariance, the finite residue-field theorem, product-ring
  Frobenius equivariance, exact-orbit descent, and pivot-factor support report
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- end: `[MZ-N25-CLOSED-POINT-CHART-PRIME]` proved

## Run 2026-08-22 (N25 closed-point residue degree)

- starting avenue: identify the chart-evaluation residue field intrinsically
  and compare its binary degree with the exact arithmetic-Frobenius period
- result: `RationalPointsN25QuotientTwoClosedPointResidueDegree.lean`
  packages the evaluation range as an intermediate coordinate field.  Every
  normalized projective coordinate lies in it, and Frobenius to its extension
  degree fixes every element and hence the point.
- result: exact periodicity makes the point period divide the coordinate-field
  degree, while the intermediate-field tower makes that degree divide the
  ambient degree.  Since the ambient field is chosen in the exact-period
  degree, mutual divisibility proves equality.
- result: the pivot-chart residue, the canonical chart-product residue, and
  the representative-independent full closed-point residue all have
  cardinality exactly `2^d` in degree `d`.  The chart evaluation kernel and
  the descended product-ring prime are maximal.
- exact residual: prove the selected chart kernel nonzero and height one,
  compare the same point and valuation order across chart overlaps, add the
  boundary points, and prove the projective degree-zero product formula.
- ChatGPT: the high-value residue-degree request found no ready bridge channel;
  the bridge was still recovering, so it was not repeatedly resubmitted.  The
  intermediate-field argument was developed and checked locally.
- verification: strict direct compilation and the integrated 8816-job build,
  including the endpoint audit, pass.  Fresh axiom audits of coordinate-degree
  equality, exact residue cardinality, full closed-point residue cardinality,
  and both maximality theorems report exactly `propext`, `Classical.choice`,
  and `Quot.sound`.  The endpoint axiom list is unchanged.
- end: `[MZ-N25-CLOSED-POINT-RESIDUE-DEGREE]` proved

## Run 2026-08-22 (N25 fixed W-open closed-point primes)

- starting avenue: avoid proving all four canonical-pivot chart rings
  integral by sending every projective point with `W ≠ 0` to the already
  integral `w = 1` chart, and prove exact residue degree and height there
- result: `RationalPointsN25QuotientTwoPlaneChartDimension.lean` proves the
  plane principal open has dimension at most one by integral extension from
  `F₂[z]`; the finite projection boundary is zero-dimensional, so every
  maximal ideal of the full integral `w = 1` chart has height at most one and
  every nonzero prime has height exactly one.
- result: `RationalPointsN25QuotientTwoClosedPointKernelNonzero.lean` packages
  the Frobenius/Kähler argument generically.  A rank-one equivalence
  `Ω¹_{B/F₂} ≃ B` supplies `b` with `db ≠ 0`; for a finite evaluation
  range of cardinality `2^d`, `b^(2^d)-b` is nonzero but lies in the kernel.
  Applied to every positive exact-period canonical-pivot point, this proves
  its chart evaluation kernel nonzero without assuming that chart is a
  domain.
- result: `RationalPointsN25QuotientTwoWOpenEvaluation.lean` defines points on
  the geometric open `W ≠ 0`, divides their canonical normalized coordinates
  by `W`, verifies the homogeneous equations after scaling, and factors
  evaluation through the fixed quotient `ChartQuotient 3`.  Coefficient-field
  equivalences preserve both the normalized ratios and the evaluation kernel.
- result: `RationalPointsN25QuotientTwoWOpenResidueDegree.lean` proves that
  fixing all `W`-ratios fixes the underlying first-nonzero normalized point.
  Exact period and the finite-field tower then force the ratio coordinate
  field degree to equal `d`, so the fixed-chart evaluation range has exactly
  `2^d` elements.
- result: `RationalPointsN25QuotientTwoPlaneChartClosedPoints.lean` uses
  `[0:0:0:1]` to prove the integral `w = 1` chart is not a field.  Hence every
  maximal ideal is nonzero and height one.  Every finite-field `W`-open point
  defines such a maximal ideal, and every positive exact-period point has the
  combined exact residue-cardinality, nonzero-kernel, maximality, and
  height-one interface.
- exact residual: classify the complementary `W = 0` closed points and attach
  the already proved hyperplane local lengths without confusing intersection
  multiplicity with residue degree.  Then build the projective divisor
  carrier, compare local orders across overlaps, and prove the degree-zero
  product formula.
- ChatGPT: Q6286 ruled out a turnkey smooth-dimension-one height API; Q6287
  identified the hidden-component obstruction to treating all four charts as
  domains; Q6288 and Q6291 supplied the Kähler/Frobenius kernel witness; Q6296
  supplied the fixed `W`-open evaluation architecture; Q6303 independently
  confirmed the exact-period ratio-field route.  All accepted API claims were
  compiled against the pinned local source.  Q6293 and Q6295 had not landed;
  Q6304 was dispatched for the complementary `W = 0` support classification.
- verification: strict direct compilation passes for all five new modules.
  The integrated 8631-job target build passes.  Fresh axiom audits of
  field-equivalence kernel invariance, ratio period detection, exact range
  cardinality, the generic Kähler kernel theorem, chart height one, and both
  exact-period W-open capstones report exactly `propext`, `Classical.choice`,
  and `Quot.sound`.
- end: `[MZ-N25-W-OPEN-CLOSED-POINTS]` proved

## Run 2026-08-22 (N25 W-boundary and orbit-prime descent)

- doctrine version: `4933cf95ecd6429af1ad50995ab78087b2f7068e194c1de530f085746e62df66`
- starting avenue: descend fixed-`W` evaluation kernels from exact-period
  representatives to full closed points and close the complementary boundary
  support without conflating residue degree with local intersection length
- result: `RationalPointsN25QuotientTwoWBoundaryClosedPoints.lean` proves that
  the geometric `W = 0` locus consists exactly of `[1:0:0:0]`,
  `[0:1:1:0]`, and `[0:0:1:0]` over every characteristic-two field.  Each is
  Frobenius fixed, so an exact-period point on the boundary has degree one;
  all three prime-field points are packaged as degree-one atoms of the full
  closed-point grading.
- result: `RationalPointsN25QuotientTwoWOpenOrbitPrime.lean` proves that
  Frobenius-related exact-period representatives have equal fixed-chart
  evaluation kernels.  Quotient descent therefore attaches a
  representative-independent nonzero height-one maximal ideal to every
  full closed point of degree greater than one, and its residue ring has
  cardinality exactly `2^d` in degree `d`.
- correction: the `W = 0` boundary has three rational support points, not
  two.  The point `[1:0:0:0]` is absent only from the separate `x = 0`
  hyperplane section.  Existing `x = 0` lengths therefore cannot be reused
  as `W = 0` local orders.
- ChatGPT: Q6304 independently detected the third boundary point and its
  degree-one status; both claims were derived and compiled locally.  Q6310,
  Q6311, and Q6312 are auditing the predicted `W = 0` local lengths, the
  global carrier, and the full boundary/open partition respectively.
- verification: strict source compilation and the integrated 8633-job target
  build pass.  Fresh axiom audits of boundary classification, exact-period
  exclusion, orbit-kernel invariance, descended height one, and exact residue
  cardinality report exactly `propext`, `Classical.choice`, and `Quot.sound`.
- exact residual: formalize the `W = 0` local lengths, assemble open primes
  and the three boundary atoms in one projective divisor carrier, compare
  local orders, and prove the projective degree-zero product formula.
- end: `[MZ-N25-W-BOUNDARY-ORBIT-PRIMES]` proved

## Run 2026-08-22 (N25 W-boundary Artin factors and full partition)

- doctrine version: `fca89e932ff541a5cf19104900057ced281bc2e72d10751f8044253a5ea3a25a`
- starting avenue: compute all three `W = 0` scheme-theoretic factors and
  extend the fixed-chart prime interface across the two degree-one points on
  `W != 0`
- result: `RationalPointsN25QuotientTwoWBoundaryArtinLocal.lean` gives exact
  principal-open equation-quotient presentations at the three boundary
  points.  At `X=[1:0:0:0]` the quotient is `F₂[t]/(t³)`; at
  `Z=[0:0:1:0]` it is `F₂[t]/(t²)`; at `YZ=[0:1:1:0]` it is `F₂`.
  Their ground-field lengths are `3,2,1`, and the associated full-grading
  effective cycle has degree six.
- result: the degree-one orbit map is proved bijective, giving an equivalence
  between semantic `F₂` curve points and full degree-one closed points.  The
  three boundary atoms are pairwise distinct.
- result: `RationalPointsN25QuotientTwoClosedPointPartition.lean` defines the
  nonboundary atom subtype.  Every such atom, including degree one, carries
  a nonzero height-one maximal ideal on the integral `w = 1` chart whose
  residue cardinality is exactly `2^d`; every full atom is therefore boundary
  or has this chart-prime certificate.
- semantic boundary: the numbers `3,2,1` are presently proved as lengths of
  explicit affine/principal-open equation quotients.  They will become honest
  local intersection orders only after constructing the curve-stalk quotient
  equivalences.  They remain distinct from the residue degree, which is one
  at all three boundary points.
- ChatGPT: Q6310 independently derived and checked the three Artin factors.
  Q6311 separated the global Finsupp carrier from the product formula.  Q6312
  caught the two missing degree-one `W`-open atoms and supplied the total
  partition architecture.  Q6314 found the explicit quartic finite-map/norm
  route to the product formula.  Q6317 isolated the precise remaining stalk
  equivalence needed before the Artin lengths can be called local orders.
  Every used declaration and proof was checked locally.
- verification: strict source compilation and the integrated 8635-job target
  build pass.  Fresh axiom audits of degree-one orbit bijectivity, all three
  Artin lengths, the degree-six cycle, and the total atom partition report
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- exact residual: prove injectivity of the nonboundary atom-to-chart-prime
  map, construct `O_{C,P}/(W)` equivalences with the three Artin factors, and
  use the finite quartic `z`-map/norm calculation to prove the projective
  degree-zero product formula.
- end: `[MZ-N25-W-BOUNDARY-ARTIN-PARTITION]` proved

## Run 2026-08-22 (N25 actual X-boundary quotient and W-open prime injectivity)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: replace the isolated boundary equation calculation by an
  actual curve-chart quotient and prove that the representative-independent
  fixed-`W` prime separates all nonboundary closed-point atoms
- result: `RationalPointsN25QuotientTwoWBoundaryChartArtin.lean` computes the
  quotient of the actual `X != 0` curve chart by `W/X`.  The curve relations
  give `Z/X = (Y/X)^2` and `(Y/X)^3 = 0`; explicit inverse algebra maps identify
  the quotient with `F₂[t]/(t³)`, so its `F₂`-length is three.
- result: `RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective.lean` proves
  that exact-period fixed-chart evaluations are surjective.  Equal kernels
  therefore differ by a finite-field automorphism, hence by a Frobenius
  power; equality of the three `W`-normalized coordinates recovers the exact
  Frobenius orbit.  Residue cardinality recovers the degree, and a separate
  `F₂` argument handles degree one, yielding injectivity of
  `fullNonBoundaryPrimeIdeal` on every nonboundary full atom.
- semantic boundary: the actual `X`-chart quotient is now verified, but the
  localization map from the stalk at `[1:0:0:0]` and its kernel still have to
  be constructed before the length-three result is recorded as a local
  intersection order.  The analogous actual-chart quotient and localization
  statements at the length-two `Z` point and length-one `YZ` point also remain.
- ChatGPT: Q6325 and Q6333 supplied the equal-kernel/Frobenius separation
  architecture; Q6335 audited the degree-one seam after it had been proved
  locally.  Q6334 supplied the direct `IsLocalization.liftAlgHom` kernel route
  for the next X-stalk quotient.  Q6339 assigned the remaining Artin factors
  incorrectly and was rejected against the compiled local factor theorems;
  Q6340 was dispatched with the corrected targets.
- verification: strict direct compilation passes for both new modules, and
  the 8637-job target build passes.  Fresh axiom audits of the actual X-chart
  equivalence and length, exact-orbit kernel separation, and uniform
  nonboundary-prime injectivity report exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- exact residual: construct the three curve-stalk quotients by the germs of
  `W`, prove their Artin equivalences and local lengths, then assemble the
  global divisor carrier and prove the projective degree-zero product formula.
- end: `[MZ-N25-W-CHART-PRIME-INJECTIVITY]` proved

## Run 2026-08-24 (N25 X-boundary local order)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: extend the actual `X`-chart quotient by `W/X` across the
  localization at the rational point `[1:0:0:0]`, identify the exact kernel,
  and convert the Artin-factor dimension into local-ring length
- result: `RationalPointsN25QuotientTwoWBoundaryXLocal.lean` constructs the
  origin evaluation prime in `ChartQuotient 0`, proves it maximal, and shows
  that every denominator outside it becomes a unit after quotienting by
  `W/X`.  A generic localization-kernel theorem identifies the induced
  kernel with the extended principal ideal.
- result: the quotient of the actual point local ring by the germ of `W/X`
  is algebra-equivalent to `F₂[t]/(t³)`.  Localization preserves the
  degree-one residue field; scalar restriction therefore converts the
  already computed `F₂`-length three into local-ring length three.
- semantic endpoint: `xWGerm_ord_eq_three` proves
  `Ring.ord XLocalRing xWGerm = 3`, so the previously formal Artin length is
  now the genuine order/intersection multiplicity of `W = 0` at
  `[1:0:0:0]`.
- ChatGPT: Q6334 supplied the direct localization-lift kernel architecture,
  and Q6338 identified `Ring.ord` plus residue-degree scalar restriction as
  the semantic endpoint.  After usage recovery the local ChatGPT bridge
  reported no ready `flt` channels, so verification and completion continued
  locally without duplicate submissions.
- verification: strict direct compilation passes.  Fresh axiom audits of the
  point evaluation, localized Artin equivalence, both field and local-ring
  length statements, and `Ring.ord` endpoint report exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- exact residual: prove the length-two order at `[0:0:1:0]` and length-one
  order at `[0:1:1:0]`, then assemble the boundary divisor with the injective
  nonboundary prime carrier and prove the projective degree-zero product
  formula.
- end: `[MZ-N25-X-LOCAL-ORDER]` proved

## Run 2026-08-24 (N25 YZ-boundary local order)

- starting avenue: compute the actual `Y != 0` chart quotient by `W/Y` and
  apply the verified localization-kernel interface at `[0:1:1:0]`
- result: `RationalPointsN25QuotientTwoWBoundaryYZChartArtin.lean` derives
  the dehomogenized relations in the actual curve chart.  After `W/Y = 0`,
  the cubic gives `(X/Y)(Z/Y) = 0` and the quadric then forces `Z/Y = 1`;
  hence `X/Y = 0`.  Explicit inverse algebra maps identify the quotient with
  `F₂`, of `F₂`-length one.
- result: `RationalPointsN25QuotientTwoWBoundaryYZLocal.lean` defines the
  corresponding evaluation prime, proves it maximal, extends the boundary
  quotient to `Localization.AtPrime`, and identifies its kernel with the
  principal germ ideal.  The local quotient is `F₂`.
- semantic endpoint: residue degree one and scalar restriction give local
  length one, and `yzWGerm_ord_eq_one` proves that the order of `W` at
  `[0:1:1:0]` is one.
- verification: both new modules compile strictly.  Fresh axiom audits of
  both chart and local equivalences, both length endpoints, and `Ring.ord`
  report exactly `propext`, `Classical.choice`, and `Quot.sound`.
- exact residual: in the standard `Z` chart the boundary quotient contains
  both the length-two `Z` component and the length-one `YZ` component.  Use
  the fact that `Y/Z + 1` is invertible at Z to isolate the double Artin
  factor and prove the final boundary order before global assembly.
- end: `[MZ-N25-YZ-LOCAL-ORDER]` proved

## Run 2026-08-24 (N25 Z-boundary local order)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: localize the actual `Z != 0` curve chart at
  `[0:0:1:0]` and remove the other boundary component by proving that
  `Y/Z + 1` is a unit there
- result: `RationalPointsN25QuotientTwoWBoundaryZLocal.lean` constructs the
  point evaluation prime and its localization, extends the map to the double
  Artin algebra, and factors it through the quotient by the germ of `W/Z`.
  In the local quotient the chart equations give
  `(Y/Z)^2 ((Y/Z) + 1) = 0`; localization makes the second factor a unit,
  hence `(Y/Z)^2 = 0` and `X/Z = Y/Z`.
- result: explicit inverse algebra maps identify the actual local quotient
  with `F₂[t]/(t²)`.  Its `F₂`-length is two, the point residue extension
  has degree one, and scalar restriction gives local-ring length two.
- semantic endpoint: `zWGerm_ord_eq_two` proves that the order of `W` at
  `[0:0:1:0]` is two.  Together with the previously verified X and YZ
  calculations, all three genuine boundary orders are now `3,2,1`, of total
  degree six.
- verification: strict source compilation and an import-level `.olean`
  compilation pass.  Fresh axiom audits of the localized Artin equivalence,
  both length statements, and `Ring.ord` report exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- exact residual: package the three local orders into the global boundary
  carrier, prove that no other boundary primes occur in that carrier, then
  join it to the injective nonboundary prime parametrization and prove the
  projective degree-zero product formula.
- end: `[MZ-N25-Z-LOCAL-ORDER]` proved

## Run 2026-08-24 (N25 global W-boundary divisor carrier)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: replace the formal coefficients of the existing
  degree-six boundary cycle by the genuine local orders and identify its
  finite carrier inside the full closed-point grading
- result: `RationalPointsN25QuotientTwoWBoundaryLocalDivisor.lean` proves
  that the coefficients at the X, YZ, and Z atoms are respectively the
  orders of `W/X`, `W/Y`, and `W/Z` in the three actual point local rings.
  A tag-indexed theorem packages all three comparisons uniformly.
- result: a full atom has nonzero coefficient in
  `wBoundaryHyperplaneDivisor` exactly when it is one of the three classified
  boundary atoms.  Consequently the `Finsupp` support is exactly the image
  of `FullBoundaryTag25Two`; there are no additional carrier terms.
- semantic boundary: this closes the effective zero divisor of the
  homogeneous section `W`.  It does not yet prove the degree-zero product
  formula for arbitrary rational functions; that requires the affine
  Dedekind divisor and the three infinity valuations to be compared in one
  common function field.
- verification: strict source and import-level `.olean` compilation pass.
  Fresh axiom audits of all three coefficient/order comparisons, their
  uniform tagged form, the nonzero-carrier characterization, and support
  equality report exactly `propext`, `Classical.choice`, and `Quot.sound`.
- exact residual: compute the pole orders of the affine projection
  `Z/W` at X, YZ, and Z, then construct the finite quartic norm bridge that
  balances the affine principal divisor against those infinity places.
- end: `[MZ-N25-W-BOUNDARY-LOCAL-DIVISOR]` proved

## Run 2026-08-24 (N25 full W-order function and z-projection poles)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: strengthen the three-point boundary carrier to a
  pointwise local-order statement on every full atom, then compute the
  numerator orders needed for the affine projection `Z/W`
- result: `RationalPointsN25QuotientTwoWBoundaryLocalDivisor.lean` now
  defines `fullWLocalOrder`.  At the three boundary atoms it uses the three
  actual point-local-ring orders; at every complementary atom it localizes
  the fixed `W != 0` chart and uses the genuine order of the trivialization
  `W/W = 1`, which is zero.  The coefficient of
  `wBoundaryHyperplaneDivisor` equals this local order pointwise on the full
  closed-point carrier.
- result: `RationalPointsN25QuotientTwoZProjectionXLocal.lean` computes the
  actual X-local quotient by `Z/X`.  The relations and invertibility of
  `Y/X + 1` identify it with `F₂[t]/(t²)`, giving
  `Ring.ord XLocalRing xZGerm = 2`.  At YZ, `Z/Y` evaluates to one and is a
  local unit; at Z, `Z/Z = 1`.  Thus the pole multiplicities of `Z/W` at
  X, YZ, and Z are `1,1,2`, with total four.
- interface: the X- and Y-chart coordinate declarations and evaluation
  lemmas needed by the new local proof are now public; their existing
  definitions and semantics are unchanged.
- ChatGPT: Q6347 correctly separated the actual order function from the
  explicit three-term `Finsupp` and identified the `W/W=1` unit calculation
  as the missing off-boundary case.  That recommendation was implemented and
  checked locally.  Q6348--Q6350 are independently auditing the X-local
  calculation, the dependent full-order definition, and the first quartic
  norm seam.
- verification: strict source and import-level `.olean` compilation pass.
  The integrated 4011-job `lake build` passes.  Fresh axiom audits of the
  double-Artin equivalence, all numerator and pole-order statements, the
  open-chart zero order, and the full pointwise coefficient theorem report
  exactly `propext`, `Classical.choice`, and `Quot.sound`; the numerical
  pole-total theorem is axiom-free.
- exact residual: formalize the quartic extension of `F₂(z)`, prove its
  separability and degree four, and then connect affine Dedekind counts and
  the three infinity orders through the field norm.
- end: `[MZ-N25-FULL-W-ORDER-Z-POLES]` proved

## Run 2026-08-24 (N25 separable quartic generic fiber)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: pass the monic irreducible plane polynomial from
  `F₂[z]` to `F₂(z)` and expose the finite separable extension needed for
  the projection norm
- result: `RationalPointsN25QuotientTwoPlaneQuarticSeparable.lean` proves
  that the outer degree is four and computes the formal derivative.  Its
  nonzero `X⁴` specialization shows that the derivative is nonzero over
  `F₂[z]`, and injectivity of the fraction map transports this fact to
  `F₂(z)`.
- result: Gauss's lemma transports the already proved irreducibility to the
  rational function field.  The mapped quartic is therefore separable, and
  its `AdjoinRoot` is a field of `F₂(z)`-dimension four.
- semantic endpoint: the adjoined generic root is separable.  Since it
  generates the whole `AdjoinRoot`, the generic quartic field is a separable
  extension of `F₂(z)`; this is registered as an actual
  `Algebra.IsSeparable` instance rather than retained as a polynomial-only
  fact.
- ChatGPT: Q6348 independently confirmed the X-local dual-number quotient
  and the resulting simple pole of `Z/W` at X.  Q6350--Q6352 are auditing
  the extension comparison and the first norm interface while all three
  bridge tabs remain occupied.
- verification: strict source and import-level `.olean` compilation pass.
  Fresh axiom audits of the degree, derivative, irreducibility, polynomial
  separability, field dimension, root separability, and extension instance
  report exactly `propext`, `Classical.choice`, and `Quot.sound`.
- exact residual: construct the compatible `F₂(z)`-algebra structure on the
  existing `PlaneFunctionField`, identify it with the separable quartic
  `AdjoinRoot`, and expose the norm of the projection function.
- end: `[MZ-N25-SEPARABLE-QUARTIC]` proved

## Run 2026-08-24 (N25 quartic function-field identification)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: put the already constructed fraction field of the
  integral plane chart over `F₂(z)` and compare it to the explicit separable
  quartic by the universal property of `AdjoinRoot`
- result: `RationalPointsN25QuotientTwoPlaneQuarticFunctionField.lean`
  installs the faithful `F₂[z]` action and the compatible lifted `F₂(z)`
  algebra structure.  Fraction-ring base change and the monic power basis
  prove that the concrete plane function field has degree four.
- result: the plane `x` coordinate is a root of the mapped quartic.  The
  resulting algebra homomorphism from the generic quartic field is injective
  because it is a field homomorphism and surjective because its source and
  target both have dimension four.  This yields an explicit `F₂(z)`-algebra
  equivalence carrying the generic root to the existing plane coordinate.
- semantic endpoint: finite dimensionality and separability transfer to the
  concrete plane function field.  The plane coordinate `z = Z/W` is exactly
  the image of `RatFunc.X`, so its field norm is
  `RatFunc.X ^ 4` by `Algebra.norm_algebraMap`.
- verification: strict source and import-level `.olean` compilation pass.
  Fresh axiom audits of the dimension, coordinate identification, root map,
  algebra equivalence, separability transfer, and norm formula report
  exactly `propext`, `Classical.choice`, and `Quot.sound`.
- exact residual: compare finite-place orders in the normalized
  `F₂[z]`-model with the full closed-point grading and combine the norm
  degree with the already proved infinity pole cycle of total degree four.
- end: `[MZ-N25-QUARTIC-FUNCTION-FIELD]` proved

## Run 2026-08-24 (N25 finite-place normalization and exact prime norm)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: construct the integral closure of `F₂[z]` in the
  concrete plane function field and recover the exact relative-norm exponent
  without assuming that the imperfect field `F₂(z)` is perfect
- result: `RationalPointsN25QuotientTwoPlaneNormalization.lean` defines the
  finite-place normalization, proves it finite over `F₂[z]`, and packages
  maximal-prime contraction and lies-over data.  The relative ideal norm is
  first identified as an unspecified power of the contracted base prime.
- result: a generic separable replacement for Mathlib's
  `Ideal.relNorm_eq_pow_of_isMaximal` is proved.  Separability of the original
  fraction-field extension passes to its normal closure; algebraic closedness
  supplies normality, hence a Galois normal closure.  Reconstructing the
  finite and Dedekind instances used in Mathlib's proof yields the exact
  exponent `inertiaDeg` without the library theorem's stronger
  `PerfectField` assumption.
- N25 specialization: the explicit separable quartic equivalence transports
  separability to the canonical fraction-ring types.  Consequently every
  maximal finite place `P` satisfies
  `relNorm(P) = (P ∩ F₂[z])^(inertiaDeg(P ∩ F₂[z], P))`.
- verification: strict source and import-level `.olean` compilation pass.
  Fresh axiom audits of the separable normal-closure construction, the exact
  generic norm theorem, the normalization instances, separability transport,
  and both N25 norm formulas report exactly `propext`, `Classical.choice`,
  and `Quot.sound`.
- exact residual: identify the normalization's maximal ideals with the
  nonboundary closed-point primes of the smooth `W = 1` chart, transport
  inertia degrees to the already certified residue degrees, and assemble the
  finite and three infinite orders into the projective product formula.
- end: `[MZ-N25-SEPARABLE-RELNORM]` proved

## Run 2026-08-24 (N25 intrinsic W-chart normalization and prime norm)

- doctrine version: `bef1fbdaec5f6f35a404c2b6f512a969c0e3d6d6f001c31bffd57956c1f48910`
- starting avenue: prove normality directly on the canonical `W = 1` chart,
  rather than transporting the finite-place model through an unproved ring
  identification
- result: `RationalPointsN25QuotientTwoWChartNormalization.lean` proves that
  the chart is finite and integral over `F₂[z]` and that its embedding in the
  plane function field exhibits that field as its fraction field.  At every
  maximal ideal, formal smoothness injects the cotangent space into the
  residue-field base change of the rank-one Kähler differential module.
  Nonfieldness forces cotangent dimension one, so every maximal localization
  is a DVR and the chart is integrally closed.
- result: the chart is therefore the integral closure of `F₂[z]` in the plane
  function field.  The canonical integral-closure equivalence identifies it
  with `PlaneNormalization` as an `F₂[z]`-algebra.
- result: quartic separability is transported through the canonical fraction
  fields.  This supplies torsion-freeness and the Dedekind-domain instance for
  the chart, and every maximal chart ideal `P` now satisfies the direct norm
  formula
  `relNorm(P) = (P ∩ F₂[z])^(inertiaDeg(P ∩ F₂[z], P))`.
- ChatGPT: Q6359 and Q6367 isolated the dependent conormal-map bottleneck and
  the current-pin residue-kernel rewrite; the proposed architecture was
  corrected and verified locally.  Q6361 supplied the integral-closure seam,
  and Q6365 identified the shortest direct relative-norm route.
- verification: strict source compilation and the integrated 8635-job target
  build pass.  Fresh axiom audits of local and global normality, the integral
  closure and normalization equivalence, both separability transports, the
  Dedekind instance, and the direct norm theorem report exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- exact residual: identify the inertia-degree/base-prime-degree product of a
  nonboundary chart prime with its already certified closed-point degree,
  then sum finite orders and combine them with the three infinity orders.
- end: `[MZ-N25-W-NORMALIZATION-RELNORM]` proved
