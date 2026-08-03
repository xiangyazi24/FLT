
## Run 2026-06-20 (keystone campaign, autonomous drive)
- Design: 6 ChatGPT rounds (dm1/2/3) consolidated to scratch/Keystone_MasterDesign.md.
  Campaign reduced to FOUR named seams (axiom-as-seam): prePsi'_separable (core1 etaleness),
  xRep coord formula (core1, provable EDS induction), Weil pairing geom props (core2),
  rational_torsion_finite (already derivable from existing mordell_weil_fg axiom).
- DECISIONS (autonomous, per Xiang "don't ask me to decide"):
  * Finiteness leg: NO new axiom. Derive rational_torsion_finite from the EXISTING
    mordell_weil_fg axiom (rational_torsion_finite_alias already does this via
    torsion_set_finite_of_fg). Discharge rational_torsion_two_invariant_factors -> axiom 6 to 5
    using only existing axioms. Full Mordell-Weil = separate later campaign.
  * Stage-0: adopt dm3 API refactor (geomNTorsion/mapLinear, AddEquiv -> LinearEquiv).
- Two self-corrections caught by verification: (1) nondegeneracy of Weil pairing does NOT
  follow from cardinality (keep as geometric package field); (2) Weil reciprocity needs
  tame-symbol calculus + resultants, not naive disjoint induction.
- Builds dispatched (Codex Pro xhigh, isolated flt-ai repo):
  * scratch/InvariantFactors.lean -- pure-algebra invariant-factor lemma (B tail), 0-axiom.
  * scratch/NTorsionCard.lean -- KEYSTONE n_torsion_card=n^2 modulo the 2 core-1 seams.
- Baseline: 6 axioms; campaign targets 3 (rational_torsion_two_invariant_factors,
  weil_pairing_primitive_root, and mordell_weil_fg feeds the first).

## Run 2026-06-21 (/automode formally invoked — keystone campaign continues)
- Doctrine = MAZUR_AXIOM_CHECKLIST.md (avenues = board atoms) + Keystone_MasterDesign.md (design).
- Approval = Xiang repeated "自主执行/继续/不要问我" + /automode invocation. No re-handshake (mid-run).
- Live threads: codex (K1 sub-D + sub-E2), dm1 (SEAM1 E1 formal group), dm2 (K2 rank-2), dm3 (A1 discharge).
- Landed this session: C1 invariant-factor 0-axiom (13265dd); K1 n_torsion_card 0-custom-axiom modulo
  2 seams+2 sub-steps (76cbc48); full axiom ledger preserved (552e603); lean skill checklist-default (e04a4ee).
- Grind order: close K1 sub-steps → K2 rank-2 → discharge A1 (6→5) → A2 (Weil) → SEAM1/SEAM2 → A4/A5/A6/A3.

## Run 2026-07-11 (automode — four composite-order seams, /fable-ora)
- doctrine: scratch/DOCTRINE_4SEAMS.md
- goal: axiom-free no_rational_point_of_order_15/16/18/21
- oracle economy: Fable used ONCE (200k tok) — caught N16 mis-modeling + N15 axiom-trap
  + N18 triple-confirm; now warm/idle for decisive re-consult. ChatGPT tabs cheap default
  (bridge flaky). Codex gpt-5.6 xhigh, resume same session across related seams.
- avenue (a) N15: builds green, 1 isolated sorry (n15_auxiliary_rank_zero_and_torsion_exhaustion),
  codex closing 2-descent core axiom-free (window 12).
- avenue (c) N16: dispatching restatement + factor-descent (verify Fermat-4 split first).
- avenue (b) N21 spec ready (CODEX_SPEC_N21.md); (d) N18 = ℤ[√-2] infinite descent.
- end: <fill on close>
- final result: <fill on close>

### PAUSE 2026-07-11 (Xiang: no lake build, free RAM for other session)
- All 3 FLT codex + lean builds killed; RAM freed 86%. No builds until Xiang OKs.
- STATE (grep-only, UNVERIFIED — no build): N15 1 sorry (core-closer interrupted, files
  modified); N16 0 sorry + 0 axiom across files (POSSIBLY closed — MUST build-verify;
  codex found real X₁(16) model in scratch/N16_DESCENT.md, Fable Fermat-4 only partly right);
  N21 1 sorry (X₀(21) exploration). N18 elementary infeasible (Fable structural verdict) —
  needs genus-2 Jacobian rank-0 or one named axiom (Xiang's method call).
- Resume: build-verify each file + #print axioms before claiming any closure.

## Run 2026-07-11 (automode: 统筹安排，不要浪费时间)
- doctrine: existing campaign DOCTRINE + N18/N35/wiring avenues
- starting avenue: (a) N18 Route C build (Codex PID 40623) + ChatGPT pre-solving 5 blocks
- parallel: N35 build (Codex PID 88877), 5 ChatGPT tabs saturated (Q4398-4402)
- goal: N18+N35 axiom-free on uisai2 + wire 15/21/35/18 in CyclicOrderAssembly
- end: <fill on close>
- final result: <fill on close>

## Run 2026-07-12 (automode: continue flt handoff; Xiang: leave N18/R3 alone, open Layer 2, do real work)
- doctrine: existing campaign DOCTRINE + MAZUR_MAP; R3 (N18 rank-0 core) left running untouched.
- avenue (L2-p11): close the LAST sorry in CyclicExclusion11.billing_mahler_global_descent
  (11a3 complete 2-descent, ideal-square over cubic K, class#1). Isolated git worktree
  ~/repos/flt-p11 (branch p11-descent) + NFS build dir uisai2:~/repos/flt-p11 (shared mathlib
  symlink, seeded FLT olean cache). Baseline green (8586 jobs) WITH sorry.
  - Codex gpt-5.6-sol xhigh dispatched (log codex_p11.log). ChatGPT firing bad-prime bookkeeping sketch.
  - VERIFIED-CORRECTION: map called Layer-3/2 "elementary"; Q4501 shows torsion-finiteness shares
    N18 formal-group infra (zombie risk) + Torsion.lean was David's (now graduated). p11 Billing-Mahler
    route is the zero-N18-overlap self-contained path — chosen over the 2-adic-separatedness route.
- avenue (L2-scaffold, Opus own hands): build PrimeTailPackage p interface (Q4499) — sharpen the
  opaque mazur_prime_torsion_bound axiom into a precise two-layer citable contract for p>=23.
- end: <fill on close>
- final result: <fill on close>

## Run 2026-07-27 (automode — structural N13 route)
- Replaced the old order-13 high-degree-polynomial boundary with a proved
  chain:
  `F13(b,c)=0` → Kubert raw `X₁(13)` chart → optimized genus-two model →
  standard monic sextic.  All exceptional denominators are excluded from
  `b≠0` and the equation itself; no finite search is used.
- Added the exact optimized/sextic equivalence
  `X=-x-1`, `Y=2y+x³+x²+1`, exposing the four affine cusps over `X=0,-1`
  and the two points at infinity.
- `CyclicExclusion13.no_F13_rational_solution` is now a theorem.  The sole
  N13 arithmetic boundary is
  `C13Sextic_affine_x_is_cuspidal`.
- Added a curve-independent smooth monic-sextic Mumford core and instantiated
  it for N13.  Smoothness uses a degree-5/4 Bézout identity equal to 104.
  Coordinate-ring domain, rank-two basis, hyperelliptic conjugation,
  balanced point representatives, and coefficient base change are being
  extracted generically from the N18 implementation.
- Verified targeted builds and `#print axioms`: all new bridge/model/Mumford
  theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- Completed both infinity branches and their evaluation API.  Polynomial
  order at `X=s⁻¹` is proved by reversing the polynomial; the leading
  coefficient becomes the constant coefficient, so the order is exactly
  `-deg`.
- Proved the two-branch norm and leading-order formulas for
  `p(X)+q(X)Y`.  In particular, a function with at most a simple pole at both
  infinities has `q=0` and degree at most one.  This is the structural
  Riemann--Roch input needed for direct Abel--Jacobi rigidity.
- Formalized the rational `C₆` diamond symmetry, its order-three genus-zero
  quotient, complete conic parametrization, and the residual cubic fiber.
  This rules out the proposed rational elliptic-quotient shortcut.
- Formalized the Gaussian norm factorization
  `f=A²+B²` and the exact `F₃` affine-point classification without
  enumeration.
- Cleared the first generic normal-form step: every invertible fractional
  ideal can be scaled to an integral ideal.  The next generic gap is the
  rank-two Hermite/Cantor reduction, for which Mathlib has no ready high-level
  theorem.
- Reproducibly computed the sextic field's integral basis, discriminant,
  class number one, units, bad-prime factorization, and the resulting
  16-class global weak-2-descent envelope.  These computations identify, but
  do not replace, the remaining local-image proof.
- Replaced the conditional N13 Abel--Jacobi injection with a direct proof for
  point-sized Mumford representatives.  Clearing a principal relation gives
  two integral factors; the two-branch norm forces both into `K[X]`, and
  ideal contraction plus monicity forces their `u`-polynomials to agree.
  Targeted builds pass, and `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Corrected the weak-2-descent interpretation.  The apparent second survivor
  `e2*a*q` is the rational scalar class `[13]`, since
  `(e2*a*q)*(ζ*e1*a)^2=13`.  Thus the two survivors coincide in the standard
  fake-Jacobian target modulo `ℚ*`; searching for another local prime to kill
  the second representative was the wrong problem.
- Formalized the generic fake square-class target
  `Lˣ / (Lˣ² · image(Kˣ))` for commutative rings and the ring-level bridge
  from `z*s²=e(q)` to a trivial quotient class.  The bridge extracts the
  required units from the equality itself.
- Formalized the N13 identity in the quotient algebra using three compressed
  low-degree polynomial reductions.  No degree-33 expansion, irreducibility
  proof, local-prime search, or representative enumeration is used.
- Targeted builds pass.  `#print axioms` for the scalar identity and quotient
  collapse reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Formalized the Gaussian cubic change of presentation.  The intrinsic
  order-four unit squares to `-1`; the sextic root obeys a cubic over that
  quadratic subalgebra; and the four long S-unit/prime generators reduce to
  exact degree-two formulas.  The relevant polynomial quotients are only
  constant or linear.
- Replaced the first useful two-adic ray-character rows by one intrinsic
  first ramified logarithm on the dual numbers over `F₈`.  The generic
  logarithm kills squares and scalar units and factors through the fake
  square-class target.
- Calculated the four N13 generator jets and proved by minimal-polynomial
  linear independence that the first-jet kernel is exactly
  `i=0`, `j=0`, `k=s`.  This reduces the sixteen global candidates to two
  in one `F₈` equation; no candidate enumeration is present.
- Targeted builds and axiom audits for the Gaussian cubic, ramified
  logarithm, and N13 first-jet kernel pass with only `propext`,
  `Classical.choice`, and `Quot.sound`.  The actual `ℚ₂` valuation adapter
  and completeness of the global S-unit envelope remain explicit.
- Proved the N13 sextic irreducible by reduction modulo three.  The
  finite-field proof uses Frobenius divisibility for an arbitrary
  irreducible factor and Bézout coprimality for degrees one, two, and
  three; it does not enumerate finite-field factors.  Gauss's lemma then
  gives irreducibility over `ℚ`.
- Exported opt-in `Fact` and field structures for the fake-descent sextic
  algebra, avoiding a global instance.  The targeted build passes, and
  axiom audits for both the finite-field and rational irreducibility
  theorems report only `propext`, `Classical.choice`, and `Quot.sound`.
- Corrected the endgame: fake-2 triviality supplies 2-divisibility, so the
  separated kernel must be 2-adic.  The good model is
  `y²+(x³+x+1)y=x⁵+x⁴`; its two affine/infinity charts stay smooth modulo
  two.  The completed-square sextic is singular modulo two and is not the
  reduction model.
- Formalized the good generalized model and its weighted-homogeneous
  completion.  The `Z=1` and `X=1` equations agree on their overlap by a
  homogeneous residual identity, and completing the square over `ℚ` gives
  exactly the existing N13 sextic.
- Proved geometric affine smoothness in every characteristic-two field by
  excluding simultaneous vanishing of the two partial derivatives.  The
  infinity fibre has two points and second partial derivative one; the
  complementary chart covers every nonzero point at infinity.
- Proved structurally that the completed curve has six points over both
  `F₂` and `F₄`.  The `F₄` proof uses Frobenius-fixed elements and the
  Artin--Schreier obstruction; it does not enumerate the 16 affine pairs.
- Formalized the Newton-identity layer.  The two counts uniquely give
  `s₁=-3`, `s₂=5`,
  `P₂(T)=1+3T+5T²+6T³+4T⁴`, and `P₂(1)=19`.
- Audited Mathlib and the repository: no genus-two point-count/zeta/Jacobian
  cardinality bridge exists.  This is now isolated from the completed
  finite-field arithmetic rather than hidden inside it.
- Replaced the missing general zeta API by the fixed genus-two
  symmetric-square route.  Mathlib's `Sym2` cardinal theorem gives 21
  effective degree-two divisors from the six curve points.
- Formalized the exact Abel-fibre counting interface: one three-element
  canonical fibre and singleton fibres elsewhere imply
  `#J(F₂)=21-3+1=19`, hence exponent 19 for the finite additive Jacobian.
  This is structural and leaves only the standard fixed-curve Abel-fibre
  geometry, not a table of 19 group elements.
- Constructed the fixed finite Abel set model.  The six points decompose as
  three hyperelliptic pairs; collapsing exactly their three canonical
  degree-two divisors gives a quotient of cardinality 19.  The production
  module explicitly distinguishes this set quotient from the geometric
  Picard group.
- Isolated the exact semantic bridge as `GeometricAbelCriterion`: Abel
  surjectivity plus the degree-two linear-equivalence criterion
  automatically supplies the previously defined fibre-counting package.
  The audit also exposed the separate nonsplit-orbit issue between
  `Sym2(C(F₂))` and `Sym²(C)(F₂)`; the absence of new `F₄` points is the
  structural input that will close it.
- Closed that nonsplit-orbit issue at the Frobenius point-set level.
  Base change from the six `F₂` points to the six `F₄` points is a
  bijection; the explicit Frobenius map fixes every affine and infinity
  point.  Hence the Frobenius-fixed unordered pairs over `F₄` are
  equivalent to `Sym2(C(F₂))` and have cardinality 21.
- `lake build FLT.Assumptions.MazurProof.N13SymmetricSquareFrobenius`
  passes.  Axiom audits for point base change, Frobenius fixedness, the
  divisor equivalence, and its cardinality report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Formalized the two-adic group-theoretic closure without finite generation.
  A trivial fake descent is represented exactly by surjectivity of doubling;
  together with the separated doubling filtration and special-fibre
  exponent 19, the existing separated-descent theorem kills the rational
  Jacobian by 19.  A formal valuation invariant under odd multiplication
  makes `[19]` injective on the reduction kernel, so reduction is injective.
  Fake-Kummer soundness, the fixed reduction map, Abel-fibre geometry, and
  the formal-kernel filtration remain explicit instance-level inputs.
- Targeted build and axiom audit pass for this endgame.  The exported
  exponent and reduction-injectivity theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Joined the first-jet kernel theorem to the rational-scalar identity.
  Every candidate with vanishing local logarithm now has trivial fake
  square class: the kernel theorem leaves only `(0,0,s,s)`, and the
  `s=1` representative is a scalar times a square.  This replaces the
  entire sixteen-candidate table by one linear-independence argument and
  one exact algebra identity.
- `lake build FLT.Assumptions.MazurProof.N13CandidateCollapse` passes.
  `#print axioms` for
  `candidateClass_eq_one_of_dlog_eq_zero` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Formalized both valuation regimes for a `ℚ₂` affine coordinate.  In the
  integral regime the first jet is constant.  In the nonintegral regime,
  the exact factorization
  `x-θ=x(1-x⁻¹θ)` removes a rational scalar, and valuation theory proves
  that the residue of `x⁻¹` is zero.  Both ramified logarithms vanish.
- Verified that the dual-number images of `i` and `θ` satisfy the Gaussian
  cubic presentation.  The module deliberately stops short of calling
  these the actual Jacobian local images: the length-two local-order
  quotient and Mumford-value compatibility are still required.
- `lake build FLT.Assumptions.MazurProof.N13LocalDlogRegimes` passes.
  Axiom audits for both regimes, the residue theorem, and the scalar
  factorization report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Constructed an explicit half of the even-sextic infinity-difference
  class.  The proof uses the Gaussian factorization to show
  `(X(X+1),Y+2X+1)²=(Y-A)`, computes the branch order of `Y-A`, and keeps
  the oriented fractional-ideal component throughout.  It yields
  `2[H]=[∞₋-∞₊]`, which removes the extra infinity alternative from the
  future exact fake-Kummer kernel.
- `lake build FLT.Assumptions.MazurProof.N13InfinityHalf` passes.  Axiom
  audits for the ideal square, branch order, oriented raw relation, and
  final doubling theorem report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Assembled the even-sextic kernel correction abstractly.  If a genuine
  Kummer homomorphism has kernel “a double or a double plus
  `[∞₋-∞₊]`”, the explicit half-class turns this into exactly the doubles.
  Triviality of that map then yields the `TwoSurjective` package used by
  the two-adic endgame.
- `lake build FLT.Assumptions.MazurProof.N13KummerKernelAssembly` passes;
  both assembly theorems audit with only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Proved generically in characteristic zero that every coordinate-ring
  unit fixed by hyperelliptic conjugation comes from a nonzero scalar of
  the ground field.  The proof uses only the canonical rank-two basis and
  the inverse-unit equation; it does not invoke divisor reduction or
  finite Mumford cases.
- `lake build FLT.Assumptions.MazurProof.SexticMumfordFixedUnit` passes.
  The key theorem's axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Constructed the sextic branch specialization
  `ℚ[X,Y]/(Y²-f) → ℚ(θ)` with `X↦θ`, `Y↦0`, and proved that it sends
  every hyperelliptic norm to a square.
- Defined `u(θ)` for every balanced N13 Mumford representative and proved
  it is nonzero from `deg u≤2<6`; irreducibility then packages it as a
  sextic-field unit and hence as a raw fake square class.  Added the
  generic theorem that every fake square-class target has exponent two.
- `lake build FLT.Assumptions.MazurProof.N13MumfordKummerValue` passes.
  Axiom audits for branch-norm squareness, nonvanishing, and the
  exponent-two consequence report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The raw N13 fake-Kummer value now sends the zero Mumford representative
  to zero.  A generic square-class bridge proves that a
  product-square-scalar identity for two values is exactly enough to
  identify their fake classes; this is the terminal algebraic step needed
  by the principal-ideal relation argument.
- `lake env lean
  FLT/Assumptions/MazurProof/N13MumfordKummerValue.lean` passes.  Axiom
  audits for the zero value, the exponent-two equality criterion, and the
  product-square-scalar bridge report only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Assembled the candidate calculation with the even-sextic kernel theorem.
  A `CandidateLocalization` now records exactly the two genuine arithmetic
  inputs: every global Kummer value enters the four-generator envelope, and
  its actual first two-adic logarithm vanishes.  These inputs imply that the
  Kummer map is trivial; the explicit infinity half then implies
  surjectivity of doubling.
- `lake build FLT.Assumptions.MazurProof.N13FakeDescentAssembly` passes.
  Axiom audits for candidate collapse, Kummer triviality, and doubling
  surjectivity report only `propext`, `Classical.choice`, and `Quot.sound`.
- Proved the principal-relation theorem for the N13 Mumford value.  After
  multiplying an ideal relation by its conjugate, the remaining coordinate
  unit is conjugation-fixed and hence rational; integral numerator and
  conumerator witnesses then give the required scalar-square identity.
  The three-ideal version proves additivity, and both results descend
  directly through equality and addition in the oriented Picard quotient.
- Constructed the actual fake-Kummer homomorphism from any proof that
  balanced Mumford representatives are surjective.  A noncomputable section
  is sufficient: principal-relation invariance makes the value independent
  of the chosen section, and the three-ideal theorem proves `map_add`.
  Uniqueness of normal forms and a transported group law on Mumford data are
  not required.
- `lake build FLT.Assumptions.MazurProof.N13MumfordKummerRelation` and
  `lake build FLT.Assumptions.MazurProof.N13MumfordKummerHom` pass.  Axiom
  audits for the six relation theorems and the descended homomorphism report
  only `propext`, `Classical.choice`, and `Quot.sound`; neither file contains
  a proof escape.
- Advanced balanced-representative existence through the quadratic
  Hermite layer.  A nonzero integral ideal has nonzero contraction to
  `K[X]`, hence a canonical monic generator `u`.  If the ideal is primitive
  (it contains an element with `Y`-coefficient one), coefficient
  decomposition constructs `v` and proves the exact graph presentation
  `J=(u,Y-v)`, with `u ∣ f-v²` and `v` reduced modulo `u`.
- Every oriented Picard class now has an integral invertible-ideal
  representative and every such ideal has a rank-two Smith presentation.
  The remaining representative work is precisely principal scaling to a
  primitive ideal followed by well-founded Cantor reduction.  The latter
  has a purely algebraic route: use `(f-v²)/u` above degree three, and at
  degree three replace `v` by `v+u` so the monic degree-six terms cancel.
- `lake build FLT.Assumptions.MazurProof.SexticMumfordRepresentative`
  passes.  Axiom audits for Smith form, contraction, primitive graph form,
  integral representatives, and the final conditional surjectivity theorem
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Proved the easy direction of the actual N13 Kummer-kernel theorem.  The
  descended homomorphism kills every double because its target has exponent
  two; it also kills the infinity-difference class because that class has
  the explicit Mumford representative `u=1`.  Hence both standard
  even-sextic branches lie in the kernel.
- `lake build
  FLT.Assumptions.MazurProof.N13MumfordKummerKernelForward` passes.  Axiom
  audits for all four forward-kernel theorems report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Constructed the fixed Gaussian cubic order over `ℤ₂` and its exact
  first ramified quotient.  The map `i ↦ 1+ε`, `θ ↦ α` is surjective onto
  `F₈[ε]/(ε²)`; two nested monic power bases prove that its kernel is
  `(1-i)²=(2)`.  Thus the order modulo the ramified-prime square is
  equivalent to the dual-number ring without a ray-class table or
  cardinality enumeration.
- `lake env lean
  FLT/Assumptions/MazurProof/N13GaussianOrderTwo.lean` passes.  Axiom
  audits for power-basis recomposition, reduction surjectivity, kernel
  equality, and the quotient equivalence report only `propext`,
  `Classical.choice`, and `Quot.sound`.  Identifying this explicit order
  with the completed maximal order and transporting the genuine Kummer
  value remain separate arithmetic-semantic bridges.
- Proved a single low-degree local lemma covering every primitive
  `ℤ₂`-polynomial of degree at most two.  Evaluation at `θ` reduces to the
  constant jet obtained by evaluating its residue polynomial at `α`, and
  this value is nonzero because no nonzero polynomial below the cubic
  minimal degree can vanish at `α`.  Thus its first ramified logarithm is
  zero, including the nonsplit quadratic case without a factor table.
- `lake build FLT.Assumptions.MazurProof.N13GaussianLowDegree` passes.
  Axiom audits for reduction/evaluation compatibility, low-degree
  nonvanishing, and logarithm vanishing report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Defined the full degree-six norm-pair target before forgetting the norm
  root.  The abstract target remembers `(α,s)` with `N(α)=s²` and quotients
  by `(β²,Nβ)` and `(q,q³)`.  Projection to the first coordinate descends
  to the fake target, every full class has exponent two, and its forgetting
  kernel is represented by pairs `(1,ε)` with `ε²=1`.
- Specialized this construction to the N13 sextic field.  The power basis
  gives rank six and the scalar norm formula; over `ℚˣ`, the only possible
  signs are `1` and `-1`.  Hence the concrete forgetting kernel consists
  of at most the identity and `(1,-1)`, without asserting that they are
  distinct.  `lake build FLT.Assumptions.MazurProof.N13FullNormPair`
  passes, and all target/kernel axiom audits report only `propext`,
  `Classical.choice`, and `Quot.sound`.  The Picard full-Kummer exactness
  theorem remains separate.
- Proved the structural one-step Cantor complement for every smooth monic
  sextic in characteristic zero.  Congruent graph polynomials define the
  same ideal; a transported Bézout relation proves
  `I(u,V)I(w,V)=(Y-V)`; squarefreeness makes `w` nonzero; normalization and
  conjugation use the essential next graph `(-V) mod normalize(w)`.
- The oriented correction is carried by the explicit function
  `(Y-V)/normalize(w)` and its positive-infinity order, so the resulting
  semireduced datum represents the same concrete Picard class.  For
  `deg u>3` the affine degree strictly falls; at `deg u=3`, taking
  `V=v+u` cancels the two monic degree-six leading terms and lands in
  degree at most two.  The target build and all nine key axiom audits are
  standard-only.  This is intentionally the affine-degree phase: the
  separate infinity-orientation balancing recursion is still required
  before claiming a balanced representative.
- Closed the primitive-scaling seam structurally.  The ideal of
  `Y`-coefficients of an integral ideal also contains all constant
  coefficients, so division by its canonical polynomial generator is an
  exact colon-ideal factorization.  The quotient ideal is primitive and
  remains fractionally invertible.  Multiplication by the corresponding
  principal function, with its actual `ordPlus`, proves equality in the
  oriented Picard quotient.
- Every oriented class therefore has a semi-Mumford representative.
  Iterating the verified Cantor step by recursion on `natDegree u` now
  produces one with `natDegree u≤2`, preserving the full oriented class at
  every step.  `lake build
  FLT.Assumptions.MazurProof.SexticMumfordStructuralReduction` passes;
  audits of content factorization, primitive scaling, graph extraction,
  the strict step, and the final existence theorem report only `propext`,
  `Classical.choice`, and `Quot.sound`.  Infinity balancing remains a
  separate Phase II.
- Removed infinity Phase II from the fake-Kummer dependency chain.  A
  low-degree semirepresentative is converted only for evaluation to a
  balanced datum with the same `(u,v)` and `nInf=0`; its original integer
  infinity coordinate remains in `semiMumfordClass`.  Equality and
  additivity first extract the finite principal-ideal relation from those
  original oriented classes, then reuse the existing `u(θ)` relation
  theorem.
- This gives an unconditional homomorphism
  `N13LowDegreeKummerHom.mumfordKummer`; no
  `Function.Surjective (classOf M O)` parameter remains.  `lake build
  FLT.Assumptions.MazurProof.N13LowDegreeKummerHom` passes.  Axiom audits
  for affine-ideal preservation, relation invariance, additivity,
  low-degree surjectivity, and the final homomorphism report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Replaced the abstract/conditional map in the forward-kernel endpoint by
  the unconditional low-degree map.  It kills doubles, the
  infinity-difference class, and their sums.  The fake-descent assembly now
  exposes `actualKummer` and a final
  `twoSurjective_of_actualCandidateLocalization` theorem whose only inputs
  are the converse even-sextic kernel statement and CandidateLocalization.
- Target builds for `N13MumfordKummerKernelForward` and
  `N13FakeDescentAssembly` pass.  All five new forward/integration theorem
  audits report only `propext`, `Classical.choice`, and `Quot.sound`.
- Closed N13 infinity balancing structurally.  The true cubic branch part
  `s=X³+2X²+X-1` satisfies `f-s²=4X(X+1)`.  Positive- and negative-adapted
  Cantor lifts have cofactor degree at most two; their opposite-branch
  leading coefficients are exactly `-2` and `2`, so the branch-norm
  identity gives the exact two orientation updates.  Recursion on the sum
  of the lower- and upper-wall defects proves
  `N13MumfordInfinityBalance.classOf_surjective`.
- The resulting unconditional balanced-representative Kummer homomorphism
  is proved extensionally equal to
  `N13LowDegreeKummerHom.mumfordKummer`.  Single-file checks pass, no
  `sorry`, `admit`, axiom, `native_decide`, enumeration, or Riemann--Roch
  input occurs, and the two endpoint audits report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Formalized the exact Gaussian cubic arithmetic behind the N13 global
  descent.  The cubic times its conjugate is the guarded N13 sextic, its
  discriminant is `(3-2i)²`, and translation by `9` gives an Eisenstein
  polynomial at `3-2i`.  The Gaussian prime proof uses norm `13`; the
  constant-coefficient test reduces to `13 ∤ 62197`, with no ideal
  factorization table.
- Added a reusable discriminant--Eisenstein integral-closure criterion.
  The trace discriminant puts a prime-power multiple of every integral
  element in the monogenic order, and Mathlib's Eisenstein denominator
  removal divides out that power.  Targeted checks for both new files pass.
- Closed the generic norm/resultant and power-basis discriminant seams.
  The norm proof canonically reindexes the product over embeddings by the
  minimal polynomial's root multiset; no roots are selected or listed.
  The resulting theorem identifies a power-basis discriminant with the
  polynomial discriminant and transports it from an integrally closed base
  to its fraction field.  The rational `AdjoinRoot` specialization is
  exported for the N13 sextic.  Single-file checks and all four endpoint
  audits pass with only `propext`, `Classical.choice`, and `Quot.sound`.
- Constructed the global relative cubic field over
  `Frac(ℤ[i])`.  Eisenstein plus Gauss proves the translated cubic
  irreducible; its root is integral over `ℤ[i]`, with the displayed cubic as
  its exact integral minimal polynomial.  The relative power-basis
  discriminant is `(3-2i)²`, so the generic denominator-removal theorem
  identifies the full relative integral closure with `ℤ[i][α]`.
  The targeted check and audits of irreducibility, minpoly, discriminant,
  and maximal-order endpoints pass with only `propext`, `Classical.choice`,
  and `Quot.sound`.

### p11 avenue — CONFIRMED finding + verdict (2026-07-12)
- billing_mahler_global_descent sorry is NOT provable as stated. It conflates:
  * Part 1 `span{δ}=I²`: PROVABLE (Dedekind ideal-square from N(δ)=y², bad primes {2,3,11},
    each unique prime ideal has ODD residue degree ⇒ even exponent). Codex grinding it in
    RationalPointsN11IdealSquare (Mathlib exists_smul_of_dvd_count + prod_normalizedFactors_eq_self).
  * Part 2 `¬IsSquare δ`: NON-LOCAL. IsSquare δ ⟺ P∈2E(ℚ). Needs a selection/minimal-
    counterexample (infinite descent, height infra absent) OR two-good-primes finiteness
    (Layer-3 route, itself blocked on the point-reduction Mathlib gap, Q4501).
- Triple-confirmed: my read of BillingMahlerField.lean:1318-1347 (only δ=w² case needs hnonsquare;
  ±sign cases die by positive norm; ε-case by coefficient system) + ChatGPT Q4560 (my Q) +
  ChatGPT Q4567 (Codex's independent Q) all agree.
- Opus hand-work banked: DedekindSquareIdeal.lean (span{a}=I² from even factor counts) —
  CORRECT + axiom-clean (commit 47af3b68) but REDUNDANT (reinvents Mathlib exists_smul_of_dvd_count /
  Associates.is_pow_of_dvd_count; should have grepped first). Codex's route supersedes.
- PrimeTailPackage.lean scaffold banked axiom-clean (commit 84c8cdf7).
- Verdict: p11 closure is a genuine descent needing absent infra (height OR the Layer-3
  reduction seam). Max provable now = Part-1 + isolate Part-2 as precise named lemma
  descentElement_square_imp_exceptional. Codex driving toward that structure.

### Fable audit (2026-07-12) — verdict MIXED + corrective actions
- Failure mode identified: stopped at diagnosis+inventory, didn't CONVERT to campaign state;
  smuggled one un-escalated scope fork (PrimeTailPackage's p>19 wing).
- Corrective actions executed:
  1. p11 finding CONFIRMED via decisive unit/norm/squareclass check (not just LLM opinion):
     four squareclasses ±w²/±εw²; +norm kills negatives; w²(square/double) vs εw² choice = global
     2-descent info, non-local; cusps are squares so no congruence excludes square case. ⇒ ¬IsSquare
     genuinely non-local. Appended FINAL DIRECTIVE to Codex spec: isolate it as named lemma
     descentElement_square_imp_exceptional (dischargeable later from two-good-primes/TorsionFinitePackage),
     do NOT grind it. Codex still on provable Part-1, uncommitted — not killed.
  2. PrimeTailPackage scope fork ESCALATED to owner: p>19 tail provable only conditionally on
     [Kato A_p(ℚ) finite, winding nonvanishing] — never dischargeable in-campaign. Awaiting written sign-off.
  3. DedekindSquareIdeal DELETED (reinvented Mathlib exists_smul_of_dvd_count / is_pow_of_dvd_count).
     TorsionFinitePackage made WIRE-READY: added rational_torsion_set_finite_of_twoGoodPrimes matching
     the exact Set.Finite shape of TorsionFinite.rational_torsion_finite_of_mw (MW-FG-free). Interface
     drift caught + fixed. Full wiring into shared TorsionFinite.lean deferred (uncommitted edits there).
- Banked this session (tail-package branch): PrimeTailPackage (84c8cdf7), TorsionFinitePackage
  (wire-ready). Removed: DedekindSquareIdeal. Net main-theorem sorry/axiom change by Opus hand: 0
  (the value is the p11 audit + two wire-ready axiom-sharpening interfaces + drift-catch).

### N13 integral special-fibre reduction (2026-07-29)

- Completed the rank-two normal-form API for the N13 special coordinate
  ring: both coefficient projections on `xClass`, `yClass`, and their
  products are now available, together with coefficientwise extensionality.
- Proved coefficientwise reduction of polynomials and the induced reduction
  of the good-model coordinate ring are surjective.
- Proved the exact kernel formula
  `ker reduceCoordinate = (2)`.  The proof uses the rank-two normal form,
  `Polynomial.ker_mapRingHom`, and
  `PadicInt.ker_toZMod`; it does not enumerate residue classes or use a
  certificate.
- Targeted checks of `N13GoodCoordinateRingTwo.lean` and
  `N13GeneralizedMumfordReduction.lean` pass.  Axiom audits of special-ring
  extensionality, reduction surjectivity, and the kernel theorem report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- ChatGPT Q2729 confirmed the proper two-chart continuation: lift a
  normalized section in the module-valued Čech kernel, use a unit on every
  completed infinity branch for non-escape, prove the zero quotient finite
  flat of rank two, and recover the Mumford graph from the lifted basis
  `{1,x}` via the characteristic polynomial.  This avoids affine
  principality and general Cartier-divisor infrastructure.

### N13 generic--special defect detection (2026-07-29)

- Attached to every integral fractional ideal `H` its integral defect ideal
  whose fractional extension is exactly `H * H⁻¹`.  Generic invertibility of
  `H` now proves automatically that this defect ideal becomes the unit ideal
  after vertical localization.
- Proved that an integral ideal is the unit ideal whenever both its generic
  vertical localization and its special reduction are unit ideals.  The
  proof extracts a nonzero two-adic scalar from localization, replaces it by
  a power of two using `PadicInt.ideal_eq_span_pow_p`, lifts a special unit
  using surjectivity and `ker reduceCoordinate = (2)`, and closes with a
  finite geometric series.
- Consequently `isUnit_of_map_defectIdeal_eq_top` reduces invertibility of
  the divisorial hull to the single honest special-fibre condition
  `Ideal.map reduceCoordinate (defectIdeal H) = ⊤`.  No regular-local UFD,
  reflexive-to-projective theorem, completion, affine generator, or
  Noetherian induction is used.
- Targeted checks of `N13IntegralFractionalHull.lean` and
  `N13IntegralFiberDetection.lean` pass.  All four new endpoint audits report
  only `propext`, `Classical.choice`, and `Quot.sound`.
- ChatGPT Q2726--Q2730 independently agree that the regularity/UFD route is
  mathematically valid but much heavier in the pinned Mathlib.  Q2730
  identifies the same special trace witness as the shortest continuation.
  Q2733--Q2735 now ask for the exact module-valued Čech evaluation lift,
  the integral generalized-Mumford inverse formula, and the dual-pairing
  adapter.

### N13 product-level trace criterion (2026-07-29)

- Named the three special affine evaluations in the coordinate ring and
  proved that their images are the products in the explicit dual frame.
  Their sum is already one before passage to the special function field.
- Replaced factorwise integral lifting by a strictly smaller interface:
  each special evaluation only needs an integral representative whose image
  lies in `L * L⁻¹`.  Finite-sum closure transports these aggregate products
  to the defect ideal of the divisorial hull and gives the required element
  reducing to one.
- Added `N13SpecialProductLift.Data`, which states exactly the remaining
  three product-level witnesses and feeds them into the generic--special
  criterion.  This avoids any reduction map on `L⁻¹` and any false claim
  that the six affine factors extend as proper global sections.
- The product witnesses are still the full special trace-unit certificate;
  they do not follow from vertical contraction and generic invertibility
  alone.  The next semantic input must identify the canonical contraction's
  special fibre with the fixed base line, or construct the equivalent trace
  witness geometrically.
- Targeted checks of `N13SpecialDualFrame.lean`,
  `N13IntegralFiberDetection.lean`, and
  `N13SpecialProductLift.lean` pass.  Axiom audits of the four new endpoints
  report only `propext`, `Classical.choice`, and `Quot.sound`.

### N13 exact integral-graph contraction (2026-07-29)

- Proved that extension of a smooth integral generalized Mumford graph to
  the standard sextic generic fibre, followed by canonical contraction,
  recovers the original graph ideal exactly.  The proof reuses the existing
  coefficient-extension `comap_map_mumfordIdeal` theorem and cancels
  completion of the square as a coordinate-ring equivalence.
- Specialized this to the literal sextic ideal attached by
  `sexticSemi D nInf`, and recorded the corresponding equality of contracted
  fractional ideals in the common function field.  These are
  representative-level equalities, not Picard-class comparisons.
- This is deliberately a downstream adapter: it applies after a smooth
  integral graph has been constructed and does not prove such a graph exists
  for an arbitrary specialization-kernel class.
- The targeted check of `N13IntegralGraphContraction.lean` passes.  Axiom
  audits of all three public endpoints report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- ChatGPT Q2757 isolates the post-invertibility geometry sharply.  An
  embedded special-fibre framing gives flatness of the affine quotient, but
  finiteness still needs one genuine no-escape input at the proper infinity
  chart.  After finiteness, the basis `{1,x}`, characteristic polynomial,
  and polynomial division recover the integral Mumford graph by pure
  algebra.

### N13 integral model and vertical Cartier fibre (2026-07-30)

- Proved both ordinary chart rings are domains and used the explicit
  two-chart cover to prove the glued two-adic model is integral.  On the
  infinity chart the regularity of `t` follows structurally from the free
  rank-two `ℤ₂[t]` presentation; no point enumeration is used.
- Identified the actual closed-fibre locus as the inverse image of the
  unique closed point of `Spec ℤ₂`.  Since the explicitly glued special
  fibre is irreducible, this locus is the unique nonempty maximal
  irreducible closed vertical subset.
- Packaged the two chart reductions as principal effective-Cartier data:
  the image of `2` is a non-zero-divisor, reduction is surjective, and its
  kernel is exactly the principal ideal generated by that image.
- Proved the two local equations agree literally under the ordinary overlap
  equivalence.  Their principal ideals therefore glue with identity
  transition; every integer vertical twist still has identity transition
  after reduction.  This supplies the geometric input for
  `special_verticalTwist` without a general Cartier-divisor library.
- Targeted checks of `N13IntegralCurveProperties.lean`,
  `N13VerticalFibreTopology.lean`, `N13VerticalCartierCharts.lean`, and
  `N13VerticalCartierGlue.lean` pass.  The three gluing endpoint audits
  report only `propext`, `Classical.choice`, and `Quot.sound`.

### N13 recovered integral graph spreads (2026-07-30)

- Combined exact graph contraction with the global relative-Jacobian
  Bézout frame.  For every smooth integral generalized Mumford graph, the
  canonical contraction is already an invertible integral fractional
  ideal, so its divisorial double inverse is literally the original graph
  ideal.
- More generally, any generic ideal whose canonical contraction is
  recovered as a smooth integral graph has an invertible divisorial hull.
  Applying the existing two-fibre basis and graph-recovery theorem shows
  that a balanced quadratic graph with the fixed mapped special ideal
  needs no further contracted-factor lift or local-factoriality argument.
- Targeted checks of `N13IntegralGraphSpread.lean` and
  `N13RecoveredGraphSpread.lean` pass.  Both endpoint audits report only
  `propext`, `Classical.choice`, and `Quot.sound`.

### N13 arbitrary-special-graph spreads (2026-07-30)

- Removed the hardcoded special graph from the two-fibre no-escape layer.
  Every monic quadratic special Mumford graph quotient has the literal
  basis `{1,x}` by graph evaluation and the canonical polynomial power
  basis.
- Factored graph recovery before its fixed-special smoothness calculation:
  an integral quotient basis `{1,x}` already reconstructs a monic
  quadratic integral semigraph and identifies its graph ideal exactly with
  the canonical contraction.
- The global integral Jacobian frame applies to every such semigraph, so a
  quadratic generic graph has an invertible divisorial spread as soon as
  its mapped contraction is the graph ideal of any quadratic special
  Mumford datum.  The remaining condition is packaged as
  `N13ArbitrarySpecialGraphSpread.SpecialGraphModel`; it no longer names a
  fixed Picard class or asks for three contracted factor lifts.
- Targeted checks of `N13SpecialGraphQuotientBasis.lean`,
  `N13TwoFiberGraphBasis.lean`, `N13RankTwoSemiGraphRecovery.lean`, and
  `N13ArbitrarySpecialGraphSpread.lean` pass.  Audits of all four endpoints
  report only `propext`, `Classical.choice`, and `Quot.sound`.

### N13 semigraph contraction and the degree-one branch (2026-07-30)

- Removed the unnecessary `SmoothMumford₂.bezout` requirement from exact
  coefficient extension and contraction.  Monicity alone makes polynomial
  divisibility descend from `ℚ₂` to `ℤ₂`, so every integral generalized
  semigraph contracts exactly to its original graph ideal.
- Combined that exact semigraph contraction with the global integral
  Jacobian frame.  Every integral semigraph now directly supplies an
  invertible divisorial spread; a separate vertical smoothness certificate
  is no longer part of this interface.
- Identified the selected Padé root's degree-one branch intrinsically.
  A balanced monic linear graph with zero infinity coordinate is exactly
  the graph of one affine rational curve point: monicity determines `u`,
  reducedness makes `v` constant, and the Mumford divisibility relation
  evaluates to the curve equation.  Thus this branch is routed to the
  existing proper affine/infinity two-chart point reduction rather than to
  the quadratic quotient-basis argument.
- Targeted checks of `N13TwoAdicMumfordTransport.lean`,
  `N13TwoAdicCoordinateBaseChange.lean`,
  `N13IntegralGraphContraction.lean`, `N13IntegralGraphSpread.lean`, and
  `N13DegreeOneGraphPoint.lean` pass.  Audits of the five new endpoints
  report only `propext`, `Classical.choice`, and `Quot.sound`.

### N13 integral affine point spreads (2026-07-30)

- Constructed the monic linear integral semigraph attached to every
  integral point of the good two-adic affine chart.  Its curve equation is
  the factor theorem applied to the point residual.
- Proved that completion of the square carries this semigraph to the
  standard sextic Mumford graph of the corresponding curve point.  Exact
  semigraph contraction and the global Jacobian frame therefore make its
  canonical divisorial hull invertible.
- Applied the construction to the selected degree-one Padé graph.  If its
  rational affine `x`-coordinate is two-adically integral, the exact
  selected graph now has an invertible spread.  Otherwise its `x`-coordinate
  has negative valuation and the point is routed, with no ambiguity, to
  the existing infinity-chart lift.
- The targeted check of `N13IntegralAffinePointSpread.lean` passes.  Audits
  of its three main endpoints report only `propext`, `Classical.choice`,
  and `Quot.sound`.

### N13 integral infinity point spreads (2026-07-30)

- Factored the generalized graph-ideal product calculation into a
  coefficient-independent ring-theoretic core.  A graph ideal times its
  hyperelliptic conjugate is the principal horizontal ideal whenever
  `u`, `2v+h`, and the residual quotient satisfy the displayed Bézout
  identity.
- For every integral point of the ordinary infinity chart above `t=0`,
  proved that the ordinate Jacobian reduces to one.  Its point ideal
  `(t-t₀,v-v₀)` therefore has an explicit conjugate inverse and is
  invertible as a fractional ideal.
- Generalized the affine global-Jacobian dual frame from monic semigraphs
  to every nondegenerate polynomial graph.  This applies to the weighted
  affine closure `(1-t₀x, y-v₀x³)` of an infinity point, whose exact graph
  factorization follows from the weighted chart equation.
- Proved that the affine and infinity point ideals agree after restriction
  to the ordinary overlap: their generators differ by the units `x` and
  `x³`.  Packaged the two invertible ideals and this equality as an honest
  two-chart line, and instantiated it for every negative-valuation affine
  point supplied by `nonintegralInfinityLift`.
- Proved that the generic fibre of the affine half is exactly the
  coefficient-extended, completed-square sextic graph.  This leaves only
  a representative comparison with the standard degree-one point graph.
- Completed that comparison for every negative-valuation point:
  `1-t₀X` is a nonzero scalar multiple of `X-x`, while the completed graph
  ordinate evaluates to `2y+h(x)` and hence differs from its constant
  point ordinate by a multiple of `X-x`.  The generic fibre of the
  two-chart line is therefore literally the standard point Mumford ideal.
- Applied the equality to the selected degree-one Padé graph.  Its escape
  alternative now supplies an explicit invertible two-chart line whose
  generic ideal is exactly the selected two-adic graph.  Thus degree one
  has no remaining unrepresented nonintegral branch.
- Targeted checks of `GeneralizedGraphIdealCore.lean`,
  `N13IntegralGraphJacobian.lean`, `N13OrdinaryCurveOverlap.lean`, and
  `N13IntegralInfinityPointSpread.lean` pass; the follow-up check of
  `N13EscapingDegreeOneSpread.lean` also passes.  No point enumeration,
  normality, local factoriality, or finite certificate is used.
