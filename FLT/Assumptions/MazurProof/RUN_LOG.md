
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
- Proved generically in characteristic zero that every coordinate-ring
  unit fixed by hyperelliptic conjugation comes from a nonzero scalar of
  the ground field.  The proof uses only the canonical rank-two basis and
  the inverse-unit equation; it does not invoke divisor reduction or
  finite Mumford cases.
- `lake build FLT.Assumptions.MazurProof.SexticMumfordFixedUnit` passes.
  The key theorem's axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

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
