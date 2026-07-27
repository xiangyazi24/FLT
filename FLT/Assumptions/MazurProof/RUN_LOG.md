
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
