# Keystone Master Design — n-torsion + Weil pairing (consolidated, rounds 1–4)

Source: 3 ChatGPT design rounds (dm1 n_torsion_card route, dm2 Route C / Weil-unavoidable,
dm3 full architecture DAG) + dm1 Miller construction (route B) + dm3 round-4 finiteness (pending).
Scaffold: David Angdinata's `FLT/EllipticCurve/Torsion.lean` (in our tree). Verdict across all
rounds: **scaffold is the right foundation, refactor the API around it.**

## The convergence: 2 irreducible hard cores + 1 independent input

Everything to discharge `weil_pairing_primitive_root` and `rational_torsion_two_invariant_factors`
reduces to these three, plus mechanical glue that Mathlib already supports.

### CORE 1 — `n_torsion_card : Nat.card (E.nTorsion n) = n²` (the keystone)
Bottleneck = ONE missing Mathlib theorem (two halves):
- (KER) `preΨ'_root_iff`: for affine P=(x,y) with 2•P≠0,  `n • P = 0 ↔ (E.preΨ' n).eval x = 0`.
- (SEP) `preΨ'_separable_of_natCast_ne_zero`: `(n:k)≠0 → (E.preΨ' n).Separable`.
These are "the algebraic geometry behind [n] is étale when char∤n." Mathlib obstruction:
the bivariate ωₙ (y-coord of [n]P) is explicitly TODO, so there is NO `[n]P=(φ/ψ²,ω/ψ³)`
coordinate formula to lean on — (KER) must be done via recursion relations OR a minimal ωₙ dev.
Everything downstream is already in Mathlib:
`natDegree_preΨ'` = (n²−(if even 4 else 1))/2, `card_rootSet_eq_natDegree` (sep+splits),
`IsSepClosed.splits_domain`, `Submodule.mem_torsionBy_iff`, parity `omega`.
Final proof once (KER)+(SEP) land: odd n → 1+2·(n²−1)/2=n²; even n → 4+2·(n²−4)/2=n² (card E[2]=4 via `Ψ₂Sq_eq`).

#### CORE 1 decomposition (dm2 round-3, task d97fd451 — the keystone bottleneck)
Two hard primitives; everything else is Mathlib-ready bookkeeping. Minimal lemma list A–E:
- **A** `two_nsmul_eq_zero_iff_Ψ₂Sq_eval_eq_zero` — small. `ψ₂=2Y+a₁X+a₃`, `Ψ₂Sq=twoTorsionPolynomial.toPoly`, `Point.add_self_of_Y_eq`.
- **B** `xRep_zsmul_some_eq_divisionPolynomial`: `SameP1 (n•P).xRep ![Φₙ(x), ΨSqₙ(x)]` — THE main missing coordinate formula. **Uses only Φ/ΨSq, NOT the TODO ωₙ** ⇒ far smaller than full [n]P map. Proof: strong induction matching EDS recurrences (`mk_ψ`,`mk_φ`) to group law (`Point.add_some/add_of_Y_ne/add_of_Y_ne'/add_self_of_Y_eq`). Mathlib anchors: `Point.xRep` (0↦![1,0], (x,y)↦![x,1]), `xRep_neg`, `xRep_eq_xRep_iff` (same xRep ⟺ P=±Q — gives the ± fiber count). HARD but mechanical.
- **C** `nsmul_eq_zero_iff_preΨ'_eval_eq_zero_of_two_nsmul_ne_zero` — easy from A+B. (`ΨSq n = preΨ n ^2 * (if even then Ψ₂Sq else 1)`; even case uses 2•P≠0 ⇒ Ψ₂Sq(x)≠0.)
- **D** `preΨ'_eval_eq_zero_iff_exists_non_two_torsion` [IsSepClosed] — no-spurious-roots converse, needed for the counting bijection.
- **E** `preΨ'_separable_of_natCast_ne_zero : (n:k)≠0 → (W.preΨ' n).Separable` = explicit étaleness of [n]. **ISOLATE AS NAMED SEAM** (dm2 round-5 verdict) — discharge n_torsion_card MODULO it now, grind the seam later. The seam→downstream bridge is SHORT and Mathlib-ready:
  `Polynomial.separable_of_resultant_derivative_ne_zero` (via `separable_def` + `resultant_eq_zero_iff`), `preΨ'_ne_zero`, then `card_rootSet_eq_natDegree` + `natDegree_preΨ'`. Mathlib HAS resultant API (`Mathlib.RingTheory.Polynomial.Resultant.Basic`: `resultant`, `discr`, `resultant_eq_zero_iff`, `resultant_deriv`, `isUnit_resultant_iff_isCoprime`).
  Two routes to PROVE the seam later, both relocate the hard content (neither is short):
  - E2 (resultant/discr): short bridge, but the hard part is `resultant_preΨ'_derivative_formula` — closed form in n/Δ for Mathlib's PARITY-SPLIT preΨ' (lead coeff n/2 even, n odd) via EDS recurrence. Long, fragile, NOT reusable. `resultant_deriv` has explicit Sylvester-size args (`natDegree`, `natDegree−1`) — derivative-degree normalization can fail in pos char, adjacent to separability itself; work with raw resultant not `discr`.
  - E1 (formal group, PREFERRED for durability): `[n]*t = n·t + h.o.t.` ⇒ nonzero differential ⇒ étale ⇒ simple roots. Mathlib has GENERIC `FormalGroup` (`Mathlib.RingTheory.FormalGroup.Basic`) but NO `WeierstrassCurve.formalGroup` — must build it (t=−x/y, formal group-law expansion, bridge to preΨ' root multiplicity). Serious dev, but REUSABLE (feeds Weil pairing, Galois reps, det=cyclotomic).
Bookkeeping (all Mathlib-ready): `card_rootSet_eq_natDegree`, `natDegree_preΨ'`, `Ψ₂Sq_eq`/`twoTorsionPolynomial_discr_ne_zero_of_isElliptic`, ± fiber via `xRep_eq_xRep_iff`.
The true hard split: (1) x-coord formula for [n]P via Φₙ/ΨSqₙ [B]; (2) simple-root/étaleness for preΨ'ₙ [E].

### CORE 2 — Weil pairing (for `weil_pairing_primitive_root`)
dm2 verdict: det=cyclotomic / ∧²E[n]≅μ_n does NOT dodge the pairing — it IS the pairing.
But for the axiom we need, the **direct pairing-value route is shorter than det**:
- Build `WeilPairingPackage` interface (pairing E[n]×E[n]→rootsOfUnity n k; bi-multiplicative;
  alternating; `exists_basis_pair_primitive`).
- **Stage 1 (easy):** `full_rational_torsion_has_primitive_root (WP) (hfull) : ∃ ζ:ℚ, IsPrimitiveRoot ζ m`
  — discharges the axiom from the abstract package. If pairing is over ℚ with ℚ-rational basis,
  ζ∈ℚ directly, NO Galois-descent needed.
- **Stage 3 (heavy):** construct the pairing — route B (Miller/line functions), blueprint below.

#### Miller construction (route B) — full blueprint (dm1, saved Miller_RouteB_Construction.md)
Mathlib has the ingredients but no bundled divisor/evaluation/reciprocity layer. Use a
**syntactic carrier**, not raw FunctionField elements.
- Line/vertical from `Affine.linePolynomial`, `Affine.slope`, `CoordinateRing.XClass/YClass`.
- `inductive MillerFactor | line | vertical | const`; `inductive MillerExpr | one|factor|mul|inv`.
- Step factor g_{A,B} normalized with a minus sign so `lcAtO (gLineExpr)=1` (kills the (−1)^m).
- Linear Miller recurrence: state ([n]P, f_{n,P}); `millerState_fst : (millerState P n).1 = n•P`.
- Divisor map `divExpr : MillerExpr → (Point →₀ ℤ)`. Key:
  `div_gLineExpr = ⟦A⟧+⟦B⟧−⟦A+B⟧−⟦0⟧`;  `div_millerExpr = n•⟦P⟧−⟦n•P⟧−(n−1)•⟦0⟧`;
  for P∈E[m]: `div_millerExpr_of_mem_nTorsion = m•⟦P⟧−m•⟦0⟧`.
- Pairing via degree-0 divisor evaluation (disjoint support): choose D_P∼[P]−[O], D_Q∼[Q]−[O],
  `e_m(P,Q)=f_{m,P}(D_Q)/f_{m,Q}(D_P)`, land in `rootsOfUnity m k` via `rootsOfUnity.mkOfPowEq`.
- Direct computational form (after perfection): `e_m(P,Q)=f_{m,P}(Q)/f_{m,Q}(P)` (normalized, no sign).

Property difficulty (build in this order):
1. **Galois-equivariant — EASIEST.** Induction over MillerExpr + `slope` base-change lemma;
   `IsFractionRing.algEquivOfAlgEquiv`, `MulEquiv.restrictRootsOfUnity`.
2. **Lands in μ_m — MEDIUM.** Follows from bilinearity: e^m=e(mP,Q)=e(0,Q)=1.
3. **Bilinearity + alternating — HARD.** Central primitive `weil_reciprocity_millerExpr`
   (evalDiv f (div g) = evalDiv g (div f) on disjoint support) — a minimal principal-divisor
   calculus, NOT a full Picard group. Then bilinearity is textbook.
4. **Nondegeneracy/perfectness — HARDEST.** ⚠ CORRECTION (dm1 round-4): does NOT follow from
   cardinality. A bilinear alternating A×A→μ_m with |A|=m², |μ_m|=m can still be TRIVIAL — kernel=⊥
   is NOT forced by card. So `nondeg_left`/`nondeg_right` must be PACKAGE FIELDS proven geometrically
   (or via explicit basis formula e(aP+bQ,cP+dQ)=ζ^{ad−bc} with ζ primitive, or Cartier duality).
   card(E[m])=m² is necessary but NOT sufficient. Keep nondeg as a package field/separate geometric
   theorem, do NOT derive from the Miller files. (Mathlib `BilinForm`/`Module.Dual` only helps AFTER
   converting μ_m→ZMod m via a chosen primitive root, and only for the additive picture.)

##### Weil reciprocity — tame-symbol architecture (dm1 round-4)
⚠ Naive `evalDiv f (div g) = evalDiv g (div f)` by pairwise disjoint induction is WRONG — raw
line/vertical functions all have poles at O so divisors share O, and intermediate factors can share
finite zeros. Clean primitive = tame-symbol product:
`tameSymbol P f g := (−1)^(ord_f P · ord_g P) · lc_g(P)^{ord_f P} / lc_f(P)^{ord_g P}`;
`tame_product_millerExpr : ∏ᶠ P, tameSymbol P f g = 1` (extend multiplicatively from base cases by
induction). Base cases = regularized resultant identities via `Polynomial.resultant_comm`
(`f.resultant g m n = (−1)^(m·n) · g.resultant f n m` — THE parity sign; line=pole-order 3, vert=2,
so ONLY line-line carries a minus). EC anchors (already in Mathlib's group-law proof):
`addPolynomial_slope` (W(X,line)=−(X−x₁)(X−x₂)(X−x₃)), `C_addPolynomial_slope`,
`XYIdeal_neg_mul`, `XYIdeal_mul_XYIdeal`. Then `weil_reciprocity_millerExpr` (disjoint-support form)
is a corollary. Time-sink rank: (1) evalDiv/local-symbol well-definedness [hardest — shared poles +
cancellation, needs the tame-symbol calculus], (2) pairwise resultant reciprocity, (3) nondeg [package].
Use MULTISETS not Finsets for repeated-root/tangent cases.

### INDEPENDENT INPUT — torsion finiteness (for `rational_torsion_two_invariant_factors`)
dm3 critical catch: `Finite (E(ℚ)_tors)` CANNOT be recovered from per-level E[n] finiteness
(ℚ/ℤ is the warning: every n-torsion finite, total infinite). Must be supplied independently:
- Route (i): full Mordell-Weil `AddGroup.FG (E(ℚ))` → `AddCommGroup.finite_of_fg_torsion`.
- Route (ii): reduction mod two good primes → torsion injects into ∏ finite E(F_p).
**dm3 round-4 VERDICT (task bk3zkq352):**
- Route (ii) mod-p reduction is a SERIOUS arithmetic-geometry project: Mathlib `Reduction` has
  curve-level `reduction`/`HasGoodReduction`/`IsMinimal`/`integralModel` but NOT the point-reduction
  map, NOT the formal group, NOT prime-to-p torsion injectivity (`reductionMap`, formal-group kernel,
  `formalGroup_nsmul_injective_of_isUnit` all absent). Comparable to a small independent dev.
- **RECOMMENDATION (b) [POLICY DECISION — Xiang's call, escalated]:** keep `rational_torsion_finite :
  Finite (RatTors E)` as a SMALL separate axiom (weaker than `mordell_weil_fg`; exactly what's needed),
  discharge `rational_torsion_two_invariant_factors` from it + keystone + pure algebra. Net: proves the
  rank-≤2 STRUCTURE, isolates the irreducible arithmetic (finiteness) into a cleaner seam.
  ⚠ Tension with no-axiom-escape doctrine: this TRADES one axiom for a smaller one rather than fully
  discharging. The "open the mountain" alternative is to grind `mordell_weil_fg` (full Mordell-Weil)
  → derive `rational_torsion_finite` via `AddCommGroup.finite_of_fg_torsion`. Method-flexibility = senior
  author decides. (`rational_torsion_finite_of_mordell_weil_fg` is the bridge if MW is later proven.)
- **Pure-algebra tail — BUILD-READY NOW, policy-independent, 0-axiom, no elliptic geometry:**
  `finite_add_comm_group_embed_zmod_sq_invariantFactors_card` (finite G ↪ (ZMod N)² ⟹ ∃ m n, m∣n ∧
  Nat.card G = m*n ∧ G ≃+ ZMod m × ZMod n). Full proof sketch from dm3:
  (1) `AddCommGroup.equiv_directSum_zmod_of_finite` → elementary-divisor form ⊕ZMod(pᵢ^eᵢ);
  (2) for each prime p, G[p] ↪ (ZMod N)²[p] (card ≤ p²) ⇒ at most TWO p-primary summands
      (3 would give #G[p]≥p³); APIs `addOrderOf_dvd_card`, `card_nsmul_eq_zero`, `AddCommGroup.torsion`;
  (3) regroup: m=∏p^(a_p), n=∏p^(b_p) with a_p≤b_p ⇒ m∣n;
  (4) reassemble via `ZMod.chineseRemainder`. A real regrouping lemma, NOT one Mathlib decl.
  → dispatched to Codex as the first concrete 0-axiom build (independent of API-shape lock).

## DESIGN CONVERGED — the four named seams (axiom-as-seam)
The whole campaign reduces to four isolated primitives. Build ALL structure around them to
0-axiom-modulo-seam; grind each seam separately. This is the same discipline that worked for the
N10/N12 cases (axiom = self-contained math seam, not sorry-escape).
- **SEAM 1** `preΨ'_separable_of_natCast_ne_zero` — [n] étaleness (core 1). Via E1 formal-group route
  (per "彻底+复用"). **dm1 SEAM1 design (scratch/SEAM1_FormalGroup_ROADMAP.md):** full
  `WeierstrassCurve.formalGroup` = thousands of lines (sigma + formalAddSeries + assoc) — DON'T build it
  just for the seam. **Shortcut: DualNumber first-jet** (R[ε], ε²=0): `tangentOPoint W a = [-aε:1:0]`,
  prove `d[n]_O(a) = n·a` by induction on the projective add formula — gives the tangent fact without
  sigma/assoc. Reusable generic piece: `FormalGroup.formalNsmul_coeff_one : coeff 1 ([n]_F) = n`.
  **The real hard primitive = the local-order bridge `preΨ'_order_one_at_non2_kernel`** (d[n]_O≠0 + x has
  double pole at O + ΨSq=preΨ'²·(2-tors factor) ⇒ preΨ' has simple zeros), then
  `preΨ'_derivative_ne_zero_at_root` → `separable_of_derivative_ne_zero_at_roots`.
  ⚠ **SEAM 1 DEPENDS ON SEAM 2**: the bridge needs `xCoord_nsmul_eq_Φ_div_ΨSq` (the x([n]) formula) +
  the root characterization. So SEAM 2 is the shared foundation — build it FIRST. Keep full formalGroup as
  a later reusable library artifact. Final assembly via `Polynomial.separable_map` from AlgebraicClosure.
- **SEAM 2** `xRep_zsmul_some_eq_divisionPolynomial` — [n]P x-coord via Φ/ΨSq (core 1). NOT really a
  seam: provable by EDS strong induction + group-law lemmas, no MISSING Mathlib primitive — HARD but
  mechanical. The first real keystone GRIND target.
- **SEAM 3** Weil pairing geometric properties (core 2): `weil_reciprocity_millerExpr` (tame symbols +
  resultants) + `nondeg_left/right` (geometric, NOT from card). Package as `WeilPairingPackage` fields;
  Stage-1 axiom discharge needs only the package, not the construction.
- **SEAM 4** finiteness leg — **DECIDED per "彻底+复用"**: NO new weak axiom. Derive
  `rational_torsion_finite` from the EXISTING `mordell_weil_fg` axiom (already done in
  `rational_torsion_finite_alias` via `torsion_set_finite_of_fg`). The THOROUGH finish = grind
  `mordell_weil_fg` itself later (full Mordell-Weil = cornerstone, max reuse) — it's the mountain to
  attack, not a permanent axiom. Discharging `rational_torsion_two_invariant_factors` now → axiom 6→5.
Everything else = Mathlib-ready bookkeeping + the Stage-0 API refactor + pure-algebra tail (Codex building).

## Dependency DAG
```
            preΨ'_root_iff (KER) + separability (SEP)      [CORE 1 bottleneck]
                          │
                  n_torsion_card = n²        ◄────────────────────┐
                          │                                       │
         geomNTorsion n ≃ₗ[ZMod n] (Fin 2→ZMod n)   [shared keystone]
                    │                    │                        │
        (B) rational_torsion       (A) WeilPairingPackage         │
          needs ALSO:                  Stage 1 (easy)             │
          torsion FINITENESS           discharges axiom           │
          (mordell_weil_fg /           │                          │
           mod-p reduction)            Stage 3 Miller ────────────┘
          + invariant-factor algebra   (perfection needs card)
                    │                    │
   rational_torsion_two_invariant   weil_pairing_primitive_root
```

## Build order (synthesized)
- **Stage 0 (design-stable, do first, no hard math):** API refactor per dm3 — `PointsOver L`,
  `nTorsionOver L n`, `geomNTorsion`, `baseNTorsion`, `nTorsionOver.map/mapLinear/map_injective`,
  `ratNTorsionToGeom`. Upgrade `n_torsion_dimension` from `≃+` to `≃ₗ[ZMod n]` /
  `Module.Basis (Fin 2) (ZMod n)`. Fix the too-broad unconditional `Module.Finite` instance
  (`n=0` breaks it) → theorem-style with `0<n`. Keep `Submodule.torsionBy ℤ Point n` as the def.
- **Phase 1:** the 4 easy Galois action sorries (already filled by Codex, commit 177e775) +
  restrict action to nTorsion.
- **Phase 2 (keystone):** CORE 1 — `preΨ'_root_iff` + separability → `n_torsion_card` →
  `geomNTorsion_rank_two_linear` (the shared keystone). Unlocks both axioms.
- **Phase 3 (B):** torsion finiteness (route ii or separate small axiom) +
  `RatTors.toGeomNTorsion` + invariant-factor algebra → `rational_torsion_two_invariant_factors`.
  Shortest axiom to close AFTER keystone+finiteness.
- **Phase 4 (A):** `WeilPairingPackage` Stage 1 (discharges axiom) → Miller Stage 3
  (Galois-equiv → μ_m → bilinear/alternating → nondegeneracy via card). Deepest.

## Codex dispatch note
Hold build until Stage-0 API shape is design-locked (dm3 just proposed the refactor; building
on the old `nTorsion` shape would be thrown away). When locked, dispatch Codex from Stage 0
(pure scaffolding, no hard math) → then Phase 2 CORE 1 as the first real grind.
