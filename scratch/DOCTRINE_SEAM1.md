# DOCTRINE — SEAM 1: `preΨ'_separable_of_natCast_ne_zero` (general n)

Goal (one sentence): discharge, for a Weierstrass curve `W` over a field `k`,
`theorem preΨ'_separable_of_natCast_ne_zero {n : ℕ} (hn : (n : k) ≠ 0) : (W.preΨ' n).Separable`
— general `n`, no bound.

## Why this is foundational (not a side lemma)
`NTorsionCard.lean` header: "SEAM 1 = preΨ'_separable (**étaleness of [n]**)". The lemma is the
ONLY thing giving `Polynomial.card_rootSet_eq_natDegree` ⟹ `#rootSet = natDegree`, which feeds
`preΨ'_rootSet_card` → `nonTwoKernelEquivRootBool` → `nTorsion_card_eq : #E[n] = n²` →
`n_torsion_dimension` → the whole Mazur torsion structure. It is used at **general n** all the way up.

## Circular-dependency finding (verified 2026-06-23)
`nTorsion_card_eq` (#E[n]=n²) routes THROUGH `preΨ'_rootSet_card`, which uses THIS sorry.
⟹ **No counting bootstrap.** Cannot derive separability from #E[n]=n² because that count rests on
separability. Separability is genuinely the root étale fact.

## Routes

### (E1) Formal group at the identity  ← CHOSEN
Build the Weierstrass formal group `Ê` (formal completion of `E` at `O`); the `[n]`-series on `Ê`
has linear coefficient `n` (Silverman IV); when `char ∤ n`, `n ∈ k^×` ⟹ `[n]` is a formal
**automorphism** ⟹ `[n]` étale at `O` ⟹ (translation) `[n]` étale everywhere ⟹ `E[n]` étale of
order `n²` ⟹ `preΨ'_n` squarefree (simple roots) ⟹ `Separable`.
- Mathlib HAS: general field-separability framework (`Separable`, `SeparableDegree`,
  `SeparableClosure`, `PurelyInseparable`), and a **thin** general formal-group API
  (`RingTheory/FormalGroup/Basic.lean`: `structure FormalGroup`, `IsComm`, `Point`, `𝔾ₐ/𝔾ₘ`, `map`).
- Mathlib LACKS: Weierstrass invariant differential `ω`, the Weierstrass formal group `Ê`,
  formal-group homomorphisms / `[n]`-series / height, isogeny theory.
- Verdict: **largest** build (mostly from scratch on a thin base) but **reusable** across all of FLT
  (isogenies/formal groups are pervasive). Per Xiang 2026-06-23 ("不怕大工程… 做稳"): this is the
  solid, reusable route. PLAN via ChatGPT multi-round before grinding (大问题先多轮规划).

### (E2) General resultant/discriminant induction  ← parked (base cases done as records)
Prove `Res(preΨ'_n, (preΨ'_n)') = ±(primes dividing n)^… · Δ^{e_n}` by induction on the EDS
recurrence; the RHS is a unit exactly when `char ∤ n`.
- Self-contained, NO new infrastructure. BUT repo design doc (`Keystone_MasterDesign.md` L34) flags
  it "long, fragile, not reusable": parity split (lead coeff `n/2` even vs `n` odd) + derivative-
  degree normalization fails in positive char (adjacent to separability itself).
- **Base-case data (verified, kernel-checked):**
  - n=3: `Res(Ψ₃, Ψ₃') = -81·Δ² = -3⁴·Δ²` → `Psi3_separable` LANDED, commit `7a383c3`, 0 axioms.
  - n=4: `Res(preΨ₄, preΨ₄') = 512·Δ⁵ = 2⁹·Δ⁵` (sympy verified; Lean cofactors A 342/B 425/Q 98 terms).
  - Pattern: the unit constant's prime support = primes dividing n (3 | 3, 2 | 4) ⟹ confirms
    "separable ⟺ char ∤ n". These are kept as sanity checks / data for any E2 revisit.

### (bounded-n) restructure API to n ≤ 16  ← REJECTED
Weakens the statement; not solid. Off the table.

## Decision
**E1**, committed. Reusable foundation, faces the difficulty head-on. Multi-round ChatGPT planning
FIRST (dispatched dm2 2026-06-23), my own derivation in parallel (verify-don't-transcribe).

## Terminal conditions
- E1 success: `preΨ'_separable_of_natCast_ne_zero` discharged, `lake build` + `#print axioms` clean
  (0 custom axioms), wired into `NTorsionCard.lean`/`Torsion.lean`.
- E1 proof-of-infeasibility (high bar): a Mathlib/architectural blocker that cannot be built around —
  documented, then reconsider E2-general.

## Open planning questions (for ChatGPT round + own work)
1. Minimal sub-theory of E1: do we need full `ω`, or just the leading coeff of the `[n]`-series on `Ê`?
2. Rigorous bridge "[n] formal-automorphism ⟹ preΨ'_n squarefree as a polynomial".
3. Smaller-build estimate E1 vs a non-fragile reformulation of E2.

## Recommended route (ChatGPT round-1, dm2 Q101, commit 3642f86; confirms my own derivation)
**First-order TANGENT argument — NOT the full formal-group/isogeny stack.** Build only the first-order
consequence. Cross-checks CONFIRMED independently: cardinality route circular; EDS-derivative
induction fails (IH indices mismatch in pos char); per-n Bezout (n=3,4) = good base cases, don't scale.

Core reduction: `preΨ'_separable` ⟸ rootwise `preΨ'_derivative_ne_zero_at_root` (over splitting field),
descended via `separable_map`. A multiple root a of preΨ'_n ⟹ non-2-torsion P=(a,y), n•P=0; multiple
root ⟹ nonzero tangent vector at P in ker[n] (over k[ε]); translate to O where d[n]=n·id ⟹ vector=0
when (n:k)≠0 — contradiction. ONLY place (n:k)≠0 enters: d[n]|_O = n·id (the minimal formal fact).

### Lemma DAG (build order)
- A (general poly): A1 `eval_dualNumber` (eval at x+εv = f(x)+ε·v·f'(x)) — BUILD (elementary, not in Mathlib);
  A3 `separable_of_deriv_ne_zero_at_roots` — BUILD (via `nodup_roots_iff_of_splits` + `one_lt_rootMultiplicity_iff_isRoot_gcd` + `count_roots`);
  A4 descent = **FREE** (`Polynomial.separable_map`, biconditional).
- B (root dictionary): B1 preΨ'_root_not_Ψ₂Sq_root (≈ repo KeystoneResultantCerts Ψ₂Sq_eval_ne + avenue-c);
  B4 preΨ'_root_iff_non_two_n_torsion_x (≈ SEAM2 nsmul_eq_zero_iff_preΨ'). PARTLY EXISTS.
- C (tangent crux, the genuinely-new minimal piece): tangent_nsmul_at_O = n·id. **k[ε] is not a field ⟹
  can't use packaged Point group; needs raw affine-coordinate addition over k[ε].** ChatGPT round-2
  (dm2 Q-crux) dispatched on this.
- D (bridge): multiple-root → nonzero tangent kernel vector → contradiction via C.
- E (final): base-change to alg closure + A3 + separable_map descent. SCAFFOLD buildable now.

### Mathlib pieces CONFIRMED present
`separable_map` (descent free), `nodup_roots_iff_of_splits`, `nodup_aroots_iff_of_splits`,
`one_lt_rootMultiplicity_iff_isRoot_gcd`, `count_roots`, `preΨ'_three/four`, `map_preΨ'`,
`natDegree_preΨ'`, `leadingCoeff_preΨ'` (= n/2 even, n odd), `preΨ'_ne_zero`, `DualNumber`/`TrivSqZeroExt`.
Missing/new: A1, A3-helper, all of C, the B root-dictionary glue, D.
