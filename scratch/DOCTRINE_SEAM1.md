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
