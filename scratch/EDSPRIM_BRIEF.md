# EDS PRIMITIVE — close xPair_double_and_diffAddOrInf_EDS_core (the FINAL keystone seam)

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2 (free). NEVER local mini build. Edit ONLY
scratch/KeystoneLadder.lean.

## STATE (verified: EXIT 0, 0 axiom, 1 sorry at L1013)
The keystone is reduced to ONE primitive seam. Everything else is proven (the outer strong pair-induction
xPair_ne_zero_and_same_xLadderRep_EDS is CLOSED, the ladder, diff-add over k, A6 doubling, n≤4). Close:
```
private theorem xPair_double_and_diffAddOrInf_EDS_core (W : WeierstrassCurve k) [W.IsElliptic] (m : ℕ) (x : k) :
    xPair W ((2*m : ℕ):ℤ) x ≠ 0 ∧
    SameP1Vec (XOnly.doubleVec (E := W⧸k) (xPair W (m:ℤ) x)) (xPair W ((2*m:ℕ):ℤ) x) ∧
    <the adjacent diff-add identity for [Φm:ΨSqm],[Φ_{m+1}:ΨSq_{m+1}],[x:1] ~ [Φ_{2m+1}:ΨSq_{2m+1}] + nonzero>
```
i.e. the two RAW per-step polynomial identities: (1) doubling `doubleVec[Φₘ:ΨSqₘ] ~ [Φ_{2m}:ΨSq_{2m}]`,
(2) adjacent diff-add `~ [Φ_{2m+1}:ΨSq_{2m+1}]`, each with the `xPair ≠ 0` (no-common-root) conclusion.

## THE DESIGN IS IN HAND (3 Pro git-drop channels converged — read them)
- scratch/EDS_dm2_design.md — the FULL recurrence-matching design. KEY exact formulas:
  - `ΨSqₙ = preΨₙ² · (if Even n then Ψ₂Sq else 1)`
  - `Φₙ = X · ΨSqₙ − preΨ_{n+1} · preΨ_{n−1} · (if Even n then 1 else Ψ₂Sq)`
  - Add the 4 parity wrappers (Φ_even/odd, ΨSq_even/odd) if not present: `rw [ΨSq, Φ, preΨ_even/preΨ_odd]` +
    parity simp + `ring`. Expand Φ_{2m},ΨSq_{2m},Φ_{2m+1},ΨSq_{2m+1} via these + `preΨ_even/odd`,
    `preΨ'_even/odd` recurrences (Mathlib `WeierstrassCurve.preΨ_even/odd`, `preΨ'_even/odd`).
- scratch/EDS_dm1_coprimality.md — the `xPair ≠ 0` route: prove the no-common-root conclusion SIMULTANEOUSLY
  within this primitive (NOT standalone — that is circular per dm1). The produced-index nonzero follows from
  the explicit factorisation (preΨ nonzero under IsElliptic + the parity structure).

## ATTACK
1. Establish the 4 parity wrappers for Φ/ΨSq (if absent).
2. DOUBLING identity: expand `doubleVec [Φₘ:ΨSqₘ]` (= `[dupNumH(Φₘ,ΨSqₘ) : dupDenH(Φₘ,ΨSqₘ)]`) and
   `[Φ_{2m}:ΨSq_{2m}]` (via parity formulas + preΨ recurrences) and prove `SameP1Vec` by cross-multiply + `ring`.
3. ADDITION identity: same for the diff-add step vs `[Φ_{2m+1}:ΨSq_{2m+1}]`, using the EDS addition recurrence
   `ψ_{a+b}ψ_{a−b} = ψ_{a+1}ψ_{a−1}ψ_b² − ψ_{b+1}ψ_{b−1}ψ_a²` form (dm2 gives the coordinate version).
4. The `xPair ≠ 0` conjuncts: from the explicit numerator/denominator factorisations (preΨ ≠ 0 under
   IsElliptic; the produced index's Φ,ΨSq cannot both vanish given the parity factorisation).

## RULES (3 Pro channels agree on this structure — trust the design, grind the ring identities)
- NO axiom-escape. Target 0 sorries → the whole keystone nsmul_eq_zero_iff_ΨSq_eval then discharges.
- These are POLYNOMIAL IDENTITIES — they WILL close by expansion + ring once the parity/recurrence
  substitutions are right. If a `ring` fails, it is a substitution/normalisation issue — fix it, don't seam it.
- If ONE genuinely-irreducible sub-identity resists (e.g. a specific preΨ recurrence not in Mathlib/repo),
  isolate it minimally + name the exact missing recurrence. Keep n≤4 sanity lemmas passing.
- When done: `grep -n "sorry\|admit\|axiom" scratch/KeystoneLadder.lean` + `lake env lean
  scratch/KeystoneLadder.lean`, PASTE BOTH VERBATIM, exact sorry count.
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named missing repo/Mathlib recurrence.
