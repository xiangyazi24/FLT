# EDS GENERAL CORE — close (or minimally reduce) xPair_ne_zero_and_same_xLadderRep_EDS

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2 (free, build freely). NEVER local mini build.
Edit ONLY scratch/KeystoneLadder.lean.

## STATE (verified: EXIT 0, 0 axiom, 1 sorry at L984)
This is the LAST keystone seam. All scaffolding is proven (SEAM2 diff-add over k, A6 doubling, corrected
Montgomery ladder, xLadderRep_correct, n=0..4 concretely). The residual:
```
theorem xPair_ne_zero_and_same_xLadderRep_EDS (W : WeierstrassCurve k) [W.IsElliptic] (n : ℕ) (x : k) :
    xPair W (n : ℤ) x ≠ 0 ∧
    SameP1Vec (XOnly.xLadderRep (E := W⧸k) x n) (xPair W (n : ℤ) x)
```
where xPair W n x = ![(W.Φ n).eval x, (W.ΨSq n).eval x]. Two conjuncts:
- (a) **coprimality / no common root**: xPair ≠ 0, i.e. Φₙ(x) and ΨSqₙ(x) never both vanish (under IsElliptic).
- (b) **general EDS compatibility**: the ladder ~ [Φₙ:ΨSqₙ] for all n.

## ATTACK (de-risk both conjuncts; do a STRONG induction together)
0. FIRST grep repo+Mathlib HARD for anything reusable: `Φ`, `ΨSq`, `preΨ'`, `preΨ₄`, `normEDS`,
   `WeierstrassCurve.Ψ`, division-polynomial recurrences/coprimality/resultant/`IsCoprime`, the relation
   `Φ_n = x·ΨSq_n − Ψ_{n-1}·Ψ_{n+1}` (or its form in this repo). REPORT what exists.
1. **(a) coprimality**: use `Φₙ = x·ΨSqₙ − preΨ'_{n-1}·preΨ'_{n+1}` (the standard relation — find/prove its
   repo form) ⇒ a common root of Φₙ,ΨSqₙ forces a common root of ΨSqₙ and Ψ_{n-1}Ψ_{n+1}. Then use the
   coprimality pattern of consecutive division polynomials (gcd(ψ_n, ψ_{n±1}) structure) under Δ≠0
   (IsElliptic). Build this as a lemma `xPair_ne_zero` by induction on the EDS recurrence.
2. **(b) EDS compatibility**: STRONG/two-step induction on n. Even n=2m: the ladder doubles (A6 dup forms) —
   match to ΨSq_{2m}/Φ_{2m} (ΨSq_even). Odd n=2m+1: the ladder diff-adds — match to the
   ψ_{a+b}ψ_{a−b} = ψ_{a+1}ψ_{a−1}ψ_b² − ψ_{b+1}ψ_{b−1}ψ_a² addition recurrence (ΨSq_odd / Φ recurrences).
   The n=0..4 base cases are already proven — extend the pattern to the inductive step.
3. If the FULL general identity needs a division-polynomial fact genuinely absent and not derivable from the
   repo recurrences, isolate the MINIMAL such polynomial sub-identity (e.g. just the addition-recurrence
   coordinate step, or just the consecutive-coprimality lemma) as ONE clearly-named sorry, and report the
   EXACT missing lemma in repo/Mathlib terms + why it can't be derived. Push everything else to 0 sorry.

## RULES (verify carefully — you've caught 2 false statements already; the n=0..4 sanity lemmas must keep passing)
- NO axiom-escape. Reuse the proven scaffolding; do not re-derive the ladder or diff-add.
- When done: `grep -n "sorry\|admit\|axiom" scratch/KeystoneLadder.lean` + `lake env lean
  scratch/KeystoneLadder.lean`, PASTE BOTH VERBATIM, exact sorry count, what closed, and (if reduced) the
  precise minimal named sub-lemma + which recurrences you used.
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named genuinely-missing repo/Mathlib decl.
