# EDS CORE — close xPair_same_xLadderRep_seam_EDS_core (the last keystone seam)

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build, uisai2 is now free — build freely). Edit ONLY scratch/KeystoneLadder.lean.

## STATE (verified: EXIT 0, 0 axiom, exactly 1 sorry)
KeystoneLadder.lean has the corrected Montgomery-pair ladder (doubling via A6 doubleVec + diff-add for the
odd step; xLadderRep_correct_seam CLOSED — ladder = x(nP)). The keystone seam nsmul_eq_zero_iff_ΨSq_eval is
reduced to ONE residual:
```
theorem xPair_same_xLadderRep_seam_EDS_core (W : WeierstrassCurve k) (n : ℕ) (x : k) :
    SameP1Vec (XOnly.xLadderRep (E := W⧸k) x n) (xPair W (n : ℤ) x)
```
where `xPair W n x = ![(W.Φ n).eval x, (W.ΨSq n).eval x]`. This is the classical division-polynomial
coordinate identity `x(nP) = Φₙ(x)/ΨSqₙ(x)`, in the form "the Montgomery ladder computes [Φₙ : ΨSqₙ]".

## TASK — close this seam (or reduce to its irreducible kernel)
0. FIRST: grep the repo + Mathlib for whether x([n]P)=Φ/ΨSq or the EDS coordinate formula already exists
   in ANY form (search `Φ`, `ΨSq`, `preΨ'`, `normEDS`, `WeierstrassCurve.Φ`, division-polynomial coordinate
   lemmas, `EllipticDivisibilitySequence`). REPORT what you find. If a usable formula exists, use it.
1. Prove by INDUCTION matching the ladder recurrence to the division-polynomial recurrence. The two key
   coordinate sub-identities to establish (using the repo's ΨSq_even/odd, Φ_*, preΨ'/preΨ₄ recurrences +
   mk_φ/mk_ψ coordinate-ring congruences):
   - DOUBLING: `doubleVec [Φₘ(x) : ΨSqₘ(x)] ~ [Φ_{2m}(x) : ΨSq_{2m}(x)]` — i.e. the A6 dup forms applied to
     the m-th division-poly point give the 2m-th. (Matches ΨSq_{2m}, Φ_{2m} recurrences.)
   - DIFF-ADD: `diffAdd([Φₘ:ΨSqₘ], [Φ_{m+1}:ΨSq_{m+1}], [Φ₁:ΨSq₁]) ~ [Φ_{2m+1}:ΨSq_{2m+1}]`. (Matches the
     ψ_{a+b}ψ_{a−b} EDS addition recurrence.)
   These two, plus the Montgomery-pair structure, give the induction.
2. If the full identity needs an intricate EDS lemma not derivable from the listed recurrences, isolate the
   PRECISE irreducible polynomial sub-identity as ONE clearly-named sorry and report exactly which EDS
   recurrence (in repo/Mathlib terms) is missing and why — do not stop at decomposition, attack each sub-identity.

## RULES (Xiang: ChatGPT now weaker — codex self-verifies, so grind the build; verify your own claims)
- NO axiom-escape. Target 0 sorries. Reuse A6 doubleVec + the corrected ladder; do NOT reintroduce the
  doubling-via-diffadd bug (the n=2/3/4 sanity lemmas guard it — keep them passing).
- When done: `grep -n "sorry\|admit\|axiom" scratch/KeystoneLadder.lean` + `lake env lean
  scratch/KeystoneLadder.lean`, PASTE BOTH VERBATIM, exact sorry count. Report: closed fully / reduced to
  which precise sub-identity, and which existing Φ/ΨSq recurrences you used.
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named genuinely-missing repo/Mathlib decl.
