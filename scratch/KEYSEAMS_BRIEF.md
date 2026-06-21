# KEYSTONE LADDER — close the 2 named seams in scratch/KeystoneLadder.lean

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build). Edit ONLY scratch/KeystoneLadder.lean. Do NOT touch built files.

## STATE (verified: EXIT 0, 0 axiom, exactly 2 sorries)
KeystoneLadder.lean builds the structure of the keystone seam `nsmul_eq_zero_iff_ΨSq_eval` over a general
field k, reduced to 2 named seams. Everything else is closed (the SEAM2 diff-add over k, the ladder defs,
the assembly `xRep_nsmul_same_xPair` → the iff). Close these two:

1. **`xLadderRep_correct_seam`** (~L403): `SameP1Vec ((n • Point.some x y h).xRep) (xLadderRep E x n)`.
   The raw x-only ladder represents the actual x-coordinate of n•P. Prove by INDUCTION on n (strong/two-step
   induction matching the Montgomery ladder), using the proven diff-add primitive `xRep_add_of_xRep_sub`
   and `xRep_zero`/`xRep_neg_same`, handling the degenerate differential-addition steps (the 2-torsion /
   collision cases where δ=0). Base cases xLadderRep_zero/one are already `rfl`.

2. **`xPair_same_xLadderRep_seam`** (~L416): `SameP1Vec (xLadderRep x n) (xPair W n x)` where
   `xPair W n x = ![Φₙ(x), ΨSqₙ(x)]`. This is the EDS/division-polynomial compatibility — the CORE.
   Prove by INDUCTION on n matching the ladder's differential-addition recurrence to the division-polynomial
   recurrences. AVAILABLE API (the codex confirmed these exist): `ΨSq_ofNat/zero/one/two/three/four/neg/
   even/odd`, `Φ_*`, the preΨ'/preΨ₄ recurrences, degree/leadingCoeff/nonzero lemmas, `map_*`/`baseChange_*`,
   and coordinate-ring congruences `mk_Ψ_sq`, `mk_ψ`, `mk_φ`. The classical identity is
   `x(nP) = Φₙ(x)/ΨSqₙ(x)`; the EDS recurrence `ψ_{m+n}ψ_{m−n} = ψ_{m+1}ψ_{m−1}ψ_n² − ψ_{n+1}ψ_{n−1}ψ_m²`
   (and the Φ analogue) is what the differential-addition step must match. Use the `ΨSq_even/odd` split.

## RULES (campaign-critical; Xiang warned ChatGPT answers are now weaker — codex self-verifies, so grind the build)
- NO axiom-escape. Target 0 sorries. If one seam closes and the other needs a genuinely-missing EDS lemma
  that you cannot derive from the listed API, isolate it as ONE clearly-named sorry and report EXACTLY which
  recurrence/lemma is missing and why the listed API is insufficient. Do not stop at decomposition — attack.
- SEAM1 (separability) is NOT needed for these — do not introduce it.
- When done: `grep -n "sorry\|admit\|axiom" scratch/KeystoneLadder.lean` + `lake env lean
  scratch/KeystoneLadder.lean`, PASTE BOTH VERBATIM, exact sorry count, and which seam(s) closed + the
  induction structure used. If seam 2 stays open, report the precise EDS-recurrence gap.
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named missing Mathlib/repo decl.
