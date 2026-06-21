# EDS FIX — add [W.IsElliptic] + coprimality, close xPair_same_xLadderRep_seam_EDS_core

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2 (now free, build freely). Build with `lake build`/
`lake env lean` here (NEVER local mini build). Edit ONLY scratch/KeystoneLadder.lean.

## STATE (verified: EXIT 0, 0 axiom, 1 sorry at L957)
The single remaining keystone seam `xPair_same_xLadderRep_seam_EDS_core` was found FALSE as stated (no
hypotheses): on the SINGULAR zero curve, n=3, x=0, `xLadderRep = [1,0]` but `xPair = [Φ₃(0),ΨSq₃(0)] = [0,0]`,
so `¬SameP1Vec` (a Lean disproof was built). Root cause: with no non-singularity, Φₙ and ΨSqₙ can share a
root (both vanish), making xPair = [0,0] (an invalid projective point).

## THE FIX
1. ADD `[W.IsElliptic]` to `xPair_same_xLadderRep_seam_EDS_core` (and propagate through xRep_nsmul_same_xPair
   / nsmul_eq_zero_iff_ΨSq_eval if needed — those ALREADY carry [W.IsElliptic], so this is SOUND). IsElliptic
   ⇒ Δ ≠ 0 ⇒ excludes the singular counterexample.
2. **Coprimality / no-common-root**: under [W.IsElliptic], prove (or locate in repo/Mathlib) that Φₙ(x) and
   ΨSqₙ(x) have NO COMMON ROOT — equivalently xPair W n x ≠ ![0,0] for all x. This is the standard fact that
   the division polynomials are coprime for an elliptic curve (use the relation Φₙ = x·ΨSqₙ − ψ_{n-1}ψ_{n+1}
   and the EDS structure; grep for existing `Φ`/`ΨSq` coprimality / resultant / nonzero lemmas first). This
   kills the [0,0] degeneracy and lets the [1,0]-infinity cases match ([Φₙ:0] ~ [1:0] when Φₙ≠0).
3. Prove the EDS recurrence matching (the actual identity): the corrected Montgomery-pair ladder (A6 doubling
   + SEAM2 diff-add) agrees with [Φₙ:ΨSqₙ], by induction using ΨSq_even/odd + Φ recurrences + mk_φ/mk_ψ.
   The doubling step ↔ ΨSq_{2m}/Φ_{2m}; the diff-add step ↔ the ψ_{a+b}ψ_{a−b} addition recurrence.
4. If a precise polynomial sub-identity genuinely cannot close from the available recurrences, isolate it as
   ONE clearly-named sorry + report exactly which EDS recurrence/coprimality lemma is missing (repo/Mathlib
   terms) — do NOT stop at decomposition; attack each sub-identity, and keep the n=2/3/4 sanity lemmas passing.

## RULES (Xiang: verify carefully — you have correctly caught 2 false statements already; keep that rigor)
- NO axiom-escape. Target 0 sorries. Adding [W.IsElliptic] is REQUIRED (the unconditional statement is false).
- When done: `grep -n "sorry\|admit\|axiom" scratch/KeystoneLadder.lean` + `lake env lean
  scratch/KeystoneLadder.lean`, PASTE BOTH VERBATIM, exact sorry count, what closed + the coprimality lemma
  + EDS recurrences used. If reduced, name the precise irreducible sub-identity.
- Unbounded grind. Only legitimate stop: math wrong even WITH IsElliptic, or a precisely-named missing decl.
