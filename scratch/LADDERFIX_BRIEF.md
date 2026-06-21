# LADDER FIX — redesign the x-only ladder with a real doubling primitive (the prior def was FALSE at n=2)

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build). Edit ONLY scratch/KeystoneLadder.lean. Do NOT touch built files.

## THE BUG (already proven false)
The current `xLadderRep` computes doubling as `diffAdd(P, P, O)`, which is DEGENERATE: δ = x·1 − x·1 = 0
gives `xLadderRep E x 2 = ![0,0]` (zero vector), so `xLadderRep_correct_seam` is FALSE at n=2 (a Lean
disproof was constructed). A Montgomery ladder needs TWO primitives — DOUBLING and DIFFERENTIAL ADDITION —
and must NEVER use diff-add for the doubling step.

## THE FIX — use BOTH primitives (both already proven, just need composing over field k)
- **DOUBLING** (from A6): `x(2P) = [dupNumH W x 1 : dupDenH W x 1]` projectively, where
  dupNumH/dupDenH are in scratch/A6HeightProto.lean (and A6 proved `xRep_two_nsmul_same_dup_affine`:
  `(2•P).xRep ~ [dupNumH(xP) : dupDenH(xP)]`). The certificates are ring-level ⇒ generalize to any field k.
- **DIFF-ADD** (from SEAM2, already over general k): `xRep_add_of_xRep_sub` in scratch/Seam2Wired.lean —
  x(P+Q) from x(P), x(Q), x(P−Q) when the difference's δ ≠ 0.

## TASKS
1. Re-define the x-only ladder correctly. Recommended: maintain the Montgomery pair state
   `(x(mP), x((m+1)P))` processing the bits of n; each step does ONE diff-add (difference is x(P), δ≠0 for
   the genuine ladder invariant) + ONE doubling (via the A6 dup primitive). Define `xLadderRep E x n` so
   that it ACTUALLY equals x(nP). Base/degenerate cases (n=0 → [1:0], n=1 → [x:1], 2-torsion x where
   dupDen=0) handled explicitly.
2. Prove **`xLadderRep_correct_seam`**: `SameP1Vec ((n • P).xRep) (xLadderRep E x n)` — by induction on the
   ladder recurrence, using the A6 doubling SameP1 lemma for doubling steps and SEAM2 diff-add for addition
   steps. (This is now TRUE with the fixed definition.)
3. Prove **`xPair_same_xLadderRep_seam`**: `SameP1Vec (xLadderRep x n) ![Φₙ(x), ΨSqₙ(x)]` — the EDS identity,
   by induction matching the corrected ladder recurrence (doubling + diff-add) to the division-polynomial
   recurrences (ΨSq_even/odd, Φ_*, mk_φ/mk_ψ congruences). This is the deep core.
4. Keep the downstream assembly (`xRep_nsmul_same_xPair` → `nsmul_eq_zero_iff_ΨSq_eval`) intact.

## RULES (Xiang flagged: verify carefully — and you already caught the prior bug by doing so; keep that rigor)
- NO axiom-escape. NEVER doubling-via-diffadd. Target 0 sorries.
- Generalize the A6 doubling SameP1 lemma to field k if it is ℚ-specific (ring-level certs port directly).
- If seam 3 (the EDS identity) cannot fully close, isolate the IRREDUCIBLE division-polynomial step as ONE
  clearly-named sorry + report the precise EDS-recurrence gap (and a small Lean sanity check that the new
  ladder def is NOT false at n=2,3,4 — i.e. don't repeat the prior bug).
- When done: `grep -n "sorry\|admit\|axiom" scratch/KeystoneLadder.lean` + `lake env lean
  scratch/KeystoneLadder.lean`, PASTE BOTH VERBATIM, exact sorry count, what closed + the ladder recurrence used.
- Unbounded grind. Only legitimate stop: math wrong, or a precisely-named missing repo/Mathlib decl.
