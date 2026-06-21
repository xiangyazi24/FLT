# KEYSTONE INTEGRATION — attack nsmul_eq_zero_iff_ΨSq_eval via the SEAM2 diff-add + division polynomials

Repo ~/repos/flt-ai, branch ai-scratch, ON uisai2. Build with `lake build`/`lake env lean` here
(NEVER local mini build). Work in a NEW file scratch/KeystoneLadder.lean. Do NOT edit built files yet;
report the wiring fit at the end.

## TARGET (the keystone seam, FLT/EllipticCurve/Torsion.lean:80, general field k)
```
theorem nsmul_eq_zero_iff_ΨSq_eval {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0
```

## ASSETS IN HAND
- scratch/Seam2Wired.lean + scratch/Seam2Proto.lean — the x-only differential-addition primitive PROVEN
  over ℚ (xRep, global Kummer biquadratic, xRep_add_of_xRep_sub; the completed-square certs). The
  `linear_combination` certificates are RING-LEVEL so they generalize to any field k with no math change.
- SEAM1 `(W.preΨ' n).Separable` (Torsion.lean:75) is a sorry — you MAY USE IT AS A HYPOTHESIS/dependency
  (do NOT re-prove it; if your proof needs separability, take it as given / cite that seam).
- Existing division-polynomial API: grep the repo + Mathlib for `WeierstrassCurve.ΨSq`, `preΨ'`, `Ψ₂Sq`,
  `Φ`, `preΨ₄`, `preNormEDS'`, and any lemmas relating `n • P` / `Point.some` to these. REPORT what exists.

## TASKS (de-risk-first; self-verify by building)
1. **Generalize** the SEAM2 diff-add to a general field `k` (re-state the certs over `[Field k]`; the
   completed-square `linear_combination` proofs port directly). Get the diff-add primitive over `k`.
2. **x-only ladder**: define `xLadder n : k` = x-coordinate of `n • P` via iterated differential addition
   (Montgomery-style: from x(P), build x(2P), x(3P), …, x(nP)). State its correctness vs `(n • P).xRep`.
3. **Connect to ΨSq**: investigate how `x(nP)` relates to the division polynomials — the classical identity
   `x(nP) = Φ_n(x)/ΨSq_n(x)` (or `φ_n/ψ_n²`), so `nP = O ⟺ ΨSq_n(x) = 0`. Build as much of
   `nsmul_eq_zero_iff_ΨSq_eval` as compiles, over `k`, using existing ΨSq API + SEAM1 as needed.
4. Whatever genuinely cannot close (deep division-polynomial facts Mathlib lacks, or SEAM1-dependent steps),
   isolate as ONE-each clearly-NAMED `sorry` seam — NOT axioms, NOT broken refs. The goal is to REDUCE the
   seam to its irreducible core and report the structure.

## RULES (campaign-critical)
- NO axiom-escape. Named sorry seams only, each clearly labelled with what it needs.
- Reuse the proven SEAM2 certs (generalize, don't re-derive the algebra). Prefer EXISTING Mathlib/repo
  division-polynomial lemmas over re-proving.
- When done: run `grep -n "sorry\|admit\|axiom" scratch/KeystoneLadder.lean` + `lake env lean
  scratch/KeystoneLadder.lean`, PASTE BOTH VERBATIM, exact sorry count. REPORT: what closed, each named
  seam + what it needs, which existing ΨSq lemmas you used, and whether nsmul_eq_zero_iff_ΨSq_eval is
  reachable (fully / modulo SEAM1 / needs deeper missing API).
- Unbounded grind. Only legitimate stop: math wrong, or precisely-named missing Mathlib API.
