# Keystone EDS-core — automode DOCTRINE (2026-06-22 continuation)

GOAL: discharge `xPair_double_and_diffAddOrInf_EDS_core` (KeystoneLadder.lean) → unblock Mazur.
4 facts: xPair(2m)≠0, SameP1Vec doubling, xPair(2m+1)≠0, SameP1Vec diff-addition.

AVENUES:
(a) DOUBLING (cert VERIFIED, banked KEYSTONE_DOUBLING_CERT.md): prove polynomial ΨSq_two_mul/Φ_two_mul
    via Ψ₃-saturated linear_combination over Adj(preΨ Somos)+Inv(Ward InvarRel→preΨ)+bRel, cancel Ψ₃ over
    universal domain, transport. Then keystone SameP1Vec doubling by eval (c=1). Terminal: ΨSq_two_mul +
    Φ_two_mul built 0-sorry.
(b) DIFF-ADDITION companion: derive its certificate (ChatGPT+CAS like doubling), encode. Terminal: built.
(c) NONZERO facts via natDegree_Φ/ΨSq (Mathlib Degree.lean). Terminal: both ≠0 built.
(d) ASSEMBLE into EDS-core. Terminal: sorry discharged, #print axioms clean.
FALLBACK: if preΨ-certificate parity bookkeeping too painful → coordinate-ring descent (mk_ψ/mk_Ψ_sq/mk_φ +
    proven AddRel/InvarRel for ψ directly).

## Run 2026-06-22 (continuation, automode)
- starting avenue: (a) doubling encoding
- relations: Adj=preΨ_adjacent_somos (PsiSomos.lean), Inv=Ward InvarRel→preΨ (to establish)
- end: <fill>

### Avenue (a) progress 2026-06-22
- chunk1 BUILT+committed: dupNumP/dupDenP poly defs, dupNumP_X_one (=Φ 2), ΨSq_two_mul_expand. (KeystoneDoubling.lean)
- Pieces located: Adj=preΨ_adjacent_somos (parity, [IsDomain]+(4≠0)); bRel=W.b_relation (4b₈=b₂b₆−b₄², Mathlib); Ψ₂Sq/Ψ₃/preΨ₄ explicit X-poly defs (Basic.lean 117/142/147); ΨSq_even/odd, Φ, ΨSq_two, Φ_two.
- Inv=preΨ_invariant: dispatched to ChatGPT dm1 (Q341, derivation mirroring preΨ_adjacent_somos: invarRel_all on ψ → coord-ring descent → cancel ψ₂). Pending.
- Certificate-core ENCODING DECISION: expand Ψ₂Sq/Ψ₃/preΨ₄ to X-forms in goal+hAdj+hInv, then `linear_combination` with banked cofactors (KEYSTONE_DOUBLING_CERT.md, all 4 CAS-verified) over hAdj+hInv+hb, by_cases parity. Heavy ring but verified. Alt if too heavy: re-CAS with s/c3/d4 as relation-hyps for cleaner cofactors.
- NEXT: harvest preΨ_invariant → build ΨSq_two_mul/Φ_two_mul cert (both parities) → cancel Ψ₃ → SameP1Vec doubling.

### Avenue (a) progress 2026-06-22 (cont)
- preΨ_invariant (Inv = Ward InvarRel→preΨ): BUILT modulo 2 named sorries (PsiInvariant.lean, committed).
  ChatGPT-derived proof; fixed namespace(open FLT.EDS)/Y(→Polynomial(Polynomial R))/parity(Int.even_add_one,
  even_sub_one, parity_simps)/type-mismatch(InvarRel in simpa). 2 sorries = coord-ring ψ→preΨ normalization
  (hq_mul even / hq2_mul odd); STATEMENT CAS-verified. Norm fix dispatched to ChatGPT dm1.
- NEXT push (on norm return): complete preΨ_invariant → build ΨSq_two_mul/Φ_two_mul certificate
  (Ψ₃-mult linear_combination over Adj=preΨ_adjacent_somos + Inv=preΨ_invariant + bRel=b_relation, banked
  cofactors KEYSTONE_DOUBLING_CERT.md, by_cases parity, expand Ψ₂Sq/Ψ₃/preΨ₄ X-forms) → cancel Ψ₃ →
  ΨSq_two_mul/Φ_two_mul → SameP1Vec doubling (c=1, by eval). Then (b)diff-add (c)nonzero (d)assemble.

### Avenue (a) state 2026-06-22 (cont 2)
- preΨ_invariant: clean buildable WIP committed (2 named sorries on hq_mul/hq2_mul coord-ring norm). Statement
  + full structure built. Norm-fix attempt (ChatGPT f1c0642ca refined approach: hmkC_apply/hq_apply rfl-folds
  + simp[mk_ψ_eq]+linear_combination(←hq4)) hit polynomial-tower COERCION issues: let-bound mkC=(mk W).comp C
  & q=mk ψ₂ dont reduce by rfl, and `C f` ambiguous in the R[X]→R[X][Y] tower. Reverted to buildable. The norm
  is the single remaining hard sub-grind (needs careful tower-coercion handling / `RingHom.comp_apply` + explicit
  Polynomial.C, possibly a fresh ChatGPT round with the exact type-mismatch).
- Both load-bearing walls are now Lean lemmas: Adj=preΨ_adjacent_somos (0-sorry), Inv=preΨ_invariant (2 norm sorries).
- NEXT: (i) finish 2 norm sorries; (ii) build ΨSq_two_mul/Φ_two_mul certificate against preΨ_invariant (heavy
  Ψ₃-mult linear_combination, banked cofactors) — buildable now (sorries inside Inv dont block its use as a lemma).
