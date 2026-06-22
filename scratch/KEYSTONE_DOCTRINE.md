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
