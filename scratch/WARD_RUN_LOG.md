## Run 2026-06-22 (automode continuation) — COMPLETE
- doctrine: WARD_DOCTRINE.md
- approval: continuation of live autonomous run
- avenue taken: (c) sympy Gröbner cofactors + universal-ring b²-cancel (polyrith ruled out — no Sage)
- RESULT: normEDS_adjacent_somos PROVEN, 0 sorry, #print axioms = [propext, Classical.choice, Quot.sound].
  Mathlib TODO (IsEllDivSequence for normEDS, the (m,2,1) instance) closed.
- commits: 438576e WardSomos | 40d4ab4 PsiSomos (ψ bridge) | f15b997 mk_C_injective (descent)
- bridge to keystone: W.ψ = normEDS ψ₂ (CΨ₃)(CpreΨ₄) [Mathlib defn] ⇒ psi_adjacent_somos, mk_psi_adjacent_somos.

## NEXT AVENUE — keystone EDS core (xPair_double_and_diffAddOrInf_EDS_core, KeystoneLadder.lean L1013)
Three pieces, all unblocked by the infra above:
(1) DOUBLING: Φ(2m)·dupDenP(Φm,ΨSqm) = ΨSq(2m)·dupNumP(Φm,ΨSqm) in R[X].
    Method: mk_C_injective ⇒ work in CoordinateRing; mk_φ/mk_Ψ_sq/mk_ψ turn Φ,ΨSq into φ,ψ²;
    expand ΨSq_even/Φ/ψ_even; over field k CoordinateRing is a domain so mk(ψ₂)≠0 cancels;
    close with mk_psi_adjacent_somos via sympy-Gröbner cofactors (same method as the Somos itself).
    Exact Mathlib defs in hand: preΨ_even (L225), ΨSq_even (L273), Φ (L349), ψ_even (L430, ·ψ₂), Φ_two.
(2) ADDITION: diffAddOrInfVec(xPair m, xPair(m+1), xPair 1) ~ xPair(2m+1). From preΨ_odd + Somos.
(3) two NONZERO: xPair(2m)≠0, xPair(2m+1)≠0 (no-common-root / separability).
Then EDS core ⇒ keystone nsmul_eq_zero_iff_ΨSq_eval. Above: SEAM1, no_rational_point_of_order_ge_17.

## Run 2026-06-22 cont. — preΨ Somos landed + doubling DIAGNOSED
- preΨ_adjacent_somos PROVEN (677f1c9), 0 custom axioms: parity-dependent (even→1, odd→Ψ₂Sq²),
  via mk_psi_adjacent_somos + mk_ψ_eq + mk_C_injective + Ψ₂Sq≠0 descent. + mk_ψ_eq (f15b997-ish).
- DOUBLING DIAGNOSIS (CAS, definitive): dupCrossDiff formula verified (=0 at concrete m=2).
  · R[X]/preΨ adjacent-Somos route: dupCrossDiff ∉ ideal(adjacent Somos) at radius 2,3,4 (9 Somos) — FAILS.
    Root cause: in R[X] the preΨ only satisfy adjacent Somos, NOT the curve relation; doubling needs the curve eqn.
  · Coord-ring free-g model (g_n=mk(ψ n), clean ψ_odd=normEDS_odd, uniform ψ Somos S=mk(CΨ₂Sq)):
    also NOT in ideal(ψ Somos) at radius 0,1,2. Because g_n are NOT free — by mk_ψ_eq g_n = mk(C preΨ n)·ψ₂^[even],
    and the curve relation lives DEEPER in the (mk Y)² reduction, not captured by free-g + single Somos.
  · CONCLUSION: the doubling needs the FULL coordinate-ring quotient structure (mk Y, curve relation), not just
    adjacent Somos. Correct CAS model = represent each mk(ψ(m+j)) as (A_j,B_j) in basis {1,mk Y}, reduce products
    via Y²=X³+a₂X²+a₄X+a₆-a₁XY-a₃Y, then the ψ Somos + curve closes it. OR do it in Lean directly (ChatGPT R3).
- NEXT: coord-ring doubling via full quotient (ChatGPT R3 dispatched on the Lean cofactor with curve relation).
  Then addition + 2 nonzeros → EDS core → keystone.
