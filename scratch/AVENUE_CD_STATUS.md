# Keystone Avenue (c)/(d) — architecture & status (2026-06-23)

Goal: discharge the two keystone sorries for Mazur |T|≤16 division-poly coprimality.

## Sorries
- **KeystoneSameP1.lean L253** — consumer `xPair_odd_phi_eval_ne_zero_of_delta_zero`
  (avenue c): given ΨSq(2m+1).eval x = 0, show Φ(2m+1).eval x ≠ 0.
- **KeystoneLadder.lean L1009** — core `xPair_double_and_diffAddOrInf_EDS_core`
  (avenue d): 4-conjunction (xPair 2m ≠0 ; doubling SameP1 ; xPair 2m+1 ≠0 ; diffAdd SameP1).

## Avenue (c) — DONE (assembled, gated on P3P4 build)
Non-circular `Φ_ΨSq_no_common_eval_zero_odd` built in KeystoneCoprimality.lean from:
- **rank-3 apparition** (`preΨ_eval_zero_iff_three_dvd_of_Ψ₃_eval_zero` + bridge
  `no_adjacent_preΨ_zero_of_Ψ₃_eval_zero`) — proven by ME, 0 custom axioms
  (Even=M+M vs 2*M cast bug fixed). Staged: /tmp/rank3_fixed.lean.
- **P2P3 + P3P4 nonsingularity certs** (Ψ₂Sq/Ψ₃ and Ψ₃/preΨ₄ no common root) via
  integer Bezout (Sylvester fraction-free, dm2 Q47; CAS cross-verified). P2P3 committed
  (77c681c). P3P4: bezout compiles at 200M heartbeats; the only blocker was the SAME
  sign bug as P2P3 (eval lemma `hb:0=Δ⁴` ⊢ `Δ⁴=0` needs `linear_combination -hb`). FIXED.
- **dm3 capstone Q44** (`no_adjacent_preΨ_zero` combiner, `ΨSq_eval_odd`, `Φ_eval_odd`,
  2-torsion `preΨ_odd_eval_ne_of_Ψ₂Sq_eval_zero`, `Φ_ΨSq_no_common_eval_zero_odd`).
- Full 576-line append staged: /tmp/coprimality_append.lean (rank3 body minus dup
  pe/sx abbrevs + capstone; bridge arg-order fixed to h4 hc3 hs2 hd4 r).
- Consumer patch staged + dry-verified: /tmp/patch_samep1.py (add import
  scratch.KeystoneCoprimality; [W.IsElliptic] on the 3 avenue-c theorems
  name-anchored; 3-line sorry discharge). NOTE: signature line matches 4 theorems,
  only 3 want it (NOT xPair_diffAdd_sameP1_of_inf_phi_ne).

## Avenue (d) — real blocker = IMPORT-LAYER INVERSION (not h4-threading)
- KeystoneLadder.lean imports ONLY Mathlib — it is the BOTTOM, holds the core sorry
  (L1009) AND its entire downstream L1024-1316 (xLadderPair_same_xPair_EDS →
  xPair_ne_zero_of_isElliptic → circular Φ_ΨSq_no_common_eval_zero L1178 →
  nsmul_eq_zero_iff_ΨSq_eval L1286 export).
- The materials to discharge the core (SameP1 wiring xPair_double_sameP1 /
  xPair_diffAdd_sameP1_core_order; non-circular no-common-root) live ABOVE it
  (KeystoneSameP1 imports KeystoneLadder; KeystoneCoprimality imports PsiSomos).
- Both `xPair_ne_zero_of_isElliptic` refs in SameP1/Coprimality are COMMENTS — refactor SOUND.
- Only KeystoneSameP1 imports KeystoneLadder, and it uses ONLY L1-1008 defs (xPair,
  SameP1Vec, diffAddOrInfVec), none of L1009-1316. NTorsionCard/Seam2 have their OWN nsmul.
- **PLAN**: move L1009-1316 → new top file (e.g. KeystoneEDS.lean) importing
  KeystoneSameP1 + KeystoneCoprimality; prove the core there from wiring + no-common-root;
  redirect downstream consumers of the export to the new file.
- Core signature has only [W.IsElliptic] (no h4/hψ_ne/hc3). Over ℚ (the Mazur app)
  h4/char≠3 are free — likely add [CharZero k] up the chain OR thread the 3 hyps.
  Open: is hψ_ne (∀n≠0, ψn≠0) derivable from [IsElliptic]+CharZero non-circularly?
- Even no-common-root needed for core part-1 (xPair 2m): general Mathlib forms —
  `Φ n = X*ΨSq n - preΨ(n+1)*preΨ(n-1)*(if Even n then 1 else Ψ₂Sq)`;
  `ΨSq(2m) = (preΨ-combo)^2 * Ψ₂Sq`; `ΨSq(2m+1) = (preΨ-combo)^2`.
- dm4 Q55 dispatched for full core assembly (needs re-brief with this DAG — its repo 404s).

## UPDATE (2026-06-23 later) — avenue-c logic VERIFIED, certs isolated
- Cert isolation: split KeystoneCoprimality into KeystoneResultantCerts.lean (header + 2 bezouts + 3 public nonsingularity lemmas; the slow P3P4 ring1) + KeystoneCoprimality.lean (imports certs + propagation + rank3 + capstone). One-time olean cache so future edits skip the ~40min bezout.
- P3P4 sign bug FIXED: eval lemma hb:0=Delta^4, goal Delta^4=0, needs linear_combination -hb (same as P2P3).
- dm3 capstone 3 integration bugs FIXED (via fast logic-test = stub the 3 certs as sorry, second-level iterate):
  (1) Phi_eval_odd: removed unreachable ring after simp;
  (2) 2-torsion simpa: preProime(nat) vs pre(int + Nat.cast) -- full simp pushes the cast before prePsi_ofNat can fire; FIX = simp only [pe, preProime_ofNat] then simpa [sx,hs,hm] using h;
  (3) Int.even_coe_nat.mp (lemma takes explicit n, dot-notation fails) -> exact_mod_cast.
- Even no-common-root (dm3 Q56: PsiSq_eval_even, Phi_eval_even, Phi_PsiSq_no_common_eval_zero_even) added -- compiled first try.
- Logic-test verdict: exit 0, only the 3 cert stubs sorry; rank3 + capstone (odd+even) + propagation all compile.
- Cert build IN PROGRESS (worker grinding P3P4 bezout, ~6.6GB, 99% CPU; poller bds9554u1). When green: build real KeystoneCoprimality (fast, certs cached) -> apply staged consumer patch (/tmp/patch_samep1.py) -> avenue-c DONE.
- GPT-job/git-drop: keystone source pushed to xiangyazi24/FLT main (connector reads default branch); chatgpt skill updated (GPT-job = default, read source from repo, do not paste). Future dispatches: short prompts by file path.
- dm4 v2 (Q60) in-flight: full avenue-d relocation L1009-1316 -> new top file KeystoneEDS.lean + thread (h4,hpsi_ne,hc3). hpsi_ne is POLYNOMIAL non-vanishing (psi_n not identically 0), derivable over CharZero via natDegree_prePsi; hc3 from hpsi_ne at 3.
- Temp file scratch/_KCLogicTest.lean = the sorry-stubbed logic test (DELETE before commit).
