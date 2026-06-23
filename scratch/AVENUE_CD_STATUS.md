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

## UPDATE 2 — avenue-c DONE + avenue-d CORE done (both 0-axiom, committed)
- Avenue-c COMPLETE: commit b83fd89. KeystoneCoprimality + certs built (42MB olean cached), KeystoneSameP1 0 sorry. #print axioms clean.
- Avenue-d CORE: commit after. KeystoneEDS.lean = helper + xPair_double_and_diffAddOrInf_EDS_core PROVEN (0 custom axioms) from no-common-root(odd+even) + SameP1 wiring, explicit (h4,hψ_ne,hc3).
- STAGE 2 REMAINING (mechanical relocation, build-guided fast loop, deps cached):
  1. Relocate WHOLE KeystoneLadder L1024-1316 (10 theorems: xLadderPair_same_xPair_EDS, xPair_ne_zero_and_same_xLadderRep_EDS, xPair_ne_zero_of_isElliptic, Φ_ΨSq_no_common_eval_zero, xPair_same_xLadderRep_three/four/seam_EDS_core/seam, xRep_nsmul_same_xPair, nsmul_eq_zero_iff_ΨSq_eval) into KeystoneEDS, AFTER the core.
  2. Thread (h4,hψ_ne,hc3): add to each theorem sig; append " h4 hψ_ne hc3" to every intra-block call of the core + xLadderPair + the other relocated theorems. (Build errors pinpoint each call needing it — fast loop.) ALTERNATIVE: add [CharZero k] instance instead (auto-propagates, no call-site threading) BUT needs a non-circular hψ_ne (ψ_n≢0) derivation from CharZero via natDegree_preΨ — defer to consumer if explicit-thread chosen.
  3. Re-prove the formerly-circular Φ_ΨSq_no_common_eval_zero (L1178) from avenue-c lemmas; xPair_ne_zero_of_isElliptic becomes genuinely non-circular.
  4. TRUNCATE KeystoneLadder.lean at L1008 (delete L1009-1316 incl. the core sorry). Boundary: keep through xPair_same_xLadderRep_two (~L985); core sorry starts ~L998.
  5. Redirect consumers: NTorsionCard.lean, Seam2.lean import scratch.KeystoneEDS for nsmul_eq_zero_iff_ΨSq_eval (they currently have own copies — reconcile).
  6. Verify: lake build scratch.KeystoneEDS green + #print axioms nsmul_eq_zero_iff_ΨSq_eval = [propext,Classical.choice,Quot.sound].
- xLadderPair extract gotcha: L1024-1155 is the theorem; L1156-1160 is the NEXT theorem docstring — cut at the real theorem boundary, not a fixed line offset.

## Stage-2 NAMESPACE note (critical)
- `namespace XOnly` is L412-965 in KeystoneLadder.lean; the core (L998) + downstream (L1024-1315) are in `namespace KeystoneLadder` (NOT XOnly), after XOnly closed.
- Stage-1 KeystoneEDS put the core in `KeystoneLadder.XOnly` — built in isolation (XOnly.doubleVec resolves via open KeystoneLadder), but the downstream uses `XOnly.`-qualified refs + calls `xPair_double_sameP1` (which lives in KeystoneLadder.XOnly).
- For Stage-2 relocation use: `namespace KeystoneLadder` + `open XOnly`. Then: my core/helper calls `xPair_double_sameP1` (unqualified, via open) resolve; downstream `XOnly.doubleVec`/`XOnly.xLadderPair` (qualified) resolve; relocated `xLadderPair_same_xPair_EDS` (now in KeystoneLadder) resolves to the new threaded one.
- Extract the ORIGINAL block L998-1315 (core sorry + downstream) AS-IS to preserve namespace structure; replace the core `sorry` with the proven body (Q55 block 9) + extended sig; prepend the helper; thread (h4,hψ_ne,hc3); end at `end KeystoneLadder`. Build-guided fix of call sites (deps cached, fast).

## Stage-2 BUILD FINDING (cross-file refactor required)
- Relocating L1024-1316 into KeystoneEDS while they STILL exist in KeystoneLadder ⇒ "already declared" (KeystoneEDS imports KeystoneSameP1 → KeystoneLadder). So Stage-2 MUST: (1) TRUNCATE KeystoneLadder at L1008 (delete core sorry + L1024-1316) in the SAME change, then (2) KeystoneEDS provides the relocated+threaded versions, then (3) redirect any consumer of the removed exports to import KeystoneEDS. NOT an isolated append.
- Also: the Q55 helper block (block_8) needs its leading `namespace KeystoneLadder / namespace XOnly` stripped cleanly before insertion (parse errors at the helper site otherwise).
- Construction script /tmp/build_eds_stage2.py does core-replace + helper + xLadderPair threading; remaining = truncate Ladder + downstream call-site threading (build-guided) + consumer redirect.
