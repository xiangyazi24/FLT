## Run 2026-06-23 (continuation, diff-add keystone)
- doctrine: DOCTRINE_diffadd.md
- starting avenue: (a) cofactors → encode sat lemmas
- in flight: dm1(even cof), dm2b(integer odd cof), dm4(assembly), GF(3) integrality test, dm3 wiring fetched
- landed so far: xPair_double_sameP1 (c83f6c6); diff-add cert scaffold +4 eval bridges (2 cofactor sorries); dm2 odd cofactors verified

### Progress 2026-06-23 (continuation)
- avenue (a) DONE: KeystoneDiffAddCert.lean 0-sorry/3-std-axioms (commit 6b67c65). Both numerator sat-lemmas via integer linear_combination cofactors (tracked-Buchberger lift, one S-poly; CAS cross-verified both parities). Mechanism validated first with dm2 cofactor×3 (sat_odd3), then clean integer (dm1 even + dm1-method-adapted odd).
- avenue (b) DONE: KeystoneSameP1.lean xPair_diffAdd_sameP1 wiring compiles (commit d42dd8b). dm3 wiring integrated + fixed (typed binders, baseChange in bridges, Φ_one/ΨSq_one, simp-only for diffAddOrInfVec, open Classical). Module lake-builds (8573 jobs).
- avenue (c) DISPATCHED: division-poly coprimality gcd(Φ_n,ΨSq_n)=1 non-circular (the 1 remaining sorry, xPair_odd_phi_eval_ne_zero_of_delta_zero). = SEAM-1 separability. ChatGPT dm1 (Q-coprimality). Promising angle: consecutive-preΨ-vanish → preΨ_1=1 contradiction via Somos; 2-torsion case separate.
- avenue (d) MAPPED: core sorry needs (c) + h4/hψ_ne/hc3 (NOT from IsElliptic alone per dm4 — char 2 exists) + (m,m+1) order symmetry + ℕ/ℤ cast. Restructure core to carry hNoCommon (dm4 design). Depends on (c).
- polyrith DEAD in this Mathlib (external service shut down) — literal cofactors mandatory; that path landed.

### Progress 2026-06-23 (continuation 2 — avenue c started)
- avenue (c) Ψ₃≠0 stratum DONE (commits 012783c, 4b43ba3): propagation core
  (preΨ_prev/next_zero_of_adjacent_zero via shifted-center Somos: 2 of 3 terms vanish,
  c3x·preΨ²=0, Ψ₃.eval≠0 forces preΨ=0) + no_adjacent_preΨ_zero_of_Ψ₃_eval_ne
  (bidirectional Int.le_induction to preΨ_1=1). 0-sorry, 3 std axioms.
- ChatGPT dmc (Q30) corrected the target: needs IsElliptic (singular-cusp counterexample
  where Φ₃,ΨSq₃ vanish at X=0 under h4/hψ_ne/hc3 alone). Core L1009 HAS [IsElliptic].
- Resultant cert CAS-verified: resultant(Ψ₂Sq,Ψ₃)+Δ² = -4·bRel·(...), so =-Δ² mod bRel.
- Remaining (c): Ψ₃=0 stratum (rank-3 apparition: preΨ_n=0 ⟺ 3∣n, needs Ψ₂Sq≠0 &
  preΨ₄≠0 at Ψ₃ roots = more resultant certs), 2-torsion (Ψ₂Sq=0, odd preΨ ≠0 strong
  induction), the resultant-cert Lean encodings, odd specialization (short, dmc-given).
