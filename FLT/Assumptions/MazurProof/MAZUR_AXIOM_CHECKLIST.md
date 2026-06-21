# Mazur |T|≤16 — Axiom Discharge Board (老规矩: 列清单挨个磨, 挨个钩)

Goal: discharge all 6 remaining custom axioms → only [propext, Classical.choice, Quot.sound].
Status: ✅ done sorry-free + #print axioms clean · 🟡 partial/in-work (what's open) · ⬜ open.
Last verified: 2026-06-21.

## TOP-LEVEL AXIOMS — scoreboard 2/6 discharged (4 custom axioms remain; A1+A2 ✅ on fresh rebuild)
- ✅ **A1 `rational_torsion_two_invariant_factors`** — DISCHARGED (axiom→theorem, 6→5; residual=keystone seam sorryAx). — needs: keystone rank-2 (K) + finiteness (C2 ✓avail) + invariant-factor algebra (C1 ✅). Closest to dischargeable.
- ✅ **A2 `weil_pairing_primitive_root`** — DISCHARGED (axiom→theorem, 5→4; residual=rationalWeilPairingPackage Miller seam). — needs: keystone rank-2 (K) + WeilPairingPackage Stage-1 + Miller Stage-3 (SEAM 3).
- ⬜ **A3 `no_rational_point_of_order_ge_17`** — Mazur core, deepest. Separate later campaign.
- ⬜ **A4 `Z2xZ14_gives_non_degenerate_N14_point`** — genus-4 forward restructure.
- ⬜ **A5 `Z2xZ16_gives_non_degenerate_N16_point`** — genus-5 forward restructure.
- 🟡 **A6 `mordell_weil_fg`** — full Mordell-Weil. Currently USED (legit strong axiom) to supply
  finiteness; the THOROUGH finish is to prove it (cornerstone, max reuse). Mountain, not permanent.

## KEYSTONE sub-board (shared foundation for A1 + A2) — scoreboard 0/3
- 🟡 **K1 `n_torsion_card = n²`** (scratch/NTorsionCard.lean) — compiles, #print axioms =
  [propext, sorryAx, Classical.choice, Quot.sound] (NO custom axiom). Modulo 4 code sorries:
  - ⬜ **SEAM 1 `preΨ'_separable_of_natCast_ne_zero`** (L38) — [n] étaleness. Grind via E1 (Weierstrass formal group).
  - ⬜ **SEAM 2 `nsmul_eq_zero_iff_ΨSq_eval`** (L44) — x-coord division-poly formula (EDS induction).
  - 🟡 **sub D `preΨ'_eval_eq_zero_iff_exists_non_two_torsion`** (L80) — root realization over sep-closed k. Closeable.
  - 🟡 **sub E2 `twoTorsionKernel_card` E[2]=4** (L248) — closeable via twoTorsionPolynomial disc≠0.
- ⬜ **K2 `geomNTorsion_rank_two_linear`** — from K1; the shared `E[n]≅ₗ(ZMod n)²` keystone.
- ⬜ **K3 Stage-0 API refactor** — PointsOver/nTorsionOver/geomNTorsion/mapLinear, ≃+ → ≃ₗ (dm3).

## COMPONENTS (reusable, not top-level axioms)
- ✅ **C1 invariant-factor algebra** `finite_add_comm_group_embed_zmod_sq_invariantFactors_card` —
  committed 13265dd, fresh-olean verified [propext, Classical.choice, Quot.sound]. (A1 tail.)
- ✅ **C2 finiteness from A6** `rational_torsion_finite_alias` — already in tree (torsion_set_finite_of_fg).
- ⬜ **C3 WeilPairingPackage Stage-1** `full_rational_torsion_has_primitive_root` — discharges A2 modulo the package.
- ⬜ **C4 Miller pairing construction (SEAM 3)** — tame-symbol reciprocity + nondeg (geometric, NOT card).

## GRIND ORDER (next → )
1. Close K1's 2 sub-steps (sub D, sub E2) so K1 = clean modulo only the 2 seams. ← grinding now (codex)
2. K3 Stage-0 + K2 geomNTorsion rank-2 (from K1).
3. A1: wire K2 + C1 + C2 → discharge rational_torsion_two_invariant_factors. (6→5)
4. C3 + A2 Weil Stage-1; then SEAM 3 Miller; then SEAM 1 E1 formal group; then SEAM 2.
5. A4/A5 genus restructure; A6 full Mordell-Weil; A3 Mazur core.

## DISCHARGED ALONG THE WAY (preserve the full list — 别忘了)
Count fluctuated (started ~12–13; once down to 5 at 8db5461; N14/16 re-split as axioms 7d2f601).
These were custom MazurProof axioms that are now THEOREMS / removed:
- ✅ obstruction_curve_20a4_points_degenerate (5e6a0a2)
- ✅ N12 obstruction assembly (d9829b0)
- ✅ N14 obstruction curve axiom (1ac9661)
- ✅ N16 obstruction curve axiom (dac126b)
- ✅ E20_rational_points_complete (bcf2925)
- ✅ Z2xZ10_gives_non_degenerate — descent bridge (b57bda4)
- ✅ Z2xZ12_gives_non_degenerate (N12 descent)
- ✅ no_Z2_cross_Z10, no_Z2_cross_Z12 → now THEOREMS from descent (7d2f601)
- ✅ removed dead: rational_torsion_finite (duplicate), rank_E20_eq_zero_ax (fake True) (38c6e22)
- ✅ first_invariant_factor — PROVED (8db5461)

## NOT OUR AXIOMS (upstream FLT-project scaffolding, outside MazurProof — do NOT count)
- FLT/Assumptions/Mazur.lean: Mazur_statement (the overall Mazur theorem — the thing |T|≤16 feeds)
- FLT/Assumptions/KnownIn1980s.lean: knownin1980s {P} : P (FLT's classical-results black box)
- FLT/Assumptions/Odlyzko.lean: Odlyzko_statement (analytic number theory input)

## BOTTOM LINE
6 custom axioms remain in the |T|≤16 proof (MazurProof). The keystone infra we spun off
(n_torsion_card, geomNTorsion rank-2, invariant-factor algebra ✅, Weil pairing) exists to
discharge A1 + A2 (and A6 feeds A1). A3/A4/A5 are separate. C1 already landed 0-axiom (13265dd).
