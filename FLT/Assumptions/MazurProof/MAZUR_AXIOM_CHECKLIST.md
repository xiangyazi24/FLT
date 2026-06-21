# Mazur |T|≤16 — Axiom Discharge Board (老规矩: 列清单挨个磨, 挨个钩)

Goal: discharge all 6 remaining custom axioms → only [propext, Classical.choice, Quot.sound].
Status: ✅ done sorry-free + #print axioms clean · 🟡 partial/in-work (what's open) · ⬜ open.
Last verified: 2026-06-21.

## TOP-LEVEL AXIOMS (6) — scoreboard 0/6 discharged
- ⬜ **A1 `rational_torsion_two_invariant_factors`** — needs: keystone rank-2 (K) + finiteness (C2 ✓avail) + invariant-factor algebra (C1 ✅). Closest to dischargeable.
- ⬜ **A2 `weil_pairing_primitive_root`** — needs: keystone rank-2 (K) + WeilPairingPackage Stage-1 + Miller Stage-3 (SEAM 3).
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
