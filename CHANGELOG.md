# CHANGELOG — Mazur |T|<=16 formalization (uisai2 ai-scratch)

Continuous log of MY changes, newest first. One entry per meaningful change (commit SHA + what + why).
Maintained so the work is traceable and nothing gets lost across long sessions / clone moves.

## 2026-06-24 (cont) — /automode: bridge-1 coprimality even-case foundation

- Bridge-1 even case (preΨ-root-Ψ2Sq-ne): CAS-VERIFIED the hCD relation preΨ4^2 + 4*Ψ3^3 = Q1*Ψ2Sq + Q2*b_relation (remainder 0; Q1 57-term/Q2 25-term cofactors, scratch/bridge1_hcd_cert.py). scratch/Bridge1HCD.lean states the eval-level lemma (CAS-verified, linear_combination lift WIP, 1 sorry). Next (fresh context): fix cert lift; then EDS-zero closed forms via normEDSRec'; then nonvanishing -> even case closed.

## 2026-06-24 — SEAM1 proven + wired; clone sync

- `97c41ca` Preserve MAZUR_CHECKLIST.md (root).
- `50fed72` Preserve 38 untracked uisai2-local files (TwoTorsionBound, EDS test probes, 33 roadmap/strategy/handoff docs) — never committed on either clone.
- `661feda` Clone sync: recover scratch/E20_FiniteFieldCounts.lean from the other (xiangyazi24) ai-scratch clone (the ONLY file uisai2 lacked); commit pending lakefile.toml scratch lean_lib + Isogeny20a4 phi-evals. Reverted an uncommitted 75-line deletion of scratch/Seam2.lean that would have lost in-progress SEAM2 field-generalization (SameP1 general-k, not present in Seam2Wired). Verified the divergent A3-descent file diffs (DenominatorQuartic etc.) were STRUCTURAL (rewire-to-import), not mathematical. No work lost either clone.
- `b00270e` WIRE SEAM1 into canonical FLT/EllipticCurve/Torsion.lean: L76 preΨ-separable sorry now routes to the proven WeierstrassCurve.preΨ-separable-of-natCast-ne-zero (scratch.SeamE1). Torsion.lean 9 -> 8 sorries; full build 8597 jobs EXIT 0.
- `9250585` SEAM1 bridge findings recorded in docstrings (bridge-1 non-circularity trap; bridge-2 deep-crux ingredients).
- `f2484bd` SEAM1 bridge-1 MECHANICAL reduction PROVEN: nonTwo_of_Psi2Sq_ne (Psi2Sq(x) != 0 => exists y on curve with psi2 != 0, via alg-closed quadratic + psi2^2 = Psi2Sq). Bridge-1 shrunk to pure coprimality sorry prePsi-root-Psi2Sq-ne.
- `91cb7e0` SEAM1 bridge designs saved (ChatGPT Q118 coprimality EDS-closed-forms + Q119 deep-crux).
- `0543656`..`ecb0411` SEAM1 E1 chain (this session): A3 helper separable_of_deriv_ne_zero_at_roots (375761d) -> E-scaffold reduction (0543656) -> A1 dual-Taylor engine eval_dualNumber (313514c) + corollary (d215912) -> Dual/TangentO d[n]=n (000b6b4) -> equation_dual_iff (e3eff8e) -> y-lifts (33cb1c7) -> MultipleRootBridge (084e0de) -> rootwise-core assembly (6ef0a7e) -> final wiring (ecb0411). All 0-custom-axiom; whole SEAM1 reduced to 2 designed bridges in SeamE1_Core.
- `7a383c3` n=3 separability brick Psi3_separable (resultant Bezout, 0 axioms). n=4 cofactor record (66dea94, Res = 2^9 * Delta^5).

### State after this session
- Mazur |T|<=16 = axiom Mazur_statement (FLT black box); our MazurProof tree proves it.
- 1 custom axiom remains: A3 no_rational_point_of_order_ge_17 (deep core).
- Torsion.lean: 8 seam sorries (SEAM2 char conds x3, sub-D, infra: n_torsion_finite [not ours] / Module.Finite / galoisRep).
- SEAM1: proven mod 2 designed bridges in SeamE1_Core (coprimality prePsi-root-Psi2Sq-ne; deep crux dual_root_implies_tangent_zero).

## How I maintain this (going forward)
Append a dated section per session; one bullet per meaningful commit (SHA + what + why). Keep newest-first.
Update the "State" block whenever the sorry/axiom count changes.
