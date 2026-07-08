# Session Handoff — 2026-07-08 (ChatGPT Harvest Mode)

## Achievements

### CyclicExclusion20: 7→2 sorry (commit 0796e235)
Closed all 4 group-theory lemmas:
- `image_order_10_of_order_20` via `addOrderOf_eq_of_nsmul_and_div_prime_nsmul`
- `image_order_12_of_order_24` (same pattern)
- `eta_ne_half_image_20` via 2•T = 0 → 10•P = 0 contradiction
- `eta_ne_half_image_24` (same pattern)

2 helpers (`image_five_nsmul_ne_zero_of_order_20`, `image_two_nsmul_ne_zero_of_order_20`, etc.)

Remaining 2 sorry: `no_rational_point_of_order_{20,24}` — needs Z/2×Z/10 embedding.

### CyclicExclusion15: Bug fix (commit 3b0e38e6)
`no_tate_order5_psi3_root_solution` was FALSE — b=-2, x=-1 is a counterexample
(ψ₃ has a rational root but the curve has no rational y with discriminant -11).
Fixed by adding `TateOrder5CurveEq` constraint.

### Total: 125→120 sorry, 27 axiom

## ChatGPT Research Harvested

### Q3905 (group theory) → USED ✓
All 4 group-theory lemma proofs. Key API: `addOrderOf_eq_of_nsmul_and_div_prime_nsmul`.

### Q3907 (Kubert bridge math) → RESEARCH ✓
- N=14 standard: w²+uw+w = u³-u (NOT the project's w²=u³+u²-2u directly)
- Need birational map from standard to project curve
- N=16: nested square condition, parametrize via α=(m²-1)/(m²+1)
- Cusps: u ∈ {-1,0,1} for N=14

### Q3915 (Z2×Z10 embedding) → PARTIAL
Code structure correct: coprod + ZMod.lift + independence lemma.
`eq_five_nsmul_of_order_two_mem_zmultiples` COMPILES.
Injectivity proof has tactic errors (ZMod↔ℤ conversion).
Follow-up question dispatched.

### Q3906 (Diophantine N18/N21) → PENDING (24+ min of extended thinking)

## Scratch Files Created
- `scratch/TestExcl20.lean` — test file for group-theory proofs (compiles clean)
- `scratch/TestZ2Z10.lean` — Z2×Z10 embedding WIP (partially compiles)

## Next Steps (priority order)

1. **Close `no_rational_point_of_order_{20,24}`**: needs the Z2×Z10 injective hom.
   `eq_five_nsmul_of_order_two_mem_zmultiples` is proved.
   Need working `torsionProductHom_injective` tactic proof.

2. **Harvest Q3906** (Diophantine): when it lands, wire into CyclicExclusion18/21.

3. **Wire scratch/ObstructionN14**: The 1924-line 0-sorry proof exists in scratch/.
   Can discharge `rank_zero_96a1` in RationalPointsN14 and
   `obstruction_curve_N14_points_degenerate` axiom in DescentBridgeN14.
   Needs: add scratch to lake build graph or copy into FLT/.

4. **CyclicExclusion14/15/16 Kubert bridges**: substantial modular-curve infra.

## Remote Build

uisai2 at /home/xhuan5/repos/flt-ai. Push to `xiang` remote.
Local `lake build` forbidden (24GB mini). Use `lake env lean` for single-file checks.
