import Mathlib
import FLT.EllipticCurve.Torsion
import scratch.QuarticD2
import scratch.QuarticD3
import scratch.QuarticD4
import scratch.QuarticD5
import scratch.QuarticD6
import scratch.QuarticD7

/-! # Quartic Obstruction Lemmas

Supporting proofs for Axiom 4 (no ℤ/2 × ℤ/n for n ∈ {10,12,14,16}).

The Kubert parametrization of curves with full 2-torsion + Z/n point reduces
to a quartic obstruction via discriminant conditions. The squeezed forms
(QuarticD d=2-7) prove non-solvability for specific parameter families.

TODO (2026-06-26): Verify exact mapping d ↔ n:
  - Kubert family → parametric obstruction curve
  - Obstruction curve → quartic form s⁴ + d²s² - d⁴ = t²
  - Rational point ↔ non-degenerate Kubert parameter

Use CAS (SageMath/SymPy) to confirm equation reductions. If mapping is non-trivial,
dispatch to Codex for the Kubert theory + reduction proofs.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Placeholder: QuarticD → Axiom 4 assembly

These lemmas will assemble the quartic proofs into Axiom 4's structure
once the d ↔ n mapping is verified.

Tentative mapping (TO BE VERIFIED):
  - QuarticD2 (s⁴ + 4s² - 16 = t²) → possibly n = 12 or auxiliary form
  - QuarticD3 (s⁴ + 9s² - 81 = t²) → possibly n = ?
  - ...
  - QuarticD7 (s⁴ + 49s² - 2401 = t²) → possibly n = ?
-/

-- TODO (priority): Dispatch to Codex for Kubert theory
-- Once d ↔ n mapping is established, wire as follows:

theorem quartic_d2_supports_axiom_4_n12 :
    ¬∃ f : ZMod 2 × ZMod 12 →+ (WeierstrassCurve ℚ)⁄ℚ.Point, Function.Injective f := by
  sorry  -- reduce to QuarticD2 via Kubert parametrization
  -- This should eventually use: quartic_no_sol_d2

theorem quartic_d3_supports_axiom_4_n14 :
    ¬∃ f : ZMod 2 × ZMod 14 →+ (WeierstrassCurve ℚ)⁄ℚ.Point, Function.Injective f := by
  sorry  -- reduce to QuarticD3 via Kubert parametrization

theorem quartic_d_supports_axiom_4 (n : ℕ) (hn : n ∈ [10, 12, 14, 16]) :
    ¬∃ f : ZMod 2 × ZMod n →+ (WeierstrassCurve ℚ)⁄ℚ.Point, Function.Injective f := by
  interval_cases n  -- Case-split: n = 10, 12, 14, 16
  -- Case n = 10: reduce via Kubert → quartic_no_sol_d? (awaiting Q1 mapping)
  case n_10 => sorry  -- quartic_no_sol_d? (confirm d via Q1)
  -- Case n = 12: reduce to quartic_no_sol_d2
  case n_12 => exact quartic_d2_supports_axiom_4_n12
  -- Case n = 14: reduce to quartic_no_sol_d3
  case n_14 => exact quartic_d3_supports_axiom_4_n14
  -- Case n = 16: reduce via Kubert → quartic_no_sol_d? (awaiting Q1 mapping)
  case n_16 => sorry  -- quartic_no_sol_d? (confirm d via Q1)

end MazurProof
