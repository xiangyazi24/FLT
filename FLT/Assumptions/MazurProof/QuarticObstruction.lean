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

-- TODO: Implement lemmas connecting QuarticD to no_degenerate_point theorems
-- Example structure (incomplete):
--
-- theorem quartic_d_gives_no_kubert_point (d : ℕ) (hd : d ∈ [2,3,4,5,6,7])
--     (E : WeierstrassCurve ℚ) [E.IsElliptic]
--     (condition : E has full 2-torsion + order d point in some form) :
--     ¬ ∃ (non-degenerate point on Kubert curve for this d) := by
--   cases' hd with hd
--   · exact quartic_no_sol_d2 ...  -- import from scratch.QuarticD2
--   · ...

end MazurProof
