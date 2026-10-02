import FLT.Assumptions.MazurProof.N18AddCongrWired

/-!
# N18 near-origin addition congruence

Source pin: 4017da66cbb1b8deff6da7116c7af5de540e1908.
The public theorem below retains its existing statement and namespace exactly.
Its origin and finite-point cases are supplied by add_congr_wired, using the
three branch proofs over the original valuation toolbox.

Two independent repairs to the historical signature must not be conflated:
* The correct domain is O or ordPi(x) < 0. Positive ordPi(z) alone also admits
  finite points away from O; the old explicit counterexample has nonzero error.
* The zero-error disjunction handles ordPi(0) = 0 on the corrected domain.

N18AddCongrProof.not_add_congr_signature remains intact. It refutes the old
z-positive signature, not this near-origin theorem. No assumptions or theorem
statements are weakened. Source-only candidate; all new Lean/kernel checks
NOT RUN. This result alone does not construct every FormalKernelData field.
-/

namespace MazurProof.N18Block5Instantiation.AddCongr

open MazurProof.N18RouteC
open MazurProof.N18RouteC.Isogeny
open MazurProof.N18RouteC.ThreeAdic

noncomputable section

/-- Addition estimate on the existing, unchanged near-origin domain. -/
theorem add_congr (P Q : E0Point)
    (hP : P = 0 ∨ ordPi (xCoord P) < 0)
    (hQ : Q = 0 ∨ ordPi (xCoord Q) < 0) :
    zParam (P + Q) - zParam P - zParam Q = 0 ∨
    v (zParam P) + v (zParam Q) ≤ v (zParam (P + Q) - zParam P - zParam Q) := by
  exact MazurProof.N18Block5Instantiation.add_congr_wired P Q hP hQ

end

end MazurProof.N18Block5Instantiation.AddCongr
