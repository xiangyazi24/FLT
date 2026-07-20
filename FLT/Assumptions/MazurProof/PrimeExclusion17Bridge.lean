import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.PrimeExclusion17

/-!
# Prime order 17 exclusion — bridge to axiom discharge

X₀(17) is a genus-1 curve with Mordell–Weil group ℤ/4ℤ and 2 cusps,
hence exactly 2 noncuspidal rational points.  At each noncuspidal point
the 17-isogeny kernel polynomial (degree 8) has no rational root
(proved in `PrimeExclusion17`).

The bridge axiom `order17_to_kernel_root` encodes the standard fact:
a rational point P of order 17 on E/ℚ generates a cyclic 17-isogeny
whose kernel polynomial coincides with one of the two fibers above
the noncuspidal points of X₀(17), so x(P) is a rational root of that
kernel polynomial.
-/

open Polynomial

namespace MazurProof.PrimeExclusion17Bridge

open PrimeExclusion17

/-- If E/ℚ has a rational point of order 17, then the kernel polynomial
of the corresponding 17-isogeny (classified by X₀(17)(ℚ)) has a
rational root.  The two fibers are `fiberQ1 * fiberQ2` and `fiber2`
from `PrimeExclusion17`. -/
axiom order17_to_kernel_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 17) :
    (∃ x : ℚ, aeval x (fiberQ1 * fiberQ2) = 0) ∨
    (∃ x : ℚ, aeval x fiber2 = 0)

theorem no_order_17_prime
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 17 := by
  intro h
  rcases order17_to_kernel_root E h with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact fiber1_no_rational_root x hx
  · exact fiber2_no_rational_root x hx

end MazurProof.PrimeExclusion17Bridge
