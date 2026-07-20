import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.PrimeExclusion19

/-!
# Prime order 19 exclusion — bridge to axiom discharge

X₀(19) is a genus-1 curve with Mordell–Weil group ℤ/3ℤ and 2 cusps,
hence exactly 1 noncuspidal rational point.  The 19-isogeny kernel
polynomial at that point (degree 9, monic) has no rational root
(proved in `PrimeExclusion19`).

The bridge axiom `order19_to_kernel_root` encodes: a rational point P
of order 19 on E/ℚ generates a cyclic 19-isogeny corresponding to the
unique noncuspidal rational point on X₀(19), so x(P) is a rational root
of that kernel polynomial.
-/

open Polynomial

namespace MazurProof.PrimeExclusion19Bridge

open PrimeExclusion19

/-- If E/ℚ has a rational point of order 19, the unique rational
19-isogeny (from the sole noncuspidal point of X₀(19)(ℚ)) has kernel
polynomial `kernelPoly19`, so x(P) is a rational root. -/
axiom order19_to_kernel_root
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 19) :
    ∃ x : ℚ, aeval x kernelPoly19 = 0

theorem no_order_19_prime
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 19 := by
  intro h
  obtain ⟨x, hx⟩ := order19_to_kernel_root E h
  exact kernelPoly19_no_rational_root x hx

end MazurProof.PrimeExclusion19Bridge
