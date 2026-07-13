import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.TateOriginDivision

/-!
# Prime order 13 exclusion

X₁(13) is a genus-2 hyperelliptic curve: y² = x⁶+4x⁵+6x⁴+2x³+x²+2x+1.
Its Jacobian J₁(13)(ℚ) ≅ ℤ/19ℤ (rank 0), and the six rational points are
all cusps.  This file reduces the prime-order axiom to the raw Tate
division polynomial system and leaves the genus-2 rational-points
classification as a precisely scoped bridge axiom.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.PrimeExclusion13

open TateOriginDivision

def RawOrder13TateObstruction : Prop :=
  ∃ b c : ℚ,
    ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
      b ≠ 0 ∧ ((W b c).preΨ' 13).eval 0 = 0

theorem order13_to_raw_tate_obstruction
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h13 : HasRationalPointOfOrder E 13) :
    RawOrder13TateObstruction := by
  obtain ⟨b, c, hEll, _hord, hb, h13eval⟩ :=
    exists_tate_parameters_of_has_rational_point_of_odd_order
      E (n := 13) (by norm_num) (by decide) h13
  exact ⟨b, c, hEll, hb, h13eval⟩

axiom no_raw_order13_tate_obstruction : ¬ RawOrder13TateObstruction

theorem no_order_13_prime
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 13 := by
  intro h13
  exact no_raw_order13_tate_obstruction
    (order13_to_raw_tate_obstruction E h13)

end MazurProof.PrimeExclusion13
