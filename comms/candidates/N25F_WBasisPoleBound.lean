import FLT.Assumptions.MazurProof.N25F_WChartBaseNorm
import FLT.Assumptions.MazurProof.N25F_PolynomialBoundaryOrders
import Mathlib.LinearAlgebra.Dimension.Free

/-! A fixed genuine rank-four polynomial basis, with one uniform pole bound
at all three boundary points. The bound is independent of any divisor. -/
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_WBasisPoleBound
open N25F_NonBoundaryPrincipalDivisor
open N25F_XBoundaryOrder N25F_YZBoundaryOrder N25F_ZBoundaryOrder
local notation "P" => Polynomial (ZMod 2)
local notation "K" => FractionRing W
open scoped BigOperators

/-- A fixed actual basis of W over its established F2[z] action. -/
def wPolynomialBasis25Two : Module.Basis (Fin 4) P W := by
  letI : Module.Free P W := Module.free_of_finite_type_torsion_free'
  exact Module.finBasisOfFinrankEq P W wChart_finrank_polynomial_eq_four

theorem wPolynomialBasis25Two_ne_zero (i : Fin 4) : wPolynomialBasis25Two i ≠ 0 :=
  wPolynomialBasis25Two.ne_zero i

/-- Each basis element is regarded as its actual nonzero common-field function. -/
def wPolynomialBasisFunction25Two (i : Fin 4) : Additive Kˣ :=
  Additive.ofMul (Units.mk0 (algebraMap W K (wPolynomialBasis25Two i))
    ((map_ne_zero_iff _ (IsFractionRing.injective W K)).mpr (wPolynomialBasis25Two_ne_zero i)))

/-- A single natural bound, constructed once from the actual finite basis.
It is deliberately coarse and contains no divisor-dependent choice. -/
def wPolynomialBasisPoleBound25Two : ℕ :=
  ∑ i : Fin 4,
    ((-xBoundaryOrder (wPolynomialBasisFunction25Two i)).toNat +
    (-yzBoundaryOrder (wPolynomialBasisFunction25Two i)).toNat +
    (-zBoundaryOrder (wPolynomialBasisFunction25Two i)).toNat)

/-- The fixed basis satisfies the pole weights 1,1,2 of the actual function Z/W. -/
theorem wPolynomialBasis_boundary_orders_bounded (i : Fin 4) :
    -(wPolynomialBasisPoleBound25Two : ℤ) ≤ xBoundaryOrder (wPolynomialBasisFunction25Two i) ∧
    -(wPolynomialBasisPoleBound25Two : ℤ) ≤ yzBoundaryOrder (wPolynomialBasisFunction25Two i) ∧
    -(2 * (wPolynomialBasisPoleBound25Two : ℤ)) ≤ zBoundaryOrder (wPolynomialBasisFunction25Two i) := by
  have hi :
      (-xBoundaryOrder (wPolynomialBasisFunction25Two i)).toNat +
      (-yzBoundaryOrder (wPolynomialBasisFunction25Two i)).toNat +
      (-zBoundaryOrder (wPolynomialBasisFunction25Two i)).toNat ≤ wPolynomialBasisPoleBound25Two :=
    Finset.single_le_sum
      (f := fun j : Fin 4 =>
        (-xBoundaryOrder (wPolynomialBasisFunction25Two j)).toNat +
        (-yzBoundaryOrder (wPolynomialBasisFunction25Two j)).toNat +
        (-zBoundaryOrder (wPolynomialBasisFunction25Two j)).toNat)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  constructor
  · omega
  constructor <;> omega

end MazurProof.N25F_WBasisPoleBound
