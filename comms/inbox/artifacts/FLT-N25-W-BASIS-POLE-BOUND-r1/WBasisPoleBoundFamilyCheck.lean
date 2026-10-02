import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Lean.Elab.Tactic.Omega
set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_WBasisPoleBound
open scoped BigOperators
variable (A : Type*) [CommRing A] [IsDomain A]
  [Algebra (Polynomial (ZMod 2)) A] [Module.Finite (Polynomial (ZMod 2)) A]
  [Module.IsTorsionFree (Polynomial (ZMod 2)) A]
variable (hrank : Module.finrank (Polynomial (ZMod 2)) A = 4)
variable (xOrder yzOrder zOrder : Additive ((FractionRing A)ˣ) →+ ℤ)
/-- A fixed actual basis of A over its established F2[z] action. -/
def wPolynomialBasis25Two : Module.Basis (Fin 4) (Polynomial (ZMod 2)) A := by
  letI : Module.Free (Polynomial (ZMod 2)) A := Module.free_of_finite_type_torsion_free'
  exact Module.finBasisOfFinrankEq (Polynomial (ZMod 2)) A hrank

omit [IsDomain A] in
theorem wPolynomialBasis25Two_ne_zero (i : Fin 4) : wPolynomialBasis25Two A hrank i ≠ 0 :=
  (wPolynomialBasis25Two A hrank).ne_zero i

/-- Each basis element is regarded as its actual nonzero common-field function. -/
def wPolynomialBasisFunction25Two (i : Fin 4) : Additive ((FractionRing A)ˣ) :=
  Additive.ofMul (Units.mk0 (algebraMap A (FractionRing A) (wPolynomialBasis25Two A hrank i))
    ((map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr (wPolynomialBasis25Two_ne_zero A hrank i)))

/-- A single natural bound, constructed once from the actual finite basis.
It is deliberately coarse and contains no divisor-dependent choice. -/
def wPolynomialBasisPoleBound25Two : ℕ :=
  ∑ i : Fin 4,
    ((-xOrder (wPolynomialBasisFunction25Two A hrank i)).toNat +
    (-yzOrder (wPolynomialBasisFunction25Two A hrank i)).toNat +
    (-zOrder (wPolynomialBasisFunction25Two A hrank i)).toNat)

/-- The fixed basis satisfies the pole weights 1,1,2 of the actual function Z/A. -/
theorem wPolynomialBasis_boundary_orders_bounded (i : Fin 4) :
    -(wPolynomialBasisPoleBound25Two A hrank xOrder yzOrder zOrder : ℤ) ≤ xOrder (wPolynomialBasisFunction25Two A hrank i) ∧
    -(wPolynomialBasisPoleBound25Two A hrank xOrder yzOrder zOrder : ℤ) ≤ yzOrder (wPolynomialBasisFunction25Two A hrank i) ∧
    -(2 * (wPolynomialBasisPoleBound25Two A hrank xOrder yzOrder zOrder : ℤ)) ≤ zOrder (wPolynomialBasisFunction25Two A hrank i) := by
  have hi :
      (-xOrder (wPolynomialBasisFunction25Two A hrank i)).toNat +
      (-yzOrder (wPolynomialBasisFunction25Two A hrank i)).toNat +
      (-zOrder (wPolynomialBasisFunction25Two A hrank i)).toNat ≤ wPolynomialBasisPoleBound25Two A hrank xOrder yzOrder zOrder :=
    Finset.single_le_sum
      (f := fun j : Fin 4 =>
        (-xOrder (wPolynomialBasisFunction25Two A hrank j)).toNat +
        (-yzOrder (wPolynomialBasisFunction25Two A hrank j)).toNat +
        (-zOrder (wPolynomialBasisFunction25Two A hrank j)).toNat)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  constructor
  · omega
  constructor <;> omega

#print axioms wPolynomialBasis25Two
#print axioms wPolynomialBasis25Two_ne_zero
#print axioms wPolynomialBasisFunction25Two
#print axioms wPolynomialBasisPoleBound25Two
#print axioms wPolynomialBasis_boundary_orders_bounded
end MazurProof.N25F_WBasisPoleBound
