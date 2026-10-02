import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Localization.FractionRing

set_option synthInstance.maxHeartbeats 200000
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace MazurProof.N25F_InfinityCanonicalSeparable

/-- Separability in a compatible fixed fraction field descends to the
canonical fraction ring, without identifying their Algebra structures. -/
theorem canonicalFractionRing_isSeparable
    {A B L : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Field L] [Algebra A B] [Module.IsTorsionFree A B]
    [Algebra A L] [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [Algebra.IsSeparable (FractionRing A) L] :
    letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra _ _
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra _ _
  letI : Algebra (FractionRing B) L := FractionRing.liftAlgebra _ _
  letI : IsScalarTower A (FractionRing B) L := IsScalarTower.to₁₃₄ A B (FractionRing B) L
  letI : IsScalarTower (FractionRing A) (FractionRing B) L :=
    IsScalarTower.of_algebraMap_eq' (by
      apply IsLocalization.ringHom_ext (nonZeroDivisors A)
      ext a
      change algebraMap (FractionRing A) L (algebraMap A (FractionRing A) a) =
        algebraMap (FractionRing B) L
          (algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a))
      rw [← IsScalarTower.algebraMap_apply A (FractionRing A) L,
        ← IsScalarTower.algebraMap_apply A (FractionRing A) (FractionRing B),
        ← IsScalarTower.algebraMap_apply A (FractionRing B) L])
  exact Algebra.isSeparable_tower_bot_of_isSeparable (FractionRing A) (FractionRing B) L

#check @canonicalFractionRing_isSeparable
#print axioms canonicalFractionRing_isSeparable
end MazurProof.N25F_InfinityCanonicalSeparable
