import Mathlib

noncomputable section

open Module
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra

namespace Q6373Check

abbrev k₂ := ZMod 2
abbrev Rz := Polynomial k₂
abbrev K := FractionRing Rz

private noncomputable def lowerFractionEquiv :
    RatFunc k₂ ≃ₐ[Rz] K :=
  (FractionRing.algEquiv Rz (RatFunc k₂)).symm

private theorem separable_K_L
    (L : Type*) [Field L]
    [Algebra Rz L]
    [Module.IsTorsionFree Rz L]
    [Algebra (RatFunc k₂) L]
    [IsScalarTower Rz (RatFunc k₂) L]
    [Algebra.IsSeparable (RatFunc k₂) L] :
    Algebra.IsSeparable K L := by
  let eK : RatFunc k₂ ≃ₐ[Rz] K := lowerFractionEquiv
  let eL : L ≃ₐ[Rz] L := AlgEquiv.refl
  refine Algebra.IsSeparable.of_equiv_equiv
    eK.toRingEquiv eL.toRingEquiv ?_
  ext x
  exact IsFractionRing.algEquiv_commutes eK eL x

private theorem torsionFree_Rz_W
    (W L : Type*)
    [CommRing W] [Field L]
    [Algebra Rz W] [Algebra Rz L] [Algebra W L]
    [IsScalarTower Rz W L]
    [IsIntegralClosure W Rz L]
    [Module.IsTorsionFree Rz L] :
    Module.IsTorsionFree Rz W :=
  IsIntegralClosure.isTorsionFree Rz L

private theorem installationProbe
    (W L : Type*)
    [CommRing W] [IsDomain W] [Field L]
    [Algebra Rz W] [Algebra Rz L] [Algebra W L]
    [IsScalarTower Rz W L]
    [IsFractionRing W L]
    [IsIntegralClosure W Rz L]
    [Module.IsTorsionFree Rz L]
    [Algebra (RatFunc k₂) L]
    [IsScalarTower Rz (RatFunc k₂) L]
    [Algebra.IsSeparable (RatFunc k₂) L]
    [FiniteDimensional K L] : True := by
  letI : Algebra.IsSeparable K L := separable_K_L L
  letI : Module.IsTorsionFree Rz W := torsionFree_Rz_W W L
  letI : IsDedekindDomain W :=
    IsIntegralClosure.isDedekindDomain Rz K L W
  -- Pin this algebra explicitly. Asking typeclass search to discover it can
  -- revisit the Rz-W-FractionRing W tower and time out.
  letI : Algebra K (FractionRing W) :=
    FractionRing.liftAlgebra Rz (FractionRing W)
  letI : Algebra.IsSeparable K (FractionRing W) := by
    let eK : RatFunc k₂ ≃ₐ[Rz] K := lowerFractionEquiv
    let eW : L ≃ₐ[W] FractionRing W :=
      (FractionRing.algEquiv W L).symm
    refine Algebra.IsSeparable.of_equiv_equiv
      eK.toRingEquiv eW.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes eK eW x
  have : Module.IsTorsionFree Rz W := inferInstance
  have : IsDedekindDomain W := inferInstance
  have : Algebra.IsSeparable K L := inferInstance
  have : Algebra.IsSeparable K (FractionRing W) := inferInstance
  trivial

private theorem directNormProbe
    (W : Type*) [CommRing W]
    [Algebra Rz W]
    [IsDedekindDomain W]
    [Module.Finite Rz W]
    [Module.IsTorsionFree Rz W]
    [Algebra.IsSeparable K (FractionRing W)]
    (hFormula :
      ∀ (P : Ideal W) (p : Ideal Rz)
        [P.LiesOver p] [P.IsMaximal] [p.IsMaximal],
        Ideal.relNorm Rz P = p ^ p.inertiaDeg P)
    (P : Ideal W) [P.IsMaximal] :
    Ideal.relNorm Rz P =
      (P.under Rz) ^ (P.under Rz).inertiaDeg P := by
  letI : P.LiesOver (P.under Rz) := by infer_instance
  letI : (P.under Rz).IsMaximal := by
    change (P.comap (algebraMap Rz W)).IsMaximal
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  exact hFormula P (P.under Rz)

end Q6373Check
