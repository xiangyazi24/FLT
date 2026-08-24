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

section WChart

variable (W L : Type*)
  [CommRing W] [IsDomain W] [Field L]
  [Algebra Rz W] [Algebra Rz L] [Algebra W L]
  [IsScalarTower Rz W L]
  [IsFractionRing W L]
  [IsIntegralClosure W Rz L]
  [Module.IsTorsionFree Rz L]
  [Algebra (RatFunc k₂) L]
  [IsScalarTower Rz (RatFunc k₂) L]
  [Algebra.IsSeparable (RatFunc k₂) L]
  [FiniteDimensional K L]

private local instance separableKL : Algebra.IsSeparable K L :=
  separable_K_L L

private local instance torsionFreeRzW : Module.IsTorsionFree Rz W :=
  IsIntegralClosure.isTorsionFree Rz L

private local instance dedekindW : IsDedekindDomain W :=
  IsIntegralClosure.isDedekindDomain Rz K L W

private local instance separableFractionRings :
    Algebra.IsSeparable K (FractionRing W) := by
  let eK : RatFunc k₂ ≃ₐ[Rz] K := lowerFractionEquiv
  let eW : L ≃ₐ[W] FractionRing W :=
    (FractionRing.algEquiv W L).symm
  refine Algebra.IsSeparable.of_equiv_equiv
    eK.toRingEquiv eW.toRingEquiv ?_
  ext x
  exact IsFractionRing.algEquiv_commutes eK eW x

#synth Algebra K L
#synth IsScalarTower Rz K L
#synth Algebra.IsSeparable K L
#synth Module.IsTorsionFree Rz W
#synth IsDedekindDomain W
#synth Algebra K (FractionRing W)
#synth IsScalarTower Rz K (FractionRing W)
#synth Algebra.IsSeparable K (FractionRing W)

private theorem directNormProbe
    [Module.Finite Rz W]
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

end WChart

end Q6373Check
