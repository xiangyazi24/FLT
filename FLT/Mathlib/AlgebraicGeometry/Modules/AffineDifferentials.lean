import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Relative differentials on an affine scheme

The universal derivation of an affine algebra extends to every principal
open by localization.  These local derivations are compatible under
restriction, so they assemble into a morphism of sheaves after restricting
scalars to the base ring.  The construction retains the Leibniz rule and
vanishing on base constants on arbitrary opens.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open TensorProduct

universe u

namespace ModuleCat.Derivation

variable {A B B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A ⟶ B'}
  {M : ModuleCat.{u} B'}

set_option backward.isDefEq.respectTransparency false in
/-- Precompose a relative derivation along a commutative square of ring maps,
viewing its target by restriction of scalars. -/
def precomp (D : M.Derivation f') (g : B ⟶ B') (h : f ≫ g = f') :
    ((ModuleCat.restrictScalars g.hom).obj M).Derivation f :=
  ModuleCat.Derivation.mk
    (fun b ↦ D.d (g b))
    (by simp)
    (by simp)
    (by
      intro a
      rw [← CommRingCat.comp_apply, h]
      exact ModuleCat.Derivation.d_map D a)

end ModuleCat.Derivation

namespace AlgebraicGeometry

variable (k R : CommRingCat.{u})
variable [Algebra k R]

def rawAffineModuleSheaf :
    TopCat.Sheaf (ModuleCat R) (Spec R) :=
  { obj := structurePresheafInModuleCat R R
    property := by
      apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (forget (ModuleCat R)) _).2
      exact (structureSheafInType R R).property }

def rawAffineKaehlerModuleSheaf :
    TopCat.Sheaf (ModuleCat R) (Spec R) :=
  { obj := structurePresheafInModuleCat R (KaehlerDifferential k R)
    property := by
      apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (forget (ModuleCat R)) _).2
      exact (structureSheafInType R (KaehlerDifferential k R)).property }

def rawAffineStructureKModuleSheaf :
    TopCat.Sheaf (ModuleCat k) (Spec R) :=
  (sheafCompose (Opens.grothendieckTopology (Spec R))
    (ModuleCat.restrictScalars (algebraMap k R))).obj
    (rawAffineModuleSheaf R)

def rawAffineKaehlerKModuleSheaf :
    TopCat.Sheaf (ModuleCat k) (Spec R) :=
  (sheafCompose (Opens.grothendieckTopology (Spec R))
    (ModuleCat.restrictScalars (algebraMap k R))).obj
    (rawAffineKaehlerModuleSheaf (k := k) R)

theorem Derivation.ext_of_isLocalization
    {k R T N : Type*} [CommRing k] [CommRing R] [CommRing T]
    [Algebra k R] [Algebra R T] [Algebra k T] [IsScalarTower k R T]
    [AddCommGroup N] [Module T N] [Module k N] [IsScalarTower k T N]
    (S : Submonoid R) [IsLocalization S T]
    (d₁ d₂ : Derivation k T N)
    (h : ∀ r : R, d₁ (algebraMap R T r) = d₂ (algebraMap R T r)) :
    d₁ = d₂ := by
  ext x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  rw [← (IsLocalization.map_units T s).smul_left_cancel]
  calc
    algebraMap R T s • d₁ (IsLocalization.mk' T r s) =
        d₁ (algebraMap R T r) - IsLocalization.mk' T r s •
          d₁ (algebraMap R T s) := by
      rw [← IsLocalization.mk'_spec T r s, d₁.leibniz]
      abel
    _ = d₂ (algebraMap R T r) - IsLocalization.mk' T r s •
          d₂ (algebraMap R T s) := by rw [h r, h s]
    _ = algebraMap R T s • d₂ (IsLocalization.mk' T r s) := by
      rw [← IsLocalization.mk'_spec T r s, d₂.leibniz]
      abel

def basicOpenDerivationAddHom (f : R) :
    (structureSheafInType R R).obj.obj (.op (PrimeSpectrum.basicOpen f)) →+
      (structureSheafInType R (KaehlerDifferential k R)).obj.obj
        (.op (PrimeSpectrum.basicOpen f)) := by
  let U : Opens (PrimeSpectrum.Top R) := PrimeSpectrum.basicOpen f
  let T := (structureSheafInType R R).obj.obj (.op U)
  let M := KaehlerDifferential k R
  let N := (structureSheafInType R M).obj.obj (.op U)
  letI : Algebra k T :=
    ((algebraMap R T).comp (algebraMap k R)).toAlgebra
  letI : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
  letI : Module k N := Module.compHom N (algebraMap k T)
  letI : IsScalarTower k T N := .of_algebraMap_smul fun _ _ => rfl
  letI : Algebra.FormallyEtale R T :=
    Algebra.FormallyEtale.of_isLocalization (.powers f)
  let e₁ : T ⊗[R] M ≃ₗ[T] KaehlerDifferential k T :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R T
  let e₂ : T ⊗[R] M ≃ₗ[T] N :=
    (IsLocalizedModule.isBaseChange (.powers f) T
      (StructureSheaf.toOpenₗ R M U)).equiv
  exact e₂.toLinearMap.toAddMonoidHom.comp
    (e₁.symm.toLinearMap.toAddMonoidHom.comp
      (KaehlerDifferential.D k T).toLinearMap.toAddMonoidHom)

set_option backward.isDefEq.respectTransparency false in
theorem basicOpenDerivationAddHom_toOpen (f r : R) :
    basicOpenDerivationAddHom k R f
        (StructureSheaf.toOpenₗ R R (PrimeSpectrum.basicOpen f) r) =
      StructureSheaf.toOpenₗ R (KaehlerDifferential k R)
        (PrimeSpectrum.basicOpen f) (KaehlerDifferential.D k R r) := by
  let U : Opens (PrimeSpectrum.Top R) := PrimeSpectrum.basicOpen f
  let T := (structureSheafInType R R).obj.obj (.op U)
  let M := KaehlerDifferential k R
  let N := (structureSheafInType R M).obj.obj (.op U)
  letI : Algebra k T :=
    ((algebraMap R T).comp (algebraMap k R)).toAlgebra
  letI : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
  letI : Module k N := Module.compHom N (algebraMap k T)
  letI : IsScalarTower k T N := .of_algebraMap_smul fun _ _ => rfl
  letI : Algebra.FormallyEtale R T :=
    Algebra.FormallyEtale.of_isLocalization (.powers f)
  let e₁ : T ⊗[R] M ≃ₗ[T] KaehlerDifferential k T :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R T
  let e₂ : T ⊗[R] M ≃ₗ[T] N :=
    (IsLocalizedModule.isBaseChange (.powers f) T
      (StructureSheaf.toOpenₗ R M U)).equiv
  change e₂ (e₁.symm (KaehlerDifferential.D k T (algebraMap R T r))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  rw [IsBaseChange.equiv_tmul]
  rw [one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem basicOpenDerivationAddHom_leibniz (f : R)
    (x y : (structureSheafInType R R).obj.obj
      (.op (PrimeSpectrum.basicOpen f))) :
    basicOpenDerivationAddHom k R f (x * y) =
      x • basicOpenDerivationAddHom k R f y +
        y • basicOpenDerivationAddHom k R f x := by
  let U : Opens (PrimeSpectrum.Top R) := PrimeSpectrum.basicOpen f
  let T := (structureSheafInType R R).obj.obj (.op U)
  let M := KaehlerDifferential k R
  let N := (structureSheafInType R M).obj.obj (.op U)
  letI : Algebra k T :=
    ((algebraMap R T).comp (algebraMap k R)).toAlgebra
  letI : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
  letI : Module k N := Module.compHom N (algebraMap k T)
  letI : IsScalarTower k T N := .of_algebraMap_smul fun _ _ => rfl
  letI : Algebra.FormallyEtale R T :=
    Algebra.FormallyEtale.of_isLocalization (.powers f)
  let e₁ : T ⊗[R] M ≃ₗ[T] KaehlerDifferential k T :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R T
  let e₂ : T ⊗[R] M ≃ₗ[T] N :=
    (IsLocalizedModule.isBaseChange (.powers f) T
      (StructureSheaf.toOpenₗ R M U)).equiv
  let d : Derivation k T N :=
    (e₁.symm.trans e₂).toLinearMap.compDer (KaehlerDifferential.D k T)
  change d (x * y) = x • d y + y • d x
  exact d.leibniz x y

set_option backward.isDefEq.respectTransparency false in
def basicOpenDerivationComponent (f : R) :
    (rawAffineStructureKModuleSheaf k R).obj.obj
        (.op (PrimeSpectrum.basicOpen f)) ⟶
      (rawAffineKaehlerKModuleSheaf k R).obj.obj
        (.op (PrimeSpectrum.basicOpen f)) := by
  dsimp [rawAffineStructureKModuleSheaf, rawAffineKaehlerKModuleSheaf,
    rawAffineModuleSheaf, rawAffineKaehlerModuleSheaf]
  let U : Opens (PrimeSpectrum.Top R) := PrimeSpectrum.basicOpen f
  let O :=
    (ModuleCat.restrictScalars (algebraMap k R)).obj
      ((structurePresheafInModuleCat R R).obj (.op U))
  let M := KaehlerDifferential k R
  let P :=
    (ModuleCat.restrictScalars (algebraMap k R)).obj
      ((structurePresheafInModuleCat R M).obj (.op U))
  let T := (structureSheafInType R R).obj.obj (.op U)
  let N := (structureSheafInType R M).obj.obj (.op U)
  change O ⟶ P
  let d : T →+ N := basicOpenDerivationAddHom k R f
  exact ModuleCat.ofHom (X := O) (Y := P)
    { toFun := d
      map_add' := by
        exact d.map_add
      map_smul' := by
        intro r x
        let rx : T := (r • x : O)
        let rdx : N := (r • (show P from d x) : P)
        change d rx = rdx
        letI : Algebra k T :=
          ((algebraMap R T).comp (algebraMap k R)).toAlgebra
        letI : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
        letI : Module k N := Module.compHom N (algebraMap k R)
        letI : IsScalarTower k T N := .of_algebraMap_smul fun c n => by
          change algebraMap R T (algebraMap k R c) • n =
            algebraMap k R c • n
          exact IsScalarTower.algebraMap_smul T (algebraMap k R c) n
        letI : Algebra.FormallyEtale R T :=
          Algebra.FormallyEtale.of_isLocalization (.powers f)
        let e₁ : T ⊗[R] M ≃ₗ[T] KaehlerDifferential k T :=
          KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R T
        let e₂ : T ⊗[R] M ≃ₗ[T] N :=
          (IsLocalizedModule.isBaseChange (.powers f) T
            (StructureSheaf.toOpenₗ R M U)).equiv
        let dₗ : T →ₗ[k] N :=
          (e₁.symm.trans e₂).toLinearMap.restrictScalars k ∘ₗ
            (KaehlerDifferential.D k T).toLinearMap
        let sx : T := (inferInstance : SMul k T).smul r x
        let sn : N := (inferInstance : SMul k N).smul r (d x)
        have hx : rx = sx := by
          dsimp only [rx, sx]
          exact Algebra.smul_def (R := R) (A := T)
            (algebraMap k R r) (show T from x)
        have hn : rdx = sn := by rfl
        rw [hx, hn]
        change dₗ sx = sn
        exact dₗ.map_smul r x }

set_option backward.isDefEq.respectTransparency false in
theorem basicOpenDerivationComponent_toOpen (f r : R) :
    (basicOpenDerivationComponent k R f).hom
        (StructureSheaf.toOpenₗ R R (PrimeSpectrum.basicOpen f) r) =
      StructureSheaf.toOpenₗ R (KaehlerDifferential k R)
        (PrimeSpectrum.basicOpen f) (KaehlerDifferential.D k R r) := by
  change basicOpenDerivationAddHom k R f
      (StructureSheaf.toOpenₗ R R (PrimeSpectrum.basicOpen f) r) = _
  exact basicOpenDerivationAddHom_toOpen k R f r

set_option backward.isDefEq.respectTransparency false in
def basicOpenDerivationNatTrans :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        (rawAffineStructureKModuleSheaf k R).obj ⟶
      (inducedFunctor (PrimeSpectrum.basicOpen (R := R))).op ⋙
        (rawAffineKaehlerKModuleSheaf k R).obj where
  app f := basicOpenDerivationComponent k R f.unop
  naturality {f g} i := by
    let U := PrimeSpectrum.basicOpen (R := R) f.unop
    let V := PrimeSpectrum.basicOpen (R := R) g.unop
    let T := (structureSheafInType R R).obj.obj (.op U)
    let S := (structureSheafInType R R).obj.obj (.op V)
    let M := KaehlerDifferential k R
    let N := (structureSheafInType R M).obj.obj (.op U)
    let P := (structureSheafInType R M).obj.obj (.op V)
    let rho : T →+* S :=
      ((structurePresheafInCommRingCat R).map i.unop.hom.op).hom
    letI : Algebra k T :=
      ((algebraMap R T).comp (algebraMap k R)).toAlgebra
    letI : Algebra k S :=
      ((algebraMap R S).comp (algebraMap k R)).toAlgebra
    letI : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower k R S := .of_algebraMap_eq fun _ => rfl
    letI : Algebra T S := rho.toAlgebra
    letI : IsScalarTower k T S := .of_algebraMap_eq fun _ => rfl
    letI : Module k N := Module.compHom N (algebraMap k R)
    letI : IsScalarTower k T N := .of_algebraMap_smul fun c n => by
      change algebraMap R T (algebraMap k R c) • n = algebraMap k R c • n
      exact IsScalarTower.algebraMap_smul T (algebraMap k R c) n
    letI : Module k P := Module.compHom P (algebraMap k R)
    letI : IsScalarTower k S P := .of_algebraMap_smul fun c n => by
      change algebraMap R S (algebraMap k R c) • n = algebraMap k R c • n
      exact IsScalarTower.algebraMap_smul S (algebraMap k R c) n
    letI : Module T P := Module.compHom P rho
    letI : IsScalarTower T S P := .of_algebraMap_smul fun _ _ => rfl
    letI : IsScalarTower k T P := .of_algebraMap_smul fun c n => by
      change rho (algebraMap R T (algebraMap k R c)) • n =
        algebraMap k R c • n
      change algebraMap R S (algebraMap k R c) • n =
        algebraMap k R c • n
      exact IsScalarTower.algebraMap_smul S (algebraMap k R c) n
    letI : Algebra.FormallyEtale R T :=
      Algebra.FormallyEtale.of_isLocalization
        (Submonoid.powers (show R from f.unop))
    letI : Algebra.FormallyEtale R S :=
      Algebra.FormallyEtale.of_isLocalization
        (Submonoid.powers (show R from g.unop))
    let eUT : T ⊗[R] M ≃ₗ[T] KaehlerDifferential k T :=
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R T
    let eUN : T ⊗[R] M ≃ₗ[T] N :=
      (IsLocalizedModule.isBaseChange
        (Submonoid.powers (show R from f.unop)) T
        (StructureSheaf.toOpenₗ R M U)).equiv
    let eVS : S ⊗[R] M ≃ₗ[S] KaehlerDifferential k S :=
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R S
    let eVP : S ⊗[R] M ≃ₗ[S] P :=
      (IsLocalizedModule.isBaseChange
        (Submonoid.powers (show R from g.unop)) S
        (StructureSheaf.toOpenₗ R M V)).equiv
    let dU : Derivation k T N :=
      (eUT.symm.trans eUN).toLinearMap.compDer
        (KaehlerDifferential.D k T)
    let dV : Derivation k S P :=
      (eVS.symm.trans eVP).toLinearMap.compDer
        (KaehlerDifferential.D k S)
    let q : N →ₗ[T] P :=
      { toFun := (structurePresheafInModuleCat R M).map i.unop.hom.op
        map_add' := by
          intro x y
          exact ((structurePresheafInModuleCat R M).map
            i.unop.hom.op).hom.map_add x y
        map_smul' := by intro a x; rfl }
    have hd : dV.compAlgebraMap T = q.compDer dU := by
      apply Derivation.ext_of_isLocalization
        (Submonoid.powers (show R from f.unop))
      intro r
      change dV (rho (algebraMap R T r)) =
        q (dU (algebraMap R T r))
      change basicOpenDerivationAddHom k R g.unop
          ((structureSheafInType R R).obj.map i.unop.hom.op
            (StructureSheaf.toOpenₗ R R U r)) =
        (structureSheafInType R M).obj.map i.unop.hom.op
          (basicOpenDerivationAddHom k R f.unop
            (StructureSheaf.toOpenₗ R R U r))
      rw [show (structureSheafInType R R).obj.map i.unop.hom.op
          (StructureSheaf.toOpenₗ R R U r) =
          StructureSheaf.toOpenₗ R R V r from rfl]
      rw [basicOpenDerivationAddHom_toOpen,
        basicOpenDerivationAddHom_toOpen]
      rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Derivation.congr_fun hd x

def rawAffineUniversalDerivationSheafHom :
    (rawAffineStructureKModuleSheaf k R).obj ⟶
      (rawAffineKaehlerKModuleSheaf k R).obj :=
  TopCat.Sheaf.restrictHomEquivHom _ _ PrimeSpectrum.isBasis_basic_opens
    (basicOpenDerivationNatTrans k R)

@[simp]
theorem rawAffineUniversalDerivationSheafHom_app_basicOpen (f : R) :
    (rawAffineUniversalDerivationSheafHom k R).app
        (.op (PrimeSpectrum.basicOpen f)) =
      basicOpenDerivationComponent k R f := by
  apply TopCat.Sheaf.extend_hom_app

set_option backward.isDefEq.respectTransparency false in
theorem rawAffineUniversalDerivationSheafHom_leibniz
    (U : Opens (PrimeSpectrum.Top R))
    (x y : (structureSheafInType R R).obj.obj (.op U)) :
    (rawAffineUniversalDerivationSheafHom k R).app (.op U) (x * y) =
      x • (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
          (.op U) from
        (rawAffineUniversalDerivationSheafHom k R).app (.op U) y) +
        y • (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
          (.op U) from
        (rawAffineUniversalDerivationSheafHom k R).app (.op U) x) := by
  apply TopCat.Presheaf.IsSheaf.section_ext
    (structureSheafInType R (KaehlerDifferential k R)).property
  intro p hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpV, hVU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.2
  refine ⟨PrimeSpectrum.basicOpen f, hVU, hpV, ?_⟩
  change ((rawAffineKaehlerKModuleSheaf k R).obj.map
      (homOfLE hVU).op).hom
        ((rawAffineUniversalDerivationSheafHom k R).app (.op U) (x * y)) =
    ((rawAffineKaehlerKModuleSheaf k R).obj.map
      (homOfLE hVU).op).hom
        (x • (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
            (.op U) from
          (rawAffineUniversalDerivationSheafHom k R).app (.op U) y) +
          y • (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
            (.op U) from
          (rawAffineUniversalDerivationSheafHom k R).app (.op U) x))
  have hD (z : (structureSheafInType R R).obj.obj (.op U)) :
      ((rawAffineKaehlerKModuleSheaf k R).obj.map
          (homOfLE hVU).op).hom
          ((rawAffineUniversalDerivationSheafHom k R).app (.op U) z) =
        (rawAffineUniversalDerivationSheafHom k R).app
          (.op (PrimeSpectrum.basicOpen f))
          (((rawAffineStructureKModuleSheaf k R).obj.map
            (homOfLE hVU).op).hom z) := by
    exact CategoryTheory.congr_fun
      ((rawAffineUniversalDerivationSheafHom k R).naturality
        (homOfLE hVU).op).symm z
  erw [hD (x * y)]
  rw [rawAffineUniversalDerivationSheafHom_app_basicOpen]
  change basicOpenDerivationAddHom k R f
      ((structurePresheafInCommRingCat R).map (homOfLE hVU).op (x * y)) = _
  rw [map_mul]
  rw [basicOpenDerivationAddHom_leibniz]
  change _ =
    ((rawAffineKaehlerKModuleSheaf k R).obj.map
      (homOfLE hVU).op).hom
      (x • (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
          (.op U) from
        (rawAffineUniversalDerivationSheafHom k R).app (.op U) y) +
        y • (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
          (.op U) from
        (rawAffineUniversalDerivationSheafHom k R).app (.op U) x))
  rw [map_add]
  change _ =
    (show (structureSheafInType R R).obj.obj
        (.op (PrimeSpectrum.basicOpen f)) from
      (structurePresheafInCommRingCat R).map (homOfLE hVU).op x) •
        (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
            (.op (PrimeSpectrum.basicOpen f)) from
          ((rawAffineKaehlerKModuleSheaf k R).obj.map
            (homOfLE hVU).op).hom
            ((rawAffineUniversalDerivationSheafHom k R).app (.op U) y)) +
      (show (structureSheafInType R R).obj.obj
          (.op (PrimeSpectrum.basicOpen f)) from
        (structurePresheafInCommRingCat R).map (homOfLE hVU).op y) •
        (show (structureSheafInType R (KaehlerDifferential k R)).obj.obj
            (.op (PrimeSpectrum.basicOpen f)) from
          ((rawAffineKaehlerKModuleSheaf k R).obj.map
            (homOfLE hVU).op).hom
            ((rawAffineUniversalDerivationSheafHom k R).app (.op U) x))
  rw [hD y, hD x]
  rw [rawAffineUniversalDerivationSheafHom_app_basicOpen]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem rawAffineUniversalDerivationSheafHom_toOpen_algebraMap
    (U : Opens (PrimeSpectrum.Top R)) (r : k) :
    (rawAffineUniversalDerivationSheafHom k R).app (.op U)
        (StructureSheaf.toOpenₗ R R U (algebraMap k R r)) = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext
    (structureSheafInType R (KaehlerDifferential k R)).property
  intro p hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpV, hVU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.2
  refine ⟨PrimeSpectrum.basicOpen f, hVU, hpV, ?_⟩
  change ((rawAffineKaehlerKModuleSheaf k R).obj.map
      (homOfLE hVU).op).hom
        ((rawAffineUniversalDerivationSheafHom k R).app (.op U)
          (StructureSheaf.toOpenₗ R R U (algebraMap k R r))) =
    ((rawAffineKaehlerKModuleSheaf k R).obj.map
      (homOfLE hVU).op).hom 0
  have hD (z : (structureSheafInType R R).obj.obj (.op U)) :
      ((rawAffineKaehlerKModuleSheaf k R).obj.map
          (homOfLE hVU).op).hom
          ((rawAffineUniversalDerivationSheafHom k R).app (.op U) z) =
        (rawAffineUniversalDerivationSheafHom k R).app
          (.op (PrimeSpectrum.basicOpen f))
          (((rawAffineStructureKModuleSheaf k R).obj.map
            (homOfLE hVU).op).hom z) := by
    exact CategoryTheory.congr_fun
      ((rawAffineUniversalDerivationSheafHom k R).naturality
        (homOfLE hVU).op).symm z
  erw [hD]
  rw [rawAffineUniversalDerivationSheafHom_app_basicOpen, map_zero]
  change basicOpenDerivationAddHom k R f
      (StructureSheaf.toOpenₗ R R (PrimeSpectrum.basicOpen f)
        (algebraMap k R r)) = 0
  rw [basicOpenDerivationAddHom_toOpen]
  rw [Derivation.map_algebraMap, map_zero]

/-! ## The affine relative derivation -/

/-- The base algebra as a constant presheaf map on `Spec R`. -/
def affineConstBaseMap :
    (Functor.const (Spec R).Opensᵒᵖ).obj k ⟶ (Spec R).presheaf where
  app U := CommRingCat.ofHom (algebraMap k R) ≫
    (Scheme.ΓSpecIso R).inv ≫
    (Spec R).presheaf.map U.unop.leTop.op
  naturality {U V} i := by
    simp only [Functor.const_obj_map, Category.assoc]
    rw [← Functor.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A relative derivation on an affine scheme with values in a module sheaf
is determined by its component on the whole affine scheme.  On a principal
open, localization extensionality reduces equality to global sections; the
sheaf condition then extends the equality to arbitrary opens. -/
theorem PresheafOfModules.Derivation'.ext_of_affine_top
    (M : (Spec R).Modules)
    (d₁ d₂ : M.val.Derivation' (affineConstBaseMap k R))
    (h : ∀ x : (Spec R).presheaf.obj (.op (⊤ : (Spec R).Opens)),
      d₁.d x = d₂.d x) :
    d₁ = d₂ := by
  apply PresheafOfModules.Derivation.ext
  funext U
  apply AddMonoidHom.ext
  intro x
  apply TopCat.Presheaf.IsSheaf.section_ext M.2
  intro p hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpV, hVU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.unop.2
  refine ⟨PrimeSpectrum.basicOpen f, hVU, hpV, ?_⟩
  change (M.val.map (homOfLE hVU).op).hom (d₁.d x) =
    (M.val.map (homOfLE hVU).op).hom (d₂.d x)
  erw [← PresheafOfModules.Derivation.d_map d₁ (homOfLE hVU).op x,
    ← PresheafOfModules.Derivation.d_map d₂ (homOfLE hVU).op x]
  have hb : d₁.app (.op (PrimeSpectrum.basicOpen f)) =
      d₂.app (.op (PrimeSpectrum.basicOpen f)) := by
    let T := (structureSheafInType R R).obj.obj
      (.op (PrimeSpectrum.basicOpen f))
    let N := M.val.obj (.op (PrimeSpectrum.basicOpen f))
    letI : Algebra k T :=
      ((algebraMap R T).comp (algebraMap k R)).toAlgebra
    letI : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
    letI : Module k N := Module.compHom N (algebraMap k T)
    letI : IsScalarTower k T N := .of_algebraMap_smul fun _ _ => rfl
    apply AlgebraicGeometry.Derivation.ext_of_isLocalization
      (k := k) (R := R) (T := T) (N := N)
      (Submonoid.powers (show R from f))
    intro r
    let rt : (Spec R).presheaf.obj (.op (⊤ : (Spec R).Opens)) :=
      StructureSheaf.toOpenₗ R R ⊤ r
    change d₁.d ((Spec R).presheaf.map
        (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op rt) =
      d₂.d ((Spec R).presheaf.map
        (homOfLE (show PrimeSpectrum.basicOpen f ≤ ⊤ from le_top)).op rt)
    erw [PresheafOfModules.Derivation.d_map d₁
        (homOfLE le_top).op rt,
      PresheafOfModules.Derivation.d_map d₂
        (homOfLE le_top).op rt]
    have hrt : d₁.d rt = d₂.d rt := by
      exact h rt
    exact congrArg (fun z ↦ (M.val.map (homOfLE le_top).op).hom z) hrt
  change (d₁.app (.op (PrimeSpectrum.basicOpen f))).d _ =
    (d₂.app (.op (PrimeSpectrum.basicOpen f))).d _
  rw [hb]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedTop_smul (M : ModuleCat.{u} R) (r : R)
    (z : Γ(tilde M, (⊤ : (Spec R).Opens))) :
    (tilde.isoTop M).inv ((Scheme.ΓSpecIso R).inv r • z) =
      r • (tilde.isoTop M).inv z := by
  have hz : (Scheme.ΓSpecIso R).inv r • z = r • z := by
    rw [Scheme.Modules.smul_Spec_def]
    have htop : (TopologicalSpace.Opens.leTop
          (⊤ : (Spec R).Opens)).op =
        𝟙 (Opposite.op (⊤ : (Spec R).Opens)) := Subsingleton.elim _ _
    rw [htop, CategoryTheory.Functor.map_id]
    rfl
  rw [hz, map_smul]

set_option maxHeartbeats 800000 in
-- The affine section isomorphisms transport both scalar actions in the Leibniz law.
set_option backward.isDefEq.respectTransparency false in
/-- Normalize the top component of an affine sheaf derivation to an ordinary
derivation of its coordinate ring. -/
def normalizedTopDerivation (M : ModuleCat.{u} R)
    (d : (tilde M).val.Derivation' (affineConstBaseMap k R)) :
    M.Derivation (CommRingCat.ofHom (algebraMap k R)) :=
  ModuleCat.Derivation.mk
    (fun r => (tilde.isoTop M).inv (d.d ((Scheme.ΓSpecIso R).inv r)))
    (by simp)
    (by
      intro x y
      rw [map_mul, PresheafOfModules.Derivation.d_mul]
      rw [map_add]
      exact congrArg₂ (fun a b => a + b)
        (normalizedTop_smul R M x
          (d.d ((Scheme.ΓSpecIso R).inv y)))
        (normalizedTop_smul R M y
          (d.d ((Scheme.ΓSpecIso R).inv x))))
    (by
      intro a
      have hd := d.d_app (X := .op (⊤ : (Spec R).Opens)) a
      change d.d ((Scheme.ΓSpecIso R).inv (algebraMap k R a)) = 0 at hd
      have := congrArg (fun z => (tilde.isoTop M).inv z) hd
      simpa using this)

set_option backward.isDefEq.respectTransparency false in
/-- The affine universal derivation as a derivation of module presheaves. -/
def affineUniversalDerivation :
    (tilde (ModuleCat.of R (KaehlerDifferential k R))).val.Derivation'
      (affineConstBaseMap k R) :=
  PresheafOfModules.Derivation'.mk
    (fun U => ModuleCat.Derivation.mk
      (fun x => show
        (tilde (ModuleCat.of R (KaehlerDifferential k R))).val.obj U from
        (rawAffineUniversalDerivationSheafHom k R).app U x)
      (by
        intro x y
        exact map_add _ x y)
      (by
        intro x y
        exact rawAffineUniversalDerivationSheafHom_leibniz k R U.unop x y)
      (by
        intro r
        change (rawAffineUniversalDerivationSheafHom k R).app U
          (StructureSheaf.toOpenₗ R R U.unop (algebraMap k R r)) = 0
        exact rawAffineUniversalDerivationSheafHom_toOpen_algebraMap
          k R U.unop r))
    (by
      intro U V i x
      change (rawAffineUniversalDerivationSheafHom k R).app V
          (((rawAffineStructureKModuleSheaf k R).obj.map i).hom x) =
        ((rawAffineKaehlerKModuleSheaf k R).obj.map i).hom
          ((rawAffineUniversalDerivationSheafHom k R).app U x)
      exact (CategoryTheory.congr_fun
        ((rawAffineUniversalDerivationSheafHom k R).naturality i).symm x).symm)

@[simp]
theorem affineUniversalDerivation_apply
    (U : (Spec R).Opensᵒᵖ) (x : (Spec R).presheaf.obj U) :
    (affineUniversalDerivation k R).d x =
      (rawAffineUniversalDerivationSheafHom k R).app U x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On affine global sections, the sheaf derivation is the usual universal
differential under the canonical tilde section map. -/
theorem affineUniversalDerivation_top_toOpen (r : R) :
    (affineUniversalDerivation k R).d
        (StructureSheaf.toOpenₗ R R ⊤ r) =
      StructureSheaf.toOpenₗ R (KaehlerDifferential k R) ⊤
        (KaehlerDifferential.D k R r) := by
  change (rawAffineUniversalDerivationSheafHom k R).app (.op ⊤)
      (StructureSheaf.toOpenₗ R R ⊤ r) = _
  erw [← PrimeSpectrum.basicOpen_one]
  rw [rawAffineUniversalDerivationSheafHom_app_basicOpen]
  change basicOpenDerivationAddHom k R 1
      (StructureSheaf.toOpenₗ R R (PrimeSpectrum.basicOpen 1) r) = _
  exact basicOpenDerivationAddHom_toOpen k R 1 r

set_option maxHeartbeats 800000 in
-- Normalization crosses the dependent sheaf and affine-tilde section identifications.
set_option backward.isDefEq.respectTransparency false in
/-- Normalizing top sections identifies the affine sheaf derivation with the
ordinary universal Kähler derivation. -/
theorem affineUniversalDerivation_normalizedTop (r : R) :
    (tilde.isoTop (ModuleCat.of R (KaehlerDifferential k R))).inv
        ((affineUniversalDerivation k R).d ((Scheme.ΓSpecIso R).inv r)) =
      KaehlerDifferential.D k R r := by
  change (tilde.isoTop (ModuleCat.of R (KaehlerDifferential k R))).inv
      ((affineUniversalDerivation k R).d
        (StructureSheaf.toOpenₗ R R ⊤ r)) = _
  calc
    _ = (tilde.isoTop (ModuleCat.of R
          (KaehlerDifferential k R))).inv
        (StructureSheaf.toOpenₗ R (KaehlerDifferential k R) ⊤
          (KaehlerDifferential.D k R r)) := congrArg
            (fun z ↦ (tilde.isoTop (ModuleCat.of R
              (KaehlerDifferential k R))).inv z)
            (affineUniversalDerivation_top_toOpen k R r)
    _ = _ := Iso.hom_inv_id_apply
      (tilde.isoTop (ModuleCat.of R (KaehlerDifferential k R))) _

set_option backward.isDefEq.respectTransparency false in
/-- The affine universal derivation commutes with the canonical section map
on every open. -/
theorem affineUniversalDerivation_toOpen
    (U : (Spec R).Opens) (r : R) :
    (affineUniversalDerivation k R).d
        ((tilde.toOpen (ModuleCat.of R R) U) r) =
      (tilde.toOpen (ModuleCat.of R (KaehlerDifferential k R)) U)
        (KaehlerDifferential.D k R r) := by
  let h : U ⟶ (⊤ : (Spec R).Opens) := homOfLE le_top
  change (affineUniversalDerivation k R).d
      ((Spec R).presheaf.map h.op ((Scheme.ΓSpecIso R).inv r)) = _
  calc
    _ = ((tilde (ModuleCat.of R (KaehlerDifferential k R))).val.map h.op).hom
        ((affineUniversalDerivation k R).d ((Scheme.ΓSpecIso R).inv r)) :=
      PresheafOfModules.Derivation.d_map (affineUniversalDerivation k R) h.op _
    _ = ((tilde (ModuleCat.of R (KaehlerDifferential k R))).val.map h.op).hom
        ((tilde.toOpen (ModuleCat.of R (KaehlerDifferential k R)) ⊤)
          (KaehlerDifferential.D k R r)) := by
      congr 1
      exact affineUniversalDerivation_top_toOpen k R r
    _ = _ := ConcreteCategory.congr_hom
      (tilde.toOpen_res (ModuleCat.of R (KaehlerDifferential k R)) ⊤ U h)
      (KaehlerDifferential.D k R r)

/-! ## Comparison with objectwise relative differentials -/

/-- The objectwise relative differential presheaf on an affine spectrum. -/
abbrev affineRelativeDifferentialsPresheaf :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (affineConstBaseMap k R)

/-- The universal affine derivation induces the canonical comparison from
objectwise relative differentials to the affine tilde differential sheaf.
Sheafifying this morphism is the affine local model for scheme-relative
differentials. -/
def affineRelativeDifferentialsToTilde :
    affineRelativeDifferentialsPresheaf k R ⟶
      (tilde (ModuleCat.of R (KaehlerDifferential k R))).val :=
  (PresheafOfModules.DifferentialsConstruction.isUniversal'
    (affineConstBaseMap k R)).desc (affineUniversalDerivation k R)

@[simp]
theorem affineRelativeDifferentialsToTilde_fac :
    (PresheafOfModules.DifferentialsConstruction.derivation'
      (affineConstBaseMap k R)).postcomp
        (affineRelativeDifferentialsToTilde k R) =
      affineUniversalDerivation k R := by
  exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
    (affineConstBaseMap k R)).fac _

@[simp]
theorem affineRelativeDifferentialsToTilde_app_d
    (U : (Spec R).Opensᵒᵖ) (x : (Spec R).presheaf.obj U) :
    (affineRelativeDifferentialsToTilde k R).app U
        (CommRingCat.KaehlerDifferential.d x) =
      (affineUniversalDerivation k R).d x := by
  have h := congrArg (fun d ↦ d.d x)
    (affineRelativeDifferentialsToTilde_fac k R)
  exact h

/-- On a principal open, formal étaleness and module localization identify
objectwise relative differentials with affine tilde sections. -/
def affineBasicOpenRelativeDifferentialsIso (f : R) :
    (affineRelativeDifferentialsPresheaf k R).obj
        (.op (PrimeSpectrum.basicOpen f)) ≅
      (tilde (ModuleCat.of R (KaehlerDifferential k R))).val.obj
        (.op (PrimeSpectrum.basicOpen f)) := by
  let U : Opens (PrimeSpectrum.Top R) := PrimeSpectrum.basicOpen f
  let T := (structureSheafInType R R).obj.obj (.op U)
  let M := KaehlerDifferential k R
  let N := (structureSheafInType R M).obj.obj (.op U)
  letI : Algebra k T :=
    ((algebraMap R T).comp (algebraMap k R)).toAlgebra
  letI : IsScalarTower k R T := .of_algebraMap_eq fun _ => rfl
  letI : Algebra.FormallyEtale R T :=
    Algebra.FormallyEtale.of_isLocalization (.powers f)
  let e₁ : T ⊗[R] M ≃ₗ[T] KaehlerDifferential k T :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R T
  let e₂ : T ⊗[R] M ≃ₗ[T] N :=
    (IsLocalizedModule.isBaseChange (.powers f) T
      (StructureSheaf.toOpenₗ R M U)).equiv
  exact (e₁.symm.trans e₂).toModuleIso

set_option maxHeartbeats 800000 in
-- Unfolding both localization equivalences crosses several dependent module structures.
set_option backward.isDefEq.respectTransparency false in
/-- The affine comparison on a principal open is the explicit localization
isomorphism.  Equality is checked on universal differentials. -/
theorem affineRelativeDifferentialsToTilde_app_basicOpen (f : R) :
    (affineRelativeDifferentialsToTilde k R).app
        (.op (PrimeSpectrum.basicOpen f)) =
      (affineBasicOpenRelativeDifferentialsIso k R f).hom := by
  apply CommRingCat.KaehlerDifferential.ext
  intro x
  erw [affineRelativeDifferentialsToTilde_app_d]
  rw [affineUniversalDerivation_apply]
  rw [rawAffineUniversalDerivationSheafHom_app_basicOpen]
  rfl

/-- The sheafification of objectwise relative differentials on an affine
spectrum. -/
abbrev affineRelativeDifferentialsSheaf : (Spec R).Modules :=
  (PresheafOfModules.sheafification
    (𝟙 (Spec R).ringCatSheaf.obj)).obj
      (affineRelativeDifferentialsPresheaf k R)

/-- The canonical affine comparison after sheafification. -/
def affineRelativeDifferentialsSheafToTilde :
    affineRelativeDifferentialsSheaf k R ⟶
      tilde (ModuleCat.of R (KaehlerDifferential k R)) :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Spec R).ringCatSheaf.obj)).symm
      (affineRelativeDifferentialsToTilde k R)

set_option backward.isDefEq.respectTransparency false in
/-- The affine sheafified comparison is an isomorphism because the original
comparison is an isomorphism on the principal-open basis. -/
instance affineRelativeDifferentialsSheafToTilde_isIso :
    IsIso (affineRelativeDifferentialsSheafToTilde k R) := by
  let Q := (PresheafOfModules.toPresheaf
    (Spec R).ringCatSheaf.obj).obj
      (tilde (ModuleCat.of R (KaehlerDifferential k R))).val
  let g := (PresheafOfModules.toPresheaf
    (Spec R).ringCatSheaf.obj).map
      (affineRelativeDifferentialsToTilde k R)
  have hBij (f : R) : Function.Bijective
      (g.app (.op (PrimeSpectrum.basicOpen f))) := by
    change Function.Bijective
      ((affineRelativeDifferentialsToTilde k R).app
        (.op (PrimeSpectrum.basicOpen f)))
    rw [affineRelativeDifferentialsToTilde_app_basicOpen]
    exact ConcreteCategory.bijective_of_isIso _
  letI : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology (Spec R)) g :=
    { equalizerSieve_mem := by
        intro U x y h p hp
        obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpV, hVU⟩ :=
          PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.unop.2
        let i : PrimeSpectrum.basicOpen f ⟶ U.unop := homOfLE hVU
        refine ⟨PrimeSpectrum.basicOpen f, i, ?_, hpV⟩
        apply (hBij f).injective
        simpa only [NatTrans.naturality_apply] using
          congrArg (fun z ↦ Q.map i.op z) h }
  letI : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology (Spec R)) g :=
    { imageSieve_mem := by
        intro U s p hp
        obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpV, hVU⟩ :=
          PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.2
        let i : PrimeSpectrum.basicOpen f ⟶ U := homOfLE hVU
        refine ⟨PrimeSpectrum.basicOpen f, i, ?_, hpV⟩
        exact (hBij f).surjective (Q.map i.op s) }
  have hgW : (Opens.grothendieckTopology (Spec R)).W g :=
    (Opens.grothendieckTopology (Spec R)).W_of_isLocallyBijective g
  letI : IsIso ((presheafToSheaf
      (Opens.grothendieckTopology (Spec R)) AddCommGrpCat).map g) :=
    ((Opens.grothendieckTopology (Spec R)).W_iff g).mp hgW
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf
    (Spec R).ringCatSheaf)]
  dsimp only [affineRelativeDifferentialsSheafToTilde]
  rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  rw [Adjunction.homEquiv_counit]
  infer_instance

end AlgebraicGeometry

end
