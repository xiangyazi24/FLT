import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Pullback of the unit module sheaf along an open immersion

For an open immersion of schemes `f : X ⟶ Y`, restriction identifies the
structure sheaf on the image of an open `U ⊆ X` with the structure sheaf on
`U`.  Consequently, restriction of the free rank-one module sheaf on `Y` is
the free rank-one module sheaf on `X`.

Mathlib already identifies restriction with pullback for module sheaves.  The
two isomorphisms below package the remaining rank-one comparison, first for
the explicit restriction functor and then for the ordinary pullback functor.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Restricting the unit module sheaf along an open immersion gives the unit
module sheaf.  On an open `U`, the component is the ring isomorphism
`Γ(Y, f(U)) ≅ Γ(X, U)`, regarded as an isomorphism of modules over
`Γ(X, U)`. -/
def restrictUnitIso :
    (restrictFunctor f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimageIso <|
    PresheafOfModules.isoMk
      (fun U ↦ ModuleCat.restrictScalarsIsoOfEquiv
        (f.appIso U.unop).symm.commRingCatIsoToRingEquiv)
      (fun {U V} g ↦ by
        have h :
            Y.presheaf.map (f.opensFunctor.op.map g) ≫
                (f.appIso V.unop).hom =
              (f.appIso U.unop).hom ≫ X.presheaf.map g := by
          apply (f.appIso U.unop).inv_comp_eq.mp
          calc
            (f.appIso U.unop).inv ≫
                (Y.presheaf.map (f.opensFunctor.op.map g) ≫
                  (f.appIso V.unop).hom) =
                ((f.appIso U.unop).inv ≫
                  Y.presheaf.map (f.opensFunctor.op.map g)) ≫
                    (f.appIso V.unop).hom :=
              (Category.assoc _ _ _).symm
            _ = (X.presheaf.map g ≫ (f.appIso V.unop).inv) ≫
                  (f.appIso V.unop).hom := congrArg
              (fun q ↦ q ≫ (f.appIso V.unop).hom)
              (Scheme.Hom.appIso_inv_naturality f g).symm
            (X.presheaf.map g ≫ (f.appIso V.unop).inv) ≫
                (f.appIso V.unop).hom = X.presheaf.map g := by
              rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        apply ConcreteCategory.hom_ext
        intro x
        exact ConcreteCategory.congr_hom h x)

/-- On sections over `U`, the forward unit-restriction comparison is the
structure-sheaf isomorphism attached to the open immersion. -/
@[simp]
theorem restrictUnitIso_hom_app_apply (U : X.Opens)
    (x : Γ(Y, f ''ᵁ U)) :
    ((restrictUnitIso f).hom.app U) x = (f.appIso U).hom x :=
  rfl

/-- On sections over `U`, the inverse unit-restriction comparison is the
inverse structure-sheaf isomorphism attached to the open immersion. -/
@[simp]
theorem restrictUnitIso_inv_app_apply (U : X.Opens)
    (x : Γ(X, U)) :
    ((restrictUnitIso f).inv.app U) x = (f.appIso U).inv x :=
  rfl

/-! ## Affine generators and restriction along `Spec.map` -/

/-- For the self-module, `tilde.toOpen` sends a ring element to the
corresponding global structure-sheaf section and then restricts it to the
chosen open. -/
theorem tildeSelf_toOpen_apply {R : CommRingCat} (U : (Spec R).Opens) (r : R) :
    (tilde.toOpen (ModuleCat.of R R) U) r =
      (Spec R).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso R).inv r) := by
  rfl

/-- The inverse structure-sheaf comparison for an affine open immersion
sends the image of an affine generator back to the same generator on the
corresponding image open. -/
theorem specMap_appIso_inv_tildeSelf_toOpen_apply {R S : CommRingCat}
    (g : R ⟶ S) [IsOpenImmersion (Spec.map g)]
    (U : (Spec S).Opens) (r : R) :
    ((Spec.map g).appIso U).inv
        ((tilde.toOpen (ModuleCat.of S S) U) (g r)) =
      (tilde.toOpen (ModuleCat.of R R) ((Spec.map g) ''ᵁ U)) r := by
  rw [tildeSelf_toOpen_apply, tildeSelf_toOpen_apply]
  have hnat :
      (Scheme.ΓSpecIso S).inv (g r) =
        (Spec.map g).appTop ((Scheme.ΓSpecIso R).inv r) := by
    exact ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality g) r
  rw [hnat]
  have hrestrict :
      (Spec.map g).appTop ≫
          (Spec S).presheaf.map (homOfLE le_top).op ≫
          ((Spec.map g).appIso U).inv =
        (Spec R).presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.appIso_inv_naturality]
    have htop :
        (Spec.map g).appTop ≫ ((Spec.map g).appIso ⊤).inv =
          (Spec R).presheaf.map
            (homOfLE (show (Spec.map g) ''ᵁ ⊤ ≤ ⊤ from le_top)).op := by
      simpa [Scheme.Hom.appLE,
        Scheme.Hom.image_top_eq_opensRange] using
        (Scheme.Hom.appLE_appIso_inv (Spec.map g)
          (U := ⊤) (V := ⊤) (e := le_top))
    erw [reassoc_of% htop]
    erw [← Functor.map_comp]
    rfl
  exact ConcreteCategory.congr_hom hrestrict ((Scheme.ΓSpecIso R).inv r)

/-- The forward structure-sheaf comparison is the inverse formulation of
`specMap_appIso_inv_tildeSelf_toOpen_apply`. -/
theorem specMap_appIso_hom_tildeSelf_toOpen_apply {R S : CommRingCat}
    (g : R ⟶ S) [IsOpenImmersion (Spec.map g)]
    (U : (Spec S).Opens) (r : R) :
    ((Spec.map g).appIso U).hom
        ((tilde.toOpen (ModuleCat.of R R) ((Spec.map g) ''ᵁ U)) r) =
      (tilde.toOpen (ModuleCat.of S S) U) (g r) := by
  rw [← specMap_appIso_inv_tildeSelf_toOpen_apply g U r]
  exact Iso.inv_hom_id_apply ((Spec.map g).appIso U) _

/-- A morphism of affine modules acts on a section generated by
`tilde.toOpen` by applying the module morphism before forming that section. -/
theorem tildeMap_toOpen_apply {R : CommRingCat} {M N : ModuleCat R}
    (g : M ⟶ N) (U : (Spec R).Opens) (x : M) :
    (tilde.map g).app U ((tilde.toOpen M U) x) =
      (tilde.toOpen N U) (g x) := by
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app g U) x

set_option maxHeartbeats 800000 in
-- Expanding the affine tilde adjunction and both unit-sheaf comparisons is
-- expensive for definitional equality, although the proof checks one generator.
/-- Conjugating a rank-one tilde transition by the unit-sheaf restriction
comparison maps its unit scalar through the affine ring homomorphism.  The
proof uses the affine generator `1`; linearity then determines the entire
morphism. -/
theorem restrictUnitIso_conjugate_tildeUnit {R S : CommRingCat}
    (g : R ⟶ S) [IsOpenImmersion (Spec.map g)] (u : Rˣ) :
    (restrictUnitIso (Spec.map g)).inv ≫
        (restrictFunctor (Spec.map g)).map
          ((tilde.functor R).mapIso
            (DistribMulAction.toLinearEquiv R R u).toModuleIso).hom ≫
        (restrictUnitIso (Spec.map g)).hom =
      ((tilde.functor S).mapIso
        (DistribMulAction.toLinearEquiv S S
          (Units.map g.hom.toMonoidHom u)).toModuleIso).hom := by
  apply ((tilde.adjunction (R := S)).homEquiv
    (ModuleCat.of S S) (tilde (ModuleCat.of S S))).injective
  simp only [Adjunction.homEquiv_apply]
  change (tilde.toTildeΓNatIso (R := S)).hom.app _ ≫ _ =
    (tilde.toTildeΓNatIso (R := S)).hom.app _ ≫ _
  apply ModuleCat.hom_ext
  change
    (((tilde.toTildeΓNatIso (R := S)).hom.app (ModuleCat.of S S) ≫
      (moduleSpecΓFunctor (R := S)).map
        ((restrictUnitIso (Spec.map g)).inv ≫
          (restrictFunctor (Spec.map g)).map
            ((tilde.functor R).mapIso
              (DistribMulAction.toLinearEquiv R R u).toModuleIso).hom ≫
          (restrictUnitIso (Spec.map g)).hom)).hom :
      S →ₗ[S] (moduleSpecΓFunctor (R := S)).obj
        (tilde (ModuleCat.of S S))) =
    (((tilde.toTildeΓNatIso (R := S)).hom.app (ModuleCat.of S S) ≫
      (moduleSpecΓFunctor (R := S)).map
        ((tilde.functor S).mapIso
          (DistribMulAction.toLinearEquiv S S
            (Units.map g.hom.toMonoidHom u)).toModuleIso).hom).hom :
      S →ₗ[S] (moduleSpecΓFunctor (R := S)).obj
        (tilde (ModuleCat.of S S)))
  apply LinearMap.ext_ring (R := S) (S := S)
  change (((restrictUnitIso (Spec.map g)).inv.app ⊤ ≫
      ((restrictFunctor (Spec.map g)).map
        ((tilde.functor R).mapIso
          (DistribMulAction.toLinearEquiv R R u).toModuleIso).hom).app ⊤ ≫
      (restrictUnitIso (Spec.map g)).hom.app ⊤)
        ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1)) =
    (((tilde.functor S).mapIso
      (DistribMulAction.toLinearEquiv S S
        (Units.map g.hom.toMonoidHom u)).toModuleIso).hom.app ⊤)
      ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1)
  simp only [CategoryTheory.comp_apply]
  change ((Spec.map g).appIso ⊤).hom
      (((((tilde.functor R).mapIso
        (DistribMulAction.toLinearEquiv R R u).toModuleIso).hom).app
          ((Spec.map g) ''ᵁ ⊤))
        (((Spec.map g).appIso ⊤).inv
          ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1))) =
    (((tilde.functor S).mapIso
      (DistribMulAction.toLinearEquiv S S
        (Units.map g.hom.toMonoidHom u)).toModuleIso).hom.app ⊤)
      ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1)
  dsimp [tilde.isoTop]
  have hOne := specMap_appIso_inv_tildeSelf_toOpen_apply g ⊤ (1 : R)
  simp only [map_one] at hOne
  erw [hOne, tildeMap_toOpen_apply,
    specMap_appIso_hom_tildeSelf_toOpen_apply, tildeMap_toOpen_apply]
  congr 1
  simp [Units.smul_def]

/-- Pulling back the unit module sheaf along an open immersion gives the unit
module sheaf.  This is the restriction comparison transported through the
canonical natural isomorphism from restriction to pullback. -/
def pullbackUnitIso :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (restrictFunctorIsoPullback f).symm.app _ ≪≫ restrictUnitIso f

end AlgebraicGeometry.Scheme.Modules
