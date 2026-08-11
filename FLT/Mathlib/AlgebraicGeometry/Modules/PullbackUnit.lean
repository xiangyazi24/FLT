import Mathlib.AlgebraicGeometry.Modules.Sheaf

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

/-- Pulling back the unit module sheaf along an open immersion gives the unit
module sheaf.  This is the restriction comparison transported through the
canonical natural isomorphism from restriction to pullback. -/
def pullbackUnitIso :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (restrictFunctorIsoPullback f).symm.app _ ≪≫ restrictUnitIso f

end AlgebraicGeometry.Scheme.Modules
