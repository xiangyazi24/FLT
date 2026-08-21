import FLT.Mathlib.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Detecting module-sheaf isomorphisms on an open cover

A morphism of module sheaves is an isomorphism when all of its restrictions
to an open cover are isomorphisms.  The proof passes from a cover member to
each stalk through the restriction-stalk natural isomorphism, then applies
the stalkwise isomorphism criterion for sheaves.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of module sheaves is an isomorphism if it is so after
restriction to every member of an open cover. -/
theorem isIso_of_restrict_openCover (𝒰 : X.OpenCover) (f : M ⟶ N)
    (h : ∀ i, IsIso ((restrictFunctor (𝒰.f i)).map f)) : IsIso f := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hStalk (x : X) :
      IsIso
        ((toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f) := by
    let i := 𝒰.idx x
    have hx := 𝒰.covers x
    change x ∈ Set.range (𝒰.f i) at hx
    obtain ⟨y, hy⟩ := hx
    let G := toPresheaf (𝒰.X i) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    have hRestrictedStalk : IsIso
        ((restrictFunctor (𝒰.f i) ⋙ G).map f) := by
      change IsIso (G.map ((restrictFunctor (𝒰.f i)).map f))
      letI := h i
      infer_instance
    have hCoverStalk : IsIso
        ((toPresheaf X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
            (𝒰.f i y)).map f) :=
      (NatIso.isIso_map_iff (restrictStalkNatIso (𝒰.f i) y) f).mp
        hRestrictedStalk
    exact hy ▸ hCoverStalk
  have hUnderlyingStalk (x : X) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (F.map f).hom) := by
    change IsIso
      ((toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)
    exact hStalk x
  letI : ∀ x : X,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (F.map f).hom) := hUnderlyingStalk
  haveI : IsIso (F.map f) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (F.map f)
  apply Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso ((F.map f).hom.app (.op U))
  infer_instance

end AlgebraicGeometry.Scheme.Modules
