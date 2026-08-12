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

open CategoryTheory CategoryTheory.Limits

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
-- The affine tilde adjunction and both unit-sheaf comparisons are unfolded
-- only to test the global generator `1`, but this still creates a large term.
/-- Conjugating a tilde morphism given by scalar multiplication through the
unit-sheaf restriction comparison maps the scalar along the affine ring
homomorphism.  This is the noninvertible analogue of the transition-unit
comparison below and is the base-change identity needed for homogeneous
equations such as projective Koszul differentials. -/
theorem restrictUnitIso_conjugate_tildeMul {R S : CommRingCat}
    (g : R ⟶ S) [IsOpenImmersion (Spec.map g)] (r : R) :
    (restrictUnitIso (Spec.map g)).inv ≫
        (restrictFunctor (Spec.map g)).map
          ((tilde.functor R).map
            (ModuleCat.ofHom (LinearMap.lsmul R R r))) ≫
        (restrictUnitIso (Spec.map g)).hom =
      (tilde.functor S).map
        (ModuleCat.ofHom (LinearMap.lsmul S S (g r))) := by
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
            ((tilde.functor R).map
              (ModuleCat.ofHom (LinearMap.lsmul R R r))) ≫
          (restrictUnitIso (Spec.map g)).hom)).hom :
      S →ₗ[S] (moduleSpecΓFunctor (R := S)).obj
        (tilde (ModuleCat.of S S))) =
    (((tilde.toTildeΓNatIso (R := S)).hom.app (ModuleCat.of S S) ≫
      (moduleSpecΓFunctor (R := S)).map
        ((tilde.functor S).map
          (ModuleCat.ofHom (LinearMap.lsmul S S (g r))))).hom :
      S →ₗ[S] (moduleSpecΓFunctor (R := S)).obj
        (tilde (ModuleCat.of S S)))
  apply LinearMap.ext_ring (R := S) (S := S)
  change (((restrictUnitIso (Spec.map g)).inv.app ⊤ ≫
      ((restrictFunctor (Spec.map g)).map
        ((tilde.functor R).map
          (ModuleCat.ofHom (LinearMap.lsmul R R r)))).app ⊤ ≫
      (restrictUnitIso (Spec.map g)).hom.app ⊤)
        ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1)) =
    (((tilde.functor S).map
      (ModuleCat.ofHom (LinearMap.lsmul S S (g r)))).app ⊤)
      ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1)
  simp only [CategoryTheory.comp_apply]
  change ((Spec.map g).appIso ⊤).hom
      ((((tilde.functor R).map
        (ModuleCat.ofHom (LinearMap.lsmul R R r))).app
          ((Spec.map g) ''ᵁ ⊤))
        (((Spec.map g).appIso ⊤).inv
          ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1))) =
    (((tilde.functor S).map
      (ModuleCat.ofHom (LinearMap.lsmul S S (g r)))).app ⊤)
      ((tilde.isoTop (R := S) (ModuleCat.of S S)).hom 1)
  dsimp [tilde.isoTop]
  have hOne := specMap_appIso_inv_tildeSelf_toOpen_apply g ⊤ (1 : R)
  simp only [map_one] at hOne
  erw [hOne, tildeMap_toOpen_apply,
    specMap_appIso_hom_tildeSelf_toOpen_apply, tildeMap_toOpen_apply]
  congr 1
  simp

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

/-- If an open immersion is an isomorphism, restriction followed by extension
by zero is naturally isomorphic to the identity.  Sectionwise, the adjunction
unit is restriction along `f '' f ⁻¹ U = U`, hence the image of an isomorphism
of opens under the module presheaf. -/
theorem restrictAdjunction_unit_app_isIso_of_isIso [IsIso f]
    (M : Y.Modules) :
    IsIso ((restrictAdjunction f).unit.app M) := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [restrictAdjunction_unit_app_app]
  have h : f ''ᵁ f ⁻¹ᵁ U = U := by
    rw [f.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have hhom : homOfLE (f.image_preimage_le U) = eqToHom h :=
    Subsingleton.elim _ _
  rw [hhom]
  change IsIso (M.presheaf.map (eqToIso h).hom.op)
  infer_instance

/-! ## Open base change for module sheaves

For a cartesian square of open immersions, restricting a direct image across
one side agrees with taking the direct image of the restriction across the
opposite side.  This is the Beck--Chevalley isomorphism needed to evaluate a
Čech equalizer on one member of an open cover.

The comparison is constructed as the mate of the square under the
restriction--direct-image adjunction.  Its proof is sectionwise: the pullback
hypothesis identifies the two open subsets on which the original sheaf is
evaluated, so every component is a presheaf restriction along an equality.
-/

variable {P U X Y : Scheme} (f' : P ⟶ U) (iX : P ⟶ X)
  (iU : U ⟶ Y) (f : X ⟶ Y)
  [IsOpenImmersion f'] [IsOpenImmersion iX] [IsOpenImmersion iU]
  [IsOpenImmersion f]

/-- Restriction of a module-sheaf morphism is evaluated on the image of the
chosen open subset.  This exposes the sectionwise form used in the base-change
calculation below. -/
@[simp]
lemma restrictFunctor_map_app {A B : Y.Modules} (g : A ⟶ B)
    (V : U.Opens) :
    ((restrictFunctor iU).map g).app V = g.app (iU ''ᵁ V) :=
  rfl

/-- The restricted Beck--Chevalley comparison on the pullback open.  It
combines functoriality of restriction, commutativity of the square, and the
counit identifying the restriction of an open direct image with its source. -/
def openBaseChangeRestrictedHom (H : IsPullback f' iX iU f)
    (M : X.Modules) :
    (restrictFunctor f').obj
        ((restrictFunctor iU).obj ((pushforward f).obj M)) ⟶
      (restrictFunctor iX).obj M :=
  (restrictFunctorComp f' iU).inv.app ((pushforward f).obj M) ≫
    (restrictFunctorCongr H.w).hom.app ((pushforward f).obj M) ≫
    (restrictFunctorComp iX f).hom.app ((pushforward f).obj M) ≫
    (restrictFunctor iX).map ((restrictAdjunction f).counit.app M)

/-- The open base-change morphism is the adjoint transpose of the comparison
after restriction to the cartesian intersection. -/
def openBaseChangeHom (H : IsPullback f' iX iU f) (M : X.Modules) :
    (restrictFunctor iU).obj ((pushforward f).obj M) ⟶
      (pushforward f').obj ((restrictFunctor iX).obj M) :=
  (restrictAdjunction f').homEquiv _ _
    (openBaseChangeRestrictedHom f' iX iU f H M)

set_option backward.isDefEq.respectTransparency false in
/-- On an open `W`, the Beck--Chevalley map is the presheaf restriction
along the equality of opens supplied by the cartesian square.  Exposing this
component is useful when checking coherence of iterated open base change. -/
@[simp]
theorem openBaseChangeHom_app (H : IsPullback f' iX iU f)
    (M : X.Modules) (W : U.Opens) :
    (openBaseChangeHom f' iX iU f H M).app W =
      (M.presheaf.mapIso
        (eqToIso
          (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op).hom := by
  rw [openBaseChangeHom, Adjunction.homEquiv_unit, Hom.comp_app,
    pushforward_map_app, restrictAdjunction_unit_app_app]
  dsimp [openBaseChangeRestrictedHom]
  rw [restrict_map, pushforward_obj_presheaf_map]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Open base change for module sheaves is invertible.  On an open subset of
`U`, its component is the restriction map along the equality between the two
pullback descriptions of the corresponding open subset of `X`. -/
theorem openBaseChangeHom_isIso (H : IsPullback f' iX iU f)
    (M : X.Modules) :
    IsIso (openBaseChangeHom f' iX iU f H M) := by
  rw [Hom.isIso_iff_isIso_app]
  intro W
  let eW :
      Γ((restrictFunctor iU).obj ((pushforward f).obj M), W) ≅
        Γ((pushforward f').obj ((restrictFunctor iX).obj M), W) :=
    M.presheaf.mapIso
      (eqToIso
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op
  have hW : (openBaseChangeHom f' iX iU f H M).app W = eW.hom := by
    rw [openBaseChangeHom, Adjunction.homEquiv_unit, Hom.comp_app,
      pushforward_map_app, restrictAdjunction_unit_app_app]
    dsimp [openBaseChangeRestrictedHom, eW]
    rw [restrict_map, pushforward_obj_presheaf_map]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp]
    congr 1
  rw [hW]
  infer_instance

/-- The Beck--Chevalley isomorphism for a cartesian square of open
immersions. -/
def openBaseChangeIso (H : IsPullback f' iX iU f) (M : X.Modules) :
    (restrictFunctor iU).obj ((pushforward f).obj M) ≅
      (pushforward f').obj ((restrictFunctor iX).obj M) := by
  letI := openBaseChangeHom_isIso f' iX iU f H M
  exact asIso (openBaseChangeHom f' iX iU f H M)

@[simp]
theorem openBaseChangeIso_hom (H : IsPullback f' iX iU f)
    (M : X.Modules) :
    (openBaseChangeIso f' iX iU f H M).hom =
      openBaseChangeHom f' iX iU f H M := by
  dsimp [openBaseChangeIso]

/-- The Beck--Chevalley isomorphism is natural in the module on the pulled
back corner.  Sectionwise, the square is exactly the naturality square for
the underlying presheaf morphism and the equality of opens supplied by the
cartesian square. -/
theorem openBaseChangeIso_hom_naturality (H : IsPullback f' iX iU f)
    {M N : X.Modules} (phi : M ⟶ N) :
    (restrictFunctor iU).map ((pushforward f).map phi) ≫
        (openBaseChangeIso f' iX iU f H N).hom =
      (openBaseChangeIso f' iX iU f H M).hom ≫
        (pushforward f').map ((restrictFunctor iX).map phi) := by
  apply hom_ext
  intro W
  simp only [Hom.comp_app, restrictFunctor_map_app, pushforward_map_app,
    openBaseChangeIso_hom, openBaseChangeHom_app]
  exact (phi.mapPresheaf.naturality _).symm

/-- The inverse Beck--Chevalley isomorphism is sectionwise the inverse
restriction along the open-set equality supplied by the pullback square. -/
@[simp]
theorem openBaseChangeIso_inv_app (H : IsPullback f' iX iU f)
    (M : X.Modules) (W : U.Opens) :
    (openBaseChangeIso f' iX iU f H M).inv.app W =
      (M.presheaf.mapIso
        (eqToIso
          (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op).inv := by
  rw [← cancel_epi ((openBaseChangeIso f' iX iU f H M).hom.app W)]
  rw [← Hom.comp_app]
  simp only [Iso.hom_inv_id, Hom.id_app]
  rw [openBaseChangeIso_hom, openBaseChangeHom_app]
  exact (M.presheaf.mapIso
    (eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W)).op).hom_inv_id.symm

/-! ## Extension by zero and pasted base change -/

variable {Q V : Scheme} (r : Q ⟶ V) (q : Q ⟶ P)
  (k : V ⟶ X) (b : P ⟶ X) (a : P ⟶ U)
  (h : V ⟶ Y)
  [IsOpenImmersion r] [IsOpenImmersion q] [IsOpenImmersion k]
  [IsOpenImmersion b] [IsOpenImmersion a] [IsOpenImmersion h]

/-- Extend a morphism from the restriction to a smaller open by zero on the
ambient scheme.  The equality `hk` records the chosen name for the composite
open immersion, so callers may use a geometrically meaningful map rather than
the raw expression `k ≫ f`. -/
def pushforwardRestrictionHomOfHom (hk : k ≫ f = h)
    (F : X.Modules) (G : V.Modules)
    (e : (restrictFunctor k).obj F ⟶ G) :
    (pushforward f).obj F ⟶ (pushforward h).obj G :=
  (pushforward f).map
      ((restrictAdjunction k).unit.app F ≫ (pushforward k).map e) ≫
    (pushforwardComp k f).hom.app G ≫
    (pushforwardCongr hk).hom.app G

set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero of a restriction morphism is natural in both its
source and target coefficients.  Thus a commuting square on the smaller open
induces the corresponding commuting square after both sheaves are pushed to
the ambient scheme.  This is the functorial bridge used to descend compatible
local morphisms through a Cech equalizer. -/
theorem pushforwardRestrictionHomOfHom_naturality (hk : k ≫ f = h)
    {F₁ F₂ : X.Modules} {G₁ G₂ : V.Modules}
    (u₁ : (restrictFunctor k).obj F₁ ⟶ G₁)
    (u₂ : (restrictFunctor k).obj F₂ ⟶ G₂)
    (a : F₁ ⟶ F₂) (b : G₁ ⟶ G₂)
    (w : (restrictFunctor k).map a ≫ u₂ = u₁ ≫ b) :
    (pushforward f).map a ≫
        pushforwardRestrictionHomOfHom (f := f) (k := k) (h := h)
          hk F₂ G₂ u₂ =
      pushforwardRestrictionHomOfHom (f := f) (k := k) (h := h)
          hk F₁ G₁ u₁ ≫
        (pushforward h).map b := by
  subst h
  have hlocal :
      a ≫ ((restrictAdjunction k).unit.app F₂ ≫
          (pushforward k).map u₂) =
        (restrictAdjunction k).unit.app F₁ ≫
          ((pushforward k).map u₁ ≫ (pushforward k).map b) := by
    calc
      _ = (restrictAdjunction k).unit.app F₁ ≫
          (pushforward k).map ((restrictFunctor k).map a) ≫
            (pushforward k).map u₂ := by
        simpa only [Functor.id_map, Functor.comp_map] using
          (restrictAdjunction k).unit.naturality_assoc a
            ((pushforward k).map u₂)
      _ = (restrictAdjunction k).unit.app F₁ ≫
          (pushforward k).map ((restrictFunctor k).map a ≫ u₂) := by
        rw [Functor.map_comp]
      _ = (restrictAdjunction k).unit.app F₁ ≫
          (pushforward k).map (u₁ ≫ b) := by rw [w]
      _ = _ := by rw [Functor.map_comp]
  have hfront :
      (pushforward f).map a ≫
          (pushforward f).map ((restrictAdjunction k).unit.app F₂ ≫
            (pushforward k).map u₂) =
        (pushforward f).map ((restrictAdjunction k).unit.app F₁ ≫
            (pushforward k).map u₁) ≫
          (pushforward f).map ((pushforward k).map b) := by
    calc
      _ = (pushforward f).map
          (a ≫ ((restrictAdjunction k).unit.app F₂ ≫
            (pushforward k).map u₂)) := (Functor.map_comp _ _ _).symm
      _ = (pushforward f).map
          ((restrictAdjunction k).unit.app F₁ ≫
            ((pushforward k).map u₁ ≫ (pushforward k).map b)) :=
        congrArg (fun z => (pushforward f).map z) hlocal
      _ = _ := by rw [← Category.assoc, Functor.map_comp]
  unfold pushforwardRestrictionHomOfHom
  simp only [Category.assoc]
  have hstep :
      (pushforward f).map a ≫
          (pushforward f).map ((restrictAdjunction k).unit.app F₂ ≫
            (pushforward k).map u₂) ≫
          (pushforwardComp k f).hom.app G₂ ≫
          (pushforwardCongr rfl).hom.app G₂ =
        (pushforward f).map ((restrictAdjunction k).unit.app F₁ ≫
            (pushforward k).map u₁) ≫
          (pushforward f).map ((pushforward k).map b) ≫
          (pushforwardComp k f).hom.app G₂ ≫
          (pushforwardCongr rfl).hom.app G₂ := by
    simpa only [Category.assoc] using congrArg
      (fun z => z ≫ (pushforwardComp k f).hom.app G₂ ≫
        (pushforwardCongr rfl).hom.app G₂) hfront
  have htail :
      (pushforward f).map ((pushforward k).map b) ≫
          (pushforwardComp k f).hom.app G₂ ≫
          (pushforwardCongr rfl).hom.app G₂ =
        (pushforwardComp k f).hom.app G₁ ≫
          (pushforwardCongr rfl).hom.app G₁ ≫
          (pushforward (k ≫ f)).map b := by
    calc
      _ = (pushforwardComp k f).hom.app G₁ ≫
          (pushforward (k ≫ f)).map b ≫
          (pushforwardCongr rfl).hom.app G₂ :=
        (pushforwardComp k f).hom.naturality_assoc
          b
          ((pushforwardCongr rfl).hom.app G₂)
      _ = _ := by
        rw [(pushforwardCongr rfl).hom.naturality]
  calc
    _ = (pushforward f).map ((restrictAdjunction k).unit.app F₁ ≫
          (pushforward k).map u₁) ≫
        ((pushforward f).map ((pushforward k).map b) ≫
          (pushforwardComp k f).hom.app G₂ ≫
          (pushforwardCongr rfl).hom.app G₂) := hstep
    _ = _ := by rw [htail]

/-- Pull a coefficient comparison through the inner cartesian square in a
vertically pasted pair of open squares.  The comparison first identifies the
two iterated restrictions and then restricts the original morphism. -/
def pullbackRestrictionHom (Hk : IsPullback r q k b)
    (F : X.Modules) (G : V.Modules)
    (e : (restrictFunctor k).obj F ⟶ G) :
    (restrictFunctor q).obj ((restrictFunctor b).obj F) ⟶
      (restrictFunctor r).obj G :=
  (restrictFunctorComp q b).inv.app F ≫
    (restrictFunctorCongr Hk.w.symm).hom.app F ≫
    (restrictFunctorComp r k).hom.app F ≫
    (restrictFunctor r).map e

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a composite coefficient morphism through a cartesian open
square is the pulled-back first morphism followed by the restricted second
morphism. -/
theorem pullbackRestrictionHom_comp (Hk : IsPullback r q k b)
    (F : X.Modules) (G K : V.Modules)
    (e : (restrictFunctor k).obj F ⟶ G) (u : G ⟶ K) :
    pullbackRestrictionHom r q k b Hk F K (e ≫ u) =
      pullbackRestrictionHom r q k b Hk F G e ≫
        (restrictFunctor r).map u := by
  unfold pullbackRestrictionHom
  rw [Functor.map_comp]
  rfl

set_option maxHeartbeats 800000 in
-- Sectionwise normalization exposes several nested pseudofunctorial maps.
set_option backward.isDefEq.respectTransparency false in
/-- Open base change carries extension by zero from a smaller open to
extension by zero from its pullback.  This is the vertical-pasting coherence
law for the explicit Beck--Chevalley isomorphism above.

The proof is sectionwise.  After removing the pseudofunctorial identity maps,
the only nontrivial step is naturality of `e`; all remaining maps between open
subsets agree because the category of opens is thin. -/
theorem openBaseChange_pushforwardRestrictionHomOfHom
    (hk : k ≫ f = h) (Hk : IsPullback r q k b)
    (Hf : IsPullback a b iU f)
    (Ht : IsPullback (q ≫ a) r iU h)
    (F : X.Modules) (G : V.Modules)
    (e : (restrictFunctor k).obj F ⟶ G) :
    (openBaseChangeIso a b iU f Hf F).inv ≫
        (restrictFunctor iU).map
          (pushforwardRestrictionHomOfHom
            (f := f) (k := k) (h := h) hk F G e) ≫
        (openBaseChangeIso (q ≫ a) r iU h Ht G).hom =
      pushforwardRestrictionHomOfHom
        (f := a) (k := q) (h := q ≫ a) rfl
        ((restrictFunctor b).obj F) ((restrictFunctor r).obj G)
        (pullbackRestrictionHom
          (r := r) (q := q) (k := k) (b := b) Hk F G e) := by
  apply hom_ext
  intro W
  dsimp [pushforwardRestrictionHomOfHom, pullbackRestrictionHom]
  simp only [openBaseChangeIso_hom, openBaseChangeHom_app,
    openBaseChangeIso_inv_app, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [restrict_map]
  have hOuter : b ''ᵁ a ⁻¹ᵁ W = f ⁻¹ᵁ iU ''ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback Hf W
  have hMiddle : r ''ᵁ q ⁻¹ᵁ a ⁻¹ᵁ W =
      k ⁻¹ᵁ f ⁻¹ᵁ iU ''ᵁ W := by
    rw [IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      Hk.flip (a ⁻¹ᵁ W), hOuter]
  let t : r ''ᵁ q ⁻¹ᵁ a ⁻¹ᵁ W ⟶
      k ⁻¹ᵁ f ⁻¹ᵁ iU ''ᵁ W := eqToHom hMiddle
  -- Combine the restriction maps contributed by base change and by the
  -- pseudofunctorial comparison before invoking naturality.
  slice_lhs 1 2 => rw [← Functor.map_comp]
  slice_rhs 1 4 =>
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  slice_lhs 2 3 => erw [Category.comp_id]
  slice_lhs 3 4 => rw [← G.presheaf.map_comp]
  slice_rhs 2 3 => erw [Category.comp_id]
  rw [((restrictFunctor r).obj G).presheaf.map_id]
  slice_rhs 2 3 => erw [Category.comp_id]
  let s : k ''ᵁ (k ⁻¹ᵁ f ⁻¹ᵁ iU ''ᵁ W) ⟶
      b ''ᵁ a ⁻¹ᵁ W :=
    homOfLE (by
      rw [hOuter]
      exact k.image_preimage_le (f ⁻¹ᵁ iU ''ᵁ W))
  calc
    _ = F.presheaf.map s.op ≫
          e.app (k ⁻¹ᵁ f ⁻¹ᵁ iU ''ᵁ W) ≫
          G.presheaf.map t.op := by
      congr 1
    _ = F.presheaf.map s.op ≫
          ((restrictFunctor k).obj F).presheaf.map t.op ≫
          e.app (r ''ᵁ q ⁻¹ᵁ a ⁻¹ᵁ W) := by
      congr 1
      exact (e.mapPresheaf.naturality t.op).symm
    _ = F.presheaf.map
          (s.op ≫ ((k.opensFunctor).map t).op) ≫
          e.app (r ''ᵁ q ⁻¹ᵁ a ⁻¹ᵁ W) := by
      rw [restrict_map]
      slice_lhs 1 2 => rw [← F.presheaf.map_comp]
    _ = _ := by
      congr 1

/-- Version of `openBaseChange_pushforwardRestrictionHomOfHom` in which the
map from the pulled-back smaller open to the base chart has a chosen name.
This is useful when two factorizations of a triple intersection define the
same geometric open immersion but are not definitionally equal. -/
theorem openBaseChange_pushforwardRestrictionHomOfHom_congr
    (g : Q ⟶ U) [IsOpenImmersion g]
    (hk : k ≫ f = h) (hq : q ≫ a = g)
    (Hk : IsPullback r q k b) (Hf : IsPullback a b iU f)
    (Ht : IsPullback g r iU h)
    (F : X.Modules) (G : V.Modules)
    (e : (restrictFunctor k).obj F ⟶ G) :
    (openBaseChangeIso a b iU f Hf F).inv ≫
        (restrictFunctor iU).map
          (pushforwardRestrictionHomOfHom
            (f := f) (k := k) (h := h) hk F G e) ≫
        (openBaseChangeIso g r iU h Ht G).hom =
      pushforwardRestrictionHomOfHom
        (f := a) (k := q) (h := g) hq
        ((restrictFunctor b).obj F) ((restrictFunctor r).obj G)
        (pullbackRestrictionHom
          (r := r) (q := q) (k := k) (b := b) Hk F G e) := by
  subst g
  simpa only using
    openBaseChange_pushforwardRestrictionHomOfHom
      (r := r) (q := q) (k := k) (b := b) (a := a)
      (iU := iU) (f := f) (h := h) hk Hk Hf Ht F G e

/-! ## Composition of extension by zero

Two successive coefficient restrictions through open immersions determine one
restriction morphism on the smallest open.  Under the restriction--pushforward
adjunction, this composite is exactly the transpose of the two corresponding
extension-by-zero morphisms.  This comparison lets Čech descent calculations
return from pushforwards on an ambient chart to coefficient maps on a multiple
intersection, where cocycle identities live.
-/

variable {Q P U : Scheme} (q : Q ⟶ P) (a : P ⟶ U) (g : Q ⟶ U)
  [IsOpenImmersion q] [IsOpenImmersion a] [IsOpenImmersion g]

/-- The coefficient morphism obtained by restricting successively through
`P ⊆ U` and `Q ⊆ P`.  The equality `hq` identifies their composite with the
chosen geometric name `g : Q ⟶ U`, so the result can be compared across
different factorizations of the same multiple intersection. -/
def iteratedRestrictionHom (hq : q ≫ a = g)
    (F : U.Modules) (H : P.Modules) (K : Q.Modules)
    (e₁ : (restrictFunctor a).obj F ⟶ H)
    (e₂ : (restrictFunctor q).obj H ⟶ K) :
    (restrictFunctor g).obj F ⟶ K :=
  (restrictFunctorCongr hq).inv.app F ≫
    (restrictFunctorComp q a).hom.app F ≫
    (restrictFunctor q).map e₁ ≫ e₂

/-- Postcomposition on the smallest open commutes with the construction of
an iterated restriction map. -/
theorem iteratedRestrictionHom_comp (hq : q ≫ a = g)
    (F : U.Modules) (H : P.Modules) (K L : Q.Modules)
    (e₁ : (restrictFunctor a).obj F ⟶ H)
    (e₂ : (restrictFunctor q).obj H ⟶ K) (u : K ⟶ L) :
    iteratedRestrictionHom q a g hq F H L e₁ (e₂ ≫ u) =
      iteratedRestrictionHom q a g hq F H K e₁ e₂ ≫ u := by
  unfold iteratedRestrictionHom
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- An intermediate isomorphism followed by its restricted inverse data
cancels inside an iterated restriction.  This is the categorical step that
removes a chart trivialization after two adjacent descent legs are pasted. -/
theorem iteratedRestrictionHom_cancel_iso (hq : q ≫ a = g)
    (F : U.Modules) (H H' : P.Modules) (K : Q.Modules)
    (e₁ : (restrictFunctor a).obj F ⟶ H)
    (e : H' ≅ H) (e₂ : (restrictFunctor q).obj H ⟶ K) :
    iteratedRestrictionHom q a g hq F H' K
        (e₁ ≫ e.inv) ((restrictFunctor q).map e.hom ≫ e₂) =
      iteratedRestrictionHom q a g hq F H K e₁ e₂ := by
  unfold iteratedRestrictionHom
  simp_rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← (restrictFunctor q).map_comp_assoc e.inv e.hom,
    Iso.inv_hom_id]
  have hmapid : (restrictFunctor q).map (𝟙 H) = 𝟙 _ :=
    (restrictFunctor q).map_id H
  rw [hmapid, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A coefficient morphism on the intermediate open may be moved from the
first leg to its restricted action on the second leg. -/
theorem iteratedRestrictionHom_middle_comp (hq : q ≫ a = g)
    (F : U.Modules) (H H' : P.Modules) (K : Q.Modules)
    (e₁ : (restrictFunctor a).obj F ⟶ H)
    (u : H ⟶ H') (e₂ : (restrictFunctor q).obj H' ⟶ K) :
    iteratedRestrictionHom q a g hq F H' K (e₁ ≫ u) e₂ =
      iteratedRestrictionHom q a g hq F H K e₁
        ((restrictFunctor q).map u ≫ e₂) := by
  unfold iteratedRestrictionHom
  simp_rw [Functor.map_comp]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The restriction morphism between two chosen trivializations of the unit
module.  Naming this composite prevents pseudofunctoriality proofs from
re-expanding all three factors at each use site. -/
def unitRestrictionHom (F : U.Modules) (H : P.Modules)
    (eF : F ≅ SheafOfModules.unit U.ringCatSheaf)
    (eH : H ≅ SheafOfModules.unit P.ringCatSheaf) :
    (restrictFunctor a).obj F ⟶ H :=
  (restrictFunctor a).map eF.hom ≫
    (restrictUnitIso a).hom ≫ eH.inv

/-- Reversing an equality of open immersions turns the forward restriction
comparison into the inverse comparison. -/
theorem restrictFunctorCongr_symm_hom_app_eq_inv
    {f g : Q ⟶ U} (hfg : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] (F : U.Modules) :
    (restrictFunctorCongr hfg.symm).hom.app F =
      (restrictFunctorCongr hfg).inv.app F := by
  apply hom_ext
  intro W
  simp only [restrictFunctorCongr_hom_app_app,
    restrictFunctorCongr_inv_app_app]

/-- The restriction comparison attached to a reflexive equality is the
identity comparison. -/
theorem restrictFunctorCongr_refl_inv_app
    (f : Q ⟶ U) [IsOpenImmersion f] (F : U.Modules) :
    (restrictFunctorCongr (rfl : f = f)).inv.app F = 𝟙 _ := by
  apply hom_ext
  intro W
  rw [restrictFunctorCongr_inv_app_app, Hom.id_app]
  change F.presheaf.map _ = 𝟙 (F.presheaf.obj (Opposite.op (f ''ᵁ W)))
  rw [← F.presheaf.map_id]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Successive canonical trivializations of the restricted unit module agree
with the canonical trivialization for the composite open immersion.  The proof
is the sectionwise composition law for the structure-sheaf isomorphisms of
open immersions; thinness of the category of opens removes the bookkeeping
equalities introduced by the restriction pseudofunctor. -/
theorem restrictUnitIso_comp (hq : q ≫ a = g) :
    iteratedRestrictionHom q a g hq
        (SheafOfModules.unit U.ringCatSheaf)
        (SheafOfModules.unit P.ringCatSheaf)
        (SheafOfModules.unit Q.ringCatSheaf)
        (restrictUnitIso a).hom (restrictUnitIso q).hom =
      (restrictUnitIso g).hom := by
  subst g
  apply hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro x
  unfold iteratedRestrictionHom
  simp only [Hom.comp_app, restrictFunctorCongr_inv_app_app,
    restrictFunctorComp_hom_app_app, restrictFunctor_map_app]
  conv_rhs => erw [restrictUnitIso_hom_app_apply]
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.comp_apply]
  conv_lhs => erw [restrictUnitIso_hom_app_apply]
  rw [(ConcreteCategory.bijective_of_isIso
    (q.appIso W).hom).injective.eq_iff]
  erw [restrictUnitIso_hom_app_apply]
  rw [(ConcreteCategory.bijective_of_isIso
    (a.appIso (q ''ᵁ W)).hom).injective.eq_iff]
  rw [← CategoryTheory.comp_apply]
  erw [← (Scheme.Modules.presheaf
    (SheafOfModules.unit U.ringCatSheaf)).map_comp]
  dsimp only [Scheme.Modules.presheaf, SheafOfModules.unit,
    PresheafOfModules.unit]
  convert rfl using 1
  all_goals first
    | apply Subsingleton.elim
    | change (U.presheaf.map _).hom x = (U.presheaf.map _).hom x
      congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Iterated restriction is invariant under replacing its three coefficient
modules by chosen trivializations of the unit module.  Naturality moves the
ambient trivialization through the restriction pseudofunctor, the intermediate
trivialization cancels with its inverse, and `restrictUnitIso_comp` identifies
the remaining canonical unit maps.  This packages the bookkeeping surrounding
a transition map without hiding that transition's mathematical content. -/
theorem iteratedRestrictionHom_of_unit (hq : q ≫ a = g)
    (F : U.Modules) (H : P.Modules) (K : Q.Modules)
    (eF : F ≅ SheafOfModules.unit U.ringCatSheaf)
    (eH : H ≅ SheafOfModules.unit P.ringCatSheaf)
    (eK : K ≅ SheafOfModules.unit Q.ringCatSheaf) :
    iteratedRestrictionHom q a g hq F H K
        ((restrictFunctor a).map eF.hom ≫
          (restrictUnitIso a).hom ≫ eH.inv)
        ((restrictFunctor q).map eH.hom ≫
          (restrictUnitIso q).hom ≫ eK.inv) =
      (restrictFunctor g).map eF.hom ≫
        (restrictUnitIso g).hom ≫ eK.inv := by
  unfold iteratedRestrictionHom
  simp_rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← (restrictFunctor q).map_comp_assoc eH.inv eH.hom,
    Iso.inv_hom_id]
  have hmapid : (restrictFunctor q).map
      (𝟙 (SheafOfModules.unit P.ringCatSheaf)) = 𝟙 _ :=
    (restrictFunctor q).map_id _
  rw [hmapid, Category.id_comp]
  have hcompNat :
      (restrictFunctorComp q a).hom.app F ≫
          (restrictFunctor q).map ((restrictFunctor a).map eF.hom) =
        (restrictFunctor (q ≫ a)).map eF.hom ≫
          (restrictFunctorComp q a).hom.app
            (SheafOfModules.unit U.ringCatSheaf) :=
    ((restrictFunctorComp q a).hom.naturality eF.hom).symm
  have hcongrNat :
      (restrictFunctorCongr hq).inv.app F ≫
          (restrictFunctor (q ≫ a)).map eF.hom =
        (restrictFunctor g).map eF.hom ≫
          (restrictFunctorCongr hq).inv.app
            (SheafOfModules.unit U.ringCatSheaf) :=
    ((restrictFunctorCongr hq).inv.naturality eF.hom).symm
  slice_lhs 2 3 =>
    rw [hcompNat]
  slice_lhs 1 2 =>
    rw [hcongrNat]
  have hunit :
      (restrictFunctorCongr hq).inv.app
            (SheafOfModules.unit U.ringCatSheaf) ≫
          (restrictFunctorComp q a).hom.app
            (SheafOfModules.unit U.ringCatSheaf) ≫
          (restrictFunctor q).map (restrictUnitIso a).hom ≫
          (restrictUnitIso q).hom =
        (restrictUnitIso g).hom := by
    simpa only [iteratedRestrictionHom] using restrictUnitIso_comp q a g hq
  slice_lhs 2 5 => rw [hunit]

set_option backward.isDefEq.respectTransparency false in
/-- Canonical unit trivializations commute around a cartesian square of open
immersions.  After cancelling the comparison for the upper composite, both
routes are iterated restrictions of the same ambient unit module, so
`iteratedRestrictionHom_of_unit` identifies each with the canonical map for
the common composite open. -/
theorem pullbackRestrictionHom_of_unit
    {V X : Scheme} (r : Q ⟶ V) (q : Q ⟶ P)
    (k : V ⟶ X) (b : P ⟶ X)
    [IsOpenImmersion r] [IsOpenImmersion q]
    [IsOpenImmersion k] [IsOpenImmersion b]
    (Hsq : IsPullback r q k b)
    (F : X.Modules) (G : V.Modules) (H : P.Modules) (K : Q.Modules)
    (eF : F ≅ SheafOfModules.unit X.ringCatSheaf)
    (eG : G ≅ SheafOfModules.unit V.ringCatSheaf)
    (eH : H ≅ SheafOfModules.unit P.ringCatSheaf)
    (eK : K ≅ SheafOfModules.unit Q.ringCatSheaf) :
    pullbackRestrictionHom r q k b Hsq F G
          (unitRestrictionHom k F G eF eG) ≫
        unitRestrictionHom r G K eG eK =
      (restrictFunctor q).map
          (unitRestrictionHom b F H eF eH) ≫
        unitRestrictionHom q H K eH eK := by
  rw [← cancel_epi ((restrictFunctorComp q b).hom.app F)]
  unfold pullbackRestrictionHom
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  rw [restrictFunctorCongr_symm_hom_app_eq_inv Hsq.w]
  rw [← Category.id_comp ((restrictFunctorComp q b).hom.app F)]
  rw [← restrictFunctorCongr_refl_inv_app (q ≫ b) F]
  change
    iteratedRestrictionHom r k (q ≫ b) Hsq.w F G K
        (unitRestrictionHom k F G eF eG)
        (unitRestrictionHom r G K eG eK) =
      iteratedRestrictionHom q b (q ≫ b) rfl F H K
        (unitRestrictionHom b F H eF eH)
        (unitRestrictionHom q H K eH eK)
  calc
    _ = (restrictFunctor (q ≫ b)).map eF.hom ≫
          (restrictUnitIso (q ≫ b)).hom ≫ eK.inv := by
      simpa only [unitRestrictionHom] using
        (iteratedRestrictionHom_of_unit
          r k (q ≫ b) Hsq.w F G K eF eG eK)
    _ = _ := by
      symm
      simpa only [unitRestrictionHom] using
        (iteratedRestrictionHom_of_unit
          q b (q ≫ b) rfl F H K eF eH eK)

set_option maxHeartbeats 800000 in
-- The mate calculation normalizes both adjunctions on every open subset.
set_option backward.isDefEq.respectTransparency false in
/-- Taking the adjoint of two successive extension-by-zero maps recovers the
successive restriction morphism on the smallest open.  Sectionwise, the proof
uses naturality of the two coefficient maps; every remaining comparison is an
equality between inclusions of open subsets.  This is the mate identity needed
to turn a pasted base-change calculation into a Čech cocycle calculation. -/
theorem pushforwardRestrictionHomOfHom_transpose
    (hq : q ≫ a = g)
    (F : U.Modules) (H : P.Modules) (K : Q.Modules)
    (e₁ : (restrictFunctor a).obj F ⟶ H)
    (e₂ : (restrictFunctor q).obj H ⟶ K) :
    ((restrictAdjunction g).homEquiv F K).symm
        ((restrictAdjunction a).unit.app F ≫
          (pushforward a).map e₁ ≫
          pushforwardRestrictionHomOfHom
            (f := a) (k := q) (h := g) hq H K e₂) =
      iteratedRestrictionHom q a g hq F H K e₁ e₂ := by
  subst g
  rw [Adjunction.homEquiv_counit]
  apply hom_ext
  intro W
  dsimp [pushforwardRestrictionHomOfHom, iteratedRestrictionHom]
  slice_lhs 4 5 => erw [Category.comp_id]
  slice_lhs 5 6 => rw [← K.presheaf.map_comp]
  slice_rhs 1 2 => rw [← F.presheaf.map_comp]
  have hQ : q ⁻¹ᵁ a ⁻¹ᵁ (q ≫ a) ''ᵁ W = W := by
    simpa only [Scheme.Hom.comp_preimage] using
      (q ≫ a).preimage_image_eq W
  have hP : a ⁻¹ᵁ (q ≫ a) ''ᵁ W = q ''ᵁ W := by
    calc
      a ⁻¹ᵁ (q ≫ a) ''ᵁ W = a ⁻¹ᵁ a ''ᵁ q ''ᵁ W := by
        rw [Scheme.Hom.comp_image]
      _ = q ''ᵁ W := a.preimage_image_eq (q ''ᵁ W)
  let tP : q ''ᵁ W ⟶ a ⁻¹ᵁ (q ≫ a) ''ᵁ W := eqToHom hP.symm
  let tQ : q ⁻¹ᵁ a ⁻¹ᵁ (q ≫ a) ''ᵁ W ⟶ W := eqToHom hQ
  let tQi : W ⟶ q ⁻¹ᵁ a ⁻¹ᵁ (q ≫ a) ''ᵁ W := eqToHom hQ.symm
  let s : a ''ᵁ (a ⁻¹ᵁ (q ≫ a) ''ᵁ W) ⟶ (q ≫ a) ''ᵁ W :=
    homOfLE (a.image_preimage_le ((q ≫ a) ''ᵁ W))
  have hK : K.presheaf.map tQ.op ≫ K.presheaf.map tQi.op = 𝟙 _ := by
    rw [← K.presheaf.map_comp]
    have ht : tQ.op ≫ tQi.op = 𝟙 _ := Subsingleton.elim _ _
    rw [ht, K.presheaf.map_id]
  calc
    _ = F.presheaf.map s.op ≫
          e₁.app (a ⁻¹ᵁ (q ≫ a) ''ᵁ W) ≫
          H.presheaf.map
            (tP.op ≫ ((q.opensFunctor).map tQ).op) ≫
          e₂.app (q ⁻¹ᵁ a ⁻¹ᵁ (q ≫ a) ''ᵁ W) ≫
          K.presheaf.map tQi.op := by
      congr 5
    _ = F.presheaf.map s.op ≫
          e₁.app (a ⁻¹ᵁ (q ≫ a) ''ᵁ W) ≫
          H.presheaf.map tP.op ≫
          (((restrictFunctor q).obj H).presheaf.map tQ.op ≫
            e₂.app (q ⁻¹ᵁ a ⁻¹ᵁ (q ≫ a) ''ᵁ W)) ≫
          K.presheaf.map tQi.op := by
      rw [H.presheaf.map_comp, ← restrict_map H q tQ]
      simp only [Category.assoc]
    _ = F.presheaf.map s.op ≫
          e₁.app (a ⁻¹ᵁ (q ≫ a) ''ᵁ W) ≫
          H.presheaf.map tP.op ≫
          (e₂.app W ≫ K.presheaf.map tQ.op) ≫
          K.presheaf.map tQi.op := by
      simpa only [Category.assoc, mapPresheaf_app] using congrArg
        (fun z => F.presheaf.map s.op ≫
          e₁.app (a ⁻¹ᵁ (q ≫ a) ''ᵁ W) ≫
          H.presheaf.map tP.op ≫ z ≫ K.presheaf.map tQi.op)
        (e₂.mapPresheaf.naturality tQ.op)
    _ = F.presheaf.map s.op ≫
          e₁.app (a ⁻¹ᵁ (q ≫ a) ''ᵁ W) ≫
          H.presheaf.map tP.op ≫ e₂.app W := by
      rw [Category.assoc, hK, Category.comp_id]
    _ = F.presheaf.map s.op ≫
          (((restrictFunctor a).obj F).presheaf.map tP.op ≫
            e₁.app (q ''ᵁ W)) ≫ e₂.app W := by
      simpa only [Category.assoc, mapPresheaf_app] using congrArg
        (fun z => F.presheaf.map s.op ≫ z ≫ e₂.app W)
        (e₁.mapPresheaf.naturality tP.op).symm
    _ = F.presheaf.map
          (s.op ≫ ((a.opensFunctor).map tP).op) ≫
          e₁.app (q ''ᵁ W) ≫ e₂.app W := by
      rw [restrict_map]
      slice_lhs 1 2 => rw [← F.presheaf.map_comp]
      rw [Category.assoc]
    _ = _ := by
      apply congrArg (fun z => z ≫ e₁.app (q ''ᵁ W) ≫ e₂.app W)
      congr 1

/-- Naturality of the mate identity with respect to a further coefficient
morphism on the smallest open.  It allows a Čech transition isomorphism to
remain attached while the two extension-by-zero maps are transposed back to
their iterated restriction. -/
theorem pushforwardRestrictionHomOfHom_transpose_comp
    (hq : q ≫ a = g)
    (F : U.Modules) (H : P.Modules) (K L : Q.Modules)
    (e₁ : (restrictFunctor a).obj F ⟶ H)
    (e₂ : (restrictFunctor q).obj H ⟶ K)
    (u : K ⟶ L) :
    ((restrictAdjunction g).homEquiv F L).symm
        (((restrictAdjunction a).unit.app F ≫
          (pushforward a).map e₁ ≫
          pushforwardRestrictionHomOfHom
            (f := a) (k := q) (h := g) hq H K e₂) ≫
          (pushforward g).map u) =
      iteratedRestrictionHom q a g hq F H K e₁ e₂ ≫ u := by
  rw [Adjunction.homEquiv_naturality_right_symm,
    pushforwardRestrictionHomOfHom_transpose]

/-! ## Limits under restriction

Restriction along an open immersion is computed by evaluating the original
sheaf on image opens and then restricting scalars along the structure-sheaf
isomorphism.  Both operations preserve limits.  Consequently restriction
preserves every limit available in the module-sheaf category, including the
products and equalizers occurring in a Čech construction.
-/

/-- Restriction of module sheaves along an open immersion preserves limits.
The proof reflects a proposed limit through the fully faithful forgetful
functor and checks it on every open subset, where it becomes evaluation
followed by restriction of scalars. -/
noncomputable instance restrictFunctorPreservesLimit {J : Type} [Category J]
    (K : J ⥤ Y.Modules) [HasLimit K] :
    PreservesLimit K (restrictFunctor f) := by
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  apply isLimitOfReflects (SheafOfModules.forget X.ringCatSheaf)
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  change IsLimit
    ((ModuleCat.restrictScalars (f.appIso V.unop).inv.hom).mapCone
      ((SheafOfModules.evaluation Y.ringCatSheaf
        (.op (f ''ᵁ V.unop))).mapCone (limit.cone K)))
  exact isLimitOfPreserves
    (ModuleCat.restrictScalars (f.appIso V.unop).inv.hom)
    (isLimitOfPreserves
      (SheafOfModules.evaluation Y.ringCatSheaf
        (.op (f ''ᵁ V.unop))) (limit.isLimit K))

end AlgebraicGeometry.Scheme.Modules
