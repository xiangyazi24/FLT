import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingDescent
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Čech gluing of the N25 twisting module sheaf

The categorical pair pullbacks have already been identified with the affine
homogeneous localizations carrying the coordinate-ratio transitions.  This
file uses those identifications to form an honest global module sheaf on the
canonical projective curve.

For the four-chart cover, the global candidate is the standard Čech
equalizer

`Eq (∏ᵢ jᵢ_* Fᵢ ⇉ ∏ᵢⱼ jᵢⱼ_* Fᵢⱼ)`.

The two arrows restrict a local section to a pair overlap.  The left arrow
then applies the transition from chart `i` to chart `j`, while the right
arrow uses the chart-`j` trivialization directly.  Products and equalizers
are taken inside the category of module sheaves, so the result is already a
sheaf; no sheafification or unproved descent axiom is introduced.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoTwistingSheafGluing

open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoTwistingTransition
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingDescent
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

/-! ## Actual morphisms from affine pair overlaps -/

/-- The explicit affine pair overlap mapped to its first coordinate chart. -/
def coordinateOverlapToLeft (i j : Fin 4) :
    Spec (.of (coordinateOverlapRing i j)) ⟶ coordinateChartScheme i :=
  (coordinateChosenPullbackIso i j).inv ≫
    (coordinateChosenPullback i j).p₁

/-- The explicit affine pair overlap mapped to its second coordinate chart. -/
def coordinateOverlapToRight (i j : Fin 4) :
    Spec (.of (coordinateOverlapRing i j)) ⟶ coordinateChartScheme j :=
  (coordinateChosenPullbackIso i j).inv ≫
    (coordinateChosenPullback i j).p₂

/-- The first overlap projection is an open immersion. -/
instance coordinateOverlapToLeftIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (coordinateOverlapToLeft i j) := by
  dsimp [coordinateOverlapToLeft]
  infer_instance

/-- The second overlap projection is an open immersion. -/
instance coordinateOverlapToRightIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (coordinateOverlapToRight i j) := by
  dsimp [coordinateOverlapToRight]
  infer_instance

/-- The pair overlap as an open subscheme of the canonical projective curve,
using its first projection. -/
def coordinateOverlapMap (i j : Fin 4) :
    Spec (.of (coordinateOverlapRing i j)) ⟶
      CanonicalProjectiveCurve25Two :=
  coordinateOverlapToLeft i j ≫ coordinateChartMap i

/-- The two routes from a pair overlap to the projective curve agree. -/
theorem coordinateOverlapMap_eq_right (i j : Fin 4) :
    coordinateOverlapToRight i j ≫ coordinateChartMap j =
      coordinateOverlapMap i j := by
  dsimp [coordinateOverlapToLeft, coordinateOverlapToRight,
    coordinateOverlapMap]
  simp only [Category.assoc]
  rw [(coordinateChosenPullback i j).condition]

/-! ## Restriction of local twists to pair overlaps -/

/-- Restricting the local twist from the first chart gives the explicit
free rank-one overlap sheaf. -/
def coordinateRestrictLeftIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).obj
        (coordinateLocalTwistModule d i) ≅
      coordinateOverlapTwistModule d i j :=
  (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).mapIso
      (coordinateLocalTwistUnitIso d i) ≪≫
    Scheme.Modules.restrictUnitIso (coordinateOverlapToLeft i j) ≪≫
    (coordinateOverlapTwistUnitIso d i j).symm

/-- Restricting the local twist from the second chart gives the same explicit
free rank-one overlap sheaf. -/
def coordinateRestrictRightIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).obj
        (coordinateLocalTwistModule d j) ≅
      coordinateOverlapTwistModule d i j :=
  (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).mapIso
      (coordinateLocalTwistUnitIso d j) ≪≫
    Scheme.Modules.restrictUnitIso (coordinateOverlapToRight i j) ≪≫
    (coordinateOverlapTwistUnitIso d i j).symm

/-- The coordinate-ratio transition as an isomorphism between restrictions
of the two actual local chart sheaves to their categorical intersection. -/
def coordinateDescentIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateOverlapToLeft i j)).obj
        (coordinateLocalTwistModule d i) ≅
      (Scheme.Modules.restrictFunctor (coordinateOverlapToRight i j)).obj
        (coordinateLocalTwistModule d j) :=
  coordinateRestrictLeftIso d i j ≪≫
    coordinateOverlapTwistIso d i j ≪≫
    (coordinateRestrictRightIso d i j).symm

/-! ## Restriction from pair overlaps to triple overlaps -/

/-- Restrict the `(i,j)` affine overlap to the ordered triple overlap
`(i,j,l)`. -/
def coordinateTripleTo12 (i j l : Fin 4) :
    Spec (.of (coordinateTripleOverlapRing i j l)) ⟶
      Spec (.of (coordinateOverlapRing i j)) :=
  Spec.map (CommRingCat.ofHom
    (Away.restrict12 literalConePiece (coordinateClass_mem_degreeOne l)))

/-- Restrict the `(j,l)` affine overlap to the same ordered triple overlap. -/
def coordinateTripleTo23 (i j l : Fin 4) :
    Spec (.of (coordinateTripleOverlapRing i j l)) ⟶
      Spec (.of (coordinateOverlapRing j l)) :=
  Spec.map (CommRingCat.ofHom
    (Away.restrict23 literalConePiece (coordinateClass_mem_degreeOne i)))

/-- Restrict the `(i,l)` affine overlap to the same ordered triple overlap. -/
def coordinateTripleTo13 (i j l : Fin 4) :
    Spec (.of (coordinateTripleOverlapRing i j l)) ⟶
      Spec (.of (coordinateOverlapRing i l)) :=
  Spec.map (CommRingCat.ofHom
    (Away.restrict13 literalConePiece (coordinateClass_mem_degreeOne j)))

/-- The first pair-to-triple localization is an open immersion. -/
instance coordinateTripleTo12IsOpenImmersion (i j l : Fin 4) :
    IsOpenImmersion (coordinateTripleTo12 i j l) := by
  letI := (Away.restrict12 literalConePiece
    (f := coordinateClass i) (g := coordinateClass j) (h := coordinateClass l)
    (coordinateClass_mem_degreeOne l)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j))
        (coordinateClass_mem_degreeOne l))
      (coordinateTripleOverlapRing i j l) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
      (coordinateClass_mem_degreeOne l) rfl (by norm_num)
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  exact IsOpenImmersion.of_isLocalization
    (Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
      (coordinateClass_mem_degreeOne l) : coordinateOverlapRing i j)

/-- The second pair-to-triple localization is an open immersion. -/
instance coordinateTripleTo23IsOpenImmersion (i j l : Fin 4) :
    IsOpenImmersion (coordinateTripleTo23 i j l) := by
  letI := (Away.restrict23 literalConePiece
    (f := coordinateClass i) (g := coordinateClass j) (h := coordinateClass l)
    (coordinateClass_mem_degreeOne i)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne j)
          (coordinateClass_mem_degreeOne l))
        (coordinateClass_mem_degreeOne i))
      (coordinateTripleOverlapRing i j l) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l))
      (coordinateClass_mem_degreeOne i) (by ring) (by norm_num)
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  exact IsOpenImmersion.of_isLocalization
    (Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne j)
        (coordinateClass_mem_degreeOne l))
      (coordinateClass_mem_degreeOne i) : coordinateOverlapRing j l)

/-- The direct first-to-third pair localization is an open immersion. -/
instance coordinateTripleTo13IsOpenImmersion (i j l : Fin 4) :
    IsOpenImmersion (coordinateTripleTo13 i j l) := by
  letI := (Away.restrict13 literalConePiece
    (f := coordinateClass i) (g := coordinateClass j) (h := coordinateClass l)
    (coordinateClass_mem_degreeOne j)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne l))
        (coordinateClass_mem_degreeOne j))
      (coordinateTripleOverlapRing i j l) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne l))
      (coordinateClass_mem_degreeOne j) (by ring) (by norm_num)
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  exact IsOpenImmersion.of_isLocalization
    (Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne l))
      (coordinateClass_mem_degreeOne j) : coordinateOverlapRing i l)

/-- Restricting the `(i,j)` overlap's free rank-one sheaf gives the free
rank-one sheaf on the ordered triple overlap. -/
def coordinatePairToTripleIso12 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateTripleTo12 i j l)).obj
        (coordinateOverlapTwistModule d i j) ≅
      coordinateTripleTwistModule d i j l :=
  Scheme.Modules.restrictUnitIso (coordinateTripleTo12 i j l)

/-- Restricting the `(j,l)` overlap's free rank-one sheaf gives the same
triple-overlap sheaf. -/
def coordinatePairToTripleIso23 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateTripleTo23 i j l)).obj
        (coordinateOverlapTwistModule d j l) ≅
      coordinateTripleTwistModule d i j l :=
  Scheme.Modules.restrictUnitIso (coordinateTripleTo23 i j l)

/-- Restricting the `(i,l)` overlap's free rank-one sheaf gives the same
triple-overlap sheaf. -/
def coordinatePairToTripleIso13 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateTripleTo13 i j l)).obj
        (coordinateOverlapTwistModule d i l) ≅
      coordinateTripleTwistModule d i j l :=
  Scheme.Modules.restrictUnitIso (coordinateTripleTo13 i j l)

set_option maxHeartbeats 800000 in
-- Unfolding the three nested homogeneous localizations is expensive even
-- though the proof is a direct application of the generic affine lemma.
/-- Transporting the `(i,j)` transition through restriction to `(i,j,l)`
gives the first explicit triple-overlap transition. -/
theorem coordinateOverlapTwistIso_restrict12 (d : ℤ) (i j l : Fin 4) :
    (coordinatePairToTripleIso12 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (coordinateTripleTo12 i j l)).map
          (coordinateOverlapTwistIso d i j).hom ≫
        (coordinatePairToTripleIso12 d i j l).hom =
      (coordinateTripleTwistIso12 d i j l).hom := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Away.restrict12 literalConePiece
          (coordinateClass_mem_degreeOne l)))) := by
    change IsOpenImmersion (coordinateTripleTo12 i j l)
    infer_instance
  dsimp [coordinatePairToTripleIso12, coordinateOverlapTwistIso,
    coordinateTripleTwistIso12, Away.ratioPowerModuleIso12,
    Away.ratioPowerTransition, Away.ratioPowerTransition12,
    coordinateTripleTo12, coordinateTripleTwistModule,
    coordinateOverlapTwistModule]
  erw [Scheme.Modules.restrictUnitIso_conjugate_tildeUnit
    (CommRingCat.ofHom
      (Away.restrict12 literalConePiece
        (coordinateClass_mem_degreeOne l)))
    ((Away.degreeOneRatioUnit literalConePiece
      (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j)) ^ d)]
  change ((AlgebraicGeometry.tilde.functor
      (.of (coordinateTripleOverlapRing i j l))).mapIso _).hom = _
  congr 1
  congr 1
  congr 1
  congr 1
  simp only [map_zpow]
  rfl

set_option maxHeartbeats 800000 in
-- Unfolding the three nested homogeneous localizations is expensive even
-- though the proof is a direct application of the generic affine lemma.
/-- Transporting the `(j,l)` transition through restriction to `(i,j,l)`
gives the second explicit triple-overlap transition. -/
theorem coordinateOverlapTwistIso_restrict23 (d : ℤ) (i j l : Fin 4) :
    (coordinatePairToTripleIso23 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (coordinateTripleTo23 i j l)).map
          (coordinateOverlapTwistIso d j l).hom ≫
        (coordinatePairToTripleIso23 d i j l).hom =
      (coordinateTripleTwistIso23 d i j l).hom := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Away.restrict23 literalConePiece
          (coordinateClass_mem_degreeOne i)))) := by
    change IsOpenImmersion (coordinateTripleTo23 i j l)
    infer_instance
  dsimp [coordinatePairToTripleIso23, coordinateOverlapTwistIso,
    coordinateTripleTwistIso23, Away.ratioPowerModuleIso23,
    Away.ratioPowerTransition, Away.ratioPowerTransition23,
    coordinateTripleTo23, coordinateTripleTwistModule,
    coordinateOverlapTwistModule]
  erw [Scheme.Modules.restrictUnitIso_conjugate_tildeUnit
    (CommRingCat.ofHom
      (Away.restrict23 literalConePiece
        (coordinateClass_mem_degreeOne i)))
    ((Away.degreeOneRatioUnit literalConePiece
      (coordinateClass_mem_degreeOne j)
      (coordinateClass_mem_degreeOne l)) ^ d)]
  change ((AlgebraicGeometry.tilde.functor
      (.of (coordinateTripleOverlapRing i j l))).mapIso _).hom = _
  congr 1
  congr 1
  congr 1
  congr 1
  simp only [map_zpow]
  rfl

set_option maxHeartbeats 800000 in
-- Unfolding the three nested homogeneous localizations is expensive even
-- though the proof is a direct application of the generic affine lemma.
/-- Transporting the direct `(i,l)` transition through restriction to
`(i,j,l)` gives the explicit first-to-third triple-overlap transition. -/
theorem coordinateOverlapTwistIso_restrict13 (d : ℤ) (i j l : Fin 4) :
    (coordinatePairToTripleIso13 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (coordinateTripleTo13 i j l)).map
          (coordinateOverlapTwistIso d i l).hom ≫
        (coordinatePairToTripleIso13 d i j l).hom =
      (coordinateTripleTwistIso13 d i j l).hom := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Away.restrict13 literalConePiece
          (coordinateClass_mem_degreeOne j)))) := by
    change IsOpenImmersion (coordinateTripleTo13 i j l)
    infer_instance
  dsimp [coordinatePairToTripleIso13, coordinateOverlapTwistIso,
    coordinateTripleTwistIso13, Away.ratioPowerModuleIso13,
    Away.ratioPowerTransition, Away.ratioPowerTransition13,
    coordinateTripleTo13, coordinateTripleTwistModule,
    coordinateOverlapTwistModule]
  erw [Scheme.Modules.restrictUnitIso_conjugate_tildeUnit
    (CommRingCat.ofHom
      (Away.restrict13 literalConePiece
        (coordinateClass_mem_degreeOne j)))
    ((Away.degreeOneRatioUnit literalConePiece
      (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne l)) ^ d)]
  change ((AlgebraicGeometry.tilde.functor
      (.of (coordinateTripleOverlapRing i j l))).mapIso _).hom = _
  congr 1
  congr 1
  congr 1
  congr 1
  simp only [map_zpow]
  rfl

/-- The three restricted pair-overlap transitions satisfy the actual Čech
cocycle on the explicit ordered triple overlap. -/
theorem coordinateRestrictedOverlapTwistIso_cocycle
    (d : ℤ) (i j l : Fin 4) :
    ((coordinatePairToTripleIso12 d i j l).inv ≫
          (Scheme.Modules.restrictFunctor (coordinateTripleTo12 i j l)).map
            (coordinateOverlapTwistIso d i j).hom ≫
          (coordinatePairToTripleIso12 d i j l).hom) ≫
        ((coordinatePairToTripleIso23 d i j l).inv ≫
          (Scheme.Modules.restrictFunctor (coordinateTripleTo23 i j l)).map
            (coordinateOverlapTwistIso d j l).hom ≫
          (coordinatePairToTripleIso23 d i j l).hom) =
      (coordinatePairToTripleIso13 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (coordinateTripleTo13 i j l)).map
          (coordinateOverlapTwistIso d i l).hom ≫
        (coordinatePairToTripleIso13 d i j l).hom := by
  rw [coordinateOverlapTwistIso_restrict12,
    coordinateOverlapTwistIso_restrict23,
    coordinateOverlapTwistIso_restrict13]
  exact coordinateTripleTwistIso_cocycle d i j l

/-! ## Pushforward maps and the Čech equalizer -/

/-- Push a restriction morphism from an open `U` to a smaller open `V`
forward to the ambient scheme `X`.  The adjunction unit restricts the local
module, the supplied isomorphism identifies that restriction with the chosen
overlap module, and functoriality rewrites the composite open immersion as
the fixed map `h : V ⟶ X`. -/
def pushforwardRestrictionHom {V U X : Scheme}
    (k : V ⟶ U) (j : U ⟶ X) (h : V ⟶ X)
    [IsOpenImmersion k] (hk : k ≫ j = h)
    (F : U.Modules) (G : V.Modules)
    (e : (Scheme.Modules.restrictFunctor k).obj F ≅ G) :
    (Scheme.Modules.pushforward j).obj F ⟶
      (Scheme.Modules.pushforward h).obj G :=
  (Scheme.Modules.pushforward j).map
      ((Scheme.Modules.restrictAdjunction k).unit.app F ≫
        (Scheme.Modules.pushforward k).map e.hom) ≫
    (Scheme.Modules.pushforwardComp k j).hom.app G ≫
    (Scheme.Modules.pushforwardCongr hk).hom.app G

/-- The local chart sheaf, extended by zero to the projective curve. -/
abbrev coordinateLocalPushforward (d : ℤ) (i : Fin 4) :
    CanonicalProjectiveCurve25Two.Modules :=
  (Scheme.Modules.pushforward (coordinateChartMap i)).obj
    (coordinateLocalTwistModule d i)

/-- The explicit pair-overlap sheaf, extended by zero to the projective
curve. -/
abbrev coordinateOverlapPushforward (d : ℤ) (p : Fin 4 × Fin 4) :
    CanonicalProjectiveCurve25Two.Modules :=
  (Scheme.Modules.pushforward (coordinateOverlapMap p.1 p.2)).obj
    (coordinateOverlapTwistModule d p.1 p.2)

/-- Product of the four local chart sheaves after extension to the whole
projective curve. -/
abbrev twistCechSource (d : ℤ) : CanonicalProjectiveCurve25Two.Modules :=
  ∏ᶜ fun i : Fin 4 ↦ coordinateLocalPushforward d i

/-- Product of the sixteen ordered pair-overlap sheaves after extension to
the whole projective curve. -/
abbrev twistCechTarget (d : ℤ) : CanonicalProjectiveCurve25Two.Modules :=
  ∏ᶜ fun p : Fin 4 × Fin 4 ↦ coordinateOverlapPushforward d p

/-- The first Čech arrow: restrict the `i`-th local section to `(i,j)` and
then apply the coordinate-ratio transition from chart `i` to chart `j`. -/
def twistCechLeft (d : ℤ) : twistCechSource d ⟶ twistCechTarget d :=
  Pi.lift fun p ↦
    Pi.π (fun i : Fin 4 ↦ coordinateLocalPushforward d i) p.1 ≫
      pushforwardRestrictionHom
        (coordinateOverlapToLeft p.1 p.2)
        (coordinateChartMap p.1)
        (coordinateOverlapMap p.1 p.2)
        rfl
        (coordinateLocalTwistModule d p.1)
        (coordinateOverlapTwistModule d p.1 p.2)
        (coordinateRestrictLeftIso d p.1 p.2 ≪≫
          coordinateOverlapTwistIso d p.1 p.2)

/-- The second Čech arrow: restrict the `j`-th local section to `(i,j)` in
the chart-`j` trivialization. -/
def twistCechRight (d : ℤ) : twistCechSource d ⟶ twistCechTarget d :=
  Pi.lift fun p ↦
    Pi.π (fun i : Fin 4 ↦ coordinateLocalPushforward d i) p.2 ≫
      pushforwardRestrictionHom
        (coordinateOverlapToRight p.1 p.2)
        (coordinateChartMap p.2)
        (coordinateOverlapMap p.1 p.2)
        (coordinateOverlapMap_eq_right p.1 p.2)
        (coordinateLocalTwistModule d p.2)
        (coordinateOverlapTwistModule d p.1 p.2)
        (coordinateRestrictRightIso d p.1 p.2)

/-- The global twisting candidate obtained by enforcing all ordered
pair-overlap compatibility equations.  Since this equalizer is formed in the
category of module sheaves, it is already an honest global module sheaf. -/
def globalTwistModule (d : ℤ) : CanonicalProjectiveCurve25Two.Modules :=
  equalizer (twistCechLeft d) (twistCechRight d)

/-- The global candidate satisfies the Čech pair-overlap equations by the
universal property of its defining equalizer. -/
@[reassoc]
theorem globalTwistModule_compatibility (d : ℤ) :
    equalizer.ι (twistCechLeft d) (twistCechRight d) ≫ twistCechLeft d =
      equalizer.ι (twistCechLeft d) (twistCechRight d) ≫ twistCechRight d :=
  equalizer.condition _ _

end MazurProof.RationalPointsN25QuotientTwoTwistingSheafGluing
