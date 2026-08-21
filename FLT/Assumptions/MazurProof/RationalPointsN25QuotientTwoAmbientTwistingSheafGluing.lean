import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAmbientTwistingDescent
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Čech gluing of the N25 twisting module sheaf

The categorical pair pullbacks have already been identified with the affine
homogeneous localizations carrying the coordinate-ratio transitions.  This
file uses those identifications to form an honest global module sheaf on the
binary projective three-space.

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

namespace MazurProof.RationalPointsN25QuotientTwoAmbientTwistingSheafGluing

open RationalPointsN25QuotientTwoChartIdeal
open RationalPointsN25QuotientTwoProj
open RationalPointsN25QuotientTwoQuotientGrading
open RationalPointsN25QuotientTwoKoszulTransition
open RationalPointsN25QuotientTwoKoszulSheafTransition
open RationalPointsN25QuotientTwoAmbientTwistingSheafCharts
open RationalPointsN25QuotientTwoAmbientTwistingDescent
open HomogeneousLocalization
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Actual morphisms from affine pair overlaps -/

/-- The explicit affine pair overlap mapped to its first coordinate chart. -/
def ambientOverlapToLeft (i j : Fin 4) :
    Spec (AmbientOverlapRingCat i j) ⟶ ambientChartScheme i :=
  Spec.map (ambientOverlapFromLeft i j)

/-- The explicit affine pair overlap mapped to its second coordinate chart. -/
def ambientOverlapToRight (i j : Fin 4) :
    Spec (AmbientOverlapRingCat i j) ⟶ ambientChartScheme j :=
  Spec.map (ambientOverlapFromRight i j)

/-- The first overlap projection is an open immersion. -/
instance ambientOverlapToLeftIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (ambientOverlapToLeft i j) := by
  dsimp [ambientOverlapToLeft]
  infer_instance

/-- The second overlap projection is an open immersion. -/
instance ambientOverlapToRightIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (ambientOverlapToRight i j) := by
  dsimp [ambientOverlapToRight]
  infer_instance

/-- The pair overlap as an open subscheme of the binary projective three-space,
using its first projection. -/
def ambientOverlapMap (i j : Fin 4) :
    Spec (.of (ambientOverlapRing i j)) ⟶
      BinaryProjectiveThreeSpace :=
  ambientOverlapToLeft i j ≫ ambientChartMap i

/-- The two routes from a pair overlap to the ambient projective space agree. -/
theorem ambientOverlapMap_eq_right (i j : Fin 4) :
    ambientOverlapToRight i j ≫ ambientChartMap j =
      ambientOverlapMap i j := by
  unfold ambientOverlapMap
  unfold ambientOverlapToLeft ambientOverlapToRight
  rw [← ambientChosenPullbackIso_inv_p₂,
    ← ambientChosenPullbackIso_inv_p₁]
  simp only [Category.assoc]
  rw [(ambientChosenPullback i j).condition]

/-- The explicit affine overlap, with its two localization maps, is the
cartesian intersection of the corresponding coordinate charts.  This is the
geometric square used by open base change below. -/
theorem ambientOverlap_isPullback (i j : Fin 4) :
    IsPullback (ambientOverlapToLeft i j)
      (ambientOverlapToRight i j)
      (ambientChartMap i) (ambientChartMap j) := by
  refine (ambientChosenPullback i j).isPullback.of_iso'
    (ambientChosenPullbackIso i j).symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
  · simpa [ambientOverlapToLeft] using
      ambientChosenPullbackIso_inv_p₁ i j
  · simpa [ambientOverlapToRight] using
      ambientChosenPullbackIso_inv_p₂ i j
  · simp
  · simp

/-- On a self-overlap the two maps to the repeated chart coincide. -/
theorem ambientOverlapToLeft_self_eq_right (i : Fin 4) :
    ambientOverlapToLeft i i = ambientOverlapToRight i i := by
  unfold ambientOverlapToLeft ambientOverlapToRight
  rw [← ambientChosenPullbackIso_inv_p₁,
    ← ambientChosenPullbackIso_inv_p₂,
    ambientChosenPullback_self_p₁_eq_p₂]

/-- The projection from a chart's self-intersection back to that chart is an
isomorphism: it is the pullback of a monomorphism along itself, transported
through the chosen affine overlap isomorphism. -/
noncomputable instance ambientOverlapToLeftSelfIsIso (i : Fin 4) :
    IsIso (ambientOverlapToLeft i i) := by
  haveI : IsIso (ambientChosenPullback i i).p₁ := by
    change IsIso (pullback.fst
      (ambientChartMap i) (ambientChartMap i))
    infer_instance
  unfold ambientOverlapToLeft
  rw [← ambientChosenPullbackIso_inv_p₁]
  infer_instance

/-! ## Open base change on the coordinate intersections

Restricting an extension-by-zero from chart `i` to chart `k` is the direct
image from their intersection into chart `k`.  This geometric conversion is
the key structural step in solving the restricted Čech equalizer: after it,
all its factors are sheaves on actual intersections inside one fixed chart.
-/

/-- Beck--Chevalley identifies the restriction to chart `k` of the local
sheaf extended from chart `i` with the pushforward from the pair intersection
`U_k ∩ U_i`. -/
def ambientLocalPushforwardBaseChangeIso (d : ℤ) (k i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        ((Scheme.Modules.pushforward (ambientChartMap i)).obj
          (ambientLocalTwistModule d i)) ≅
      (Scheme.Modules.pushforward (ambientOverlapToLeft k i)).obj
        ((Scheme.Modules.restrictFunctor
          (ambientOverlapToRight k i)).obj
            (ambientLocalTwistModule d i)) := by
  exact Scheme.Modules.openBaseChangeIso
    (ambientOverlapToLeft k i) (ambientOverlapToRight k i)
    (ambientChartMap k) (ambientChartMap i)
    (ambientOverlap_isPullback k i) (ambientLocalTwistModule d i)

/-! ## Restriction of local twists to pair overlaps -/

/-- Restricting the local twist from the first chart gives the explicit
free rank-one overlap sheaf. -/
def ambientRestrictLeftIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).obj
        (ambientLocalTwistModule d i) ≅
      ambientOverlapTwistModule d i j :=
  (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).mapIso
      (ambientLocalTwistUnitIso d i) ≪≫
    Scheme.Modules.restrictUnitIso (ambientOverlapToLeft i j) ≪≫
    (ambientOverlapTwistUnitIso d i j).symm

/-- Restricting the local twist from the second chart gives the same explicit
free rank-one overlap sheaf. -/
def ambientRestrictRightIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToRight i j)).obj
        (ambientLocalTwistModule d j) ≅
      ambientOverlapTwistModule d i j :=
  (Scheme.Modules.restrictFunctor (ambientOverlapToRight i j)).mapIso
      (ambientLocalTwistUnitIso d j) ≪≫
    Scheme.Modules.restrictUnitIso (ambientOverlapToRight i j) ≪≫
    (ambientOverlapTwistUnitIso d i j).symm

/-- The coordinate-ratio transition as an isomorphism between restrictions
of the two actual local chart sheaves to their categorical intersection. -/
def ambientDescentIso (d : ℤ) (i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientOverlapToLeft i j)).obj
        (ambientLocalTwistModule d i) ≅
      (Scheme.Modules.restrictFunctor (ambientOverlapToRight i j)).obj
        (ambientLocalTwistModule d j) :=
  ambientRestrictLeftIso d i j ≪≫
    ambientOverlapTwistIso d i j ≪≫
    (ambientRestrictRightIso d i j).symm

/-! ## Restriction from pair overlaps to triple overlaps -/

/-- Restrict the `(i,j)` affine overlap to the ordered triple overlap
`(i,j,l)`. -/
def ambientTripleTo12 (i j l : Fin 4) :
    Spec (.of (ambientTripleOverlapRing i j l)) ⟶
      Spec (.of (ambientOverlapRing i j)) :=
  Spec.map (CommRingCat.ofHom
    (Away.restrict12 standardConePiece (coordinate_isHomogeneous l)))

/-- Restrict the `(j,l)` affine overlap to the same ordered triple overlap. -/
def ambientTripleTo23 (i j l : Fin 4) :
    Spec (.of (ambientTripleOverlapRing i j l)) ⟶
      Spec (.of (ambientOverlapRing j l)) :=
  Spec.map (CommRingCat.ofHom
    (Away.restrict23 standardConePiece (coordinate_isHomogeneous i)))

/-- Restrict the `(i,l)` affine overlap to the same ordered triple overlap. -/
def ambientTripleTo13 (i j l : Fin 4) :
    Spec (.of (ambientTripleOverlapRing i j l)) ⟶
      Spec (.of (ambientOverlapRing i l)) :=
  Spec.map (CommRingCat.ofHom
    (Away.restrict13 standardConePiece (coordinate_isHomogeneous j)))

/-- The first pair-to-triple localization is an open immersion. -/
instance ambientTripleTo12IsOpenImmersion (i j l : Fin 4) :
    IsOpenImmersion (ambientTripleTo12 i j l) := by
  letI := (Away.restrict12 standardConePiece
    (f := MvPolynomial.X i) (g := MvPolynomial.X j) (h := MvPolynomial.X l)
    (coordinate_isHomogeneous l)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinate_isHomogeneous i)
          (coordinate_isHomogeneous j))
        (coordinate_isHomogeneous l))
      (ambientTripleOverlapRing i j l) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinate_isHomogeneous i)
        (coordinate_isHomogeneous j))
      (coordinate_isHomogeneous l) rfl (by norm_num)
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  exact IsOpenImmersion.of_isLocalization
    (Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinate_isHomogeneous i)
        (coordinate_isHomogeneous j))
      (coordinate_isHomogeneous l) : ambientOverlapRing i j)

/-- The second pair-to-triple localization is an open immersion. -/
instance ambientTripleTo23IsOpenImmersion (i j l : Fin 4) :
    IsOpenImmersion (ambientTripleTo23 i j l) := by
  letI := (Away.restrict23 standardConePiece
    (f := MvPolynomial.X i) (g := MvPolynomial.X j) (h := MvPolynomial.X l)
    (coordinate_isHomogeneous i)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinate_isHomogeneous j)
          (coordinate_isHomogeneous l))
        (coordinate_isHomogeneous i))
      (ambientTripleOverlapRing i j l) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinate_isHomogeneous j)
        (coordinate_isHomogeneous l))
      (coordinate_isHomogeneous i) (by ring) (by norm_num)
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  exact IsOpenImmersion.of_isLocalization
    (Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinate_isHomogeneous j)
        (coordinate_isHomogeneous l))
      (coordinate_isHomogeneous i) : ambientOverlapRing j l)

/-- The direct first-to-third pair localization is an open immersion. -/
instance ambientTripleTo13IsOpenImmersion (i j l : Fin 4) :
    IsOpenImmersion (ambientTripleTo13 i j l) := by
  letI := (Away.restrict13 standardConePiece
    (f := MvPolynomial.X i) (g := MvPolynomial.X j) (h := MvPolynomial.X l)
    (coordinate_isHomogeneous j)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinate_isHomogeneous i)
          (coordinate_isHomogeneous l))
        (coordinate_isHomogeneous j))
      (ambientTripleOverlapRing i j l) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinate_isHomogeneous i)
        (coordinate_isHomogeneous l))
      (coordinate_isHomogeneous j) (by ring) (by norm_num)
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
  exact IsOpenImmersion.of_isLocalization
    (Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinate_isHomogeneous i)
        (coordinate_isHomogeneous l))
      (coordinate_isHomogeneous j) : ambientOverlapRing i l)

/-! ## Triple overlaps as geometric pullbacks -/

/-- The triple overlap mapped to chart `k` through the `(k,i)` pair
intersection. -/
def ambientTripleToFirstChart (k i j : Fin 4) :
    Spec (.of (ambientTripleOverlapRing k i j)) ⟶
      ambientChartScheme k :=
  ambientTripleTo12 k i j ≫ ambientOverlapToLeft k i

/-- The triple-overlap map to its first chart is an open immersion because
it is a composite of localization opens. -/
instance ambientTripleToFirstChartIsOpenImmersion (k i j : Fin 4) :
    IsOpenImmersion (ambientTripleToFirstChart k i j) := by
  dsimp [ambientTripleToFirstChart]
  infer_instance

/-- A pair overlap is open in the ambient projective space through either chart. -/
instance ambientOverlapMapIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (ambientOverlapMap i j) := by
  dsimp [ambientOverlapMap]
  infer_instance

/-- In chart `i`, the overlap with chart `j` is the principal open where
the degree-zero ratio `x_j/x_i` is nonzero. -/
theorem ambientOverlapToLeft_opensRange (i j : Fin 4) :
    (ambientOverlapToLeft i j).opensRange =
      PrimeSpectrum.basicOpen
        (Away.isLocalizationElem (coordinate_isHomogeneous i)
          (coordinate_isHomogeneous j)) := by
  letI := (awayMap standardConePiece (f := MvPolynomial.X i)
    (coordinate_isHomogeneous j) rfl).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinate_isHomogeneous i)
        (coordinate_isHomogeneous j))
      (ambientOverlapRing i j) :=
    Away.isLocalization_mul (coordinate_isHomogeneous i)
      (coordinate_isHomogeneous j) rfl (by norm_num)
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  have hmap : ambientOverlapToLeft i j =
      Spec.map (CommRingCat.ofHom (algebraMap
        (ambientChartRing i) (ambientOverlapRing i j))) := by
    rfl
  rw [hmap]
  exact PrimeSpectrum.localization_away_comap_range
    (ambientOverlapRing i j) _

/-- Within the `(k,i)` overlap, imposing `x_j ≠ 0` gives the ordered
triple overlap. -/
theorem ambientTripleTo12_opensRange (k i j : Fin 4) :
    (ambientTripleTo12 k i j).opensRange =
      PrimeSpectrum.basicOpen
        (Away.isLocalizationElem
          (SetLike.mul_mem_graded (coordinate_isHomogeneous k)
            (coordinate_isHomogeneous i))
          (coordinate_isHomogeneous j)) := by
  letI := (Away.restrict12 standardConePiece
    (f := MvPolynomial.X k) (g := MvPolynomial.X i)
    (h := MvPolynomial.X j) (coordinate_isHomogeneous j)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinate_isHomogeneous k)
          (coordinate_isHomogeneous i))
        (coordinate_isHomogeneous j))
      (ambientTripleOverlapRing k i j) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinate_isHomogeneous k)
        (coordinate_isHomogeneous i))
      (coordinate_isHomogeneous j) rfl (by norm_num)
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  change Set.range (PrimeSpectrum.comap (algebraMap
      (ambientOverlapRing k i) (ambientTripleOverlapRing k i j))) = _
  exact PrimeSpectrum.localization_away_comap_range
    (ambientTripleOverlapRing k i j) _

/-- The two iterated localization maps from the triple overlap to chart `i`
agree.  This is the affine associativity statement underlying the geometric
triple intersection. -/
theorem ambientTripleTo12_comp_right_eq_ambientTripleTo23_comp_left
    (k i j : Fin 4) :
    ambientTripleTo12 k i j ≫ ambientOverlapToRight k i =
      ambientTripleTo23 k i j ≫ ambientOverlapToLeft i j := by
  dsimp [ambientOverlapToRight, ambientOverlapToLeft]
  dsimp [ambientTripleTo12, ambientTripleTo23, Away.restrict12,
    Away.restrict23]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change
    Away.restrict12 standardConePiece (coordinate_isHomogeneous j)
        (awayMap standardConePiece (coordinate_isHomogeneous k)
          (mul_comm _ _) x) =
      Away.restrict23 standardConePiece (coordinate_isHomogeneous k)
        (awayMap standardConePiece (coordinate_isHomogeneous j) rfl x)
  obtain ⟨q, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    standardConePiece (coordinate_isHomogeneous i) x
  simp only [Away.restrict12, Away.restrict23]
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk]
  apply (HomogeneousLocalization.ext_iff_val _ _).2
  simp only [HomogeneousLocalization.Away.val_mk]
  congr 1
  ring

/-- Inside chart `i`, the triple overlap is the cartesian intersection of
the `(k,i)` and `(i,j)` pair overlaps. -/
theorem ambientTripleInner_isPullback (k i j : Fin 4) :
    IsPullback (ambientTripleTo23 k i j)
      (ambientTripleTo12 k i j)
      (ambientOverlapToLeft i j) (ambientOverlapToRight k i) := by
  refine IsOpenImmersion.isPullback _ _ _ _
    (ambientTripleTo12_comp_right_eq_ambientTripleTo23_comp_left k i j)
    ?_
  guard_target =
    ambientOverlapToRight k i ⁻¹ᵁ
        (ambientOverlapToLeft i j).opensRange =
      (ambientTripleTo12 k i j).opensRange
  rw [ambientOverlapToLeft_opensRange,
    ambientTripleTo12_opensRange]
  letI := (awayMap standardConePiece (f := MvPolynomial.X i)
    (coordinate_isHomogeneous k) (mul_comm _ _)).toAlgebra
  have hmap : ambientOverlapToRight k i =
      Spec.map (CommRingCat.ofHom (algebraMap
        (ambientChartRing i) (ambientOverlapRing k i))) := by
    rfl
  rw [hmap]
  change PrimeSpectrum.basicOpen
      (awayMap standardConePiece (coordinate_isHomogeneous k)
        (mul_comm _ _)
        (Away.isLocalizationElem (coordinate_isHomogeneous i)
          (coordinate_isHomogeneous j))) = _
  let a : ambientOverlapRing k i :=
    awayMap standardConePiece (coordinate_isHomogeneous k)
      (mul_comm _ _)
      (Away.isLocalizationElem (coordinate_isHomogeneous i)
        (coordinate_isHomogeneous j))
  let b : ambientOverlapRing k i :=
    Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinate_isHomogeneous k)
        (coordinate_isHomogeneous i))
      (coordinate_isHomogeneous j)
  let u : (ambientOverlapRing k i)ˣ :=
    Away.degreeOneRatioUnit standardConePiece
      (coordinate_isHomogeneous k) (coordinate_isHomogeneous i)
  change PrimeSpectrum.basicOpen a = PrimeSpectrum.basicOpen b
  have hab : b = a ^ 2 * (u : ambientOverlapRing k i) := by
    apply (HomogeneousLocalization.ext_iff_val _ _).2
    simp only [a, b, u, Away.isLocalizationElem,
      Away.degreeOneRatioUnit, Away.degreeOneRatio,
      HomogeneousLocalization.awayMap_mk,
      HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      HomogeneousLocalization.Away.val_mk, Localization.mk_pow,
      Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp
    ring
  rw [hab, PrimeSpectrum.basicOpen_mul,
    PrimeSpectrum.basicOpen_pow _ 2 (by norm_num)]
  have hu : PrimeSpectrum.basicOpen (u : ambientOverlapRing k i) = ⊤ := by
    apply TopologicalSpace.Opens.ext
    ext p
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      TopologicalSpace.Opens.mem_top]
    constructor
    · intro
      trivial
    · intro
      exact Ideal.notMem_of_isUnit p.asIdeal (Units.isUnit u)
  rw [hu]
  simp

/-- The ordered triple overlap is the pullback of the pair overlap
`U_i ∩ U_j` along the chart inclusion `U_k ⟶ X`.  It is obtained by
pasting the affine intersection square inside `U_i` with the cartesian
square defining `U_k ∩ U_i`. -/
theorem ambientTriple_isPullback (k i j : Fin 4) :
    IsPullback (ambientTripleTo23 k i j)
      (ambientTripleToFirstChart k i j)
      (ambientOverlapMap i j) (ambientChartMap k) := by
  simpa only [ambientTripleToFirstChart, ambientOverlapMap] using
    (ambientTripleInner_isPullback k i j).paste_vert
      (ambientOverlap_isPullback k i).flip

/-- The two localization routes from the ordered triple overlap to its third
chart agree.  On affine rings this is associativity of homogeneous
localization; the proof compares the two maps on a common fraction
representative. -/
theorem ambientTripleTo23_comp_right_eq_ambientTripleTo13_comp_right
    (k i j : Fin 4) :
    ambientTripleTo23 k i j ≫ ambientOverlapToRight i j =
      ambientTripleTo13 k i j ≫ ambientOverlapToRight k j := by
  dsimp [ambientOverlapToRight]
  dsimp [ambientTripleTo23, ambientTripleTo13, Away.restrict23,
    Away.restrict13]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change
    Away.restrict23 standardConePiece (coordinate_isHomogeneous k)
        (awayMap standardConePiece (coordinate_isHomogeneous i)
          (mul_comm _ _) x) =
      Away.restrict13 standardConePiece (coordinate_isHomogeneous i)
        (awayMap standardConePiece (coordinate_isHomogeneous k)
          (mul_comm _ _) x)
  obtain ⟨q, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    standardConePiece (coordinate_isHomogeneous j) x
  simp only [Away.restrict23, Away.restrict13]
  rw [HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk]
  apply (HomogeneousLocalization.ext_iff_val _ _).2
  simp only [HomogeneousLocalization.Away.val_mk]
  congr 1
  ring

/-- The route through the `(k,j)` pair overlap gives the same map from the
triple overlap to chart `k` as the route through `(k,i)`.  Monicity of the
chart inclusion reduces the assertion to the two pair-overlap pullback
conditions and the affine localization identity above. -/
theorem ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart
    (k i j : Fin 4) :
    ambientTripleTo13 k i j ≫ ambientOverlapToLeft k j =
      ambientTripleToFirstChart k i j := by
  rw [← cancel_mono (ambientChartMap k)]
  simp only [Category.assoc]
  calc
    ambientTripleTo13 k i j ≫ ambientOverlapToLeft k j ≫
          ambientChartMap k =
        ambientTripleTo13 k i j ≫ ambientOverlapMap k j := rfl
    _ = ambientTripleTo13 k i j ≫ ambientOverlapToRight k j ≫
          ambientChartMap j := by
      rw [ambientOverlapMap_eq_right]
    _ = ambientTripleTo23 k i j ≫ ambientOverlapToRight i j ≫
          ambientChartMap j := by
      slice_lhs 1 2 =>
        rw [← ambientTripleTo23_comp_right_eq_ambientTripleTo13_comp_right]
      rw [Category.assoc]
    _ = ambientTripleTo23 k i j ≫ ambientOverlapMap i j := by
      rw [ambientOverlapMap_eq_right]
    _ = ambientTripleToFirstChart k i j ≫ ambientChartMap k :=
      (ambientTriple_isPullback k i j).w

/-- The alternative inner square through the `(k,j)` overlap is cartesian.
It is obtained by cancelling the cartesian outer `(k,j)` chart square from
the already cartesian triple-overlap square.  This supplies the second
factorization needed to compare Čech reconstruction paths. -/
theorem ambientTripleInner13_isPullback (k i j : Fin 4) :
    IsPullback (ambientTripleTo23 k i j)
      (ambientTripleTo13 k i j)
      (ambientOverlapToRight i j) (ambientOverlapToRight k j) := by
  have hTotal : IsPullback (ambientTripleTo23 k i j)
      (ambientTripleTo13 k i j ≫ ambientOverlapToLeft k j)
      (ambientOverlapToRight i j ≫ ambientChartMap j)
      (ambientChartMap k) := by
    simpa only [
      ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart,
      ambientOverlapMap_eq_right] using
      ambientTriple_isPullback k i j
  exact hTotal.of_bot
    (ambientTripleTo23_comp_right_eq_ambientTripleTo13_comp_right
      k i j)
    (ambientOverlap_isPullback k j).flip

/-- Restricting the `(i,j)` overlap's free rank-one sheaf gives the free
rank-one sheaf on the ordered triple overlap. -/
def ambientPairToTripleIso12 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientTripleTo12 i j l)).obj
        (ambientOverlapTwistModule d i j) ≅
      ambientTripleTwistModule d i j l :=
  (Scheme.Modules.restrictFunctor (ambientTripleTo12 i j l)).mapIso
      (ambientOverlapTwistUnitIso d i j) ≪≫
    Scheme.Modules.restrictUnitIso (ambientTripleTo12 i j l) ≪≫
    (ambientTripleTwistUnitIso d i j l).symm

/-- Restricting the `(j,l)` overlap's free rank-one sheaf gives the same
triple-overlap sheaf. -/
def ambientPairToTripleIso23 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientTripleTo23 i j l)).obj
        (ambientOverlapTwistModule d j l) ≅
      ambientTripleTwistModule d i j l :=
  (Scheme.Modules.restrictFunctor (ambientTripleTo23 i j l)).mapIso
      (ambientOverlapTwistUnitIso d j l) ≪≫
    Scheme.Modules.restrictUnitIso (ambientTripleTo23 i j l) ≪≫
    (ambientTripleTwistUnitIso d i j l).symm

/-- Restricting the `(i,l)` overlap's free rank-one sheaf gives the same
triple-overlap sheaf. -/
def ambientPairToTripleIso13 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientTripleTo13 i j l)).obj
        (ambientOverlapTwistModule d i l) ≅
      ambientTripleTwistModule d i j l :=
  (Scheme.Modules.restrictFunctor (ambientTripleTo13 i j l)).mapIso
      (ambientOverlapTwistUnitIso d i l) ≪≫
    Scheme.Modules.restrictUnitIso (ambientTripleTo13 i j l) ≪≫
    (ambientTripleTwistUnitIso d i j l).symm

set_option maxHeartbeats 800000 in
-- Unfolding the three nested homogeneous localizations is expensive even
-- though the proof is a direct application of the generic affine lemma.
/-- Transporting the `(i,j)` transition through restriction to `(i,j,l)`
gives the first explicit triple-overlap transition. -/
theorem ambientOverlapTwistIso_restrict12 (d : ℤ) (i j l : Fin 4) :
    (ambientPairToTripleIso12 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (ambientTripleTo12 i j l)).map
          (ambientOverlapTwistIso d i j).hom ≫
        (ambientPairToTripleIso12 d i j l).hom =
      (ambientTripleTwistIso12 d i j l).hom := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Away.restrict12 standardConePiece
          (coordinate_isHomogeneous l)))) := by
    change IsOpenImmersion (ambientTripleTo12 i j l)
    infer_instance
  dsimp [ambientPairToTripleIso12, ambientOverlapTwistIso,
    ambientTripleTwistIso12, Away.ratioPowerModuleIso12,
    Away.ratioPowerTransition, Away.ratioPowerTransition12,
    ambientTripleTo12, ambientTripleTwistModule,
    ambientOverlapTwistModule]
  erw [Scheme.Modules.restrictUnitIso_conjugate_tildeUnit
    (CommRingCat.ofHom
      (Away.restrict12 standardConePiece
        (coordinate_isHomogeneous l)))
    ((Away.degreeOneRatioUnit standardConePiece
      (coordinate_isHomogeneous i)
      (coordinate_isHomogeneous j)) ^ d)]
  change ((AlgebraicGeometry.tilde.functor
      (.of (ambientTripleOverlapRing i j l))).mapIso _).hom = _
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
theorem ambientOverlapTwistIso_restrict23 (d : ℤ) (i j l : Fin 4) :
    (ambientPairToTripleIso23 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (ambientTripleTo23 i j l)).map
          (ambientOverlapTwistIso d j l).hom ≫
        (ambientPairToTripleIso23 d i j l).hom =
      (ambientTripleTwistIso23 d i j l).hom := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Away.restrict23 standardConePiece
          (coordinate_isHomogeneous i)))) := by
    change IsOpenImmersion (ambientTripleTo23 i j l)
    infer_instance
  dsimp [ambientPairToTripleIso23, ambientOverlapTwistIso,
    ambientTripleTwistIso23, Away.ratioPowerModuleIso23,
    Away.ratioPowerTransition, Away.ratioPowerTransition23,
    ambientTripleTo23, ambientTripleTwistModule,
    ambientOverlapTwistModule]
  erw [Scheme.Modules.restrictUnitIso_conjugate_tildeUnit
    (CommRingCat.ofHom
      (Away.restrict23 standardConePiece
        (coordinate_isHomogeneous i)))
    ((Away.degreeOneRatioUnit standardConePiece
      (coordinate_isHomogeneous j)
      (coordinate_isHomogeneous l)) ^ d)]
  change ((AlgebraicGeometry.tilde.functor
      (.of (ambientTripleOverlapRing i j l))).mapIso _).hom = _
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
theorem ambientOverlapTwistIso_restrict13 (d : ℤ) (i j l : Fin 4) :
    (ambientPairToTripleIso13 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (ambientTripleTo13 i j l)).map
          (ambientOverlapTwistIso d i l).hom ≫
        (ambientPairToTripleIso13 d i j l).hom =
      (ambientTripleTwistIso13 d i j l).hom := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (Away.restrict13 standardConePiece
          (coordinate_isHomogeneous j)))) := by
    change IsOpenImmersion (ambientTripleTo13 i j l)
    infer_instance
  dsimp [ambientPairToTripleIso13, ambientOverlapTwistIso,
    ambientTripleTwistIso13, Away.ratioPowerModuleIso13,
    Away.ratioPowerTransition, Away.ratioPowerTransition13,
    ambientTripleTo13, ambientTripleTwistModule,
    ambientOverlapTwistModule]
  erw [Scheme.Modules.restrictUnitIso_conjugate_tildeUnit
    (CommRingCat.ofHom
      (Away.restrict13 standardConePiece
        (coordinate_isHomogeneous j)))
    ((Away.degreeOneRatioUnit standardConePiece
      (coordinate_isHomogeneous i)
      (coordinate_isHomogeneous l)) ^ d)]
  change ((AlgebraicGeometry.tilde.functor
      (.of (ambientTripleOverlapRing i j l))).mapIso _).hom = _
  congr 1
  congr 1
  congr 1
  congr 1
  simp only [map_zpow]
  rfl

/-- The three restricted pair-overlap transitions satisfy the actual Čech
cocycle on the explicit ordered triple overlap. -/
theorem ambientRestrictedOverlapTwistIso_cocycle
    (d : ℤ) (i j l : Fin 4) :
    ((ambientPairToTripleIso12 d i j l).inv ≫
          (Scheme.Modules.restrictFunctor (ambientTripleTo12 i j l)).map
            (ambientOverlapTwistIso d i j).hom ≫
          (ambientPairToTripleIso12 d i j l).hom) ≫
        ((ambientPairToTripleIso23 d i j l).inv ≫
          (Scheme.Modules.restrictFunctor (ambientTripleTo23 i j l)).map
            (ambientOverlapTwistIso d j l).hom ≫
          (ambientPairToTripleIso23 d i j l).hom) =
      (ambientPairToTripleIso13 d i j l).inv ≫
        (Scheme.Modules.restrictFunctor (ambientTripleTo13 i j l)).map
          (ambientOverlapTwistIso d i l).hom ≫
        (ambientPairToTripleIso13 d i j l).hom := by
  rw [ambientOverlapTwistIso_restrict12,
    ambientOverlapTwistIso_restrict23,
    ambientOverlapTwistIso_restrict13]
  exact ambientTripleTwistIso_cocycle d i j l

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
  Scheme.Modules.pushforwardRestrictionHomOfHom
    (f := j) (k := k) (h := h) hk F G e.hom

/-- The local chart sheaf, extended by zero to the ambient projective space. -/
abbrev ambientLocalPushforward (d : ℤ) (i : Fin 4) :
    BinaryProjectiveThreeSpace.Modules :=
  (Scheme.Modules.pushforward (ambientChartMap i)).obj
    (ambientLocalTwistModule d i)

/-- The explicit pair-overlap sheaf, extended by zero to the projective
ambient space. -/
abbrev ambientOverlapPushforward (d : ℤ) (p : Fin 4 × Fin 4) :
    BinaryProjectiveThreeSpace.Modules :=
  (Scheme.Modules.pushforward (ambientOverlapMap p.1 p.2)).obj
    (ambientOverlapTwistModule d p.1 p.2)

/-! ## Base change from pair overlaps to triple overlaps -/

/-- Open base change along `U_k ⟶ X` identifies a pair-overlap
pushforward with the pushforward from the explicit triple overlap. -/
def ambientTripleBaseChangeIso (k i j : Fin 4)
    (M : (Spec (.of (ambientOverlapRing i j))).Modules) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        ((Scheme.Modules.pushforward (ambientOverlapMap i j)).obj M) ≅
      (Scheme.Modules.pushforward (ambientTripleToFirstChart k i j)).obj
        ((Scheme.Modules.restrictFunctor
          (ambientTripleTo23 k i j)).obj M) := by
  exact Scheme.Modules.openBaseChangeIso
    (ambientTripleToFirstChart k i j) (ambientTripleTo23 k i j)
    (ambientChartMap k) (ambientOverlapMap i j)
    (ambientTriple_isPullback k i j).flip M

/-- For the twisting sheaves, triple-overlap base change is transported to
the fixed free rank-one module used by the explicit cocycle theorem. -/
def ambientTripleTwistBaseChangeIso (d : ℤ) (k i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (ambientOverlapPushforward d (i, j)) ≅
      (Scheme.Modules.pushforward (ambientTripleToFirstChart k i j)).obj
        (ambientTripleTwistModule d k i j) :=
  ambientTripleBaseChangeIso k i j
      (ambientOverlapTwistModule d i j) ≪≫
    (Scheme.Modules.pushforward
      (ambientTripleToFirstChart k i j)).mapIso
        (ambientPairToTripleIso23 d k i j)

/-- Product of the four local chart sheaves after extension to the whole
ambient projective space. -/
abbrev twistCechSource (d : ℤ) : BinaryProjectiveThreeSpace.Modules :=
  ∏ᶜ fun i : Fin 4 ↦ ambientLocalPushforward d i

/-- Product of the sixteen ordered pair-overlap sheaves after extension to
the whole ambient projective space. -/
abbrev twistCechTarget (d : ℤ) : BinaryProjectiveThreeSpace.Modules :=
  ∏ᶜ fun p : Fin 4 × Fin 4 ↦ ambientOverlapPushforward d p

/-- The first Čech arrow: restrict the `i`-th local section to `(i,j)` and
then apply the coordinate-ratio transition from chart `i` to chart `j`. -/
def twistCechLeft (d : ℤ) : twistCechSource d ⟶ twistCechTarget d :=
  Pi.lift fun p ↦
    Pi.π (fun i : Fin 4 ↦ ambientLocalPushforward d i) p.1 ≫
      pushforwardRestrictionHom
        (ambientOverlapToLeft p.1 p.2)
        (ambientChartMap p.1)
        (ambientOverlapMap p.1 p.2)
        rfl
        (ambientLocalTwistModule d p.1)
        (ambientOverlapTwistModule d p.1 p.2)
        (ambientRestrictLeftIso d p.1 p.2 ≪≫
          ambientOverlapTwistIso d p.1 p.2)

/-- The second Čech arrow: restrict the `j`-th local section to `(i,j)` in
the chart-`j` trivialization. -/
def twistCechRight (d : ℤ) : twistCechSource d ⟶ twistCechTarget d :=
  Pi.lift fun p ↦
    Pi.π (fun i : Fin 4 ↦ ambientLocalPushforward d i) p.2 ≫
      pushforwardRestrictionHom
        (ambientOverlapToRight p.1 p.2)
        (ambientChartMap p.2)
        (ambientOverlapMap p.1 p.2)
        (ambientOverlapMap_eq_right p.1 p.2)
        (ambientLocalTwistModule d p.2)
        (ambientOverlapTwistModule d p.1 p.2)
        (ambientRestrictRightIso d p.1 p.2)

/-- The global twisting candidate obtained by enforcing all ordered
pair-overlap compatibility equations.  Since this equalizer is formed in the
category of module sheaves, it is already an honest global module sheaf. -/
def globalTwistModule (d : ℤ) : BinaryProjectiveThreeSpace.Modules :=
  equalizer (twistCechLeft d) (twistCechRight d)

/-- The global candidate satisfies the Čech pair-overlap equations by the
universal property of its defining equalizer. -/
@[reassoc]
theorem globalTwistModule_compatibility (d : ℤ) :
    equalizer.ι (twistCechLeft d) (twistCechRight d) ≫ twistCechLeft d =
      equalizer.ι (twistCechLeft d) (twistCechRight d) ≫ twistCechRight d :=
  equalizer.condition _ _

/-! ## Restriction to a coordinate chart

Open base change and preservation of limits put the restriction of the global
Čech equalizer into a form that can be solved on one fixed chart.  A local
section on chart `k` determines its representative on every chart `i` by
restricting to `U_k ∩ U_i` and applying the descent transition.  The remaining
effectivity equation is exactly the triple-overlap cocycle for this family.
-/

/-- Evaluation of a compatible global family in the `i`-th chart.  The map is
the adjoint of the equalizer inclusion followed by the `i`-th product
projection, so it extracts precisely the local representative of a glued
section. -/
def globalTwistModuleToLocal (d : ℤ) (i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap i)).obj
        (globalTwistModule d) ⟶ ambientLocalTwistModule d i :=
  ((Scheme.Modules.restrictAdjunction (ambientChartMap i)).homEquiv
      (globalTwistModule d) (ambientLocalTwistModule d i))
    |>.symm (equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
      Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Literal Čech evaluation satisfies the transition equation on every
ordered ambient pair overlap.  Transposition reduces the assertion to one
component of the defining equalizer equation. -/
theorem globalTwistModuleToLocal_pair_compatibility
    (d : ℤ) (i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (ambientOverlapToLeft i j) (ambientChartMap i)
        (ambientOverlapMap i j) rfl
        (globalTwistModule d) (ambientLocalTwistModule d i)
        (ambientOverlapTwistModule d i j)
        (globalTwistModuleToLocal d i)
        (ambientRestrictLeftIso d i j ≪≫
          ambientOverlapTwistIso d i j).hom =
      Scheme.Modules.iteratedRestrictionHom
        (ambientOverlapToRight i j) (ambientChartMap j)
        (ambientOverlapMap i j) (ambientOverlapMap_eq_right i j)
        (globalTwistModule d) (ambientLocalTwistModule d j)
        (ambientOverlapTwistModule d i j)
        (globalTwistModuleToLocal d j)
        (ambientRestrictRightIso d i j).hom := by
  have h := congrArg
    (fun z => z ≫ Pi.π
      (fun p : Fin 4 × Fin 4 ↦ ambientOverlapPushforward d p) (i, j))
    (globalTwistModule_compatibility d)
  simp only [twistCechLeft, twistCechRight, Category.assoc,
    Pi.lift_π] at h
  have heval (k : Fin 4) :
      (Scheme.Modules.restrictAdjunction
          (ambientChartMap k)).unit.app (globalTwistModule d) ≫
        (Scheme.Modules.pushforward (ambientChartMap k)).map
          (globalTwistModuleToLocal d k) =
      equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
        Pi.π (fun l : Fin 4 ↦ ambientLocalPushforward d l) k := by
    change ((Scheme.Modules.restrictAdjunction
      (ambientChartMap k)).homEquiv
        (globalTwistModule d) (ambientLocalTwistModule d k))
          (globalTwistModuleToLocal d k) = _
    unfold globalTwistModuleToLocal
    exact Equiv.apply_symm_apply _ _
  rw [← Scheme.Modules.pushforwardRestrictionHomOfHom_transpose,
    ← Scheme.Modules.pushforwardRestrictionHomOfHom_transpose]
  simp only [← Category.assoc]
  rw [heval i, heval j]
  exact congrArg
    ((Scheme.Modules.restrictAdjunction
      (ambientOverlapMap i j)).homEquiv
        (globalTwistModule d)
        (ambientOverlapTwistModule d i j)).symm h

/-- Restriction carries the product of extended local sheaves to the product
of their restrictions on the fixed chart. -/
def restrictedTwistCechSourceIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (twistCechSource d) ≅
      ∏ᶜ fun i : Fin 4 ↦
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
          (ambientLocalPushforward d i) :=
  PreservesProduct.iso
    (Scheme.Modules.restrictFunctor (ambientChartMap k))
    (fun i : Fin 4 ↦ ambientLocalPushforward d i)

/-- The inverse product comparison followed by a restricted projection is the
corresponding projection from the product of restricted factors. -/
@[reassoc (attr := simp)]
theorem restrictedTwistCechSourceIso_inv_map_π (d : ℤ) (k i : Fin 4) :
    (restrictedTwistCechSourceIso d k).inv ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) i) =
      Pi.π (fun j : Fin 4 ↦
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
          (ambientLocalPushforward d j)) i := by
  rw [← piComparison_comp_π]
  exact (restrictedTwistCechSourceIso d k).inv_hom_id_assoc _

/-- Restriction similarly carries the overlap product to the product of its
restricted overlap factors. -/
def restrictedTwistCechTargetIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (twistCechTarget d) ≅
      ∏ᶜ fun p : Fin 4 × Fin 4 ↦
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
          (ambientOverlapPushforward d p) :=
  PreservesProduct.iso
    (Scheme.Modules.restrictFunctor (ambientChartMap k))
    (fun p : Fin 4 × Fin 4 ↦ ambientOverlapPushforward d p)

/-- Restriction of the global Čech equalizer is the equalizer of the two
restricted Čech arrows. -/
def restrictedGlobalTwistCechIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (globalTwistModule d) ≅
      equalizer
        ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (twistCechLeft d))
        ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (twistCechRight d)) :=
  PreservesEqualizer.iso
    (Scheme.Modules.restrictFunctor (ambientChartMap k))
    (twistCechLeft d) (twistCechRight d)

/-- A section on chart `k` determines its representative in the `i`-th
extended chart factor: restrict it to `U_k ∩ U_i`, transport by the descent
transition, push it forward inside `U_k`, and invert open base change. -/
def ambientLocalReconstructionHom (d : ℤ) (k i : Fin 4) :
    ambientLocalTwistModule d k ⟶
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (ambientLocalPushforward d i) :=
  (Scheme.Modules.restrictAdjunction
      (ambientOverlapToLeft k i)).unit.app
        (ambientLocalTwistModule d k) ≫
    (Scheme.Modules.pushforward (ambientOverlapToLeft k i)).map
      (ambientDescentIso d k i).hom ≫
    (ambientLocalPushforwardBaseChangeIso d k i).inv

/-- The representatives reconstructed from chart `k`, assembled into the
restricted product of all four local extension-by-zero factors. -/
def ambientLocalReconstruction (d : ℤ) (k : Fin 4) :
    ambientLocalTwistModule d k ⟶
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (twistCechSource d) :=
  Pi.lift (fun i : Fin 4 ↦ ambientLocalReconstructionHom d k i) ≫
    (restrictedTwistCechSourceIso d k).inv

/-! ## Compatibility of reconstructed local families

The following lemmas normalize the two routes from a chart to a triple
overlap.  They keep base change, adjunction, unit trivializations, and the
coordinate cocycle as separate mathematical steps.
-/

set_option backward.isDefEq.respectTransparency false in
/-- Explicit unit trivializations compose along the first pair-to-triple
route. -/
theorem ambientUnitRoute12 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo12 k i j) (ambientOverlapToLeft k i)
        (ambientTripleToFirstChart k i j) rfl
        (ambientLocalTwistModule d k)
        (ambientOverlapTwistModule d k i)
        (ambientTripleTwistModule d k i j)
        (ambientRestrictLeftIso d k i).hom
        (ambientPairToTripleIso12 d k i j).hom =
      (Scheme.Modules.restrictFunctor
          (ambientTripleToFirstChart k i j)).map
          (ambientLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (ambientTripleToFirstChart k i j)).hom ≫
        (ambientTripleTwistUnitIso d k i j).inv := by
  simpa only [ambientRestrictLeftIso,
    ambientPairToTripleIso12, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_of_unit
      (q := ambientTripleTo12 k i j)
      (a := ambientOverlapToLeft k i)
      (g := ambientTripleToFirstChart k i j)
      rfl
      (ambientLocalTwistModule d k)
      (ambientOverlapTwistModule d k i)
      (ambientTripleTwistModule d k i j)
      (ambientLocalTwistUnitIso d k)
      (ambientOverlapTwistUnitIso d k i)
      (ambientTripleTwistUnitIso d k i j))

set_option backward.isDefEq.respectTransparency false in
/-- Explicit unit trivializations also compose along the direct
first-to-third pair route to the same canonical triple-open map. -/
theorem ambientUnitRoute13 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo13 k i j) (ambientOverlapToLeft k j)
        (ambientTripleToFirstChart k i j)
        (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
        (ambientLocalTwistModule d k)
        (ambientOverlapTwistModule d k j)
        (ambientTripleTwistModule d k i j)
        (ambientRestrictLeftIso d k j).hom
        (ambientPairToTripleIso13 d k i j).hom =
      (Scheme.Modules.restrictFunctor
          (ambientTripleToFirstChart k i j)).map
          (ambientLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (ambientTripleToFirstChart k i j)).hom ≫
        (ambientTripleTwistUnitIso d k i j).inv := by
  simpa only [ambientRestrictLeftIso,
    ambientPairToTripleIso13, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_of_unit
      (q := ambientTripleTo13 k i j)
      (a := ambientOverlapToLeft k j)
      (g := ambientTripleToFirstChart k i j)
      (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
      (ambientLocalTwistModule d k)
      (ambientOverlapTwistModule d k j)
      (ambientTripleTwistModule d k i j)
      (ambientLocalTwistUnitIso d k)
      (ambientOverlapTwistUnitIso d k j)
      (ambientTripleTwistUnitIso d k i j))

/-- The canonical first-pair unit route remains in normal form under any
further morphism out of the triple-overlap module. -/
theorem ambientUnitRoute12_comp
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (ambientTripleOverlapRing k i j))).Modules)
    (u : ambientTripleTwistModule d k i j ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo12 k i j) (ambientOverlapToLeft k i)
        (ambientTripleToFirstChart k i j) rfl
        (ambientLocalTwistModule d k)
        (ambientOverlapTwistModule d k i) K
        (ambientRestrictLeftIso d k i).hom
        ((ambientPairToTripleIso12 d k i j).hom ≫ u) =
      ((Scheme.Modules.restrictFunctor
          (ambientTripleToFirstChart k i j)).map
          (ambientLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (ambientTripleToFirstChart k i j)).hom ≫
        (ambientTripleTwistUnitIso d k i j).inv) ≫ u := by
  rw [Scheme.Modules.iteratedRestrictionHom_comp, ambientUnitRoute12]

/-- The direct first-to-third unit route has the analogous normal form under
postcomposition. -/
theorem ambientUnitRoute13_comp
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (ambientTripleOverlapRing k i j))).Modules)
    (u : ambientTripleTwistModule d k i j ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo13 k i j) (ambientOverlapToLeft k j)
        (ambientTripleToFirstChart k i j)
        (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
        (ambientLocalTwistModule d k)
        (ambientOverlapTwistModule d k j) K
        (ambientRestrictLeftIso d k j).hom
        ((ambientPairToTripleIso13 d k i j).hom ≫ u) =
      ((Scheme.Modules.restrictFunctor
          (ambientTripleToFirstChart k i j)).map
          (ambientLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (ambientTripleToFirstChart k i j)).hom ≫
        (ambientTripleTwistUnitIso d k i j).inv) ≫ u := by
  rw [Scheme.Modules.iteratedRestrictionHom_comp, ambientUnitRoute13]

set_option backward.isDefEq.respectTransparency false in
/-- The unit trivializations on the two sides of the inner `(k,i,j)`
pullback square agree after transport to the fixed triple-overlap module. -/
theorem ambientUnitPullback12 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.pullbackRestrictionHom
        (ambientTripleTo23 k i j) (ambientTripleTo12 k i j)
        (ambientOverlapToLeft i j) (ambientOverlapToRight k i)
        (ambientTripleInner_isPullback k i j)
        (ambientLocalTwistModule d i)
        (ambientOverlapTwistModule d i j)
        (ambientRestrictLeftIso d i j).hom ≫
      (ambientPairToTripleIso23 d k i j).hom =
    (Scheme.Modules.restrictFunctor
        (ambientTripleTo12 k i j)).map
        (ambientRestrictRightIso d k i).hom ≫
      (ambientPairToTripleIso12 d k i j).hom := by
  simpa only [Scheme.Modules.unitRestrictionHom,
    ambientRestrictLeftIso, ambientRestrictRightIso,
    ambientPairToTripleIso12, ambientPairToTripleIso23,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.pullbackRestrictionHom_of_unit
      (ambientTripleTo23 k i j) (ambientTripleTo12 k i j)
      (ambientOverlapToLeft i j) (ambientOverlapToRight k i)
      (ambientTripleInner_isPullback k i j)
      (ambientLocalTwistModule d i)
      (ambientOverlapTwistModule d i j)
      (ambientOverlapTwistModule d k i)
      (ambientTripleTwistModule d k i j)
      (ambientLocalTwistUnitIso d i)
      (ambientOverlapTwistUnitIso d i j)
      (ambientOverlapTwistUnitIso d k i)
      (ambientTripleTwistUnitIso d k i j))

set_option backward.isDefEq.respectTransparency false in
/-- The unit trivializations on the two sides of the inner `(k,j,i)`
pullback square agree after transport to the fixed triple-overlap module. -/
theorem ambientUnitPullback13 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.pullbackRestrictionHom
        (ambientTripleTo23 k i j) (ambientTripleTo13 k i j)
        (ambientOverlapToRight i j) (ambientOverlapToRight k j)
        (ambientTripleInner13_isPullback k i j)
        (ambientLocalTwistModule d j)
        (ambientOverlapTwistModule d i j)
        (ambientRestrictRightIso d i j).hom ≫
      (ambientPairToTripleIso23 d k i j).hom =
    (Scheme.Modules.restrictFunctor
        (ambientTripleTo13 k i j)).map
        (ambientRestrictRightIso d k j).hom ≫
      (ambientPairToTripleIso13 d k i j).hom := by
  simpa only [Scheme.Modules.unitRestrictionHom, ambientRestrictRightIso,
    ambientPairToTripleIso13, ambientPairToTripleIso23,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.pullbackRestrictionHom_of_unit
      (ambientTripleTo23 k i j) (ambientTripleTo13 k i j)
      (ambientOverlapToRight i j) (ambientOverlapToRight k j)
      (ambientTripleInner13_isPullback k i j)
      (ambientLocalTwistModule d j)
      (ambientOverlapTwistModule d i j)
      (ambientOverlapTwistModule d k j)
      (ambientTripleTwistModule d k i j)
      (ambientLocalTwistUnitIso d j)
      (ambientOverlapTwistUnitIso d i j)
      (ambientOverlapTwistUnitIso d k j)
      (ambientTripleTwistUnitIso d k i j))

/-! ## Cancellation of adjacent descent trivializations

After the inner pullback square has been normalized, the right-hand
trivialization of the first descent leg meets its inverse on the second leg.
The following two coordinate forms expose that cancellation without unfolding
the surrounding restriction pseudofunctors.
-/

set_option backward.isDefEq.respectTransparency false in
/-- Along the `(k,i)` route, the right chart trivialization cancels after
restriction to the ordered triple overlap. -/
theorem ambientDescentCancel12
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (ambientTripleOverlapRing k i j))).Modules)
    (u : (Scheme.Modules.restrictFunctor
        (ambientTripleTo12 k i j)).obj
          (ambientOverlapTwistModule d k i) ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo12 k i j) (ambientOverlapToLeft k i)
        (ambientTripleToFirstChart k i j) rfl
        (ambientLocalTwistModule d k)
        ((Scheme.Modules.restrictFunctor
          (ambientOverlapToRight k i)).obj
            (ambientLocalTwistModule d i)) K
        (ambientDescentIso d k i).hom
        ((Scheme.Modules.restrictFunctor
          (ambientTripleTo12 k i j)).map
            (ambientRestrictRightIso d k i).hom ≫ u) =
      Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo12 k i j) (ambientOverlapToLeft k i)
        (ambientTripleToFirstChart k i j) rfl
        (ambientLocalTwistModule d k)
        (ambientOverlapTwistModule d k i) K
        ((ambientRestrictLeftIso d k i).hom ≫
          (ambientOverlapTwistIso d k i).hom) u := by
  simpa only [ambientDescentIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_cancel_iso
      (ambientTripleTo12 k i j) (ambientOverlapToLeft k i)
      (ambientTripleToFirstChart k i j) rfl
      (ambientLocalTwistModule d k)
      (ambientOverlapTwistModule d k i)
      ((Scheme.Modules.restrictFunctor
        (ambientOverlapToRight k i)).obj
          (ambientLocalTwistModule d i)) K
      ((ambientRestrictLeftIso d k i).hom ≫
        (ambientOverlapTwistIso d k i).hom)
      (ambientRestrictRightIso d k i) u)

set_option backward.isDefEq.respectTransparency false in
/-- Along the direct `(k,j)` route, the right chart trivialization cancels
after restriction to the ordered triple overlap. -/
theorem ambientDescentCancel13
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (ambientTripleOverlapRing k i j))).Modules)
    (u : (Scheme.Modules.restrictFunctor
        (ambientTripleTo13 k i j)).obj
          (ambientOverlapTwistModule d k j) ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo13 k i j) (ambientOverlapToLeft k j)
        (ambientTripleToFirstChart k i j)
        (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
        (ambientLocalTwistModule d k)
        ((Scheme.Modules.restrictFunctor
          (ambientOverlapToRight k j)).obj
            (ambientLocalTwistModule d j)) K
        (ambientDescentIso d k j).hom
        ((Scheme.Modules.restrictFunctor
          (ambientTripleTo13 k i j)).map
            (ambientRestrictRightIso d k j).hom ≫ u) =
      Scheme.Modules.iteratedRestrictionHom
        (ambientTripleTo13 k i j) (ambientOverlapToLeft k j)
        (ambientTripleToFirstChart k i j)
        (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
        (ambientLocalTwistModule d k)
        (ambientOverlapTwistModule d k j) K
        ((ambientRestrictLeftIso d k j).hom ≫
          (ambientOverlapTwistIso d k j).hom) u := by
  simpa only [ambientDescentIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_cancel_iso
      (ambientTripleTo13 k i j) (ambientOverlapToLeft k j)
      (ambientTripleToFirstChart k i j)
      (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
      (ambientLocalTwistModule d k)
      (ambientOverlapTwistModule d k j)
      ((Scheme.Modules.restrictFunctor
        (ambientOverlapToRight k j)).obj
          (ambientLocalTwistModule d j)) K
      ((ambientRestrictLeftIso d k j).hom ≫
        (ambientOverlapTwistIso d k j).hom)
      (ambientRestrictRightIso d k j) u)

set_option backward.isDefEq.respectTransparency false in
/-- One pair component of the family reconstructed from chart `k` satisfies
its Čech compatibility equation on the ordered overlap `(i,j)`.

The proof pulls both extensions by zero back to the triple overlap `(k,i,j)`,
transposes them along the smallest-open adjunction, and cancels the canonical
unit trivializations.  What remains is precisely the coordinate transition
cocycle proved above. -/
theorem ambientLocalReconstruction_pair
    (d : ℤ) (k i j : Fin 4) :
    ambientLocalReconstructionHom d k i ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (pushforwardRestrictionHom
            (ambientOverlapToLeft i j)
            (ambientChartMap i)
            (ambientOverlapMap i j)
            rfl
            (ambientLocalTwistModule d i)
            (ambientOverlapTwistModule d i j)
            (ambientRestrictLeftIso d i j ≪≫
              ambientOverlapTwistIso d i j)) =
      ambientLocalReconstructionHom d k j ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (pushforwardRestrictionHom
            (ambientOverlapToRight i j)
            (ambientChartMap j)
            (ambientOverlapMap i j)
            (ambientOverlapMap_eq_right i j)
            (ambientLocalTwistModule d j)
            (ambientOverlapTwistModule d i j)
            (ambientRestrictRightIso d i j)) := by
  rw [← cancel_mono (ambientTripleTwistBaseChangeIso d k i j).hom]
  have hleft0 :=
    Scheme.Modules.openBaseChange_pushforwardRestrictionHomOfHom_congr
      (iU := ambientChartMap k) (f := ambientChartMap i)
      (r := ambientTripleTo23 k i j)
      (q := ambientTripleTo12 k i j)
      (k := ambientOverlapToLeft i j)
      (b := ambientOverlapToRight k i)
      (a := ambientOverlapToLeft k i)
      (h := ambientOverlapMap i j)
      (g := ambientTripleToFirstChart k i j)
      rfl rfl
      (ambientTripleInner_isPullback k i j)
      (ambientOverlap_isPullback k i)
      (ambientTriple_isPullback k i j).flip
      (ambientLocalTwistModule d i)
      (ambientOverlapTwistModule d i j)
      (ambientRestrictLeftIso d i j ≪≫
        ambientOverlapTwistIso d i j).hom
  have hright0 :=
    Scheme.Modules.openBaseChange_pushforwardRestrictionHomOfHom_congr
      (iU := ambientChartMap k) (f := ambientChartMap j)
      (r := ambientTripleTo23 k i j)
      (q := ambientTripleTo13 k i j)
      (k := ambientOverlapToRight i j)
      (b := ambientOverlapToRight k j)
      (a := ambientOverlapToLeft k j)
      (h := ambientOverlapMap i j)
      (g := ambientTripleToFirstChart k i j)
      (ambientOverlapMap_eq_right i j)
      (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
      (ambientTripleInner13_isPullback k i j)
      (ambientOverlap_isPullback k j)
      (ambientTriple_isPullback k i j).flip
      (ambientLocalTwistModule d j)
      (ambientOverlapTwistModule d i j)
      (ambientRestrictRightIso d i j).hom
  dsimp only [ambientLocalReconstructionHom,
    ambientTripleTwistBaseChangeIso,
    ambientTripleBaseChangeIso, ambientLocalPushforwardBaseChangeIso]
  simp only [pushforwardRestrictionHom, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] at hleft0 hright0 ⊢
  slice_lhs 3 5 => rw [hleft0]
  slice_rhs 3 5 => rw [hright0]
  apply ((Scheme.Modules.restrictAdjunction
    (ambientTripleToFirstChart k i j)).homEquiv _ _).symm.injective
  have htransposeLeft :=
    Scheme.Modules.pushforwardRestrictionHomOfHom_transpose_comp
      (q := ambientTripleTo12 k i j)
      (a := ambientOverlapToLeft k i)
      (g := ambientTripleToFirstChart k i j)
      rfl
      (ambientLocalTwistModule d k)
      ((Scheme.Modules.restrictFunctor
        (ambientOverlapToRight k i)).obj
          (ambientLocalTwistModule d i))
      ((Scheme.Modules.restrictFunctor
        (ambientTripleTo23 k i j)).obj
          (ambientOverlapTwistModule d i j))
      (ambientTripleTwistModule d k i j)
      (ambientDescentIso d k i).hom
      (Scheme.Modules.pullbackRestrictionHom
        (ambientTripleTo23 k i j) (ambientTripleTo12 k i j)
        (ambientOverlapToLeft i j) (ambientOverlapToRight k i)
        (ambientTripleInner_isPullback k i j)
        (ambientLocalTwistModule d i)
        (ambientOverlapTwistModule d i j)
        ((ambientRestrictLeftIso d i j).hom ≫
          (ambientOverlapTwistIso d i j).hom))
      (ambientPairToTripleIso23 d k i j).hom
  have htransposeRight :=
    Scheme.Modules.pushforwardRestrictionHomOfHom_transpose_comp
      (q := ambientTripleTo13 k i j)
      (a := ambientOverlapToLeft k j)
      (g := ambientTripleToFirstChart k i j)
      (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k i j)
      (ambientLocalTwistModule d k)
      ((Scheme.Modules.restrictFunctor
        (ambientOverlapToRight k j)).obj
          (ambientLocalTwistModule d j))
      ((Scheme.Modules.restrictFunctor
        (ambientTripleTo23 k i j)).obj
          (ambientOverlapTwistModule d i j))
      (ambientTripleTwistModule d k i j)
      (ambientDescentIso d k j).hom
      (Scheme.Modules.pullbackRestrictionHom
        (ambientTripleTo23 k i j) (ambientTripleTo13 k i j)
        (ambientOverlapToRight i j) (ambientOverlapToRight k j)
        (ambientTripleInner13_isPullback k i j)
        (ambientLocalTwistModule d j)
        (ambientOverlapTwistModule d i j)
        (ambientRestrictRightIso d i j).hom)
      (ambientPairToTripleIso23 d k i j).hom
  simp only [Category.assoc] at htransposeLeft htransposeRight
  rw [htransposeLeft, htransposeRight]
  rw [Scheme.Modules.pullbackRestrictionHom_comp]
  rw [← (ambientPairToTripleIso23 d k i j).hom_inv_id_assoc
    ((Scheme.Modules.restrictFunctor
      (ambientTripleTo23 k i j)).map
        (ambientOverlapTwistIso d i j).hom)]
  rw [reassoc_of% ambientUnitPullback12]
  conv_rhs => rw [← Scheme.Modules.iteratedRestrictionHom_comp]
  rw [ambientUnitPullback13]
  rw [ambientDescentCancel12, ambientDescentCancel13]
  conv_lhs => rw [Scheme.Modules.iteratedRestrictionHom_middle_comp]
  conv_rhs => rw [Scheme.Modules.iteratedRestrictionHom_middle_comp]
  conv_lhs =>
    rw [← (ambientPairToTripleIso12 d k i j).hom_inv_id_assoc
      ((Scheme.Modules.restrictFunctor
        (ambientTripleTo12 k i j)).map
          (ambientOverlapTwistIso d k i).hom ≫
        (ambientPairToTripleIso12 d k i j).hom ≫
        (ambientPairToTripleIso23 d k i j).inv ≫
        (Scheme.Modules.restrictFunctor
          (ambientTripleTo23 k i j)).map
            (ambientOverlapTwistIso d i j).hom)]
  conv_rhs =>
    rw [← (ambientPairToTripleIso13 d k i j).hom_inv_id_assoc
      ((Scheme.Modules.restrictFunctor
        (ambientTripleTo13 k i j)).map
          (ambientOverlapTwistIso d k j).hom ≫
        (ambientPairToTripleIso13 d k i j).hom)]
  rw [ambientUnitRoute12_comp, ambientUnitRoute13_comp]
  simp only [Category.assoc]
  rw [cancel_epi
    ((Scheme.Modules.restrictFunctor
      (ambientTripleToFirstChart k i j)).map
        (ambientLocalTwistUnitIso d k).hom)]
  rw [cancel_epi
    (Scheme.Modules.restrictUnitIso
      (ambientTripleToFirstChart k i j)).hom]
  rw [cancel_epi (ambientTripleTwistUnitIso d k i j).inv]
  simpa only [Category.assoc] using
    ambientRestrictedOverlapTwistIso_cocycle d k i j

/-- The restricted overlap-product comparison intertwines each product
projection with restriction of the corresponding global projection. -/
@[reassoc]
theorem restrictedTwistCechTargetIso_hom_π
    (d : ℤ) (k : Fin 4) (p : Fin 4 × Fin 4) :
    (restrictedTwistCechTargetIso d k).hom ≫
        Pi.π (fun q : Fin 4 × Fin 4 ↦
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
            (ambientOverlapPushforward d q)) p =
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (Pi.π (fun q : Fin 4 × Fin 4 ↦
          ambientOverlapPushforward d q) p) := by
  exact piComparison_comp_π
    (Scheme.Modules.restrictFunctor (ambientChartMap k))
    (fun q : Fin 4 × Fin 4 ↦ ambientOverlapPushforward d q) p

/-- The product family reconstructed from chart `k` satisfies every
restricted Čech equation, hence defines an object of the restricted
equalizer.  Product extensionality reduces the assertion to
`ambientLocalReconstruction_pair` for each ordered pair. -/
theorem ambientLocalReconstruction_compatibility
    (d : ℤ) (k : Fin 4) :
    ambientLocalReconstruction d k ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (twistCechLeft d) =
      ambientLocalReconstruction d k ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (twistCechRight d) := by
  rw [← cancel_mono (restrictedTwistCechTargetIso d k).hom]
  apply Pi.hom_ext _ _
  intro p
  simp only [Category.assoc]
  rw [restrictedTwistCechTargetIso_hom_π]
  rw [← Functor.map_comp, ← Functor.map_comp]
  unfold twistCechLeft twistCechRight
  rw [Pi.lift_π, Pi.lift_π]
  rw [Functor.map_comp, Functor.map_comp]
  unfold ambientLocalReconstruction
  simp only [Category.assoc]
  rw [restrictedTwistCechSourceIso_inv_map_π_assoc,
    restrictedTwistCechSourceIso_inv_map_π_assoc]
  simpa only [Pi.lift_π_assoc] using
    ambientLocalReconstruction_pair d k p.1 p.2

/-- The reconstructed compatible family, viewed as a section of the
restriction of the global Čech equalizer to chart `k`.  The first arrow is
the equalizer lift justified by the cocycle; the second transports it back
through preservation of the equalizer by open restriction. -/
def ambientLocalToRestrictedGlobalTwist (d : ℤ) (k : Fin 4) :
    ambientLocalTwistModule d k ⟶
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (globalTwistModule d) :=
  equalizer.lift (ambientLocalReconstruction d k)
      (ambientLocalReconstruction_compatibility d k) ≫
    (restrictedGlobalTwistCechIso d k).inv

/-- After returning to the restricted equalizer and forgetting compatibility,
the reconstructed section is the original product family. -/
@[reassoc]
theorem ambientLocalToRestrictedGlobalTwist_comp_comparison_ι
    (d : ℤ) (k : Fin 4) :
    ambientLocalToRestrictedGlobalTwist d k ≫
        (restrictedGlobalTwistCechIso d k).hom ≫
        equalizer.ι
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechRight d)) =
      ambientLocalReconstruction d k := by
  unfold ambientLocalToRestrictedGlobalTwist
  simp only [Category.assoc, Iso.inv_hom_id_assoc, equalizer.lift_ι]

/-! ## Diagonal evaluation

The remaining effectivity argument begins by evaluating a reconstructed
family back on its base chart.  This composite is automatically invertible:
the self-intersection projection is an isomorphism, and every other factor is
an explicitly named descent, base-change, or adjunction isomorphism.
-/

/-- Every factor in diagonal reconstruction is invertible: the self-overlap
projection, descent transition, Beck--Chevalley comparison, and chart counit. -/
theorem ambientLocalReconstruction_diagonal_isIso (d : ℤ) (i : Fin 4) :
    IsIso (ambientLocalReconstructionHom d i i ≫
      (Scheme.Modules.restrictAdjunction
        (ambientChartMap i)).counit.app
          (ambientLocalTwistModule d i)) := by
  haveI : IsIso ((Scheme.Modules.restrictAdjunction
      (ambientOverlapToLeft i i)).unit.app
        (ambientLocalTwistModule d i)) :=
    Scheme.Modules.restrictAdjunction_unit_app_isIso_of_isIso _ _
  let eUnit := asIso ((Scheme.Modules.restrictAdjunction
    (ambientOverlapToLeft i i)).unit.app
      (ambientLocalTwistModule d i))
  let eDescent := (Scheme.Modules.pushforward
    (ambientOverlapToLeft i i)).mapIso (ambientDescentIso d i i)
  let eBase := (ambientLocalPushforwardBaseChangeIso d i i).symm
  let eCounit := asIso ((Scheme.Modules.restrictAdjunction
    (ambientChartMap i)).counit.app
      (ambientLocalTwistModule d i))
  change IsIso ((eUnit ≪≫ eDescent ≪≫ eBase ≪≫ eCounit).hom)
  infer_instance

/-- The adjoint definition of local evaluation is restriction of the global
product projection followed by the counit of the open-immersion adjunction. -/
theorem globalTwistModuleToLocal_eq (d : ℤ) (k : Fin 4) :
    globalTwistModuleToLocal d k =
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
            Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) k) ≫
        (Scheme.Modules.restrictAdjunction
          (ambientChartMap k)).counit.app
            (ambientLocalTwistModule d k) := by
  unfold globalTwistModuleToLocal
  rw [Adjunction.homEquiv_counit]
  rfl

/-- Restriction of the global equalizer inclusion is the inclusion of the
restricted equalizer produced by preservation of limits. -/
@[reassoc]
theorem restrictedGlobalTwistCechIso_hom_ι (d : ℤ) (k : Fin 4) :
    (restrictedGlobalTwistCechIso d k).hom ≫
        equalizer.ι
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechRight d)) =
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (equalizer.ι (twistCechLeft d) (twistCechRight d)) := by
  exact equalizerComparison_comp_π
    (twistCechLeft d) (twistCechRight d)
    (Scheme.Modules.restrictFunctor (ambientChartMap k))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation after reconstruction reduces to the diagonal reconstructed
component followed by the adjunction counit. -/
theorem ambientLocalToRestrictedGlobalTwist_comp_evaluation
    (d : ℤ) (k : Fin 4) :
    ambientLocalToRestrictedGlobalTwist d k ≫
        globalTwistModuleToLocal d k =
      ambientLocalReconstructionHom d k k ≫
        (Scheme.Modules.restrictAdjunction
          (ambientChartMap k)).counit.app
            (ambientLocalTwistModule d k) := by
  calc
    _ = ambientLocalToRestrictedGlobalTwist d k ≫
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (equalizer.ι (twistCechLeft d) (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) k) ≫
          (Scheme.Modules.restrictAdjunction
            (ambientChartMap k)).counit.app
              (ambientLocalTwistModule d k) := by
        rw [globalTwistModuleToLocal_eq, Functor.map_comp]
        simp only [Category.assoc]
    _ = ambientLocalToRestrictedGlobalTwist d k ≫
          (restrictedGlobalTwistCechIso d k).hom ≫
          equalizer.ι
            ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
              (twistCechLeft d))
            ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
              (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) k) ≫
          (Scheme.Modules.restrictAdjunction
            (ambientChartMap k)).counit.app
              (ambientLocalTwistModule d k) := by
        rw [← restrictedGlobalTwistCechIso_hom_ι_assoc]
    _ = ambientLocalReconstruction d k ≫
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) k) ≫
          (Scheme.Modules.restrictAdjunction
            (ambientChartMap k)).counit.app
              (ambientLocalTwistModule d k) := by
        rw [ambientLocalToRestrictedGlobalTwist_comp_comparison_ι_assoc]
    _ = _ := by
      unfold ambientLocalReconstruction
      simp only [Category.assoc]
      rw [restrictedTwistCechSourceIso_inv_map_π_assoc]
      rw [Pi.lift_π_assoc]

/-- Reconstructing from chart `k` and evaluating there is an isomorphism.
The stronger statement that reconstruction itself is an isomorphism now
reduces to uniqueness of compatible families from their `k`-th component. -/
theorem ambientLocalToRestrictedGlobalTwist_comp_evaluation_isIso
    (d : ℤ) (k : Fin 4) :
    IsIso (ambientLocalToRestrictedGlobalTwist d k ≫
      globalTwistModuleToLocal d k) := by
  rw [ambientLocalToRestrictedGlobalTwist_comp_evaluation]
  exact ambientLocalReconstruction_diagonal_isIso d k

/-! ## Uniqueness and effectivity of compatible families

On the fixed chart `k`, the right Čech leg for `(k,i)` is invertible:
the triple overlap `(k,k,i)` is the self-pullback of the pair overlap.
Consequently every compatible family is determined by its `k`-th
component, which upgrades reconstruction to an isomorphism.
-/

/-- The right leg of the restricted Čech equation at `(k,i)`. -/
def ambientRestrictedCechRightHom (d : ℤ) (k i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (ambientLocalPushforward d i) ⟶
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (ambientOverlapPushforward d (k, i)) :=
  (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
    (pushforwardRestrictionHom
      (ambientOverlapToRight k i)
      (ambientChartMap i)
      (ambientOverlapMap k i)
      (ambientOverlapMap_eq_right k i)
      (ambientLocalTwistModule d i)
      (ambientOverlapTwistModule d k i)
      (ambientRestrictRightIso d k i))

/-- The left leg of the restricted Čech equation at `(k,i)`. -/
def ambientRestrictedCechLeftHom (d : ℤ) (k i : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (ambientLocalPushforward d k) ⟶
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (ambientOverlapPushforward d (k, i)) :=
  (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
    (pushforwardRestrictionHom
      (ambientOverlapToLeft k i)
      (ambientChartMap k)
      (ambientOverlapMap k i)
      rfl
      (ambientLocalTwistModule d k)
      (ambientOverlapTwistModule d k i)
      (ambientRestrictLeftIso d k i ≪≫
        ambientOverlapTwistIso d k i))

/-- The restricted equalizer condition projected to `(k,i)` says that its
`k`-th and `i`-th components agree after the two corresponding Čech legs. -/
@[reassoc]
theorem restrictedEqualizer_condition_component
    (d : ℤ) (k i : Fin 4) :
    equalizer.ι
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechRight d)) ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) k) ≫
        ambientRestrictedCechLeftHom d k i =
      equalizer.ι
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (twistCechRight d)) ≫
        (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
          (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) i) ≫
        ambientRestrictedCechRightHom d k i := by
  have h := congrArg
    (fun z => z ≫
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (Pi.π (fun p : Fin 4 × Fin 4 ↦
          ambientOverlapPushforward d p) (k, i)))
    (equalizer.condition
      ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (twistCechLeft d))
      ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (twistCechRight d)))
  simp only [Category.assoc, ← Functor.map_comp] at h
  unfold twistCechLeft twistCechRight at h
  rw [Pi.lift_π, Pi.lift_π] at h
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The explicit triple overlap `(k,k,i)` maps isomorphically to the pair
overlap `(k,i)`, since it is the self-pullback of an open immersion. -/
instance ambientTripleTo13SelfIsIso (k i : Fin 4) :
    IsIso (ambientTripleTo13 k k i) :=
  (ambientTripleInner13_isPullback k k i).isIso_snd_iso_of_mono

set_option maxHeartbeats 800000 in
/-- After base change, the right Čech leg is extension by zero along the
isomorphism from `(k,k,i)` to `(k,i)`, so it is invertible. -/
theorem ambientRestrictedCechRightHom_isIso
    (d : ℤ) (k i : Fin 4) :
    IsIso (ambientRestrictedCechRightHom d k i) := by
  let e := Scheme.Modules.pullbackRestrictionHom
    (ambientTripleTo23 k k i) (ambientTripleTo13 k k i)
    (ambientOverlapToRight k i) (ambientOverlapToRight k i)
    (ambientTripleInner13_isPullback k k i)
    (ambientLocalTwistModule d i)
    (ambientOverlapTwistModule d k i)
    (ambientRestrictRightIso d k i).hom
  haveI : IsIso e := by
    let eIso :=
      (Scheme.Modules.restrictFunctorComp
          (ambientTripleTo13 k k i)
          (ambientOverlapToRight k i)).symm.app
            (ambientLocalTwistModule d i) ≪≫
        (Scheme.Modules.restrictFunctorCongr
          (ambientTripleInner13_isPullback k k i).w.symm).app
            (ambientLocalTwistModule d i) ≪≫
        (Scheme.Modules.restrictFunctorComp
          (ambientTripleTo23 k k i)
          (ambientOverlapToRight k i)).app
            (ambientLocalTwistModule d i) ≪≫
        (Scheme.Modules.restrictFunctor
          (ambientTripleTo23 k k i)).mapIso
            (ambientRestrictRightIso d k i)
    change IsIso eIso.hom
    infer_instance
  haveI : IsIso ((Scheme.Modules.restrictAdjunction
      (ambientTripleTo13 k k i)).unit.app
        ((Scheme.Modules.restrictFunctor
          (ambientOverlapToRight k i)).obj
            (ambientLocalTwistModule d i))) :=
    Scheme.Modules.restrictAdjunction_unit_app_isIso_of_isIso _ _
  let rhs := Scheme.Modules.pushforwardRestrictionHomOfHom
    (ambientOverlapToLeft k i) (ambientTripleTo13 k k i)
    (ambientTripleToFirstChart k k i)
    (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k k i)
    ((Scheme.Modules.restrictFunctor
      (ambientOverlapToRight k i)).obj
        (ambientLocalTwistModule d i))
    ((Scheme.Modules.restrictFunctor
      (ambientTripleTo23 k k i)).obj
        (ambientOverlapTwistModule d k i)) e
  haveI : IsIso rhs := by
    let innerIso := asIso ((Scheme.Modules.restrictAdjunction
        (ambientTripleTo13 k k i)).unit.app
          ((Scheme.Modules.restrictFunctor
            (ambientOverlapToRight k i)).obj
              (ambientLocalTwistModule d i))) ≪≫
      (Scheme.Modules.pushforward
        (ambientTripleTo13 k k i)).mapIso (asIso e)
    let rhsIso :=
      (Scheme.Modules.pushforward
        (ambientOverlapToLeft k i)).mapIso innerIso ≪≫
      (Scheme.Modules.pushforwardComp
        (ambientTripleTo13 k k i)
        (ambientOverlapToLeft k i)).app
          ((Scheme.Modules.restrictFunctor
            (ambientTripleTo23 k k i)).obj
              (ambientOverlapTwistModule d k i)) ≪≫
      (Scheme.Modules.pushforwardCongr
        (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart
          k k i)).app
          ((Scheme.Modules.restrictFunctor
            (ambientTripleTo23 k k i)).obj
              (ambientOverlapTwistModule d k i))
    change IsIso rhsIso.hom
    infer_instance
  have h :=
    Scheme.Modules.openBaseChange_pushforwardRestrictionHomOfHom_congr
      (iU := ambientChartMap k) (f := ambientChartMap i)
      (r := ambientTripleTo23 k k i)
      (q := ambientTripleTo13 k k i)
      (k := ambientOverlapToRight k i)
      (b := ambientOverlapToRight k i)
      (a := ambientOverlapToLeft k i)
      (h := ambientOverlapMap k i)
      (g := ambientTripleToFirstChart k k i)
      (ambientOverlapMap_eq_right k i)
      (ambientTripleTo13_comp_left_eq_ambientTripleToFirstChart k k i)
      (ambientTripleInner13_isPullback k k i)
      (ambientOverlap_isPullback k i)
      (ambientTriple_isPullback k k i).flip
      (ambientLocalTwistModule d i)
      (ambientOverlapTwistModule d k i)
      (ambientRestrictRightIso d k i).hom
  change
    (ambientLocalPushforwardBaseChangeIso d k i).inv ≫
        ambientRestrictedCechRightHom d k i ≫
        (ambientTripleBaseChangeIso k k i
          (ambientOverlapTwistModule d k i)).hom = rhs at h
  have hfac :
      ((ambientLocalPushforwardBaseChangeIso d k i).inv ≫
          ambientRestrictedCechRightHom d k i) ≫
          (ambientTripleBaseChangeIso k k i
            (ambientOverlapTwistModule d k i)).hom = rhs := by
    simpa only [Category.assoc] using h
  haveI : IsIso
      ((ambientLocalPushforwardBaseChangeIso d k i).inv ≫
        ambientRestrictedCechRightHom d k i) :=
    IsIso.of_isIso_fac_right hfac
  exact IsIso.of_isIso_comp_left
    (ambientLocalPushforwardBaseChangeIso d k i).inv
    (ambientRestrictedCechRightHom d k i)

/-- The restricted source-product comparison intertwines its projections
with the restricted global product projections. -/
@[reassoc]
theorem restrictedTwistCechSourceIso_hom_π
    (d : ℤ) (k i : Fin 4) :
    (restrictedTwistCechSourceIso d k).hom ≫
        Pi.π (fun j : Fin 4 ↦
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
            (ambientLocalPushforward d j)) i =
      (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) i) := by
  exact piComparison_comp_π
    (Scheme.Modules.restrictFunctor (ambientChartMap k))
    (fun j : Fin 4 ↦ ambientLocalPushforward d j) i

set_option backward.isDefEq.respectTransparency false in
/-- A compatible restricted family is determined by its component on chart
`k`.  The `(k,i)` equalizer equation recovers every other component because
its right Čech leg is an isomorphism. -/
theorem globalTwistModuleToLocal_mono (d : ℤ) (k : Fin 4) :
    Mono (globalTwistModuleToLocal d k) := by
  constructor
  intro Z u v huv
  have hk :
      u ≫ (restrictedGlobalTwistCechIso d k).hom ≫
          equalizer.ι
            ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
              (twistCechLeft d))
            ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
              (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) k) =
        v ≫ (restrictedGlobalTwistCechIso d k).hom ≫
          equalizer.ι
            ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
              (twistCechLeft d))
            ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
              (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (ambientChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ ambientLocalPushforward d j) k) := by
    rw [globalTwistModuleToLocal_eq, Functor.map_comp] at huv
    simp only [Category.assoc] at huv ⊢
    have hc := congrArg
      (fun z => z ≫ inv
        ((Scheme.Modules.restrictAdjunction
          (ambientChartMap k)).counit.app
            (ambientLocalTwistModule d k))) huv
    simp only [Category.assoc] at hc
    rw [IsIso.hom_inv_id] at hc
    simp only [Category.comp_id] at hc
    simpa only [restrictedGlobalTwistCechIso_hom_ι_assoc] using hc
  rw [← cancel_mono (restrictedGlobalTwistCechIso d k).hom]
  rw [← cancel_mono
    (equalizer.ι
      ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (twistCechLeft d))
      ((Scheme.Modules.restrictFunctor (ambientChartMap k)).map
        (twistCechRight d)))]
  rw [← cancel_mono (restrictedTwistCechSourceIso d k).hom]
  apply Pi.hom_ext _ _
  intro i
  simp only [Category.assoc]
  rw [restrictedTwistCechSourceIso_hom_π]
  letI := ambientRestrictedCechRightHom_isIso d k i
  rw [← cancel_mono (ambientRestrictedCechRightHom d k i)]
  simp only [Category.assoc]
  rw [← restrictedEqualizer_condition_component]
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ ambientRestrictedCechLeftHom d k i) hk

/-- Reconstruction is an isomorphism.  Its composite with evaluation is
already invertible, while uniqueness makes evaluation monic; these two facts
give an explicit two-sided inverse to reconstruction. -/
theorem ambientLocalToRestrictedGlobalTwist_isIso
    (d : ℤ) (k : Fin 4) :
    IsIso (ambientLocalToRestrictedGlobalTwist d k) := by
  letI : Mono (globalTwistModuleToLocal d k) :=
    globalTwistModuleToLocal_mono d k
  letI : IsIso (ambientLocalToRestrictedGlobalTwist d k ≫
      globalTwistModuleToLocal d k) :=
    ambientLocalToRestrictedGlobalTwist_comp_evaluation_isIso d k
  refine IsIso.mk ⟨globalTwistModuleToLocal d k ≫
      inv (ambientLocalToRestrictedGlobalTwist d k ≫
        globalTwistModuleToLocal d k), ?_, ?_⟩
  · rw [← Category.assoc, IsIso.hom_inv_id]
  · rw [← cancel_mono (globalTwistModuleToLocal d k)]
    simp only [Category.assoc]
    rw [IsIso.inv_hom_id]
    simp only [Category.comp_id, Category.id_comp]

/-- Evaluation itself is invertible.  Reconstruction is invertible and its
composite with evaluation is the invertible diagonal self-overlap
identification, so two-out-of-three gives this claim. -/
theorem globalTwistModuleToLocal_isIso (d : ℤ) (k : Fin 4) :
    IsIso (globalTwistModuleToLocal d k) := by
  letI := ambientLocalToRestrictedGlobalTwist_isIso d k
  letI := ambientLocalToRestrictedGlobalTwist_comp_evaluation_isIso d k
  exact IsIso.of_isIso_comp_left
    (ambientLocalToRestrictedGlobalTwist d k)
    (globalTwistModuleToLocal d k)

/-- Restriction of the global Čech equalizer to chart `k` recovers the local
twisting module used to define the descent datum.  We use literal evaluation
as the comparison, so descended morphisms satisfy chartwise naturality
without an additional diagonal normalization. -/
def globalTwistModuleLocalIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (globalTwistModule d) ≅ ambientLocalTwistModule d k := by
  letI := globalTwistModuleToLocal_isIso d k
  exact asIso (globalTwistModuleToLocal d k)

/-- On every standard coordinate chart, the global twisting module is free
of rank one.  This is the local effectivity statement needed to use the Čech
equalizer as an invertible sheaf rather than merely a global module sheaf. -/
def globalTwistModuleLocalUnitIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (ambientChartMap k)).obj
        (globalTwistModule d) ≅
      SheafOfModules.unit (ambientChartScheme k).ringCatSheaf :=
  globalTwistModuleLocalIso d k ≪≫ ambientLocalTwistUnitIso d k


end MazurProof.RationalPointsN25QuotientTwoAmbientTwistingSheafGluing
