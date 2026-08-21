import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoTwistingDescent
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

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

/-- The explicit affine overlap, with its two localization maps, is the
cartesian intersection of the corresponding coordinate charts.  This is the
geometric square used by open base change below. -/
theorem coordinateOverlap_isPullback (i j : Fin 4) :
    IsPullback (coordinateOverlapToLeft i j)
      (coordinateOverlapToRight i j)
      (coordinateChartMap i) (coordinateChartMap j) := by
  refine (coordinateChosenPullback i j).isPullback.of_iso'
    (coordinateChosenPullbackIso i j).symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · simp
  · simp

/-- On a self-overlap the two maps to the repeated chart coincide. -/
theorem coordinateOverlapToLeft_self_eq_right (i : Fin 4) :
    coordinateOverlapToLeft i i = coordinateOverlapToRight i i := by
  unfold coordinateOverlapToLeft coordinateOverlapToRight
  rw [coordinateChosenPullback_self_p₁_eq_p₂]

/-- The projection from a chart's self-intersection back to that chart is an
isomorphism: it is the pullback of a monomorphism along itself, transported
through the chosen affine overlap isomorphism. -/
noncomputable instance coordinateOverlapToLeftSelfIsIso (i : Fin 4) :
    IsIso (coordinateOverlapToLeft i i) := by
  haveI : IsIso (coordinateChosenPullback i i).p₁ := by
    change IsIso (pullback.fst
      (coordinateChartMap i) (coordinateChartMap i))
    infer_instance
  unfold coordinateOverlapToLeft
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
def coordinateLocalPushforwardBaseChangeIso (d : ℤ) (k i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        ((Scheme.Modules.pushforward (coordinateChartMap i)).obj
          (coordinateLocalTwistModule d i)) ≅
      (Scheme.Modules.pushforward (coordinateOverlapToLeft k i)).obj
        ((Scheme.Modules.restrictFunctor
          (coordinateOverlapToRight k i)).obj
            (coordinateLocalTwistModule d i)) := by
  exact Scheme.Modules.openBaseChangeIso
    (coordinateOverlapToLeft k i) (coordinateOverlapToRight k i)
    (coordinateChartMap k) (coordinateChartMap i)
    (coordinateOverlap_isPullback k i) (coordinateLocalTwistModule d i)

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

/-! ## Triple overlaps as geometric pullbacks -/

/-- The triple overlap mapped to chart `k` through the `(k,i)` pair
intersection. -/
def coordinateTripleToFirstChart (k i j : Fin 4) :
    Spec (.of (coordinateTripleOverlapRing k i j)) ⟶
      coordinateChartScheme k :=
  coordinateTripleTo12 k i j ≫ coordinateOverlapToLeft k i

/-- The triple-overlap map to its first chart is an open immersion because
it is a composite of localization opens. -/
instance coordinateTripleToFirstChartIsOpenImmersion (k i j : Fin 4) :
    IsOpenImmersion (coordinateTripleToFirstChart k i j) := by
  dsimp [coordinateTripleToFirstChart]
  infer_instance

/-- A pair overlap is open in the projective curve through either chart. -/
instance coordinateOverlapMapIsOpenImmersion (i j : Fin 4) :
    IsOpenImmersion (coordinateOverlapMap i j) := by
  dsimp [coordinateOverlapMap]
  infer_instance

/-- In chart `i`, the overlap with chart `j` is the principal open where
the degree-zero ratio `x_j/x_i` is nonzero. -/
theorem coordinateOverlapToLeft_opensRange (i j : Fin 4) :
    (coordinateOverlapToLeft i j).opensRange =
      PrimeSpectrum.basicOpen
        (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j)) := by
  letI := (awayMap literalConePiece (f := coordinateClass i)
    (coordinateClass_mem_degreeOne j) rfl).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
      (coordinateOverlapRing i j) :=
    Away.isLocalization_mul (coordinateClass_mem_degreeOne i)
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  have hmap : coordinateOverlapToLeft i j =
      Spec.map (CommRingCat.ofHom (algebraMap
        (coordinateChartRing i) (coordinateOverlapRing i j))) := by
    dsimp [coordinateOverlapToLeft]
    exact coordinateChosenPullbackIso_inv_p₁ i j
  rw [hmap]
  exact PrimeSpectrum.localization_away_comap_range
    (coordinateOverlapRing i j) _

/-- Within the `(k,i)` overlap, imposing `x_j ≠ 0` gives the ordered
triple overlap. -/
theorem coordinateTripleTo12_opensRange (k i j : Fin 4) :
    (coordinateTripleTo12 k i j).opensRange =
      PrimeSpectrum.basicOpen
        (Away.isLocalizationElem
          (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne k)
            (coordinateClass_mem_degreeOne i))
          (coordinateClass_mem_degreeOne j)) := by
  letI := (Away.restrict12 literalConePiece
    (f := coordinateClass k) (g := coordinateClass i)
    (h := coordinateClass j) (coordinateClass_mem_degreeOne j)).toAlgebra
  letI : IsLocalization.Away
      (Away.isLocalizationElem
        (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne k)
          (coordinateClass_mem_degreeOne i))
        (coordinateClass_mem_degreeOne j))
      (coordinateTripleOverlapRing k i j) :=
    Away.isLocalization_mul
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne k)
        (coordinateClass_mem_degreeOne i))
      (coordinateClass_mem_degreeOne j) rfl (by norm_num)
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  change Set.range (PrimeSpectrum.comap (algebraMap
      (coordinateOverlapRing k i) (coordinateTripleOverlapRing k i j))) = _
  exact PrimeSpectrum.localization_away_comap_range
    (coordinateTripleOverlapRing k i j) _

/-- The two iterated localization maps from the triple overlap to chart `i`
agree.  This is the affine associativity statement underlying the geometric
triple intersection. -/
theorem coordinateTripleTo12_comp_right_eq_coordinateTripleTo23_comp_left
    (k i j : Fin 4) :
    coordinateTripleTo12 k i j ≫ coordinateOverlapToRight k i =
      coordinateTripleTo23 k i j ≫ coordinateOverlapToLeft i j := by
  dsimp [coordinateOverlapToRight, coordinateOverlapToLeft]
  rw [coordinateChosenPullbackIso_inv_p₂,
    coordinateChosenPullbackIso_inv_p₁]
  dsimp [coordinateTripleTo12, coordinateTripleTo23, Away.restrict12,
    Away.restrict23]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change
    Away.restrict12 literalConePiece (coordinateClass_mem_degreeOne j)
        (awayMap literalConePiece (coordinateClass_mem_degreeOne k)
          (mul_comm _ _) x) =
      Away.restrict23 literalConePiece (coordinateClass_mem_degreeOne k)
        (awayMap literalConePiece (coordinateClass_mem_degreeOne j) rfl x)
  obtain ⟨q, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    literalConePiece (coordinateClass_mem_degreeOne i) x
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
theorem coordinateTripleInner_isPullback (k i j : Fin 4) :
    IsPullback (coordinateTripleTo23 k i j)
      (coordinateTripleTo12 k i j)
      (coordinateOverlapToLeft i j) (coordinateOverlapToRight k i) := by
  refine IsOpenImmersion.isPullback _ _ _ _
    (coordinateTripleTo12_comp_right_eq_coordinateTripleTo23_comp_left k i j)
    ?_
  guard_target =
    coordinateOverlapToRight k i ⁻¹ᵁ
        (coordinateOverlapToLeft i j).opensRange =
      (coordinateTripleTo12 k i j).opensRange
  rw [coordinateOverlapToLeft_opensRange,
    coordinateTripleTo12_opensRange]
  letI := (awayMap literalConePiece (f := coordinateClass i)
    (coordinateClass_mem_degreeOne k) (mul_comm _ _)).toAlgebra
  have hmap : coordinateOverlapToRight k i =
      Spec.map (CommRingCat.ofHom (algebraMap
        (coordinateChartRing i) (coordinateOverlapRing k i))) := by
    dsimp [coordinateOverlapToRight]
    exact coordinateChosenPullbackIso_inv_p₂ k i
  rw [hmap]
  change PrimeSpectrum.basicOpen
      (awayMap literalConePiece (coordinateClass_mem_degreeOne k)
        (mul_comm _ _)
        (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
          (coordinateClass_mem_degreeOne j))) = _
  let a : coordinateOverlapRing k i :=
    awayMap literalConePiece (coordinateClass_mem_degreeOne k)
      (mul_comm _ _)
      (Away.isLocalizationElem (coordinateClass_mem_degreeOne i)
        (coordinateClass_mem_degreeOne j))
  let b : coordinateOverlapRing k i :=
    Away.isLocalizationElem
      (SetLike.mul_mem_graded (coordinateClass_mem_degreeOne k)
        (coordinateClass_mem_degreeOne i))
      (coordinateClass_mem_degreeOne j)
  let u : (coordinateOverlapRing k i)ˣ :=
    Away.degreeOneRatioUnit literalConePiece
      (coordinateClass_mem_degreeOne k) (coordinateClass_mem_degreeOne i)
  change PrimeSpectrum.basicOpen a = PrimeSpectrum.basicOpen b
  have hab : b = a ^ 2 * (u : coordinateOverlapRing k i) := by
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
  have hu : PrimeSpectrum.basicOpen (u : coordinateOverlapRing k i) = ⊤ := by
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
theorem coordinateTriple_isPullback (k i j : Fin 4) :
    IsPullback (coordinateTripleTo23 k i j)
      (coordinateTripleToFirstChart k i j)
      (coordinateOverlapMap i j) (coordinateChartMap k) := by
  simpa only [coordinateTripleToFirstChart, coordinateOverlapMap] using
    (coordinateTripleInner_isPullback k i j).paste_vert
      (coordinateOverlap_isPullback k i).flip

/-- The two localization routes from the ordered triple overlap to its third
chart agree.  On affine rings this is associativity of homogeneous
localization; the proof compares the two maps on a common fraction
representative. -/
theorem coordinateTripleTo23_comp_right_eq_coordinateTripleTo13_comp_right
    (k i j : Fin 4) :
    coordinateTripleTo23 k i j ≫ coordinateOverlapToRight i j =
      coordinateTripleTo13 k i j ≫ coordinateOverlapToRight k j := by
  dsimp [coordinateOverlapToRight]
  rw [coordinateChosenPullbackIso_inv_p₂ i j,
    coordinateChosenPullbackIso_inv_p₂ k j]
  dsimp [coordinateTripleTo23, coordinateTripleTo13, Away.restrict23,
    Away.restrict13]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change
    Away.restrict23 literalConePiece (coordinateClass_mem_degreeOne k)
        (awayMap literalConePiece (coordinateClass_mem_degreeOne i)
          (mul_comm _ _) x) =
      Away.restrict13 literalConePiece (coordinateClass_mem_degreeOne i)
        (awayMap literalConePiece (coordinateClass_mem_degreeOne k)
          (mul_comm _ _) x)
  obtain ⟨q, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    literalConePiece (coordinateClass_mem_degreeOne j) x
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
theorem coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart
    (k i j : Fin 4) :
    coordinateTripleTo13 k i j ≫ coordinateOverlapToLeft k j =
      coordinateTripleToFirstChart k i j := by
  rw [← cancel_mono (coordinateChartMap k)]
  simp only [Category.assoc]
  calc
    coordinateTripleTo13 k i j ≫ coordinateOverlapToLeft k j ≫
          coordinateChartMap k =
        coordinateTripleTo13 k i j ≫ coordinateOverlapMap k j := rfl
    _ = coordinateTripleTo13 k i j ≫ coordinateOverlapToRight k j ≫
          coordinateChartMap j := by
      rw [coordinateOverlapMap_eq_right]
    _ = coordinateTripleTo23 k i j ≫ coordinateOverlapToRight i j ≫
          coordinateChartMap j := by
      slice_lhs 1 2 =>
        rw [← coordinateTripleTo23_comp_right_eq_coordinateTripleTo13_comp_right]
      rw [Category.assoc]
    _ = coordinateTripleTo23 k i j ≫ coordinateOverlapMap i j := by
      rw [coordinateOverlapMap_eq_right]
    _ = coordinateTripleToFirstChart k i j ≫ coordinateChartMap k :=
      (coordinateTriple_isPullback k i j).w

/-- The alternative inner square through the `(k,j)` overlap is cartesian.
It is obtained by cancelling the cartesian outer `(k,j)` chart square from
the already cartesian triple-overlap square.  This supplies the second
factorization needed to compare Čech reconstruction paths. -/
theorem coordinateTripleInner13_isPullback (k i j : Fin 4) :
    IsPullback (coordinateTripleTo23 k i j)
      (coordinateTripleTo13 k i j)
      (coordinateOverlapToRight i j) (coordinateOverlapToRight k j) := by
  have hTotal : IsPullback (coordinateTripleTo23 k i j)
      (coordinateTripleTo13 k i j ≫ coordinateOverlapToLeft k j)
      (coordinateOverlapToRight i j ≫ coordinateChartMap j)
      (coordinateChartMap k) := by
    simpa only [
      coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart,
      coordinateOverlapMap_eq_right] using
      coordinateTriple_isPullback k i j
  exact hTotal.of_bot
    (coordinateTripleTo23_comp_right_eq_coordinateTripleTo13_comp_right
      k i j)
    (coordinateOverlap_isPullback k j).flip

/-- Restricting the `(i,j)` overlap's free rank-one sheaf gives the free
rank-one sheaf on the ordered triple overlap. -/
def coordinatePairToTripleIso12 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateTripleTo12 i j l)).obj
        (coordinateOverlapTwistModule d i j) ≅
      coordinateTripleTwistModule d i j l :=
  (Scheme.Modules.restrictFunctor (coordinateTripleTo12 i j l)).mapIso
      (coordinateOverlapTwistUnitIso d i j) ≪≫
    Scheme.Modules.restrictUnitIso (coordinateTripleTo12 i j l) ≪≫
    (coordinateTripleTwistUnitIso d i j l).symm

/-- Restricting the `(j,l)` overlap's free rank-one sheaf gives the same
triple-overlap sheaf. -/
def coordinatePairToTripleIso23 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateTripleTo23 i j l)).obj
        (coordinateOverlapTwistModule d j l) ≅
      coordinateTripleTwistModule d i j l :=
  (Scheme.Modules.restrictFunctor (coordinateTripleTo23 i j l)).mapIso
      (coordinateOverlapTwistUnitIso d j l) ≪≫
    Scheme.Modules.restrictUnitIso (coordinateTripleTo23 i j l) ≪≫
    (coordinateTripleTwistUnitIso d i j l).symm

/-- Restricting the `(i,l)` overlap's free rank-one sheaf gives the same
triple-overlap sheaf. -/
def coordinatePairToTripleIso13 (d : ℤ) (i j l : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateTripleTo13 i j l)).obj
        (coordinateOverlapTwistModule d i l) ≅
      coordinateTripleTwistModule d i j l :=
  (Scheme.Modules.restrictFunctor (coordinateTripleTo13 i j l)).mapIso
      (coordinateOverlapTwistUnitIso d i l) ≪≫
    Scheme.Modules.restrictUnitIso (coordinateTripleTo13 i j l) ≪≫
    (coordinateTripleTwistUnitIso d i j l).symm

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
  Scheme.Modules.pushforwardRestrictionHomOfHom
    (f := j) (k := k) (h := h) hk F G e.hom

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

/-! ## Base change from pair overlaps to triple overlaps -/

/-- Open base change along `U_k ⟶ X` identifies a pair-overlap
pushforward with the pushforward from the explicit triple overlap. -/
def coordinateTripleBaseChangeIso (k i j : Fin 4)
    (M : (Spec (.of (coordinateOverlapRing i j))).Modules) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        ((Scheme.Modules.pushforward (coordinateOverlapMap i j)).obj M) ≅
      (Scheme.Modules.pushforward (coordinateTripleToFirstChart k i j)).obj
        ((Scheme.Modules.restrictFunctor
          (coordinateTripleTo23 k i j)).obj M) := by
  exact Scheme.Modules.openBaseChangeIso
    (coordinateTripleToFirstChart k i j) (coordinateTripleTo23 k i j)
    (coordinateChartMap k) (coordinateOverlapMap i j)
    (coordinateTriple_isPullback k i j).flip M

/-- For the twisting sheaves, triple-overlap base change is transported to
the fixed free rank-one module used by the explicit cocycle theorem. -/
def coordinateTripleTwistBaseChangeIso (d : ℤ) (k i j : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (coordinateOverlapPushforward d (i, j)) ≅
      (Scheme.Modules.pushforward (coordinateTripleToFirstChart k i j)).obj
        (coordinateTripleTwistModule d k i j) :=
  coordinateTripleBaseChangeIso k i j
      (coordinateOverlapTwistModule d i j) ≪≫
    (Scheme.Modules.pushforward
      (coordinateTripleToFirstChart k i j)).mapIso
        (coordinatePairToTripleIso23 d k i j)

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
    (Scheme.Modules.restrictFunctor (coordinateChartMap i)).obj
        (globalTwistModule d) ⟶ coordinateLocalTwistModule d i :=
  ((Scheme.Modules.restrictAdjunction (coordinateChartMap i)).homEquiv
      (globalTwistModule d) (coordinateLocalTwistModule d i))
    |>.symm (equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
      Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Literal Čech evaluation satisfies the transition equation on every
ordered pair overlap.  Transposing both iterated restriction maps turns the
claim back into the corresponding component of the defining equalizer
equation. -/
theorem globalTwistModuleToLocal_pair_compatibility
    (d : ℤ) (i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToLeft i j) (coordinateChartMap i)
        (coordinateOverlapMap i j) rfl
        (globalTwistModule d) (coordinateLocalTwistModule d i)
        (coordinateOverlapTwistModule d i j)
        (globalTwistModuleToLocal d i)
        (coordinateRestrictLeftIso d i j ≪≫
          coordinateOverlapTwistIso d i j).hom =
      Scheme.Modules.iteratedRestrictionHom
        (coordinateOverlapToRight i j) (coordinateChartMap j)
        (coordinateOverlapMap i j) (coordinateOverlapMap_eq_right i j)
        (globalTwistModule d) (coordinateLocalTwistModule d j)
        (coordinateOverlapTwistModule d i j)
        (globalTwistModuleToLocal d j)
        (coordinateRestrictRightIso d i j).hom := by
  have h := congrArg
    (fun z => z ≫ Pi.π
      (fun p : Fin 4 × Fin 4 ↦ coordinateOverlapPushforward d p) (i, j))
    (globalTwistModule_compatibility d)
  simp only [twistCechLeft, twistCechRight, Category.assoc,
    Pi.lift_π] at h
  have heval (k : Fin 4) :
      (Scheme.Modules.restrictAdjunction
          (coordinateChartMap k)).unit.app (globalTwistModule d) ≫
        (Scheme.Modules.pushforward (coordinateChartMap k)).map
          (globalTwistModuleToLocal d k) =
      equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
        Pi.π (fun l : Fin 4 ↦ coordinateLocalPushforward d l) k := by
    change ((Scheme.Modules.restrictAdjunction
      (coordinateChartMap k)).homEquiv
        (globalTwistModule d) (coordinateLocalTwistModule d k))
          (globalTwistModuleToLocal d k) = _
    unfold globalTwistModuleToLocal
    exact Equiv.apply_symm_apply _ _
  rw [← Scheme.Modules.pushforwardRestrictionHomOfHom_transpose,
    ← Scheme.Modules.pushforwardRestrictionHomOfHom_transpose]
  simp only [← Category.assoc]
  rw [heval i, heval j]
  exact congrArg
    ((Scheme.Modules.restrictAdjunction
      (coordinateOverlapMap i j)).homEquiv
        (globalTwistModule d)
        (coordinateOverlapTwistModule d i j)).symm h

/-- Restriction carries the product of extended local sheaves to the product
of their restrictions on the fixed chart. -/
def restrictedTwistCechSourceIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (twistCechSource d) ≅
      ∏ᶜ fun i : Fin 4 ↦
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
          (coordinateLocalPushforward d i) :=
  PreservesProduct.iso
    (Scheme.Modules.restrictFunctor (coordinateChartMap k))
    (fun i : Fin 4 ↦ coordinateLocalPushforward d i)

/-- The inverse product comparison followed by a restricted projection is the
corresponding projection from the product of restricted factors. -/
@[reassoc (attr := simp)]
theorem restrictedTwistCechSourceIso_inv_map_π (d : ℤ) (k i : Fin 4) :
    (restrictedTwistCechSourceIso d k).inv ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) i) =
      Pi.π (fun j : Fin 4 ↦
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
          (coordinateLocalPushforward d j)) i := by
  rw [← piComparison_comp_π]
  exact (restrictedTwistCechSourceIso d k).inv_hom_id_assoc _

/-- Restriction similarly carries the overlap product to the product of its
restricted overlap factors. -/
def restrictedTwistCechTargetIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (twistCechTarget d) ≅
      ∏ᶜ fun p : Fin 4 × Fin 4 ↦
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
          (coordinateOverlapPushforward d p) :=
  PreservesProduct.iso
    (Scheme.Modules.restrictFunctor (coordinateChartMap k))
    (fun p : Fin 4 × Fin 4 ↦ coordinateOverlapPushforward d p)

/-- Restriction of the global Čech equalizer is the equalizer of the two
restricted Čech arrows. -/
def restrictedGlobalTwistCechIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (globalTwistModule d) ≅
      equalizer
        ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (twistCechLeft d))
        ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (twistCechRight d)) :=
  PreservesEqualizer.iso
    (Scheme.Modules.restrictFunctor (coordinateChartMap k))
    (twistCechLeft d) (twistCechRight d)

/-- A section on chart `k` determines its representative in the `i`-th
extended chart factor: restrict it to `U_k ∩ U_i`, transport by the descent
transition, push it forward inside `U_k`, and invert open base change. -/
def coordinateLocalReconstructionHom (d : ℤ) (k i : Fin 4) :
    coordinateLocalTwistModule d k ⟶
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (coordinateLocalPushforward d i) :=
  (Scheme.Modules.restrictAdjunction
      (coordinateOverlapToLeft k i)).unit.app
        (coordinateLocalTwistModule d k) ≫
    (Scheme.Modules.pushforward (coordinateOverlapToLeft k i)).map
      (coordinateDescentIso d k i).hom ≫
    (coordinateLocalPushforwardBaseChangeIso d k i).inv

/-- The representatives reconstructed from chart `k`, assembled into the
restricted product of all four local extension-by-zero factors. -/
def coordinateLocalReconstruction (d : ℤ) (k : Fin 4) :
    coordinateLocalTwistModule d k ⟶
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (twistCechSource d) :=
  Pi.lift (fun i : Fin 4 ↦ coordinateLocalReconstructionHom d k i) ≫
    (restrictedTwistCechSourceIso d k).inv

/-! ## Compatibility of reconstructed local families

The following lemmas normalize the two routes from a chart to a triple
overlap.  They keep base change, adjunction, unit trivializations, and the
coordinate cocycle as separate mathematical steps.
-/

set_option backward.isDefEq.respectTransparency false in
/-- Explicit unit trivializations compose along the first pair-to-triple
route. -/
theorem coordinateUnitRoute12 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo12 k i j) (coordinateOverlapToLeft k i)
        (coordinateTripleToFirstChart k i j) rfl
        (coordinateLocalTwistModule d k)
        (coordinateOverlapTwistModule d k i)
        (coordinateTripleTwistModule d k i j)
        (coordinateRestrictLeftIso d k i).hom
        (coordinatePairToTripleIso12 d k i j).hom =
      (Scheme.Modules.restrictFunctor
          (coordinateTripleToFirstChart k i j)).map
          (coordinateLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (coordinateTripleToFirstChart k i j)).hom ≫
        (coordinateTripleTwistUnitIso d k i j).inv := by
  simpa only [coordinateRestrictLeftIso,
    coordinatePairToTripleIso12, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_of_unit
      (q := coordinateTripleTo12 k i j)
      (a := coordinateOverlapToLeft k i)
      (g := coordinateTripleToFirstChart k i j)
      rfl
      (coordinateLocalTwistModule d k)
      (coordinateOverlapTwistModule d k i)
      (coordinateTripleTwistModule d k i j)
      (coordinateLocalTwistUnitIso d k)
      (coordinateOverlapTwistUnitIso d k i)
      (coordinateTripleTwistUnitIso d k i j))

set_option backward.isDefEq.respectTransparency false in
/-- Explicit unit trivializations also compose along the direct
first-to-third pair route to the same canonical triple-open map. -/
theorem coordinateUnitRoute13 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo13 k i j) (coordinateOverlapToLeft k j)
        (coordinateTripleToFirstChart k i j)
        (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
        (coordinateLocalTwistModule d k)
        (coordinateOverlapTwistModule d k j)
        (coordinateTripleTwistModule d k i j)
        (coordinateRestrictLeftIso d k j).hom
        (coordinatePairToTripleIso13 d k i j).hom =
      (Scheme.Modules.restrictFunctor
          (coordinateTripleToFirstChart k i j)).map
          (coordinateLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (coordinateTripleToFirstChart k i j)).hom ≫
        (coordinateTripleTwistUnitIso d k i j).inv := by
  simpa only [coordinateRestrictLeftIso,
    coordinatePairToTripleIso13, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_of_unit
      (q := coordinateTripleTo13 k i j)
      (a := coordinateOverlapToLeft k j)
      (g := coordinateTripleToFirstChart k i j)
      (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
      (coordinateLocalTwistModule d k)
      (coordinateOverlapTwistModule d k j)
      (coordinateTripleTwistModule d k i j)
      (coordinateLocalTwistUnitIso d k)
      (coordinateOverlapTwistUnitIso d k j)
      (coordinateTripleTwistUnitIso d k i j))

/-- The canonical first-pair unit route remains in normal form under any
further morphism out of the triple-overlap module. -/
theorem coordinateUnitRoute12_comp
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (coordinateTripleOverlapRing k i j))).Modules)
    (u : coordinateTripleTwistModule d k i j ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo12 k i j) (coordinateOverlapToLeft k i)
        (coordinateTripleToFirstChart k i j) rfl
        (coordinateLocalTwistModule d k)
        (coordinateOverlapTwistModule d k i) K
        (coordinateRestrictLeftIso d k i).hom
        ((coordinatePairToTripleIso12 d k i j).hom ≫ u) =
      ((Scheme.Modules.restrictFunctor
          (coordinateTripleToFirstChart k i j)).map
          (coordinateLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (coordinateTripleToFirstChart k i j)).hom ≫
        (coordinateTripleTwistUnitIso d k i j).inv) ≫ u := by
  rw [Scheme.Modules.iteratedRestrictionHom_comp, coordinateUnitRoute12]

/-- The direct first-to-third unit route has the analogous normal form under
postcomposition. -/
theorem coordinateUnitRoute13_comp
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (coordinateTripleOverlapRing k i j))).Modules)
    (u : coordinateTripleTwistModule d k i j ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo13 k i j) (coordinateOverlapToLeft k j)
        (coordinateTripleToFirstChart k i j)
        (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
        (coordinateLocalTwistModule d k)
        (coordinateOverlapTwistModule d k j) K
        (coordinateRestrictLeftIso d k j).hom
        ((coordinatePairToTripleIso13 d k i j).hom ≫ u) =
      ((Scheme.Modules.restrictFunctor
          (coordinateTripleToFirstChart k i j)).map
          (coordinateLocalTwistUnitIso d k).hom ≫
        (Scheme.Modules.restrictUnitIso
          (coordinateTripleToFirstChart k i j)).hom ≫
        (coordinateTripleTwistUnitIso d k i j).inv) ≫ u := by
  rw [Scheme.Modules.iteratedRestrictionHom_comp, coordinateUnitRoute13]

set_option backward.isDefEq.respectTransparency false in
/-- The unit trivializations on the two sides of the inner `(k,i,j)`
pullback square agree after transport to the fixed triple-overlap module. -/
theorem coordinateUnitPullback12 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.pullbackRestrictionHom
        (coordinateTripleTo23 k i j) (coordinateTripleTo12 k i j)
        (coordinateOverlapToLeft i j) (coordinateOverlapToRight k i)
        (coordinateTripleInner_isPullback k i j)
        (coordinateLocalTwistModule d i)
        (coordinateOverlapTwistModule d i j)
        (coordinateRestrictLeftIso d i j).hom ≫
      (coordinatePairToTripleIso23 d k i j).hom =
    (Scheme.Modules.restrictFunctor
        (coordinateTripleTo12 k i j)).map
        (coordinateRestrictRightIso d k i).hom ≫
      (coordinatePairToTripleIso12 d k i j).hom := by
  simpa only [Scheme.Modules.unitRestrictionHom,
    coordinateRestrictLeftIso, coordinateRestrictRightIso,
    coordinatePairToTripleIso12, coordinatePairToTripleIso23,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.pullbackRestrictionHom_of_unit
      (coordinateTripleTo23 k i j) (coordinateTripleTo12 k i j)
      (coordinateOverlapToLeft i j) (coordinateOverlapToRight k i)
      (coordinateTripleInner_isPullback k i j)
      (coordinateLocalTwistModule d i)
      (coordinateOverlapTwistModule d i j)
      (coordinateOverlapTwistModule d k i)
      (coordinateTripleTwistModule d k i j)
      (coordinateLocalTwistUnitIso d i)
      (coordinateOverlapTwistUnitIso d i j)
      (coordinateOverlapTwistUnitIso d k i)
      (coordinateTripleTwistUnitIso d k i j))

set_option backward.isDefEq.respectTransparency false in
/-- The unit trivializations on the two sides of the inner `(k,j,i)`
pullback square agree after transport to the fixed triple-overlap module. -/
theorem coordinateUnitPullback13 (d : ℤ) (k i j : Fin 4) :
    Scheme.Modules.pullbackRestrictionHom
        (coordinateTripleTo23 k i j) (coordinateTripleTo13 k i j)
        (coordinateOverlapToRight i j) (coordinateOverlapToRight k j)
        (coordinateTripleInner13_isPullback k i j)
        (coordinateLocalTwistModule d j)
        (coordinateOverlapTwistModule d i j)
        (coordinateRestrictRightIso d i j).hom ≫
      (coordinatePairToTripleIso23 d k i j).hom =
    (Scheme.Modules.restrictFunctor
        (coordinateTripleTo13 k i j)).map
        (coordinateRestrictRightIso d k j).hom ≫
      (coordinatePairToTripleIso13 d k i j).hom := by
  simpa only [Scheme.Modules.unitRestrictionHom, coordinateRestrictRightIso,
    coordinatePairToTripleIso13, coordinatePairToTripleIso23,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using
    (Scheme.Modules.pullbackRestrictionHom_of_unit
      (coordinateTripleTo23 k i j) (coordinateTripleTo13 k i j)
      (coordinateOverlapToRight i j) (coordinateOverlapToRight k j)
      (coordinateTripleInner13_isPullback k i j)
      (coordinateLocalTwistModule d j)
      (coordinateOverlapTwistModule d i j)
      (coordinateOverlapTwistModule d k j)
      (coordinateTripleTwistModule d k i j)
      (coordinateLocalTwistUnitIso d j)
      (coordinateOverlapTwistUnitIso d i j)
      (coordinateOverlapTwistUnitIso d k j)
      (coordinateTripleTwistUnitIso d k i j))

/-! ## Cancellation of adjacent descent trivializations

After the inner pullback square has been normalized, the right-hand
trivialization of the first descent leg meets its inverse on the second leg.
The following two coordinate forms expose that cancellation without unfolding
the surrounding restriction pseudofunctors.
-/

set_option backward.isDefEq.respectTransparency false in
/-- Along the `(k,i)` route, the right chart trivialization cancels after
restriction to the ordered triple overlap. -/
theorem coordinateDescentCancel12
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (coordinateTripleOverlapRing k i j))).Modules)
    (u : (Scheme.Modules.restrictFunctor
        (coordinateTripleTo12 k i j)).obj
          (coordinateOverlapTwistModule d k i) ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo12 k i j) (coordinateOverlapToLeft k i)
        (coordinateTripleToFirstChart k i j) rfl
        (coordinateLocalTwistModule d k)
        ((Scheme.Modules.restrictFunctor
          (coordinateOverlapToRight k i)).obj
            (coordinateLocalTwistModule d i)) K
        (coordinateDescentIso d k i).hom
        ((Scheme.Modules.restrictFunctor
          (coordinateTripleTo12 k i j)).map
            (coordinateRestrictRightIso d k i).hom ≫ u) =
      Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo12 k i j) (coordinateOverlapToLeft k i)
        (coordinateTripleToFirstChart k i j) rfl
        (coordinateLocalTwistModule d k)
        (coordinateOverlapTwistModule d k i) K
        ((coordinateRestrictLeftIso d k i).hom ≫
          (coordinateOverlapTwistIso d k i).hom) u := by
  simpa only [coordinateDescentIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_cancel_iso
      (coordinateTripleTo12 k i j) (coordinateOverlapToLeft k i)
      (coordinateTripleToFirstChart k i j) rfl
      (coordinateLocalTwistModule d k)
      (coordinateOverlapTwistModule d k i)
      ((Scheme.Modules.restrictFunctor
        (coordinateOverlapToRight k i)).obj
          (coordinateLocalTwistModule d i)) K
      ((coordinateRestrictLeftIso d k i).hom ≫
        (coordinateOverlapTwistIso d k i).hom)
      (coordinateRestrictRightIso d k i) u)

set_option backward.isDefEq.respectTransparency false in
/-- Along the direct `(k,j)` route, the right chart trivialization cancels
after restriction to the ordered triple overlap. -/
theorem coordinateDescentCancel13
    (d : ℤ) (k i j : Fin 4)
    (K : (Spec (.of (coordinateTripleOverlapRing k i j))).Modules)
    (u : (Scheme.Modules.restrictFunctor
        (coordinateTripleTo13 k i j)).obj
          (coordinateOverlapTwistModule d k j) ⟶ K) :
    Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo13 k i j) (coordinateOverlapToLeft k j)
        (coordinateTripleToFirstChart k i j)
        (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
        (coordinateLocalTwistModule d k)
        ((Scheme.Modules.restrictFunctor
          (coordinateOverlapToRight k j)).obj
            (coordinateLocalTwistModule d j)) K
        (coordinateDescentIso d k j).hom
        ((Scheme.Modules.restrictFunctor
          (coordinateTripleTo13 k i j)).map
            (coordinateRestrictRightIso d k j).hom ≫ u) =
      Scheme.Modules.iteratedRestrictionHom
        (coordinateTripleTo13 k i j) (coordinateOverlapToLeft k j)
        (coordinateTripleToFirstChart k i j)
        (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
        (coordinateLocalTwistModule d k)
        (coordinateOverlapTwistModule d k j) K
        ((coordinateRestrictLeftIso d k j).hom ≫
          (coordinateOverlapTwistIso d k j).hom) u := by
  simpa only [coordinateDescentIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using
    (Scheme.Modules.iteratedRestrictionHom_cancel_iso
      (coordinateTripleTo13 k i j) (coordinateOverlapToLeft k j)
      (coordinateTripleToFirstChart k i j)
      (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
      (coordinateLocalTwistModule d k)
      (coordinateOverlapTwistModule d k j)
      ((Scheme.Modules.restrictFunctor
        (coordinateOverlapToRight k j)).obj
          (coordinateLocalTwistModule d j)) K
      ((coordinateRestrictLeftIso d k j).hom ≫
        (coordinateOverlapTwistIso d k j).hom)
      (coordinateRestrictRightIso d k j) u)

set_option backward.isDefEq.respectTransparency false in
/-- One pair component of the family reconstructed from chart `k` satisfies
its Čech compatibility equation on the ordered overlap `(i,j)`.

The proof pulls both extensions by zero back to the triple overlap `(k,i,j)`,
transposes them along the smallest-open adjunction, and cancels the canonical
unit trivializations.  What remains is precisely the coordinate transition
cocycle proved above. -/
theorem coordinateLocalReconstruction_pair
    (d : ℤ) (k i j : Fin 4) :
    coordinateLocalReconstructionHom d k i ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (pushforwardRestrictionHom
            (coordinateOverlapToLeft i j)
            (coordinateChartMap i)
            (coordinateOverlapMap i j)
            rfl
            (coordinateLocalTwistModule d i)
            (coordinateOverlapTwistModule d i j)
            (coordinateRestrictLeftIso d i j ≪≫
              coordinateOverlapTwistIso d i j)) =
      coordinateLocalReconstructionHom d k j ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (pushforwardRestrictionHom
            (coordinateOverlapToRight i j)
            (coordinateChartMap j)
            (coordinateOverlapMap i j)
            (coordinateOverlapMap_eq_right i j)
            (coordinateLocalTwistModule d j)
            (coordinateOverlapTwistModule d i j)
            (coordinateRestrictRightIso d i j)) := by
  rw [← cancel_mono (coordinateTripleTwistBaseChangeIso d k i j).hom]
  have hleft0 :=
    Scheme.Modules.openBaseChange_pushforwardRestrictionHomOfHom_congr
      (iU := coordinateChartMap k) (f := coordinateChartMap i)
      (r := coordinateTripleTo23 k i j)
      (q := coordinateTripleTo12 k i j)
      (k := coordinateOverlapToLeft i j)
      (b := coordinateOverlapToRight k i)
      (a := coordinateOverlapToLeft k i)
      (h := coordinateOverlapMap i j)
      (g := coordinateTripleToFirstChart k i j)
      rfl rfl
      (coordinateTripleInner_isPullback k i j)
      (coordinateOverlap_isPullback k i)
      (coordinateTriple_isPullback k i j).flip
      (coordinateLocalTwistModule d i)
      (coordinateOverlapTwistModule d i j)
      (coordinateRestrictLeftIso d i j ≪≫
        coordinateOverlapTwistIso d i j).hom
  have hright0 :=
    Scheme.Modules.openBaseChange_pushforwardRestrictionHomOfHom_congr
      (iU := coordinateChartMap k) (f := coordinateChartMap j)
      (r := coordinateTripleTo23 k i j)
      (q := coordinateTripleTo13 k i j)
      (k := coordinateOverlapToRight i j)
      (b := coordinateOverlapToRight k j)
      (a := coordinateOverlapToLeft k j)
      (h := coordinateOverlapMap i j)
      (g := coordinateTripleToFirstChart k i j)
      (coordinateOverlapMap_eq_right i j)
      (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
      (coordinateTripleInner13_isPullback k i j)
      (coordinateOverlap_isPullback k j)
      (coordinateTriple_isPullback k i j).flip
      (coordinateLocalTwistModule d j)
      (coordinateOverlapTwistModule d i j)
      (coordinateRestrictRightIso d i j).hom
  dsimp only [coordinateLocalReconstructionHom,
    coordinateTripleTwistBaseChangeIso,
    coordinateTripleBaseChangeIso, coordinateLocalPushforwardBaseChangeIso]
  simp only [pushforwardRestrictionHom, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] at hleft0 hright0 ⊢
  slice_lhs 3 5 => rw [hleft0]
  slice_rhs 3 5 => rw [hright0]
  apply ((Scheme.Modules.restrictAdjunction
    (coordinateTripleToFirstChart k i j)).homEquiv _ _).symm.injective
  have htransposeLeft :=
    Scheme.Modules.pushforwardRestrictionHomOfHom_transpose_comp
      (q := coordinateTripleTo12 k i j)
      (a := coordinateOverlapToLeft k i)
      (g := coordinateTripleToFirstChart k i j)
      rfl
      (coordinateLocalTwistModule d k)
      ((Scheme.Modules.restrictFunctor
        (coordinateOverlapToRight k i)).obj
          (coordinateLocalTwistModule d i))
      ((Scheme.Modules.restrictFunctor
        (coordinateTripleTo23 k i j)).obj
          (coordinateOverlapTwistModule d i j))
      (coordinateTripleTwistModule d k i j)
      (coordinateDescentIso d k i).hom
      (Scheme.Modules.pullbackRestrictionHom
        (coordinateTripleTo23 k i j) (coordinateTripleTo12 k i j)
        (coordinateOverlapToLeft i j) (coordinateOverlapToRight k i)
        (coordinateTripleInner_isPullback k i j)
        (coordinateLocalTwistModule d i)
        (coordinateOverlapTwistModule d i j)
        ((coordinateRestrictLeftIso d i j).hom ≫
          (coordinateOverlapTwistIso d i j).hom))
      (coordinatePairToTripleIso23 d k i j).hom
  have htransposeRight :=
    Scheme.Modules.pushforwardRestrictionHomOfHom_transpose_comp
      (q := coordinateTripleTo13 k i j)
      (a := coordinateOverlapToLeft k j)
      (g := coordinateTripleToFirstChart k i j)
      (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k i j)
      (coordinateLocalTwistModule d k)
      ((Scheme.Modules.restrictFunctor
        (coordinateOverlapToRight k j)).obj
          (coordinateLocalTwistModule d j))
      ((Scheme.Modules.restrictFunctor
        (coordinateTripleTo23 k i j)).obj
          (coordinateOverlapTwistModule d i j))
      (coordinateTripleTwistModule d k i j)
      (coordinateDescentIso d k j).hom
      (Scheme.Modules.pullbackRestrictionHom
        (coordinateTripleTo23 k i j) (coordinateTripleTo13 k i j)
        (coordinateOverlapToRight i j) (coordinateOverlapToRight k j)
        (coordinateTripleInner13_isPullback k i j)
        (coordinateLocalTwistModule d j)
        (coordinateOverlapTwistModule d i j)
        (coordinateRestrictRightIso d i j).hom)
      (coordinatePairToTripleIso23 d k i j).hom
  simp only [Category.assoc] at htransposeLeft htransposeRight
  rw [htransposeLeft, htransposeRight]
  rw [Scheme.Modules.pullbackRestrictionHom_comp]
  rw [← (coordinatePairToTripleIso23 d k i j).hom_inv_id_assoc
    ((Scheme.Modules.restrictFunctor
      (coordinateTripleTo23 k i j)).map
        (coordinateOverlapTwistIso d i j).hom)]
  rw [reassoc_of% coordinateUnitPullback12]
  conv_rhs => rw [← Scheme.Modules.iteratedRestrictionHom_comp]
  rw [coordinateUnitPullback13]
  rw [coordinateDescentCancel12, coordinateDescentCancel13]
  conv_lhs => rw [Scheme.Modules.iteratedRestrictionHom_middle_comp]
  conv_rhs => rw [Scheme.Modules.iteratedRestrictionHom_middle_comp]
  conv_lhs =>
    rw [← (coordinatePairToTripleIso12 d k i j).hom_inv_id_assoc
      ((Scheme.Modules.restrictFunctor
        (coordinateTripleTo12 k i j)).map
          (coordinateOverlapTwistIso d k i).hom ≫
        (coordinatePairToTripleIso12 d k i j).hom ≫
        (coordinatePairToTripleIso23 d k i j).inv ≫
        (Scheme.Modules.restrictFunctor
          (coordinateTripleTo23 k i j)).map
            (coordinateOverlapTwistIso d i j).hom)]
  conv_rhs =>
    rw [← (coordinatePairToTripleIso13 d k i j).hom_inv_id_assoc
      ((Scheme.Modules.restrictFunctor
        (coordinateTripleTo13 k i j)).map
          (coordinateOverlapTwistIso d k j).hom ≫
        (coordinatePairToTripleIso13 d k i j).hom)]
  rw [coordinateUnitRoute12_comp, coordinateUnitRoute13_comp]
  simp only [Category.assoc]
  rw [cancel_epi
    ((Scheme.Modules.restrictFunctor
      (coordinateTripleToFirstChart k i j)).map
        (coordinateLocalTwistUnitIso d k).hom)]
  rw [cancel_epi
    (Scheme.Modules.restrictUnitIso
      (coordinateTripleToFirstChart k i j)).hom]
  rw [cancel_epi (coordinateTripleTwistUnitIso d k i j).inv]
  simpa only [Category.assoc] using
    coordinateRestrictedOverlapTwistIso_cocycle d k i j

/-- The restricted overlap-product comparison intertwines each product
projection with restriction of the corresponding global projection. -/
@[reassoc]
theorem restrictedTwistCechTargetIso_hom_π
    (d : ℤ) (k : Fin 4) (p : Fin 4 × Fin 4) :
    (restrictedTwistCechTargetIso d k).hom ≫
        Pi.π (fun q : Fin 4 × Fin 4 ↦
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
            (coordinateOverlapPushforward d q)) p =
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (Pi.π (fun q : Fin 4 × Fin 4 ↦
          coordinateOverlapPushforward d q) p) := by
  exact piComparison_comp_π
    (Scheme.Modules.restrictFunctor (coordinateChartMap k))
    (fun q : Fin 4 × Fin 4 ↦ coordinateOverlapPushforward d q) p

/-- The product family reconstructed from chart `k` satisfies every
restricted Čech equation, hence defines an object of the restricted
equalizer.  Product extensionality reduces the assertion to
`coordinateLocalReconstruction_pair` for each ordered pair. -/
theorem coordinateLocalReconstruction_compatibility
    (d : ℤ) (k : Fin 4) :
    coordinateLocalReconstruction d k ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (twistCechLeft d) =
      coordinateLocalReconstruction d k ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
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
  unfold coordinateLocalReconstruction
  simp only [Category.assoc]
  rw [restrictedTwistCechSourceIso_inv_map_π_assoc,
    restrictedTwistCechSourceIso_inv_map_π_assoc]
  simpa only [Pi.lift_π_assoc] using
    coordinateLocalReconstruction_pair d k p.1 p.2

/-- The reconstructed compatible family, viewed as a section of the
restriction of the global Čech equalizer to chart `k`.  The first arrow is
the equalizer lift justified by the cocycle; the second transports it back
through preservation of the equalizer by open restriction. -/
def coordinateLocalToRestrictedGlobalTwist (d : ℤ) (k : Fin 4) :
    coordinateLocalTwistModule d k ⟶
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (globalTwistModule d) :=
  equalizer.lift (coordinateLocalReconstruction d k)
      (coordinateLocalReconstruction_compatibility d k) ≫
    (restrictedGlobalTwistCechIso d k).inv

/-- After returning to the restricted equalizer and forgetting compatibility,
the reconstructed section is the original product family. -/
@[reassoc]
theorem coordinateLocalToRestrictedGlobalTwist_comp_comparison_ι
    (d : ℤ) (k : Fin 4) :
    coordinateLocalToRestrictedGlobalTwist d k ≫
        (restrictedGlobalTwistCechIso d k).hom ≫
        equalizer.ι
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechRight d)) =
      coordinateLocalReconstruction d k := by
  unfold coordinateLocalToRestrictedGlobalTwist
  simp only [Category.assoc, Iso.inv_hom_id_assoc, equalizer.lift_ι]

/-! ## Diagonal evaluation

The remaining effectivity argument begins by evaluating a reconstructed
family back on its base chart.  This composite is automatically invertible:
the self-intersection projection is an isomorphism, and every other factor is
an explicitly named descent, base-change, or adjunction isomorphism.
-/

/-- Every factor in diagonal reconstruction is invertible: the self-overlap
projection, descent transition, Beck--Chevalley comparison, and chart counit. -/
theorem coordinateLocalReconstruction_diagonal_isIso (d : ℤ) (i : Fin 4) :
    IsIso (coordinateLocalReconstructionHom d i i ≫
      (Scheme.Modules.restrictAdjunction
        (coordinateChartMap i)).counit.app
          (coordinateLocalTwistModule d i)) := by
  haveI : IsIso ((Scheme.Modules.restrictAdjunction
      (coordinateOverlapToLeft i i)).unit.app
        (coordinateLocalTwistModule d i)) :=
    Scheme.Modules.restrictAdjunction_unit_app_isIso_of_isIso _ _
  let eUnit := asIso ((Scheme.Modules.restrictAdjunction
    (coordinateOverlapToLeft i i)).unit.app
      (coordinateLocalTwistModule d i))
  let eDescent := (Scheme.Modules.pushforward
    (coordinateOverlapToLeft i i)).mapIso (coordinateDescentIso d i i)
  let eBase := (coordinateLocalPushforwardBaseChangeIso d i i).symm
  let eCounit := asIso ((Scheme.Modules.restrictAdjunction
    (coordinateChartMap i)).counit.app
      (coordinateLocalTwistModule d i))
  change IsIso ((eUnit ≪≫ eDescent ≪≫ eBase ≪≫ eCounit).hom)
  infer_instance

/-- The adjoint definition of local evaluation is restriction of the global
product projection followed by the counit of the open-immersion adjunction. -/
theorem globalTwistModuleToLocal_eq (d : ℤ) (k : Fin 4) :
    globalTwistModuleToLocal d k =
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (equalizer.ι (twistCechLeft d) (twistCechRight d) ≫
            Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) k) ≫
        (Scheme.Modules.restrictAdjunction
          (coordinateChartMap k)).counit.app
            (coordinateLocalTwistModule d k) := by
  unfold globalTwistModuleToLocal
  rw [Adjunction.homEquiv_counit]
  rfl

/-- Restriction of the global equalizer inclusion is the inclusion of the
restricted equalizer produced by preservation of limits. -/
@[reassoc]
theorem restrictedGlobalTwistCechIso_hom_ι (d : ℤ) (k : Fin 4) :
    (restrictedGlobalTwistCechIso d k).hom ≫
        equalizer.ι
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechRight d)) =
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (equalizer.ι (twistCechLeft d) (twistCechRight d)) := by
  exact equalizerComparison_comp_π
    (twistCechLeft d) (twistCechRight d)
    (Scheme.Modules.restrictFunctor (coordinateChartMap k))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation after reconstruction reduces to the diagonal reconstructed
component followed by the adjunction counit. -/
theorem coordinateLocalToRestrictedGlobalTwist_comp_evaluation
    (d : ℤ) (k : Fin 4) :
    coordinateLocalToRestrictedGlobalTwist d k ≫
        globalTwistModuleToLocal d k =
      coordinateLocalReconstructionHom d k k ≫
        (Scheme.Modules.restrictAdjunction
          (coordinateChartMap k)).counit.app
            (coordinateLocalTwistModule d k) := by
  calc
    _ = coordinateLocalToRestrictedGlobalTwist d k ≫
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (equalizer.ι (twistCechLeft d) (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) k) ≫
          (Scheme.Modules.restrictAdjunction
            (coordinateChartMap k)).counit.app
              (coordinateLocalTwistModule d k) := by
        rw [globalTwistModuleToLocal_eq, Functor.map_comp]
        simp only [Category.assoc]
    _ = coordinateLocalToRestrictedGlobalTwist d k ≫
          (restrictedGlobalTwistCechIso d k).hom ≫
          equalizer.ι
            ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
              (twistCechLeft d))
            ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
              (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) k) ≫
          (Scheme.Modules.restrictAdjunction
            (coordinateChartMap k)).counit.app
              (coordinateLocalTwistModule d k) := by
        rw [← restrictedGlobalTwistCechIso_hom_ι_assoc]
    _ = coordinateLocalReconstruction d k ≫
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) k) ≫
          (Scheme.Modules.restrictAdjunction
            (coordinateChartMap k)).counit.app
              (coordinateLocalTwistModule d k) := by
        rw [coordinateLocalToRestrictedGlobalTwist_comp_comparison_ι_assoc]
    _ = _ := by
      unfold coordinateLocalReconstruction
      simp only [Category.assoc]
      rw [restrictedTwistCechSourceIso_inv_map_π_assoc]
      rw [Pi.lift_π_assoc]

/-- Reconstructing from chart `k` and evaluating there is an isomorphism.
The stronger statement that reconstruction itself is an isomorphism now
reduces to uniqueness of compatible families from their `k`-th component. -/
theorem coordinateLocalToRestrictedGlobalTwist_comp_evaluation_isIso
    (d : ℤ) (k : Fin 4) :
    IsIso (coordinateLocalToRestrictedGlobalTwist d k ≫
      globalTwistModuleToLocal d k) := by
  rw [coordinateLocalToRestrictedGlobalTwist_comp_evaluation]
  exact coordinateLocalReconstruction_diagonal_isIso d k

/-! ## Uniqueness and effectivity of compatible families

On the fixed chart `k`, the right Čech leg for `(k,i)` is invertible:
the triple overlap `(k,k,i)` is the self-pullback of the pair overlap.
Consequently every compatible family is determined by its `k`-th
component, which upgrades reconstruction to an isomorphism.
-/

/-- The right leg of the restricted Čech equation at `(k,i)`. -/
def coordinateRestrictedCechRightHom (d : ℤ) (k i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (coordinateLocalPushforward d i) ⟶
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (coordinateOverlapPushforward d (k, i)) :=
  (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
    (pushforwardRestrictionHom
      (coordinateOverlapToRight k i)
      (coordinateChartMap i)
      (coordinateOverlapMap k i)
      (coordinateOverlapMap_eq_right k i)
      (coordinateLocalTwistModule d i)
      (coordinateOverlapTwistModule d k i)
      (coordinateRestrictRightIso d k i))

/-- The left leg of the restricted Čech equation at `(k,i)`. -/
def coordinateRestrictedCechLeftHom (d : ℤ) (k i : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (coordinateLocalPushforward d k) ⟶
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (coordinateOverlapPushforward d (k, i)) :=
  (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
    (pushforwardRestrictionHom
      (coordinateOverlapToLeft k i)
      (coordinateChartMap k)
      (coordinateOverlapMap k i)
      rfl
      (coordinateLocalTwistModule d k)
      (coordinateOverlapTwistModule d k i)
      (coordinateRestrictLeftIso d k i ≪≫
        coordinateOverlapTwistIso d k i))

/-- The restricted equalizer condition projected to `(k,i)` says that its
`k`-th and `i`-th components agree after the two corresponding Čech legs. -/
@[reassoc]
theorem restrictedEqualizer_condition_component
    (d : ℤ) (k i : Fin 4) :
    equalizer.ι
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechRight d)) ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) k) ≫
        coordinateRestrictedCechLeftHom d k i =
      equalizer.ι
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechLeft d))
          ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (twistCechRight d)) ≫
        (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
          (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) i) ≫
        coordinateRestrictedCechRightHom d k i := by
  have h := congrArg
    (fun z => z ≫
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (Pi.π (fun p : Fin 4 × Fin 4 ↦
          coordinateOverlapPushforward d p) (k, i)))
    (equalizer.condition
      ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (twistCechLeft d))
      ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (twistCechRight d)))
  simp only [Category.assoc, ← Functor.map_comp] at h
  unfold twistCechLeft twistCechRight at h
  rw [Pi.lift_π, Pi.lift_π] at h
  rw [Functor.map_comp, Functor.map_comp] at h
  exact h

/-- The explicit triple overlap `(k,k,i)` maps isomorphically to the pair
overlap `(k,i)`, since it is the self-pullback of an open immersion. -/
instance coordinateTripleTo13SelfIsIso (k i : Fin 4) :
    IsIso (coordinateTripleTo13 k k i) :=
  (coordinateTripleInner13_isPullback k k i).isIso_snd_iso_of_mono

/-- After base change, the right Čech leg is extension by zero along the
isomorphism from `(k,k,i)` to `(k,i)`, so it is invertible. -/
theorem coordinateRestrictedCechRightHom_isIso
    (d : ℤ) (k i : Fin 4) :
    IsIso (coordinateRestrictedCechRightHom d k i) := by
  let e := Scheme.Modules.pullbackRestrictionHom
    (coordinateTripleTo23 k k i) (coordinateTripleTo13 k k i)
    (coordinateOverlapToRight k i) (coordinateOverlapToRight k i)
    (coordinateTripleInner13_isPullback k k i)
    (coordinateLocalTwistModule d i)
    (coordinateOverlapTwistModule d k i)
    (coordinateRestrictRightIso d k i).hom
  haveI : IsIso e := by
    let eIso :=
      (Scheme.Modules.restrictFunctorComp
          (coordinateTripleTo13 k k i)
          (coordinateOverlapToRight k i)).symm.app
            (coordinateLocalTwistModule d i) ≪≫
        (Scheme.Modules.restrictFunctorCongr
          (coordinateTripleInner13_isPullback k k i).w.symm).app
            (coordinateLocalTwistModule d i) ≪≫
        (Scheme.Modules.restrictFunctorComp
          (coordinateTripleTo23 k k i)
          (coordinateOverlapToRight k i)).app
            (coordinateLocalTwistModule d i) ≪≫
        (Scheme.Modules.restrictFunctor
          (coordinateTripleTo23 k k i)).mapIso
            (coordinateRestrictRightIso d k i)
    change IsIso eIso.hom
    infer_instance
  haveI : IsIso ((Scheme.Modules.restrictAdjunction
      (coordinateTripleTo13 k k i)).unit.app
        ((Scheme.Modules.restrictFunctor
          (coordinateOverlapToRight k i)).obj
            (coordinateLocalTwistModule d i))) :=
    Scheme.Modules.restrictAdjunction_unit_app_isIso_of_isIso _ _
  let rhs := Scheme.Modules.pushforwardRestrictionHomOfHom
    (coordinateOverlapToLeft k i) (coordinateTripleTo13 k k i)
    (coordinateTripleToFirstChart k k i)
    (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k k i)
    ((Scheme.Modules.restrictFunctor
      (coordinateOverlapToRight k i)).obj
        (coordinateLocalTwistModule d i))
    ((Scheme.Modules.restrictFunctor
      (coordinateTripleTo23 k k i)).obj
        (coordinateOverlapTwistModule d k i)) e
  haveI : IsIso rhs := by
    let innerIso := asIso ((Scheme.Modules.restrictAdjunction
        (coordinateTripleTo13 k k i)).unit.app
          ((Scheme.Modules.restrictFunctor
            (coordinateOverlapToRight k i)).obj
              (coordinateLocalTwistModule d i))) ≪≫
      (Scheme.Modules.pushforward
        (coordinateTripleTo13 k k i)).mapIso (asIso e)
    let rhsIso :=
      (Scheme.Modules.pushforward
        (coordinateOverlapToLeft k i)).mapIso innerIso ≪≫
      (Scheme.Modules.pushforwardComp
        (coordinateTripleTo13 k k i)
        (coordinateOverlapToLeft k i)).app
          ((Scheme.Modules.restrictFunctor
            (coordinateTripleTo23 k k i)).obj
              (coordinateOverlapTwistModule d k i)) ≪≫
      (Scheme.Modules.pushforwardCongr
        (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart
          k k i)).app
          ((Scheme.Modules.restrictFunctor
            (coordinateTripleTo23 k k i)).obj
              (coordinateOverlapTwistModule d k i))
    change IsIso rhsIso.hom
    infer_instance
  have h :=
    Scheme.Modules.openBaseChange_pushforwardRestrictionHomOfHom_congr
      (iU := coordinateChartMap k) (f := coordinateChartMap i)
      (r := coordinateTripleTo23 k k i)
      (q := coordinateTripleTo13 k k i)
      (k := coordinateOverlapToRight k i)
      (b := coordinateOverlapToRight k i)
      (a := coordinateOverlapToLeft k i)
      (h := coordinateOverlapMap k i)
      (g := coordinateTripleToFirstChart k k i)
      (coordinateOverlapMap_eq_right k i)
      (coordinateTripleTo13_comp_left_eq_coordinateTripleToFirstChart k k i)
      (coordinateTripleInner13_isPullback k k i)
      (coordinateOverlap_isPullback k i)
      (coordinateTriple_isPullback k k i).flip
      (coordinateLocalTwistModule d i)
      (coordinateOverlapTwistModule d k i)
      (coordinateRestrictRightIso d k i).hom
  change
    (coordinateLocalPushforwardBaseChangeIso d k i).inv ≫
        coordinateRestrictedCechRightHom d k i ≫
        (coordinateTripleBaseChangeIso k k i
          (coordinateOverlapTwistModule d k i)).hom = rhs at h
  rw [← isIso_comp_left_iff
    (coordinateLocalPushforwardBaseChangeIso d k i).inv]
  rw [← isIso_comp_right_iff _
    (coordinateTripleBaseChangeIso k k i
      (coordinateOverlapTwistModule d k i)).hom]
  rw [Category.assoc, h]
  infer_instance

/-- The restricted source-product comparison intertwines its projections
with the restricted global product projections. -/
@[reassoc]
theorem restrictedTwistCechSourceIso_hom_π
    (d : ℤ) (k i : Fin 4) :
    (restrictedTwistCechSourceIso d k).hom ≫
        Pi.π (fun j : Fin 4 ↦
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
            (coordinateLocalPushforward d j)) i =
      (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) i) := by
  exact piComparison_comp_π
    (Scheme.Modules.restrictFunctor (coordinateChartMap k))
    (fun j : Fin 4 ↦ coordinateLocalPushforward d j) i

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
            ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
              (twistCechLeft d))
            ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
              (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) k) =
        v ≫ (restrictedGlobalTwistCechIso d k).hom ≫
          equalizer.ι
            ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
              (twistCechLeft d))
            ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
              (twistCechRight d)) ≫
          (Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
            (Pi.π (fun j : Fin 4 ↦ coordinateLocalPushforward d j) k) := by
    rw [globalTwistModuleToLocal_eq, Functor.map_comp] at huv
    simp only [Category.assoc] at huv ⊢
    have hc := congrArg
      (fun z => z ≫ inv
        ((Scheme.Modules.restrictAdjunction
          (coordinateChartMap k)).counit.app
            (coordinateLocalTwistModule d k))) huv
    simp only [Category.assoc] at hc
    rw [IsIso.hom_inv_id] at hc
    simp only [Category.comp_id] at hc
    simpa only [restrictedGlobalTwistCechIso_hom_ι_assoc] using hc
  rw [← cancel_mono (restrictedGlobalTwistCechIso d k).hom]
  rw [← cancel_mono
    (equalizer.ι
      ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (twistCechLeft d))
      ((Scheme.Modules.restrictFunctor (coordinateChartMap k)).map
        (twistCechRight d)))]
  rw [← cancel_mono (restrictedTwistCechSourceIso d k).hom]
  apply Pi.hom_ext _ _
  intro i
  simp only [Category.assoc]
  rw [restrictedTwistCechSourceIso_hom_π]
  letI := coordinateRestrictedCechRightHom_isIso d k i
  rw [← cancel_mono (coordinateRestrictedCechRightHom d k i)]
  simp only [Category.assoc]
  rw [← restrictedEqualizer_condition_component]
  simpa only [Category.assoc] using congrArg
    (fun z => z ≫ coordinateRestrictedCechLeftHom d k i) hk

/-- Reconstruction is an isomorphism.  Its composite with evaluation is
already invertible, while uniqueness makes evaluation monic; these two facts
give an explicit two-sided inverse to reconstruction. -/
theorem coordinateLocalToRestrictedGlobalTwist_isIso
    (d : ℤ) (k : Fin 4) :
    IsIso (coordinateLocalToRestrictedGlobalTwist d k) := by
  letI : Mono (globalTwistModuleToLocal d k) :=
    globalTwistModuleToLocal_mono d k
  letI : IsIso (coordinateLocalToRestrictedGlobalTwist d k ≫
      globalTwistModuleToLocal d k) :=
    coordinateLocalToRestrictedGlobalTwist_comp_evaluation_isIso d k
  refine IsIso.mk ⟨globalTwistModuleToLocal d k ≫
      inv (coordinateLocalToRestrictedGlobalTwist d k ≫
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
  letI := coordinateLocalToRestrictedGlobalTwist_isIso d k
  letI := coordinateLocalToRestrictedGlobalTwist_comp_evaluation_isIso d k
  exact IsIso.of_isIso_comp_left
    (coordinateLocalToRestrictedGlobalTwist d k)
    (globalTwistModuleToLocal d k)

/-- Restriction of the global Čech equalizer to chart `k` recovers the local
twisting module used to define the descent datum.  We use literal evaluation
as the comparison, so descended morphisms satisfy chartwise naturality
without an additional diagonal normalization. -/
def globalTwistModuleLocalIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (globalTwistModule d) ≅ coordinateLocalTwistModule d k := by
  letI := globalTwistModuleToLocal_isIso d k
  exact asIso (globalTwistModuleToLocal d k)

/-- On every standard coordinate chart, the global twisting module is free
of rank one.  This is the local effectivity statement needed to use the Čech
equalizer as an invertible sheaf rather than merely a global module sheaf. -/
def globalTwistModuleLocalUnitIso (d : ℤ) (k : Fin 4) :
    (Scheme.Modules.restrictFunctor (coordinateChartMap k)).obj
        (globalTwistModule d) ≅
      SheafOfModules.unit (coordinateChartScheme k).ringCatSheaf :=
  globalTwistModuleLocalIso d k ≪≫ coordinateLocalTwistUnitIso d k


end MazurProof.RationalPointsN25QuotientTwoTwistingSheafGluing
