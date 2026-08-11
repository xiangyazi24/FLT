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
open RationalPointsN25QuotientTwoTwistingSheafCharts
open RationalPointsN25QuotientTwoTwistingDescent
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
