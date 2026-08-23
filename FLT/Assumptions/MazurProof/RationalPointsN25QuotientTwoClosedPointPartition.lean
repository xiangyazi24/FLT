import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrime

/-!
# Boundary/open partition of full binary closed points

The full closed-point carrier splits into the three explicit degree-one
points on `W = 0` and a complementary subtype.  Every complementary atom,
including the two degree-one points on `W != 0`, receives a nonzero
height-one maximal ideal of the fixed integral `w = 1` chart with the exact
residue cardinality dictated by its closed-point degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoClosedPointPartition

open CurveZetaFrobeniusOrbitGrading
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientMiddleRiemannRoch
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenOrbitPrime
open RationalPointsN25QuotientTwoPlaneChartClosedPoints

abbrev FullAtom25Two := fullClosedPointGrading25Two.Atom

/-- The three atoms on the complement of the fixed `W` chart. -/
def IsFullBoundaryAtom (A : FullAtom25Two) : Prop :=
  A = fullBoundaryAtomX ∨
    A = fullBoundaryAtomYZ ∨ A = fullBoundaryAtomZ

/-- The full closed-point atoms belonging to `W != 0`. -/
def FullNonBoundaryAtom25Two :=
  {A : FullAtom25Two // ¬ IsFullBoundaryAtom A}

/-- Forget that a full atom avoids the boundary. -/
def fullNonBoundaryAtomEmbedding : FullNonBoundaryAtom25Two ↪ FullAtom25Two :=
  Function.Embedding.subtype _

inductive FullBoundaryTag25Two
  | X
  | YZ
  | Z
deriving DecidableEq, Fintype

/-- The three boundary tags enumerate the explicit boundary atoms. -/
def fullBoundaryAtomOfTag : FullBoundaryTag25Two → FullAtom25Two
  | .X => fullBoundaryAtomX
  | .YZ => fullBoundaryAtomYZ
  | .Z => fullBoundaryAtomZ

/-- The boundary tags select pairwise distinct atoms. -/
theorem fullBoundaryAtomOfTag_injective :
    Function.Injective fullBoundaryAtomOfTag := by
  intro i j hij
  cases i <;> cases j
  · rfl
  · exact False.elim (fullBoundaryAtomX_ne_YZ hij)
  · exact False.elim (fullBoundaryAtomX_ne_Z hij)
  · exact False.elim (fullBoundaryAtomX_ne_YZ hij.symm)
  · rfl
  · exact False.elim (fullBoundaryAtomYZ_ne_Z hij)
  · exact False.elim (fullBoundaryAtomX_ne_Z hij.symm)
  · exact False.elim (fullBoundaryAtomYZ_ne_Z hij.symm)
  · rfl

/-- Data carried by the fixed-chart prime attached to a nonboundary closed
point. -/
structure WOpenPrimeData25Two (d : ℕ) where
  ideal : Ideal WChartQuotient
  ne_bot : ideal ≠ ⊥
  isMaximal : ideal.IsMaximal
  height_eq_one : ideal.height = 1
  residue_card : Nat.card (WChartQuotient ⧸ ideal) = 2 ^ d

private theorem wOpenEvalF2_surjective
    (P : CurvePointOnWOpen F2) :
    Function.Surjective (wOpenChartQuotientEval P) := by
  intro y
  refine ⟨algebraMap (ZMod 2) WChartQuotient y, ?_⟩
  exact (wOpenChartQuotientEvalAlgHom P).commutes y

/-- A prime-field point on `W != 0` supplies the degree-one instance of the
fixed-chart prime data. -/
noncomputable def degreeOneWOpenPrimeData
    (P : ExtensionIndex25Two.pointType .degreeOne)
    (hW : (normalizedCoordinates25 P.1).w ≠ 0) :
    WOpenPrimeData25Two 1 := by
  let PW : CurvePointOnWOpen F2 := ⟨P, hW⟩
  let m : Ideal WChartQuotient := RingHom.ker (wOpenChartQuotientEval PW)
  have hm : m.IsMaximal := by
    exact wOpenChartQuotientEval_ker_isMaximal PW
  have hsurj : Function.Surjective (wOpenChartQuotientEval PW) :=
    wOpenEvalF2_surjective PW
  refine
    { ideal := m
      ne_bot := canonicalWChart_maximal_ne_bot m hm
      isMaximal := hm
      height_eq_one := canonicalWChart_maximal_height_eq_one m hm
      residue_card := ?_ }
  calc
    Nat.card (WChartQuotient ⧸ m) = Nat.card F2 :=
      Nat.card_congr
        (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
    _ = 2 ^ 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card]
      norm_num

/-- The already descended orbit prime supplies all higher-degree fixed-chart
prime data. -/
noncomputable def higherWOpenPrimeData
    (d : ℕ) (hd : 1 < d)
    (c : fullClosedPointGrading25Two.Closed d) :
    WOpenPrimeData25Two d where
  ideal := (fullClosedPointWOpenPrime d hd c).asIdeal
  ne_bot := fullClosedPointWOpenPrime_ne_bot d hd c
  isMaximal := fullClosedPointWOpenPrime_isMaximal d hd c
  height_eq_one := fullClosedPointWOpenPrime_height_eq_one d hd c
  residue_card := fullClosedPointWOpenResidue_card d hd c

private theorem sigma_degree_one_eq
    {c c' : fullClosedPointGrading25Two.Closed 1} (h : c = c') :
    (⟨1, c⟩ : FullAtom25Two) = ⟨1, c'⟩ := by
  subst c'
  rfl

/-- Every nonboundary full atom has fixed-chart prime data, with the
degree-one case supplied by its unique prime-field representative. -/
noncomputable def fullNonBoundaryPrimeData
    (A : FullNonBoundaryAtom25Two) :
    WOpenPrimeData25Two (fullClosedPointGrading25Two.atomDegree A.1) := by
  rcases A with ⟨⟨d, c⟩, hnb⟩
  change WOpenPrimeData25Two d
  cases d with
  | zero => exact isEmptyElim c
  | succ n =>
      cases n with
      | zero =>
          let P : ExtensionIndex25Two.pointType .degreeOne :=
            fullDegreeOnePointEquiv.symm c
          have hPc : fullDegreeOnePointEquiv P = c :=
            fullDegreeOnePointEquiv.apply_symm_apply c
          have hW : (normalizedCoordinates25 P.1).w ≠ 0 := by
            intro hzero
            rcases primeFieldCurvePoint_w_eq_zero_classification P hzero with
              hX | hYZ | hZ
            · have hc : c = fullBoundaryClosedPointX :=
                hPc.symm.trans (congrArg fullDegreeOnePointEquiv hX)
              exact hnb (Or.inl (by
                simpa [fullBoundaryAtomX] using sigma_degree_one_eq hc))
            · have hc : c = fullBoundaryClosedPointYZ :=
                hPc.symm.trans (congrArg fullDegreeOnePointEquiv hYZ)
              exact hnb (Or.inr (Or.inl (by
                simpa [fullBoundaryAtomYZ] using sigma_degree_one_eq hc)))
            · have hc : c = fullBoundaryClosedPointZ :=
                hPc.symm.trans (congrArg fullDegreeOnePointEquiv hZ)
              exact hnb (Or.inr (Or.inr (by
                simpa [fullBoundaryAtomZ] using sigma_degree_one_eq hc)))
          exact degreeOneWOpenPrimeData P hW
      | succ n =>
          exact higherWOpenPrimeData (n + 2) (by omega) c

/-- Every full closed-point atom is one of the three explicit boundary atoms
or has a nonzero height-one maximal ideal on the fixed chart with exact
residue cardinality. -/
theorem fullClosedPoint_boundary_or_chartPrime
    (A : FullAtom25Two) :
    IsFullBoundaryAtom A ∨
      ∃ m : Ideal WChartQuotient,
        m ≠ ⊥ ∧ m.IsMaximal ∧ m.height = 1 ∧
          Nat.card (WChartQuotient ⧸ m) =
            2 ^ fullClosedPointGrading25Two.atomDegree A := by
  classical
  by_cases hA : IsFullBoundaryAtom A
  · exact Or.inl hA
  · let B : FullNonBoundaryAtom25Two := ⟨A, hA⟩
    let D := fullNonBoundaryPrimeData B
    exact Or.inr
      ⟨D.ideal, D.ne_bot, D.isMaximal, D.height_eq_one,
        by simpa [B] using D.residue_card⟩

end MazurProof.RationalPointsN25QuotientTwoClosedPointPartition
