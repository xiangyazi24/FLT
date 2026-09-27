import FLT.Assumptions.MazurProof.CurveDivisorPicard
import FLT.Assumptions.MazurProof.N25F_ProjectiveDivisorSplit
import Mathlib.Tactic

/-!
# Degree on the split characteristic-two N25 divisor carrier

The existing projective-divisor equivalence separates a signed divisor into
three boundary coefficients and a finitely supported divisor on maximal ideals
of the fixed `W = 1` chart.  This file transports the genuine projective
divisor degree through that equivalence and identifies the transported map
with the expected weighted finite sum.

This is only additive degree bookkeeping.  It makes no statement about
principal divisors or the product formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ProjectiveDivisorDegree

open CurveZetaEffectiveDivisors
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWOpenPrimeSurjective
open N25F_ProjectiveDivisorSplit

/-! ## Degrees of the two kinds of split index -/

/-- Each of the three tagged boundary atoms has its actual source-defined
closed-point degree, namely one. -/
@[simp]
theorem fullBoundaryAtomOfTag_degree (t : FullBoundaryTag25Two) :
    fullClosedPointGrading25Two.atomDegree (fullBoundaryAtomOfTag t) = 1 := by
  cases t with
  | X => exact fullBoundaryAtomX_degree
  | YZ => exact fullBoundaryAtomYZ_degree
  | Z => exact fullBoundaryAtomZ_degree

/-- The degree assigned to a maximal ideal of the fixed `W = 1` chart is its
binary residue-field degree. -/
noncomputable def wChartMaximalIdealDegree
    (m : WChartMaximalIdeal) : ℕ := by
  letI : m.1.IsMaximal := m.2
  exact residueDegree m.1

/-- The maximal-ideal equivalence has the original geometric prime ideal as
its underlying ideal. -/
@[simp]
theorem fullNonBoundaryAtomEquivMaximalIdeal_val
    (A : FullNonBoundaryAtom25Two) :
    (fullNonBoundaryAtomEquivMaximalIdeal A).1 =
      fullNonBoundaryPrimeIdeal A := by
  rfl

/-- The chart weight is exactly the full closed-point degree carried by the
corresponding nonboundary atom.  This is the residue-degree bridge already
proved by the fixed-chart construction. -/
@[simp]
theorem wChartMaximalIdealDegree_fullNonBoundary
    (A : FullNonBoundaryAtom25Two) :
    wChartMaximalIdealDegree
        (fullNonBoundaryAtomEquivMaximalIdeal A) =
      fullClosedPointGrading25Two.atomDegree A.1 := by
  change residueDegree (fullNonBoundaryPrimeIdeal A) = _
  exact residueDegree_fullNonBoundaryPrimeIdeal A

/-- Equivalent inverse-oriented form of the preceding transport theorem. -/
@[simp]
theorem wChartMaximalIdealDegree_eq_atomDegree
    (m : WChartMaximalIdeal) :
    wChartMaximalIdealDegree m =
      fullClosedPointGrading25Two.atomDegree
        (fullNonBoundaryAtomEquivMaximalIdeal.symm m).1 := by
  simpa using
    wChartMaximalIdealDegree_fullNonBoundary
      (fullNonBoundaryAtomEquivMaximalIdeal.symm m)

/-! ## Explicit contributions on the split carrier -/

/-- Boundary contribution before simplifying the three source-derived
closed-point degrees to one.  The coefficient order is `X`, `YZ`, `Z`. -/
noncomputable def boundaryCoefficientDegree :
    BoundaryCoefficients25Two →+ ℤ where
  toFun c :=
    c.1 *
        (fullClosedPointGrading25Two.atomDegree
          (fullBoundaryAtomOfTag .X) : ℤ) +
      c.2.1 *
        (fullClosedPointGrading25Two.atomDegree
          (fullBoundaryAtomOfTag .YZ) : ℤ) +
      c.2.2 *
        (fullClosedPointGrading25Two.atomDegree
          (fullBoundaryAtomOfTag .Z) : ℤ)
  map_zero' := by simp
  map_add' c d := by
    rcases c with ⟨cx, cyz⟩
    rcases cyz with ⟨cy, cz⟩
    rcases d with ⟨dx, dyz⟩
    rcases dyz with ⟨dy, dz⟩
    dsimp
    ring

/-- After deriving the boundary atom degrees from source, their contribution
is the signed sum of the three coefficients. -/
@[simp]
theorem boundaryCoefficientDegree_apply
    (c : BoundaryCoefficients25Two) :
    boundaryCoefficientDegree c = c.1 + c.2.1 + c.2.2 := by
  simp [boundaryCoefficientDegree]

/-- The chart contribution is the requested finite `Finsupp.sum`, with every
coefficient weighted by the binary residue degree of its maximal ideal. -/
noncomputable def wChartDivisorDegree : WChartDivisor25Two →+ ℤ where
  toFun D :=
    D.sum fun m n => n * (wChartMaximalIdealDegree m : ℤ)
  map_zero' := by simp
  map_add' D E := by
    classical
    exact Finsupp.sum_add_index' (by simp) (by
      intro m a b
      simp only [add_mul])

@[simp]
theorem wChartDivisorDegree_apply (D : WChartDivisor25Two) :
    wChartDivisorDegree D =
      D.sum fun m n => n * (wChartMaximalIdealDegree m : ℤ) := by
  rfl

/-! ## Degree transported through the divisor split -/

/-- The genuine full projective divisor degree transported to the already
constructed split carrier. -/
noncomputable def splitDegree :
    (BoundaryCoefficients25Two × WChartDivisor25Two) →+ ℤ :=
  fullClosedPointGrading25Two.divisorDegree.comp
    fullDivisorEquivBoundaryCoefficientsChart.symm.toAddMonoidHom

/-- Exact compatibility with the genuine degree on full projective signed
divisors.  This is transport through an additive equivalence, not a new
geometric assumption. -/
@[simp]
theorem divisorDegree_eq_splitDegree (D : ProjectiveDivisor25Two) :
    fullClosedPointGrading25Two.divisorDegree D =
      splitDegree (fullDivisorEquivBoundaryCoefficientsChart D) := by
  simp [splitDegree]

/-! ## Computing the transported map -/

@[simp]
theorem fullAtomEquivBoundaryNonBoundary_boundary
    (t : FullBoundaryTag25Two) :
    fullAtomEquivBoundaryNonBoundary (fullBoundaryAtomOfTag t) =
      Sum.inl t := by
  apply boundaryNonBoundaryEquivFullAtom.injective
  simp [fullAtomEquivBoundaryNonBoundary,
    boundaryNonBoundaryEquivFullAtom,
    boundaryNonBoundaryToFullAtom]

@[simp]
theorem fullAtomEquivBoundaryNonBoundary_nonBoundary
    (A : FullNonBoundaryAtom25Two) :
    fullAtomEquivBoundaryNonBoundary A.1 = Sum.inr A := by
  apply boundaryNonBoundaryEquivFullAtom.injective
  simp [fullAtomEquivBoundaryNonBoundary,
    boundaryNonBoundaryEquivFullAtom,
    boundaryNonBoundaryToFullAtom]

private theorem fullDivisorEquivBoundaryNonBoundary_single_boundary
    (t : FullBoundaryTag25Two) (n : ℤ) :
    fullDivisorEquivBoundaryNonBoundary
        (Finsupp.single (fullBoundaryAtomOfTag t) n) =
      (Finsupp.single t n, 0) := by
  apply Prod.ext
  · ext s
    simp [fullDivisorEquivBoundaryNonBoundary,
      Finsupp.domCongr,
      Finsupp.sumFinsuppAddEquivProdFinsupp,
      Finsupp.sumFinsuppEquivProdFinsupp]
  · ext A
    simp [fullDivisorEquivBoundaryNonBoundary,
      Finsupp.domCongr,
      Finsupp.sumFinsuppAddEquivProdFinsupp,
      Finsupp.sumFinsuppEquivProdFinsupp]

private theorem fullDivisorEquivBoundaryNonBoundary_single_nonBoundary
    (A : FullNonBoundaryAtom25Two) (n : ℤ) :
    fullDivisorEquivBoundaryNonBoundary (Finsupp.single A.1 n) =
      (0, Finsupp.single A n) := by
  apply Prod.ext
  · ext t
    simp [fullDivisorEquivBoundaryNonBoundary,
      Finsupp.domCongr,
      Finsupp.sumFinsuppAddEquivProdFinsupp,
      Finsupp.sumFinsuppEquivProdFinsupp]
  · ext B
    simp [fullDivisorEquivBoundaryNonBoundary,
      Finsupp.domCongr,
      Finsupp.sumFinsuppAddEquivProdFinsupp,
      Finsupp.sumFinsuppEquivProdFinsupp]

private theorem fullDivisorEquivBoundaryCoefficientsChart_single_boundary
    (t : FullBoundaryTag25Two) (n : ℤ) :
    fullDivisorEquivBoundaryCoefficientsChart
        (Finsupp.single (fullBoundaryAtomOfTag t) n) =
      (boundaryDivisorEquivCoefficients (Finsupp.single t n), 0) := by
  change
    boundaryChartDivisorEquivCoefficientsChart
      (boundaryNonBoundaryDivisorEquivBoundaryChart
        (fullDivisorEquivBoundaryNonBoundary
          (Finsupp.single (fullBoundaryAtomOfTag t) n))) = _
  rw [fullDivisorEquivBoundaryNonBoundary_single_boundary]
  simp [boundaryNonBoundaryDivisorEquivBoundaryChart,
    boundaryChartDivisorEquivCoefficientsChart]

private theorem fullDivisorEquivBoundaryCoefficientsChart_single_nonBoundary
    (A : FullNonBoundaryAtom25Two) (n : ℤ) :
    fullDivisorEquivBoundaryCoefficientsChart
        (Finsupp.single A.1 n) =
      (0,
        Finsupp.single (fullNonBoundaryAtomEquivMaximalIdeal A) n) := by
  change
    boundaryChartDivisorEquivCoefficientsChart
      (boundaryNonBoundaryDivisorEquivBoundaryChart
        (fullDivisorEquivBoundaryNonBoundary
          (Finsupp.single A.1 n))) = _
  rw [fullDivisorEquivBoundaryNonBoundary_single_nonBoundary]
  simp [boundaryNonBoundaryDivisorEquivBoundaryChart,
    boundaryChartDivisorEquivCoefficientsChart,
    nonBoundaryDivisorEquivWChart,
    Finsupp.domCongr]

private theorem divisorDegree_single_boundary_components
    (t : FullBoundaryTag25Two) (n : ℤ) :
    fullClosedPointGrading25Two.divisorDegree
        (Finsupp.single (fullBoundaryAtomOfTag t) n) =
      boundaryCoefficientDegree
          (fullDivisorEquivBoundaryCoefficientsChart
            (Finsupp.single (fullBoundaryAtomOfTag t) n)).1 +
        wChartDivisorDegree
          (fullDivisorEquivBoundaryCoefficientsChart
            (Finsupp.single (fullBoundaryAtomOfTag t) n)).2 := by
  rw [fullDivisorEquivBoundaryCoefficientsChart_single_boundary]
  cases t <;>
    simp [CurveZetaEffectiveDivisors.ClosedPointGrading.divisorDegree,
      boundaryCoefficientDegree, boundaryDivisorEquivCoefficients,
      wChartDivisorDegree, fullBoundaryAtomOfTag]

private theorem divisorDegree_single_nonBoundary_components
    (A : FullNonBoundaryAtom25Two) (n : ℤ) :
    fullClosedPointGrading25Two.divisorDegree (Finsupp.single A.1 n) =
      boundaryCoefficientDegree
          (fullDivisorEquivBoundaryCoefficientsChart
            (Finsupp.single A.1 n)).1 +
        wChartDivisorDegree
          (fullDivisorEquivBoundaryCoefficientsChart
            (Finsupp.single A.1 n)).2 := by
  rw [fullDivisorEquivBoundaryCoefficientsChart_single_nonBoundary]
  simp [CurveZetaEffectiveDivisors.ClosedPointGrading.divisorDegree,
    boundaryCoefficientDegree, wChartDivisorDegree,
    wChartMaximalIdealDegree_fullNonBoundary]

private theorem divisorDegree_single_components
    (A : FullAtom25Two) (n : ℤ) :
    fullClosedPointGrading25Two.divisorDegree (Finsupp.single A n) =
      boundaryCoefficientDegree
          (fullDivisorEquivBoundaryCoefficientsChart
            (Finsupp.single A n)).1 +
        wChartDivisorDegree
          (fullDivisorEquivBoundaryCoefficientsChart
            (Finsupp.single A n)).2 := by
  cases hA : fullAtomEquivBoundaryNonBoundary A with
  | inl t =>
      have h : A = fullBoundaryAtomOfTag t := by
        apply fullAtomEquivBoundaryNonBoundary.injective
        simpa using hA
      subst A
      exact divisorDegree_single_boundary_components t n
  | inr B =>
      have h : A = B.1 := by
        apply fullAtomEquivBoundaryNonBoundary.injective
        simpa using hA
      subst A
      exact divisorDegree_single_nonBoundary_components B n

/-- The transported degree is the sum of the genuine boundary and chart
contributions. -/
theorem divisorDegree_eq_boundary_add_chart
    (D : ProjectiveDivisor25Two) :
    fullClosedPointGrading25Two.divisorDegree D =
      boundaryCoefficientDegree
          (fullDivisorEquivBoundaryCoefficientsChart D).1 +
        wChartDivisorDegree
          (fullDivisorEquivBoundaryCoefficientsChart D).2 := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | @single_add A n D hA hn ih =>
      calc
        fullClosedPointGrading25Two.divisorDegree
            (Finsupp.single A n + D) =
          fullClosedPointGrading25Two.divisorDegree
              (Finsupp.single A n) +
            fullClosedPointGrading25Two.divisorDegree D := by
              simpa using
                (fullClosedPointGrading25Two.divisorDegree.map_add
                  (Finsupp.single A n) D)
        _ =
          (boundaryCoefficientDegree
                (fullDivisorEquivBoundaryCoefficientsChart
                  (Finsupp.single A n)).1 +
              wChartDivisorDegree
                (fullDivisorEquivBoundaryCoefficientsChart
                  (Finsupp.single A n)).2) +
            (boundaryCoefficientDegree
                (fullDivisorEquivBoundaryCoefficientsChart D).1 +
              wChartDivisorDegree
                (fullDivisorEquivBoundaryCoefficientsChart D).2) := by
              rw [divisorDegree_single_components, ih]
        _ =
          boundaryCoefficientDegree
              ((fullDivisorEquivBoundaryCoefficientsChart
                (Finsupp.single A n)).1 +
                (fullDivisorEquivBoundaryCoefficientsChart D).1) +
            wChartDivisorDegree
              ((fullDivisorEquivBoundaryCoefficientsChart
                (Finsupp.single A n)).2 +
                (fullDivisorEquivBoundaryCoefficientsChart D).2) := by
              simp only [map_add]
              abel
        _ =
          boundaryCoefficientDegree
              (fullDivisorEquivBoundaryCoefficientsChart
                (Finsupp.single A n + D)).1 +
            wChartDivisorDegree
              (fullDivisorEquivBoundaryCoefficientsChart
                (Finsupp.single A n + D)).2 := by
              have hsplit :=
                fullDivisorEquivBoundaryCoefficientsChart.map_add
                  (Finsupp.single A n) D
              rw [hsplit, Prod.fst_add, Prod.snd_add]

/-- Component formula for the transported map itself. -/
theorem splitDegree_apply_components
    (S : BoundaryCoefficients25Two × WChartDivisor25Two) :
    splitDegree S =
      boundaryCoefficientDegree S.1 + wChartDivisorDegree S.2 := by
  let D : ProjectiveDivisor25Two :=
    fullDivisorEquivBoundaryCoefficientsChart.symm S
  have hD : fullDivisorEquivBoundaryCoefficientsChart D = S :=
    fullDivisorEquivBoundaryCoefficientsChart.apply_symm_apply S
  calc
    splitDegree S =
        fullClosedPointGrading25Two.divisorDegree D := by
      rfl
    _ = boundaryCoefficientDegree
          (fullDivisorEquivBoundaryCoefficientsChart D).1 +
        wChartDivisorDegree
          (fullDivisorEquivBoundaryCoefficientsChart D).2 :=
      divisorDegree_eq_boundary_add_chart D
    _ = boundaryCoefficientDegree S.1 + wChartDivisorDegree S.2 := by
      rw [hD]

/-- Fully explicit split-degree formula.  Coefficient signs are unchanged;
all weights are the exact source-derived residue degrees. -/
theorem splitDegree_apply
    (S : BoundaryCoefficients25Two × WChartDivisor25Two) :
    splitDegree S =
      S.1.1 + S.1.2.1 + S.1.2.2 +
          S.2.sum
            (fun m n => n * (wChartMaximalIdealDegree m : ℤ)) := by
  exact (splitDegree_apply_components S).trans
    (congrArg₂ (fun b c : ℤ => b + c)
      (boundaryCoefficientDegree_apply S.1)
      (wChartDivisorDegree_apply S.2))

end MazurProof.N25F_ProjectiveDivisorDegree
