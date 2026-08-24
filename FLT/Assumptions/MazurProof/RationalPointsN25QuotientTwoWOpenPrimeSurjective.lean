import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenPointConstruction
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Surjectivity of the W-chart closed-point map

Every maximal ideal of the fixed `W = 1` chart has a finite residue field.
Its three coordinate classes give a curve point over the canonical binary
field of the residue degree.  Surjectivity of the residue evaluation forces
that point to have exact Frobenius period equal to the residue degree.  The
resulting nonboundary closed-point atom recovers the original maximal ideal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective

open CurveZetaFrobeniusOrbitGrading
open FiniteFieldFrobeniusDescent
open Function
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientBaseChange
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoClosedPointPartition
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoCanonicalDivisor
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoPlaneFunctionField
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoWOpenOrbitPrime
open RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
open RationalPointsN25QuotientTwoWOpenPointConstruction

abbrev W := WChartQuotient
abbrev k₂ := ZMod 2

/-- The image of the affine `X` variable in the fixed chart quotient. -/
noncomputable def qx : W :=
  Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
    (MvPolynomial.X (⟨0, by decide⟩ : OtherCoordinate (3 : Fin 4)))

/-- The image of the affine `Y` variable in the fixed chart quotient. -/
noncomputable def qy : W :=
  Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
    (MvPolynomial.X (⟨1, by decide⟩ : OtherCoordinate (3 : Fin 4)))

/-- The image of the affine `Z` variable in the fixed chart quotient. -/
noncomputable def qz : W :=
  Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
    (MvPolynomial.X (⟨2, by decide⟩ : OtherCoordinate (3 : Fin 4)))

section Maximal

variable (m : Ideal W) [m.IsMaximal]

local instance : Field (W ⧸ m) := Ideal.Quotient.field m

local instance : Module.Finite k₂ (W ⧸ m) :=
  finite_of_finite_type_of_isJacobsonRing k₂ (W ⧸ m)

/-- The binary residue degree of a maximal ideal of the fixed chart. -/
noncomputable abbrev residueDegree : ℕ := Module.finrank k₂ (W ⧸ m)

/-- A maximal quotient has positive binary residue degree. -/
theorem residueDegree_pos : 0 < residueDegree m := by
  exact Module.finrank_pos

/-- The residue field has cardinality `2` to its binary degree. -/
theorem residue_natCard : Nat.card (W ⧸ m) = 2 ^ residueDegree m := by
  simpa [residueDegree] using
    (Module.natCard_eq_pow_finrank (K := k₂) (V := W ⧸ m))

/-- Identify the finite residue field with the canonical field of the same
binary degree. -/
noncomputable def residueEquivCommon :
    (W ⧸ m) ≃ₐ[k₂] CommonField 2 (residueDegree m) :=
  GaloisField.algEquivGaloisField 2 (residueDegree m) (residue_natCard m)

/-- The quotient map followed by the canonical finite-field equivalence. -/
noncomputable def residueEval :
    W →ₐ[k₂] CommonField 2 (residueDegree m) :=
  (residueEquivCommon m).toAlgHom.comp (Ideal.Quotient.mkₐ k₂ m)

/-- The canonical residue evaluation is onto. -/
theorem residueEval_surjective : Function.Surjective (residueEval m) := by
  exact (residueEquivCommon m).surjective.comp Ideal.Quotient.mk_surjective

/-- The canonical residue evaluation has the original maximal ideal as its
kernel. -/
theorem residueEval_ker : RingHom.ker (residueEval m).toRingHom = m := by
  ext a
  change (residueEquivCommon m) ((Ideal.Quotient.mk m) a) = 0 ↔ a ∈ m
  constructor
  · intro h
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (residueEquivCommon m).injective
    simpa using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- The first affine coordinate in the canonical residue field. -/
noncomputable def residueX : CommonField 2 (residueDegree m) := residueEval m qx
/-- The second affine coordinate in the canonical residue field. -/
noncomputable def residueY : CommonField 2 (residueDegree m) := residueEval m qy
/-- The third affine coordinate in the canonical residue field. -/
noncomputable def residueZ : CommonField 2 (residueDegree m) := residueEval m qz

/-- The residue coordinates satisfy the dehomogenized quadric. -/
theorem residue_quadric :
    canonicalQuadric25CharTwo
      (wChartPoint (residueX m) (residueY m) (residueZ m)) = 0 := by
  have hW :
      Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
          (chartAffineQuadric 3) = (0 : W) := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have h := congrArg (residueEval m) hW
  simpa [canonicalQuadric25CharTwo, wChartPoint, residueX, residueY,
    residueZ, qx, qy, qz, chartAffineQuadric, ambientDehomogenize,
    dehomogenizedVariable,
    RationalPointsN25QuotientTwoConormal.canonicalQuadricPolynomial25Two]
    using h

/-- The residue coordinates satisfy the dehomogenized cubic. -/
theorem residue_cubic :
    canonicalCubic25CharTwo
      (wChartPoint (residueX m) (residueY m) (residueZ m)) = 0 := by
  have hW :
      Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
          (chartAffineCubic 3) = (0 : W) := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (by simp)
  have h := congrArg (residueEval m) hW
  simpa [canonicalCubic25CharTwo, wChartPoint, residueX, residueY,
    residueZ, qx, qy, qz, chartAffineCubic, ambientDehomogenize,
    dehomogenizedVariable,
    RationalPointsN25QuotientTwoConormal.canonicalCubicPolynomial25Two]
    using h

/-- The residue coordinates define a point of the projective curve on the
`W` open. -/
noncomputable def residuePoint :
    CurvePointOnWOpen (CommonField 2 (residueDegree m)) :=
  curvePointOnWOpenOfCoordinates (residueX m) (residueY m) (residueZ m)
    (residue_quadric m) (residue_cubic m)

/-- Evaluation at the constructed point is the canonical residue map. -/
theorem residuePoint_eval :
    wOpenChartQuotientEvalAlgHom (residuePoint m) = residueEval m := by
  apply AlgHom.coe_ringHom_injective
  apply Ideal.Quotient.ringHom_ext
  change wOpenAffineEval (residuePoint m) =
    (residueEval m).toRingHom.comp
      (Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4)))
  apply MvPolynomial.ringHom_ext
  · intro r
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective r
    simp [wOpenAffineEval]
  · intro j
    fin_cases j <;>
      simp [wOpenAffineEval, residuePoint, residueX, residueY, residueZ,
        qx, qy, qz, coordinates4ToFun, wChartPoint]

/-- Evaluation at the constructed residue point is onto its full field. -/
theorem residuePoint_eval_surjective :
    Function.Surjective (wOpenChartQuotientEvalAlgHom (residuePoint m)) := by
  rw [residuePoint_eval m]
  exact residueEval_surjective m

/-- Evaluation at the constructed residue point recovers the maximal ideal. -/
theorem residuePoint_eval_ker :
    RingHom.ker (wOpenChartQuotientEval (residuePoint m)) = m := by
  change RingHom.ker
      (wOpenChartQuotientEvalAlgHom (residuePoint m)).toRingHom = m
  rw [residuePoint_eval m]
  exact residueEval_ker m

/-- If a Frobenius iterate fixes a point whose chart evaluation is onto,
the field degree divides the iterate. -/
theorem degree_dvd_of_pointFrobenius_iterate_fixed
    {d n : ℕ} (hd : 0 < d)
    (P : CurvePointOnWOpen (CommonField 2 d))
    (hsurj : Function.Surjective (wOpenChartQuotientEvalAlgHom P))
    (hfix : ((degreePointFrobeniusTwo d : _ → _)^[n]) P.point = P.point) :
    d ∣ n := by
  change Function.Surjective (wOpenChartQuotientEval P) at hsurj
  let e : CommonField 2 d ≃+* CommonField 2 d :=
    (commonFrobenius 2 d ^ n).toRingEquiv
  have hiter := pointFrobenius_iterate_val
    canonicalTwoModel 2 d n P.point
  have hval :
      NormalizedProjective4.map e.toRingHom P.point.1 = P.point.1 := by
    change NormalizedProjective4.map
      (commonFrobenius 2 d ^ n).toRingEquiv.toRingHom P.point.1 =
        P.point.1
    exact hiter.symm.trans (congrArg Subtype.val hfix)
  have hopen : P.map e = P := by
    apply CurvePointOnWOpen.ext
    exact Subtype.ext hval
  have heq : commonFrobenius 2 d ^ n = 1 := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨a, rfl⟩ := hsurj y
    have hmap := DFunLike.congr_fun (wOpenChartQuotientEval_map e P) a
    rw [hopen] at hmap
    simpa [e] using hmap
  have hord : orderOf (commonFrobenius 2 d) = d := by
    simpa [commonFrobenius, GaloisField.finrank 2 hd.ne'] using
      (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic
        (ZMod 2) (CommonField 2 d))
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one heq

/-- Degree-many Frobenius iterations fix every point over the canonical
degree-`d` field. -/
theorem pointFrobenius_degree_fixed
    {d : ℕ} (hd : 0 < d)
    (P : CurvePointOnWOpen (CommonField 2 d)) :
    ((degreePointFrobeniusTwo d : _ → _)^[d]) P.point = P.point := by
  have hord : orderOf (commonFrobenius 2 d) = d := by
    simpa [commonFrobenius, GaloisField.finrank 2 hd.ne'] using
      (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic
        (ZMod 2) (CommonField 2 d))
  have hpow : commonFrobenius 2 d ^ d = 1 := by
    calc
      commonFrobenius 2 d ^ d =
          commonFrobenius 2 d ^ orderOf (commonFrobenius 2 d) := by rw [hord]
      _ = 1 := pow_orderOf_eq_one (commonFrobenius 2 d)
  change ((pointFrobeniusFun canonicalTwoModel 2 d : _ → _)^[d])
    P.point = P.point
  apply Subtype.ext
  rw [pointFrobenius_iterate_val, hpow]
  cases P.point.1 <;> simp [NormalizedProjective4.map]

/-- The point reconstructed from a maximal residue field has exact period
equal to that field's binary degree. -/
theorem residuePoint_minimalPeriod :
    Function.minimalPeriod (degreePointFrobeniusTwo (residueDegree m))
      (residuePoint m).point = residueDegree m := by
  let d := residueDegree m
  have hd : 0 < d := residueDegree_pos m
  apply Nat.dvd_antisymm
  · have hperiodic : IsPeriodicPt
        (degreePointFrobeniusTwo d) d (residuePoint m).point :=
      pointFrobenius_degree_fixed hd (residuePoint m)
    exact hperiodic.minimalPeriod_dvd
  · apply degree_dvd_of_pointFrobenius_iterate_fixed hd (residuePoint m)
      (residuePoint_eval_surjective m)
    exact Function.iterate_minimalPeriod
      (f := (degreePointFrobeniusTwo d : _ → _))
      (x := (residuePoint m).point)

/-- Package the reconstructed point with its exact Frobenius period. -/
noncomputable def residueExactPeriodicPoint :
    ExactPeriodicPoint (degreePointFrobeniusTwo (residueDegree m))
      (residueDegree m) :=
  ⟨(residuePoint m).point, residuePoint_minimalPeriod m⟩

/-- A prime-field point on the `W` open is not one of the three boundary
atoms. -/
theorem degreeOneAtomOfWOpen_nonboundary (P : CurvePointOnWOpen F2) :
    ¬ IsFullBoundaryAtom
      (⟨1, fullDegreeOnePointEquiv P.point⟩ : FullAtom25Two) := by
  intro hboundary
  rcases hboundary with hX | hYZ | hZ
  · have hclosed : fullDegreeOnePointEquiv P.point =
        fullDegreeOnePointEquiv wBoundaryPointX := by
      simpa [fullBoundaryAtomX, fullBoundaryClosedPointX,
        fullDegreeOneClosedPoint] using
          (Sigma.mk.inj_iff.mp hX).2
    have hpoint : P.point = wBoundaryPointX :=
      fullDegreeOnePointEquiv.injective hclosed
    apply P.w_ne_zero
    rw [hpoint]
    rfl
  · have hclosed : fullDegreeOnePointEquiv P.point =
        fullDegreeOnePointEquiv hyperplanePointYZ := by
      simpa [fullBoundaryAtomYZ, fullBoundaryClosedPointYZ,
        fullDegreeOneClosedPoint] using
          (Sigma.mk.inj_iff.mp hYZ).2
    have hpoint : P.point = hyperplanePointYZ :=
      fullDegreeOnePointEquiv.injective hclosed
    apply P.w_ne_zero
    rw [hpoint]
    rfl
  · have hclosed : fullDegreeOnePointEquiv P.point =
        fullDegreeOnePointEquiv hyperplanePointZ := by
      simpa [fullBoundaryAtomZ, fullBoundaryClosedPointZ,
        fullDegreeOneClosedPoint] using
          (Sigma.mk.inj_iff.mp hZ).2
    have hpoint : P.point = hyperplanePointZ :=
      fullDegreeOnePointEquiv.injective hclosed
    apply P.w_ne_zero
    rw [hpoint]
    rfl

/-- Every atom of degree greater than one is automatically nonboundary,
since all three boundary atoms have degree one. -/
theorem higherAtom_nonboundary
    {d : ℕ} (hd : 1 < d)
    (c : fullClosedPointGrading25Two.Closed d) :
    ¬ IsFullBoundaryAtom (⟨d, c⟩ : FullAtom25Two) := by
  intro hboundary
  rcases hboundary with hX | hYZ | hZ
  · have hdegree := congrArg fullClosedPointGrading25Two.atomDegree hX
    change d = 1 at hdegree
    exact hd.ne' hdegree
  · have hdegree := congrArg fullClosedPointGrading25Two.atomDegree hYZ
    change d = 1 at hdegree
    exact hd.ne' hdegree
  · have hdegree := congrArg fullClosedPointGrading25Two.atomDegree hZ
    change d = 1 at hdegree
    exact hd.ne' hdegree

/-- Unfold the prime attached to a degree-one nonboundary atom. -/
theorem fullNonBoundaryPrimeIdeal_degreeOne
    (c : fullClosedPointGrading25Two.Closed 1)
    (hnb : ¬ IsFullBoundaryAtom (⟨1, c⟩ : FullAtom25Two)) :
    fullNonBoundaryPrimeIdeal ⟨⟨1, c⟩, hnb⟩ =
      RingHom.ker
        (wOpenChartQuotientEval (fullDegreeOneNonBoundaryWOpenPoint c hnb)) := by
  rfl

/-- Unfold the prime attached to a higher-degree nonboundary atom. -/
theorem fullNonBoundaryPrimeIdeal_higher
    {d : ℕ} (hd : 1 < d)
    (c : fullClosedPointGrading25Two.Closed d)
    (hnb : ¬ IsFullBoundaryAtom (⟨d, c⟩ : FullAtom25Two)) :
    fullNonBoundaryPrimeIdeal ⟨⟨d, c⟩, hnb⟩ =
      (fullClosedPointWOpenPrime d hd c).asIdeal := by
  cases d with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ n => rfl

/-- An exact higher-degree point with prescribed evaluation kernel supplies
a nonboundary atom with that prime. -/
theorem exists_fullNonBoundaryAtom_prime_eq_of_higher
    {d : ℕ} (hd : 1 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (P : CurvePointOnWOpen (CommonField 2 d))
    (hpoint : Q.1 = P.point)
    (m : Ideal W)
    (hker : RingHom.ker (wOpenChartQuotientEval P) = m) :
    ∃ A : FullNonBoundaryAtom25Two, fullNonBoundaryPrimeIdeal A = m := by
  cases d with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ n =>
          let c : fullClosedPointGrading25Two.Closed (n + 2) :=
            orbitClassMk (degreePointFrobeniusTwo (n + 2)) (n + 2)
              (by omega) Q
          let hnb := higherAtom_nonboundary (d := n + 2) (by omega) c
          let A : FullNonBoundaryAtom25Two := ⟨⟨n + 2, c⟩, hnb⟩
          refine ⟨A, ?_⟩
          rw [show fullNonBoundaryPrimeIdeal A =
              (fullClosedPointWOpenPrime (n + 2) (by omega) c).asIdeal by
            exact fullNonBoundaryPrimeIdeal_higher (by omega) c hnb]
          change RingHom.ker
            (wOpenChartQuotientEval
              (exactPeriodicPointOnWOpen (n + 2) (by omega) Q)) = m
          have hopen :
              exactPeriodicPointOnWOpen (n + 2) (by omega) Q = P := by
            apply CurvePointOnWOpen.ext
            exact hpoint
          rw [hopen]
          exact hker

/-- Every maximal ideal of the fixed `W` chart is the prime of a
nonboundary full closed-point atom. -/
theorem exists_fullNonBoundaryAtom_prime_eq :
    ∃ A : FullNonBoundaryAtom25Two, fullNonBoundaryPrimeIdeal A = m := by
  have hd : 0 < residueDegree m := residueDegree_pos m
  by_cases hd1 : residueDegree m = 1
  ·
    let e : CommonField 2 (residueDegree m) ≃+* F2 := by
      rw [hd1]
      exact (GaloisField.equivZmodP (p := 2)).toRingEquiv
    let P : CurvePointOnWOpen F2 := (residuePoint m).map e
    let A : FullNonBoundaryAtom25Two :=
      ⟨⟨1, fullDegreeOnePointEquiv P.point⟩,
        degreeOneAtomOfWOpen_nonboundary P⟩
    refine ⟨A, ?_⟩
    have hkerMap := wOpenChartQuotientEval_ker_map e (residuePoint m)
    let P' : CurvePointOnWOpen F2 :=
      { point := fullDegreeOnePointEquiv.symm
          (fullDegreeOnePointEquiv P.point)
        w_ne_zero := fullDegreeOneNonBoundary_w_ne_zero
          (fullDegreeOnePointEquiv P.point)
          (degreeOneAtomOfWOpen_nonboundary P) }
    have hP' : P' = P := by
      apply CurvePointOnWOpen.ext
      exact fullDegreeOnePointEquiv.symm_apply_apply P.point
    rw [show fullNonBoundaryPrimeIdeal A =
        RingHom.ker (wOpenChartQuotientEval P') by
      exact fullNonBoundaryPrimeIdeal_degreeOne _ _]
    rw [hP']
    exact hkerMap.trans (residuePoint_eval_ker m)
  · have hd2 : 1 < residueDegree m := by omega
    exact exists_fullNonBoundaryAtom_prime_eq_of_higher hd2
      (residueExactPeriodicPoint m) (residuePoint m) rfl m
      (residuePoint_eval_ker m)

end Maximal

/-- Maximal ideals of the fixed affine `W` chart. -/
def WChartMaximalIdeal := {m : Ideal W // m.IsMaximal}

/-- Send a nonboundary closed-point atom to its maximal chart ideal. -/
noncomputable def fullNonBoundaryMaximalIdeal
    (A : FullNonBoundaryAtom25Two) : WChartMaximalIdeal :=
  ⟨fullNonBoundaryPrimeIdeal A, (fullNonBoundaryPrimeData A).isMaximal⟩

/-- The closed-point-to-maximal-ideal map is injective. -/
theorem fullNonBoundaryMaximalIdeal_injective :
    Function.Injective fullNonBoundaryMaximalIdeal := by
  intro A B h
  apply fullNonBoundaryPrimeIdeal_injective
  exact congrArg Subtype.val h

/-- Every maximal ideal of the fixed chart is reached by a nonboundary
closed-point atom. -/
theorem fullNonBoundaryMaximalIdeal_surjective :
    Function.Surjective fullNonBoundaryMaximalIdeal := by
  intro m
  letI : m.1.IsMaximal := m.2
  obtain ⟨A, hA⟩ := exists_fullNonBoundaryAtom_prime_eq m.1
  exact ⟨A, Subtype.ext hA⟩

/-- Nonboundary closed-point atoms are equivalent to maximal ideals of the
fixed affine chart. -/
noncomputable def fullNonBoundaryAtomEquivMaximalIdeal :
    FullNonBoundaryAtom25Two ≃ WChartMaximalIdeal :=
  Equiv.ofBijective fullNonBoundaryMaximalIdeal
    ⟨fullNonBoundaryMaximalIdeal_injective,
      fullNonBoundaryMaximalIdeal_surjective⟩

/-- Under the closed-point/maximal-ideal correspondence, the residue-field
degree is the Frobenius atom degree. -/
theorem residueDegree_fullNonBoundaryPrimeIdeal
    (A : FullNonBoundaryAtom25Two) :
    residueDegree (fullNonBoundaryPrimeIdeal A) =
      fullClosedPointGrading25Two.atomDegree A.1 := by
  let P := fullNonBoundaryPrimeIdeal A
  letI : P.IsMaximal := (fullNonBoundaryPrimeData A).isMaximal
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
  calc
    2 ^ residueDegree P = Nat.card (W ⧸ P) :=
      (residue_natCard P).symm
    _ = 2 ^ fullClosedPointGrading25Two.atomDegree A.1 :=
      fullNonBoundaryPrimeIdeal_residue_card A

end MazurProof.RationalPointsN25QuotientTwoWOpenPrimeSurjective
