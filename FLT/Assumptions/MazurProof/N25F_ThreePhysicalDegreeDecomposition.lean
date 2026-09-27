import FLT.Assumptions.MazurProof.N25F_Next


/-!
# Physical-degree rational-point decomposition in characteristic three


For every positive physical degree n, actual points of the characteristic-
three canonical N25 curve over CommonField 3 n decompose by their exact
arithmetic-Frobenius period d dividing n.  The established full closed-point
carrier is successor-indexed internally, so this module keeps separate
physical-degree aliases and identifies them with the existing carrier only
inside the positive successor fiber.


No cardinality-only equivalence of curve-point types is used.
-/


noncomputable section


namespace MazurProof.N25F_ThreePhysicalDegreeDecomposition


open Function
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientBaseChange
open RationalPointsN25QuotientThreeBaseChange
open CurveZetaFrobeniusOrbitGrading
open N25F_ThreeFullClosedPoints


/-- Actual characteristic-three canonical-curve points over the physical
extension field CommonField 3 n. -/
abbrev PhysicalDegreeCurvePointThree (n : ℕ) :=
  CurvePoint canonicalThreeModel (CommonField 3 n)


/-- Arithmetic Frobenius on the physical degree-n point type. -/
noncomputable def physicalDegreePointFrobeniusThree (n : ℕ) :
    Equiv.Perm (PhysicalDegreeCurvePointThree n) :=
  pointFrobenius canonicalThreeModel 3 n


/-- Cardinality of a positive physical-degree characteristic-three field. -/
theorem physicalCommonFieldThree_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (CommonField 3 d) = 3 ^ d := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 3 d hd.ne'


/-- Realize CommonField 3 d as the d-th Frobenius-fixed subfield of
CommonField 3 n whenever d divides n. -/
noncomputable def physicalDegreeFieldRealizationThree
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    Realization 3 n d (CommonField 3 d) :=
  realization 3 n (CommonField 3 d) d hd hn hdvd
    (physicalCommonFieldThree_card d hd)


/-- The coefficient-field embedding stored in the coherent realization. -/
noncomputable def physicalDegreeFieldEmbeddingThree
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    CommonField 3 d →+* CommonField 3 n :=
  (physicalDegreeFieldRealizationThree n d hn hd hdvd).embedding


/-- The selected field embedding commutes with one arithmetic-Frobenius
step. -/
theorem physicalDegreeFieldEmbeddingThree_frobenius
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n)
    (a : CommonField 3 d) :
    physicalDegreeFieldEmbeddingThree n d hn hd hdvd
        (commonFrobenius 3 d a) =
      commonFrobenius 3 n
        (physicalDegreeFieldEmbeddingThree n d hn hd hdvd a) := by
  have hdF := commonFrobenius_pow_apply 3 d 1 a
  have hnF := commonFrobenius_pow_apply 3 n 1
    (physicalDegreeFieldEmbeddingThree n d hn hd hdvd a)
  simp only [pow_one] at hdF hnF
  rw [hdF, hnF, map_pow]


/-- Physical degree-d curve points are exactly the points in the physical
degree-n ambient curve fixed by the d-th Frobenius iterate. -/
noncomputable def physicalDegreePointEquivAmbientFixedThree
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    PhysicalDegreeCurvePointThree d ≃
      CurveZetaFrobeniusOrbitGrading.FixedByIterate
        (physicalDegreePointFrobeniusThree n) d := by
  change CurvePoint canonicalThreeModel (CommonField 3 d) ≃
    CurveZetaFrobeniusOrbitGrading.FixedByIterate
      (pointFrobenius canonicalThreeModel 3 n) d
  exact
    NormalizedProjectiveCurveFrobenius.curvePointEquivFixedByIterate
      canonicalThreeModel 3 n d (CommonField 3 d)
      (physicalDegreeFieldRealizationThree n d hn hd hdvd)


/-- The underlying injection of physical degree-d curve points into the
physical degree-n ambient curve. -/
noncomputable def physicalDegreePointEmbeddingThree
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    PhysicalDegreeCurvePointThree d ↪ PhysicalDegreeCurvePointThree n where
  toFun P :=
    (physicalDegreePointEquivAmbientFixedThree n d hn hd hdvd P).1
  inj' := by
    intro P Q hPQ
    apply
      (physicalDegreePointEquivAmbientFixedThree
        n d hn hd hdvd).injective
    exact Subtype.ext hPQ


/-- On normalized-projective coordinates, the point embedding is exactly
coordinatewise application of the stored field embedding. -/
@[simp]
theorem physicalDegreePointEmbeddingThree_apply_val
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n)
    (P : PhysicalDegreeCurvePointThree d) :
    (physicalDegreePointEmbeddingThree n d hn hd hdvd P).1 =
      NormalizedProjective4.map
        (physicalDegreeFieldEmbeddingThree n d hn hd hdvd) P.1 := by
  change
    (((physicalDegreePointEquivAmbientFixedThree
      n d hn hd hdvd P).1).1 =
      NormalizedProjective4.map
        (physicalDegreeFieldRealizationThree
          n d hn hd hdvd).embedding P.1)
  exact
    NormalizedProjectiveCurveFrobenius.curvePointEquivFixedByIterate_apply_val
      canonicalThreeModel 3 n d (CommonField 3 d)
      (physicalDegreeFieldRealizationThree n d hn hd hdvd) P


set_option maxRecDepth 10000 in
/-- The curve-point embedding commutes with one arithmetic-Frobenius
step. -/
theorem physicalDegreePointEmbeddingThree_frobenius
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n)
    (P : PhysicalDegreeCurvePointThree d) :
    physicalDegreePointEmbeddingThree n d hn hd hdvd
        (physicalDegreePointFrobeniusThree d P) =
      physicalDegreePointFrobeniusThree n
        (physicalDegreePointEmbeddingThree n d hn hd hdvd P) := by
  apply Subtype.ext
  simp only [physicalDegreePointEmbeddingThree_apply_val,
    physicalDegreePointFrobeniusThree,
    NormalizedProjectiveCurveFrobenius.pointFrobenius_apply_val]
  have hcomp :
      (physicalDegreeFieldEmbeddingThree n d hn hd hdvd).comp
          (commonFrobenius 3 d).toRingEquiv.toRingHom =
        (commonFrobenius 3 n).toRingEquiv.toRingHom.comp
          (physicalDegreeFieldEmbeddingThree n d hn hd hdvd) := by
    ext a
    exact physicalDegreeFieldEmbeddingThree_frobenius
      n d hn hd hdvd a
  simpa only [NormalizedProjective4.map_comp] using
    congrArg
      (fun f : CommonField 3 d →+* CommonField 3 n =>
        NormalizedProjective4.map f P.1)
      hcomp


/-- Frobenius semiconjugacy for the physical-degree point embedding. -/
theorem physicalDegreePointEmbeddingThree_semiconj
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    Function.Semiconj
      (physicalDegreePointEmbeddingThree n d hn hd hdvd)
      (physicalDegreePointFrobeniusThree d)
      (physicalDegreePointFrobeniusThree n) := by
  intro P
  exact physicalDegreePointEmbeddingThree_frobenius
    n d hn hd hdvd P


/-- The physical-degree embedding preserves least Frobenius period. -/
theorem physicalDegreePointEmbeddingThree_minimalPeriod
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n)
    (P : PhysicalDegreeCurvePointThree d) :
    minimalPeriod (physicalDegreePointFrobeniusThree d) P =
      minimalPeriod (physicalDegreePointFrobeniusThree n)
        (physicalDegreePointEmbeddingThree n d hn hd hdvd P) := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro k
  change
    (((physicalDegreePointFrobeniusThree d :
        PhysicalDegreeCurvePointThree d →
          PhysicalDegreeCurvePointThree d)^[k]) P = P) ↔
      (((physicalDegreePointFrobeniusThree n :
        PhysicalDegreeCurvePointThree n →
          PhysicalDegreeCurvePointThree n)^[k])
          (physicalDegreePointEmbeddingThree
            n d hn hd hdvd P) =
        physicalDegreePointEmbeddingThree n d hn hd hdvd P)
  constructor
  · intro hP
    calc
      ((physicalDegreePointFrobeniusThree n :
          PhysicalDegreeCurvePointThree n →
            PhysicalDegreeCurvePointThree n)^[k])
          (physicalDegreePointEmbeddingThree n d hn hd hdvd P) =
        physicalDegreePointEmbeddingThree n d hn hd hdvd
          (((physicalDegreePointFrobeniusThree d :
            PhysicalDegreeCurvePointThree d →
              PhysicalDegreeCurvePointThree d)^[k]) P) := by
          exact
            ((physicalDegreePointEmbeddingThree_semiconj
              n d hn hd hdvd).iterate_right k P).symm
      _ = physicalDegreePointEmbeddingThree n d hn hd hdvd P :=
        congrArg
          (physicalDegreePointEmbeddingThree n d hn hd hdvd) hP
  · intro hP
    apply (physicalDegreePointEmbeddingThree n d hn hd hdvd).injective
    calc
      physicalDegreePointEmbeddingThree n d hn hd hdvd
          (((physicalDegreePointFrobeniusThree d :
            PhysicalDegreeCurvePointThree d →
              PhysicalDegreeCurvePointThree d)^[k]) P) =
        ((physicalDegreePointFrobeniusThree n :
          PhysicalDegreeCurvePointThree n →
            PhysicalDegreeCurvePointThree n)^[k])
          (physicalDegreePointEmbeddingThree n d hn hd hdvd P) := by
            exact
              (physicalDegreePointEmbeddingThree_semiconj
                n d hn hd hdvd).iterate_right k P
      _ = physicalDegreePointEmbeddingThree n d hn hd hdvd P := hP


/-- Send an exact-period-d point over CommonField 3 d into the physical
degree-n ambient field. -/
noncomputable def exactPeriodicPointToAmbientThree
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    ExactPeriodicPoint (physicalDegreePointFrobeniusThree d) d →
      ExactPeriodicPoint (physicalDegreePointFrobeniusThree n) d :=
  fun P =>
    ⟨physicalDegreePointEmbeddingThree n d hn hd hdvd P.1,
      (physicalDegreePointEmbeddingThree_minimalPeriod
        n d hn hd hdvd P.1).symm.trans P.2⟩


/-- Exact-period-d points over CommonField 3 d are exactly exact-period-d
points inside CommonField 3 n whenever d divides n.  Surjectivity is the
fixed-subfield theorem, not a point-count argument. -/
noncomputable def exactPeriodicPointEquivAmbientThree
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) :
    ExactPeriodicPoint (physicalDegreePointFrobeniusThree d) d ≃
      ExactPeriodicPoint (physicalDegreePointFrobeniusThree n) d := by
  refine Equiv.ofBijective
    (exactPeriodicPointToAmbientThree n d hn hd hdvd) ?_
  constructor
  · intro P Q hPQ
    apply Subtype.ext
    apply (physicalDegreePointEmbeddingThree n d hn hd hdvd).injective
    exact congrArg
      (fun R : ExactPeriodicPoint
          (physicalDegreePointFrobeniusThree n) d => R.1)
      hPQ
  · intro Q
    let Qfixed :
        CurveZetaFrobeniusOrbitGrading.FixedByIterate
          (physicalDegreePointFrobeniusThree n) d :=
      ⟨Q.1, exactPeriodicPoint_iterate
        (physicalDegreePointFrobeniusThree n) Q⟩
    let P0 : PhysicalDegreeCurvePointThree d :=
      (physicalDegreePointEquivAmbientFixedThree
        n d hn hd hdvd).symm Qfixed
    have hP0 :
        physicalDegreePointEmbeddingThree
            n d hn hd hdvd P0 = Q.1 := by
      change
        ((physicalDegreePointEquivAmbientFixedThree
          n d hn hd hdvd P0).1 = Qfixed.1)
      exact congrArg Subtype.val
        ((physicalDegreePointEquivAmbientFixedThree
          n d hn hd hdvd).apply_symm_apply Qfixed)
    have hperiod :
        minimalPeriod (physicalDegreePointFrobeniusThree d) P0 = d := by
      calc
        minimalPeriod (physicalDegreePointFrobeniusThree d) P0 =
            minimalPeriod (physicalDegreePointFrobeniusThree n)
              (physicalDegreePointEmbeddingThree
                n d hn hd hdvd P0) :=
          physicalDegreePointEmbeddingThree_minimalPeriod
            n d hn hd hdvd P0
        _ = minimalPeriod
            (physicalDegreePointFrobeniusThree n) Q.1 :=
          congrArg
            (minimalPeriod (physicalDegreePointFrobeniusThree n)) hP0
        _ = d := Q.2
    let P : ExactPeriodicPoint
        (physicalDegreePointFrobeniusThree d) d :=
      ⟨P0, hperiod⟩
    refine ⟨P, ?_⟩
    apply Subtype.ext
    exact hP0


/-- For a positive divisor d of n, ambient exact-period-d points are one
degree-d full-grading orbit class together with one of its d Frobenius
positions.  Only the successor branch uses the established predecessor-index
permutation degreePointFrobeniusThree. -/
noncomputable def ambientExactPeriodicPointEquivFullClosedSlotThree
    (n : ℕ) (hn : 0 < n) (d : PositiveDivisor n) :
    ExactPeriodicPoint (physicalDegreePointFrobeniusThree n) d.1 ≃
      fullClosedPointGrading25Three.Closed d.1 × Fin d.1 := by
  rcases d with ⟨d, hd, hdvd⟩
  cases d with
  | zero =>
      exact False.elim (Nat.lt_asymm hd hd)
  | succ d =>
      change
        ExactPeriodicPoint
            (physicalDegreePointFrobeniusThree n) (d + 1) ≃
          OrbitClass (degreePointFrobeniusThree d)
            (d + 1) (Nat.succ_pos d) × Fin (d + 1)
      exact
        (exactPeriodicPointEquivAmbientThree
          n (d + 1) hn (Nat.succ_pos d) hdvd).symm.trans
          (by
            change
              ExactPeriodicPoint
                  (degreePointFrobeniusThree d) (d + 1) ≃
                OrbitClass (degreePointFrobeniusThree d)
                  (d + 1) (Nat.succ_pos d) × Fin (d + 1)
            exact exactPeriodicPointEquivOrbitClassProd
              (degreePointFrobeniusThree d)
              (d + 1) (Nat.succ_pos d))


/-- Fixed points of the n-th physical Frobenius decompose over the positive
physical divisors d ∣ n. -/
noncomputable def fixedByIterateEquivFullClosedSlotsThree
    (n : ℕ) (hn : 0 < n) :
    CurveZetaFrobeniusOrbitGrading.FixedByIterate
        (physicalDegreePointFrobeniusThree n) n ≃
      Σ d : PositiveDivisor n,
        fullClosedPointGrading25Three.Closed d.1 × Fin d.1 :=
  (fixedByIterateEquivSigmaExact
      (physicalDegreePointFrobeniusThree n) n hn).trans
    (Equiv.sigmaCongrRight fun d =>
      ambientExactPeriodicPointEquivFullClosedSlotThree n hn d)


/-- The corrected all-degree characteristic-three rational-point
decomposition.


The positivity parameter is exactly the physical positive-degree domain. -/
noncomputable def curvePointEquivFullClosedSlotsThree
    (n : ℕ) (hn : 0 < n) :
    NormalizedProjectiveCurveFrobenius.CurvePoint
        canonicalThreeModel (CommonField 3 n) ≃
      Σ d : CurveZetaFrobeniusOrbitGrading.PositiveDivisor n,
        fullClosedPointGrading25Three.Closed d.1 × Fin d.1 :=
  (physicalDegreePointEquivAmbientFixedThree
      n n hn hn dvd_rfl).trans
    (fixedByIterateEquivFullClosedSlotsThree n hn)


end MazurProof.N25F_ThreePhysicalDegreeDecomposition
