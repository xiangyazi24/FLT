import FLT.Assumptions.MazurProof.N25F_Next
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientFrobeniusOrbits
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientMiddleRiemannRoch

noncomputable section

namespace MazurProof.N25F_ThreeFullClosedPoints

open CurveZetaEffectiveDivisors
open CurveZetaFrobeniusOrbitGrading
open CurveZetaMarkedDivisors
open CurveZetaPointOrbitClassification
open RationalPointsN25QuotientBaseChange
open RationalPointsN25QuotientMiddleRiemannRoch
open RationalPointsN25QuotientThreeBaseChange
open RationalPointsN25QuotientFrobeniusOrbits
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius

theorem commonFieldThree_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (CommonField 3 d) = 3 ^ d := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 3 d hd.ne'

noncomputable def degreeRealizationThree
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    Realization 3 12 (d + 1) (CommonField 3 (d + 1)) :=
  RationalPointsN25QuotientFrobeniusOrbits.fieldRealization
    (CommonField 3 (d + 1)) (d + 1) (Nat.succ_pos d) hd12
    (commonFieldThree_card (d + 1) (Nat.succ_pos d))

noncomputable def degreeCurvePointEmbeddingToCommon12
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    DegreeCurvePointThree d ↪
      NormalizedProjectiveCurveFrobenius.CurvePoint
        canonicalThreeModel (CommonField 3 12) :=
  curvePointEmbedding canonicalThreeModel
    (degreeRealizationThree d hd12).embedding

theorem degreeRealizationThree_frobenius
    (d : ℕ) (hd12 : d + 1 ∣ 12)
    (x : CommonField 3 (d + 1)) :
    (degreeRealizationThree d hd12).embedding
        (FiniteFieldFrobeniusDescent.commonFrobenius 3 (d + 1) x) =
      FiniteFieldFrobeniusDescent.commonFrobenius 3 12
        ((degreeRealizationThree d hd12).embedding x) := by
  let R := degreeRealizationThree d hd12
  calc
    R.embedding
        (FiniteFieldFrobeniusDescent.commonFrobenius 3 (d + 1) x) =
      R.embedding (x ^ 3) := by
        apply congrArg R.embedding
        simpa using
          (FiniteFieldFrobeniusDescent.commonFrobenius_pow_apply
            3 (d + 1) 1 x)
    _ = (R.embedding x) ^ 3 := by simp
    _ = FiniteFieldFrobeniusDescent.commonFrobenius 3 12
        (R.embedding x) := by
      symm
      simpa using
        (FiniteFieldFrobeniusDescent.commonFrobenius_pow_apply
          3 12 1 (R.embedding x))

set_option maxRecDepth 10000 in
theorem degreeCurvePointEmbeddingToCommon12_semiconj
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    Function.Semiconj
      (degreeCurvePointEmbeddingToCommon12 d hd12)
      (degreePointFrobeniusThree d)
      commonPointFrobenius := by
  intro P
  apply Subtype.ext
  change NormalizedProjective4.map
      (degreeRealizationThree d hd12).embedding
      (NormalizedProjective4.map
        (FiniteFieldFrobeniusDescent.commonFrobenius
          3 (d + 1)).toRingEquiv.toRingHom P.1) =
    NormalizedProjective4.map
      (FiniteFieldFrobeniusDescent.commonFrobenius
        3 12).toRingEquiv.toRingHom
      (NormalizedProjective4.map
        (degreeRealizationThree d hd12).embedding P.1)
  rw [NormalizedProjective4.map_comp, NormalizedProjective4.map_comp]
  have hcomp :
      (degreeRealizationThree d hd12).embedding.comp
          (FiniteFieldFrobeniusDescent.commonFrobenius
            3 (d + 1)).toRingEquiv.toRingHom =
        (FiniteFieldFrobeniusDescent.commonFrobenius
          3 12).toRingEquiv.toRingHom.comp
          (degreeRealizationThree d hd12).embedding := by
    ext x
    exact degreeRealizationThree_frobenius d hd12 x
  rw [hcomp]

noncomputable def degreeToCommonFixedEquiv
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    DegreeCurvePointThree d ≃
      NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalThreeModel 3 12 (d + 1) :=
  NormalizedProjectiveCurveFrobenius.curvePointEquivFixedByIterate
    canonicalThreeModel 3 12 (d + 1)
    (CommonField 3 (d + 1)) (degreeRealizationThree d hd12)

theorem degreeCurvePointEmbeddingToCommon12_minimalPeriod
    (d : ℕ) (hd12 : d + 1 ∣ 12)
    (P : DegreeCurvePointThree d) :
    Function.minimalPeriod commonPointFrobenius
        (degreeCurvePointEmbeddingToCommon12 d hd12 P) =
      Function.minimalPeriod (degreePointFrobeniusThree d) P := by
  symm
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  constructor
  · intro h
    exact h.map (degreeCurvePointEmbeddingToCommon12_semiconj d hd12)
  · intro h
    change ((degreePointFrobeniusThree d : _ → _)^[n]) P = P
    apply (degreeCurvePointEmbeddingToCommon12 d hd12).injective
    calc
      degreeCurvePointEmbeddingToCommon12 d hd12
          (((degreePointFrobeniusThree d : _ → _)^[n]) P) =
        ((commonPointFrobenius : _ → _)^[n])
          (degreeCurvePointEmbeddingToCommon12 d hd12 P) := by
            exact
              (degreeCurvePointEmbeddingToCommon12_semiconj
                d hd12).iterate_right n P
      _ = degreeCurvePointEmbeddingToCommon12 d hd12 P := h

noncomputable def exactPeriodicPointEquivDegreeToCommon12
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    ExactPeriodicPoint (degreePointFrobeniusThree d) (d + 1) ≃
      ExactPeriodicPoint commonPointFrobenius (d + 1) where
  toFun P :=
    ⟨degreeCurvePointEmbeddingToCommon12 d hd12 P.1, by
      rw [degreeCurvePointEmbeddingToCommon12_minimalPeriod d hd12 P.1]
      exact P.2⟩
  invFun Q := by
    let qfix : NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalThreeModel 3 12 (d + 1) :=
      ⟨Q.1, exactPeriodicPoint_iterate commonPointFrobenius Q⟩
    let P := (degreeToCommonFixedEquiv d hd12).symm qfix
    refine ⟨P, ?_⟩
    have hval :
        degreeCurvePointEmbeddingToCommon12 d hd12 P = Q.1 := by
      change ((degreeToCommonFixedEquiv d hd12 P).1 = Q.1)
      exact congrArg Subtype.val
        ((degreeToCommonFixedEquiv d hd12).apply_symm_apply qfix)
    rw [← degreeCurvePointEmbeddingToCommon12_minimalPeriod d hd12 P,
      hval]
    exact Q.2
  left_inv P := by
    apply Subtype.ext
    let qfix : NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalThreeModel 3 12 (d + 1) :=
      ⟨degreeCurvePointEmbeddingToCommon12 d hd12 P.1,
        exactPeriodicPoint_iterate commonPointFrobenius
          ⟨degreeCurvePointEmbeddingToCommon12 d hd12 P.1, by
            rw [degreeCurvePointEmbeddingToCommon12_minimalPeriod
              d hd12 P.1]
            exact P.2⟩⟩
    change (degreeToCommonFixedEquiv d hd12).symm qfix = P.1
    apply (degreeToCommonFixedEquiv d hd12).injective
    rw [(degreeToCommonFixedEquiv d hd12).apply_symm_apply]
    exact Subtype.ext (by rfl)
  right_inv Q := by
    apply Subtype.ext
    let qfix : NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalThreeModel 3 12 (d + 1) :=
      ⟨Q.1, exactPeriodicPoint_iterate commonPointFrobenius Q⟩
    change degreeCurvePointEmbeddingToCommon12 d hd12
        ((degreeToCommonFixedEquiv d hd12).symm qfix) = Q.1
    change ((degreeToCommonFixedEquiv d hd12
        ((degreeToCommonFixedEquiv d hd12).symm qfix)).1 = Q.1)
    exact congrArg Subtype.val
      ((degreeToCommonFixedEquiv d hd12).apply_symm_apply qfix)

theorem sameExactOrbit_degreeToCommon12_iff
    (d : ℕ) (hd12 : d + 1 ∣ 12)
    (P Q : ExactPeriodicPoint (degreePointFrobeniusThree d) (d + 1)) :
    SameExactOrbit commonPointFrobenius (d + 1)
        (exactPeriodicPointEquivDegreeToCommon12 d hd12 P)
        (exactPeriodicPointEquivDegreeToCommon12 d hd12 Q) ↔
      SameExactOrbit (degreePointFrobeniusThree d) (d + 1) P Q := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply (degreeCurvePointEmbeddingToCommon12 d hd12).injective
    calc
      degreeCurvePointEmbeddingToCommon12 d hd12
          (((degreePointFrobeniusThree d : _ → _)^[i.1]) P.1) =
        ((commonPointFrobenius : _ → _)^[i.1])
          (degreeCurvePointEmbeddingToCommon12 d hd12 P.1) := by
            exact
              (degreeCurvePointEmbeddingToCommon12_semiconj
                d hd12).iterate_right i.1 P.1
      _ = degreeCurvePointEmbeddingToCommon12 d hd12 Q.1 := hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    calc
      ((commonPointFrobenius : _ → _)^[i.1])
          (degreeCurvePointEmbeddingToCommon12 d hd12 P.1) =
        degreeCurvePointEmbeddingToCommon12 d hd12
          (((degreePointFrobeniusThree d : _ → _)^[i.1]) P.1) := by
            exact
              ((degreeCurvePointEmbeddingToCommon12_semiconj
                d hd12).iterate_right i.1 P.1).symm
      _ = degreeCurvePointEmbeddingToCommon12 d hd12 Q.1 := by
        rw [hi]

noncomputable def orbitClassEquivDegreeToCommon12
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    OrbitClass (degreePointFrobeniusThree d) (d + 1) (Nat.succ_pos d) ≃
      OrbitClass commonPointFrobenius (d + 1) (Nat.succ_pos d) := by
  let E := exactPeriodicPointEquivDegreeToCommon12 d hd12
  let f :
      OrbitClass (degreePointFrobeniusThree d) (d + 1) (Nat.succ_pos d) →
        OrbitClass commonPointFrobenius (d + 1) (Nat.succ_pos d) :=
    Quotient.map E (by
      intro P Q hPQ
      exact (sameExactOrbit_degreeToCommon12_iff d hd12 P Q).2 hPQ)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ P =>
      induction b using Quotient.inductionOn with
      | _ Q =>
        apply Quotient.sound
        exact (sameExactOrbit_degreeToCommon12_iff
          d hd12 P Q).1 (Quotient.exact hab)
  · intro q
    induction q using Quotient.inductionOn with
    | _ Q =>
      refine ⟨orbitClassMk (degreePointFrobeniusThree d)
        (d + 1) (Nat.succ_pos d) (E.symm Q), ?_⟩
      exact congrArg
        (orbitClassMk commonPointFrobenius
          (d + 1) (Nat.succ_pos d))
        (E.apply_symm_apply Q)

noncomputable def closedPointEquivCommon12ToFull
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    frobeniusOrbitGrading25ThreeLE4.Closed d ≃
      fullClosedPointGrading25Three.Closed d := by
  cases d with
  | zero => omega
  | succ d =>
      exact (orbitClassEquivDegreeToCommon12 d hd12).symm

noncomputable def closedPointEquivCommon12ToFullLE4
    (d : Fin 5) :
    frobeniusOrbitGrading25ThreeLE4.Closed d.1 ≃
      fullClosedPointGrading25Three.Closed d.1 := by
  by_cases hd : d.1 = 0
  · have hdeq : d = 0 := Fin.ext hd
    subst d
    exact Equiv.refl _
  · apply closedPointEquivCommon12ToFull d.1 (Nat.pos_of_ne_zero hd)
    have hdle : d.1 ≤ 4 := Nat.le_of_lt_succ d.2
    have hcases : d.1 = 1 ∨ d.1 = 2 ∨ d.1 = 3 ∨ d.1 = 4 := by
      omega
    rcases hcases with h | h | h | h <;> simp [h]

noncomputable def closedPointEquivCommon12ToFullLE
    (k : ℕ) (hk : k ≤ 4) (d : Fin (k + 1)) :
    frobeniusOrbitGrading25ThreeLE4.Closed d.1 ≃
      fullClosedPointGrading25Three.Closed d.1 :=
  closedPointEquivCommon12ToFullLE4
    ⟨d.1, Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.2).trans hk)⟩

noncomputable def atomLEEquivCommon12ToFull
    (k : ℕ) (hk : k ≤ 4) :
    frobeniusOrbitGrading25ThreeLE4.AtomLE k ≃
      fullClosedPointGrading25Three.AtomLE k :=
  (frobeniusOrbitGrading25ThreeLE4.atomLEEquivSigma k).trans
    ((Equiv.sigmaCongrRight fun d =>
      closedPointEquivCommon12ToFullLE k hk d).trans
        (fullClosedPointGrading25Three.atomLEEquivSigma k).symm)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
noncomputable def exactGhostSlotEquivCommon12ToFull
    (k : ℕ) (hk : k ≤ 4) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        frobeniusOrbitGrading25ThreeLE4 k ≃
      CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        fullClosedPointGrading25Three k where
  toFun s := by
    rcases s with ⟨x, r, t⟩
    let e := atomLEEquivCommon12ToFull k hk
    let x' := e x
    have hdegree :
        fullClosedPointGrading25Three.atomDegree x'.1 =
          frobeniusOrbitGrading25ThreeLE4.atomDegree x.1 := by
      rfl
    let r' : CurveZetaMarkedDivisors.ClosedPointGrading.ExactCopies
        fullClosedPointGrading25Three k x' :=
      ⟨r.1, r.2.1, by simpa only [hdegree] using r.2.2⟩
    let t' : Fin (fullClosedPointGrading25Three.atomDegree x'.1) :=
      Fin.cast hdegree.symm t
    exact ⟨x', r', t'⟩
  invFun s := by
    rcases s with ⟨x, r, t⟩
    let e := atomLEEquivCommon12ToFull k hk
    let x' := e.symm x
    have hdegree :
        frobeniusOrbitGrading25ThreeLE4.atomDegree x'.1 =
          fullClosedPointGrading25Three.atomDegree x.1 := by
      rfl
    let r' : CurveZetaMarkedDivisors.ClosedPointGrading.ExactCopies
        frobeniusOrbitGrading25ThreeLE4 k x' :=
      ⟨r.1, r.2.1, by simpa only [hdegree] using r.2.2⟩
    let t' : Fin (frobeniusOrbitGrading25ThreeLE4.atomDegree x'.1) :=
      Fin.cast hdegree.symm t
    exact ⟨x', r', t'⟩
  left_inv s := by
    apply CurveZetaMarkedDivisors.ClosedPointGrading.exactGhostCoordinates_injective
      frobeniusOrbitGrading25ThreeLE4 k
    rcases s with ⟨x, r, t⟩
    change
      (((atomLEEquivCommon12ToFull k hk).symm
          (atomLEEquivCommon12ToFull k hk x)).1, r.1.1, t.1) =
        (x.1, r.1.1, t.1)
    rw [(atomLEEquivCommon12ToFull k hk).symm_apply_apply]
  right_inv s := by
    apply CurveZetaMarkedDivisors.ClosedPointGrading.exactGhostCoordinates_injective
      fullClosedPointGrading25Three k
    rcases s with ⟨x, r, t⟩
    change
      ((atomLEEquivCommon12ToFull k hk
          ((atomLEEquivCommon12ToFull k hk).symm x)).1, r.1.1, t.1) =
        (x.1, r.1.1, t.1)
    rw [(atomLEEquivCommon12ToFull k hk).apply_symm_apply]

noncomputable def fullClosedPointBridge25ThreeLE4 :
    ClosedPointBridge25ThreeLE4 fullClosedPointGrading25Three where
  classify i :=
    (frobeniusClosedPointBridge25ThreeLE4.classify i).trans
      (exactGhostSlotEquivCommon12ToFull
        (ExtensionIndex25Three.exponent i) (by
          cases i <;> norm_num [ExtensionIndex25Three.exponent]))

end MazurProof.N25F_ThreeFullClosedPoints
