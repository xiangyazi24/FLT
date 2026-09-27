import FLT.Assumptions.MazurProof.N25F_ThreeDegreeDescent
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientFrobeniusOrbits


/-!
# Full characteristic-three closed-point bridge through degree four


The full carrier in `N25F_Next` stores degree `d + 1` as exact arithmetic-
Frobenius orbits on the canonical curve over `CommonField 3 (d + 1)`.
The older semantic bridge uses exact orbits inside `CommonField 3 12`.


For degrees one through four, the coherent finite-field realization embeds
the degree field into the common field, commutes with arithmetic Frobenius,
and identifies the source curve with the appropriate fixed-point locus.
Consequently it preserves least periods and induces an equivalence of exact
orbit classes.  Transporting the intrinsic ghost slots along these
closed-point equivalences gives the desired semantic bridge on the full
carrier.


No point-count equality is used to construct an equivalence.
-/


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


/-- Embed the actual degree-`d + 1` curve-point carrier into the common
characteristic-three degree-twelve curve. -/
noncomputable def degreeCurvePointEmbeddingToCommon12
    (d : ℕ) (hd12 : d + 1 ∣ 12) :
    DegreeCurvePointThree d ↪
      NormalizedProjectiveCurveFrobenius.CurvePoint
        canonicalThreeModel (CommonField 3 12) :=
  curvePointEmbedding canonicalThreeModel
    (degreeRealizationThree d hd12).embedding


/-- The coherent coefficient-field embedding commutes with one arithmetic
Frobenius step. -/
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


-- The nested normalized-projective maps produce a deep elaboration term.
set_option maxRecDepth 10000 in
/-- The curve-point embedding intertwines source and common-field arithmetic
Frobenius. -/
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


/-- The coherent point embedding preserves least Frobenius period. -/
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


/-- Exact-period points over the actual degree field are exactly the
corresponding exact-period points in the common degree-twelve field. -/
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


/-- The degreewise exact-period equivalence preserves and reflects the
bounded exact-orbit relation. -/
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


/-- Exact Frobenius orbit classes over `CommonField 3 (d + 1)` agree with the
period-`d + 1` orbit classes inside `CommonField 3 12`. -/
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


/-- At every positive degree dividing twelve, the old common-field orbit
carrier agrees with the current full degreewise carrier. -/
noncomputable def closedPointEquivCommon12ToFull
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    frobeniusOrbitGrading25ThreeLE4.Closed d ≃
      fullClosedPointGrading25Three.Closed d := by
  cases d with
  | zero => omega
  | succ d =>
      exact (orbitClassEquivDegreeToCommon12 d hd12).symm


/-- Pointwise comparison of the old and full closed-point carriers through
degree four, including the common empty degree-zero fiber. -/
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


/-- Degreewise comparison at every degree bounded by `k`, for `k ≤ 4`. -/
noncomputable def closedPointEquivCommon12ToFullLE
    (k : ℕ) (hk : k ≤ 4) (d : Fin (k + 1)) :
    frobeniusOrbitGrading25ThreeLE4.Closed d.1 ≃
      fullClosedPointGrading25Three.Closed d.1 :=
  closedPointEquivCommon12ToFullLE4
    ⟨d.1, Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.2).trans hk)⟩


/-- Transport bounded closed-point atoms through degree four while preserving
their degree coordinate. -/
noncomputable def atomLEEquivCommon12ToFull
    (k : ℕ) (hk : k ≤ 4) :
    frobeniusOrbitGrading25ThreeLE4.AtomLE k ≃
      fullClosedPointGrading25Three.AtomLE k :=
  (frobeniusOrbitGrading25ThreeLE4.atomLEEquivSigma k).trans
    ((Equiv.sigmaCongrRight fun d =>
      closedPointEquivCommon12ToFullLE k hk d).trans
        (fullClosedPointGrading25Three.atomLEEquivSigma k).symm)


private noncomputable def exactGhostSlotEquivOfClosedEquivs
    (C D : CurveZetaEffectiveDivisors.ClosedPointGrading)
    (k : ℕ)
    (E : ∀ d : Fin (k + 1), C.Closed d.1 ≃ D.Closed d.1) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot C k ≃
      CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot D k := by
  let e : C.AtomLE k ≃ D.AtomLE k :=
    (C.atomLEEquivSigma k).trans
      ((Equiv.sigmaCongrRight E).trans
        (D.atomLEEquivSigma k).symm)
  have hdegree (x : C.AtomLE k) :
      D.atomDegree (e x).1 = C.atomDegree x.1 := by
    rfl
  unfold CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
  refine Equiv.sigmaCongr e (fun x => ?_)
  let Fiber (n : ℕ) : Type :=
    Σ _r : {r : Fin (k + 1) // 1 ≤ r.1 ∧ r.1 * n = k}, Fin n
  change Fiber (C.atomDegree x.1) ≃ Fiber (D.atomDegree (e x).1)
  exact Equiv.cast (congrArg Fiber (hdegree x).symm)

/-- Transport the common-field ghost slots to the full grading, preserving
the closed-point degree, exact copy count, and Frobenius position. -/
noncomputable def exactGhostSlotEquivCommon12ToFull
    (k : ℕ) (hk : k ≤ 4) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        frobeniusOrbitGrading25ThreeLE4 k ≃
      CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        fullClosedPointGrading25Three k :=
  exactGhostSlotEquivOfClosedEquivs
    frobeniusOrbitGrading25ThreeLE4 fullClosedPointGrading25Three k
    (fun d => closedPointEquivCommon12ToFullLE k hk d)


/-- The four semantic characteristic-three point types, now classified by
intrinsic ghost slots of the actual full degreewise closed-point carrier. -/
noncomputable def fullClosedPointBridge25ThreeLE4 :
    ClosedPointBridge25ThreeLE4 fullClosedPointGrading25Three where
  classify i :=
    (frobeniusClosedPointBridge25ThreeLE4.classify i).trans
      (exactGhostSlotEquivCommon12ToFull
        (ExtensionIndex25Three.exponent i) (by
          cases i <;> norm_num [ExtensionIndex25Three.exponent]))


end MazurProof.N25F_ThreeFullClosedPoints
