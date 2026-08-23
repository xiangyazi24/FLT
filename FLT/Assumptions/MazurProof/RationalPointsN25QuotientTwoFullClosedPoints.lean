import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoFrobeniusOrbits
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointChart

/-!
# Degreewise closed points of the binary N25 curve

The finite common-field orbit grading used for point counts through degree
four is not a global divisor carrier.  This file instead constructs degree
`d` closed points from exact arithmetic-Frobenius orbits on curve points over
`F_(2^d)`.  The exact-period subtype removes points defined over proper
subfields before taking the orbit quotient.

For degrees dividing twelve, coefficient-field descent compares this full
degreewise grading with the existing common degree-twelve grading.  The
comparison is structural: embeddings commute with Frobenius, hence preserve
least periods and exact orbit classes.  No point-count equality is used.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoFullClosedPoints

open CurveZetaEffectiveDivisors
open CurveZetaFrobeniusOrbitGrading
open CurveZetaMarkedDivisors
open CurveZetaPointOrbitClassification
open RationalPointsN25QuotientBaseChange
open RationalPointsN25QuotientMiddleRiemannRoch
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoClosedPointChart
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius

/-- Curve points over the canonical binary field of degree `d`. -/
abbrev DegreeCurvePointTwo (d : ℕ) :=
  CurvePointTwo (CommonField 2 d)

/-- Arithmetic Frobenius on curve points over the degree-`d` binary field. -/
noncomputable def degreePointFrobeniusTwo (d : ℕ) :
    Equiv.Perm (DegreeCurvePointTwo d) :=
  pointFrobenius canonicalTwoModel 2 d

/-- Full closed points degree by degree.  Degree zero is empty; positive
degree `d` consists of exact-period-`d` Frobenius orbits over `F_(2^d)`. -/
noncomputable def fullClosedPointType25Two : ℕ → Type
  | 0 => ULift Empty
  | d + 1 =>
      OrbitClass (degreePointFrobeniusTwo (d + 1))
        (d + 1) (Nat.succ_pos d)

/-- Curve points over every positive-degree canonical binary field form a
finite type. -/
noncomputable instance degreeCurvePointTwoFintype (d : ℕ) :
    Fintype (DegreeCurvePointTwo (d + 1)) := by
  have : Finite (DegreeCurvePointTwo (d + 1)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Each degree of the full closed-point carrier is finite. -/
noncomputable instance fullClosedPointType25TwoFinite (d : ℕ) :
    Finite (fullClosedPointType25Two d) := by
  cases d with
  | zero =>
      exact Finite.of_injective ULift.down (by
        intro x y h
        cases x
        cases y
        cases h
        rfl)
  | succ d =>
      exact orbitClassFinite (degreePointFrobeniusTwo (d + 1))
        (d + 1) (Nat.succ_pos d)

/-- The locally finite closed-point grading containing every residue degree. -/
noncomputable def fullClosedPointGrading25Two : ClosedPointGrading where
  Closed := fullClosedPointType25Two
  finite_closed := fullClosedPointType25TwoFinite
  empty_degree_zero := by
    change IsEmpty (ULift Empty)
    infer_instance

/-- The canonical normalized chart of a positive-degree closed Frobenius
orbit.  Frobenius invariance makes the pivot independent of its exact-period
representative. -/
noncomputable def fullClosedPointPivot
    {d : ℕ} (hd : 0 < d)
    (P : fullClosedPointGrading25Two.Closed d) : Fin 4 := by
  cases d with
  | zero => omega
  | succ n =>
      exact Quotient.lift
        (fun Q : ExactPeriodicPoint (degreePointFrobeniusTwo (n + 1)) (n + 1) =>
          normalizedPivot Q.1.1)
        (by
          intro Q R hQR
          rcases hQR with ⟨i, hi⟩
          rw [← hi]
          exact (normalizedPivot_pointFrobeniusFun_iterate
            canonicalTwoModel 2 (n + 1) i.1 Q.1).symm)
        P

/-- The canonical chart pivot of an atom in the full closed-point grading. -/
noncomputable def fullClosedPointAtomPivot
    (P : fullClosedPointGrading25Two.Atom) : Fin 4 :=
  fullClosedPointPivot (fullClosedPointGrading25Two.atomDegree_pos P) P.2

/-- Full closed points whose canonical normalized representative has pivot
`i`. -/
def FullClosedPointPivotStratum (i : Fin 4) :=
  {P : fullClosedPointGrading25Two.Atom //
    fullClosedPointAtomPivot P = i}

/-- The canonical binary degree-`d` field has `2^d` elements. -/
theorem commonFieldTwo_card (d : ℕ) (hd : 0 < d) :
    Fintype.card (CommonField 2 d) = 2 ^ d := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 d hd.ne'

/-- The coherent realization of the degree-`d` binary field inside the
degree-twelve common field. -/
noncomputable def degreeRealizationTwo
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    Realization 2 12 d (CommonField 2 d) :=
  fieldRealizationTwo (CommonField 2 d) d hd hd12
    (commonFieldTwo_card d hd)

/-- Embed degree-`d` curve points into the common degree-twelve curve. -/
noncomputable def degreeCurvePointEmbeddingToCommon12
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    DegreeCurvePointTwo d ↪ CurvePointTwo CommonTwoField :=
  curvePointEmbedding canonicalTwoModel
    (degreeRealizationTwo d hd hd12).embedding

/-- The realized coefficient embedding commutes with one arithmetic
Frobenius step. -/
theorem degreeRealizationTwo_frobenius
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12)
    (x : CommonField 2 d) :
    (degreeRealizationTwo d hd hd12).embedding
        (commonFrobenius 2 d x) =
      commonFrobenius 2 12
        ((degreeRealizationTwo d hd hd12).embedding x) := by
  let R := degreeRealizationTwo d hd hd12
  calc
    R.embedding (commonFrobenius 2 d x) = R.embedding (x ^ 2) := by
      congr 1
    _ = (R.embedding x) ^ 2 := by simp
    _ = commonFrobenius 2 12 (R.embedding x) := by
      symm
      simpa using commonFrobenius_pow_apply 2 12 1 (R.embedding x)

-- The nested normalized-projective maps produce a deep elaboration term.
set_option maxRecDepth 10000 in
/-- The curve-point embedding intertwines the source and common-field
Frobenius permutations. -/
theorem degreeCurvePointEmbeddingToCommon12_semiconj
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    Function.Semiconj
      (degreeCurvePointEmbeddingToCommon12 d hd hd12)
      (degreePointFrobeniusTwo d)
      commonPointFrobeniusTwo := by
  intro P
  apply Subtype.ext
  change NormalizedProjective4.map
      (degreeRealizationTwo d hd hd12).embedding
      (NormalizedProjective4.map
        (commonFrobenius 2 d).toRingEquiv.toRingHom P.1) =
    NormalizedProjective4.map
      (commonFrobenius 2 12).toRingEquiv.toRingHom
      (NormalizedProjective4.map
        (degreeRealizationTwo d hd hd12).embedding P.1)
  rw [NormalizedProjective4.map_comp, NormalizedProjective4.map_comp]
  have hcomp :
      (degreeRealizationTwo d hd hd12).embedding.comp
          (commonFrobenius 2 d).toRingEquiv.toRingHom =
        (commonFrobenius 2 12).toRingEquiv.toRingHom.comp
          (degreeRealizationTwo d hd hd12).embedding := by
    ext x
    exact degreeRealizationTwo_frobenius d hd hd12 x
  rw [hcomp]

/-- Degree-`d` curve points are the points in the common field fixed by the
`d`-fold Frobenius iterate. -/
noncomputable def degreeToCommonFixedEquiv
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    DegreeCurvePointTwo d ≃
      NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalTwoModel 2 12 d :=
  curvePointEquivFixedByIterate canonicalTwoModel 2 12 d
    (CommonField 2 d) (degreeRealizationTwo d hd hd12)

/-- The coherent coefficient embedding preserves the least Frobenius
period of every degree-`d` curve point. -/
theorem degreeCurvePointEmbeddingToCommon12_minimalPeriod
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12)
    (P : DegreeCurvePointTwo d) :
    Function.minimalPeriod commonPointFrobeniusTwo
        (degreeCurvePointEmbeddingToCommon12 d hd hd12 P) =
      Function.minimalPeriod (degreePointFrobeniusTwo d) P := by
  symm
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  constructor
  · intro h
    exact h.map (degreeCurvePointEmbeddingToCommon12_semiconj d hd hd12)
  · intro h
    change ((degreePointFrobeniusTwo d : _ → _)^[n]) P = P
    apply (degreeCurvePointEmbeddingToCommon12 d hd hd12).injective
    calc
      degreeCurvePointEmbeddingToCommon12 d hd hd12
          (((degreePointFrobeniusTwo d : _ → _)^[n]) P) =
        ((commonPointFrobeniusTwo : _ → _)^[n])
          (degreeCurvePointEmbeddingToCommon12 d hd hd12 P) := by
            exact
              (degreeCurvePointEmbeddingToCommon12_semiconj
                d hd hd12).iterate_right n P
      _ = degreeCurvePointEmbeddingToCommon12 d hd hd12 P := h

/-- Exact-period points over the degree-`d` field are exactly the
exact-period-`d` points in the common degree-twelve field. -/
noncomputable def exactPeriodicPointEquivDegreeToCommon12
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    ExactPeriodicPoint (degreePointFrobeniusTwo d) d ≃
      ExactPeriodicPoint commonPointFrobeniusTwo d where
  toFun P :=
    ⟨degreeCurvePointEmbeddingToCommon12 d hd hd12 P.1, by
      rw [degreeCurvePointEmbeddingToCommon12_minimalPeriod d hd hd12 P.1]
      exact P.2⟩
  invFun Q := by
    let qfix : NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalTwoModel 2 12 d :=
      ⟨Q.1, exactPeriodicPoint_iterate commonPointFrobeniusTwo Q⟩
    let P := (degreeToCommonFixedEquiv d hd hd12).symm qfix
    refine ⟨P, ?_⟩
    have hval :
        degreeCurvePointEmbeddingToCommon12 d hd hd12 P = Q.1 := by
      change ((degreeToCommonFixedEquiv d hd hd12 P).1 = Q.1)
      exact congrArg Subtype.val
        ((degreeToCommonFixedEquiv d hd hd12).apply_symm_apply qfix)
    rw [← degreeCurvePointEmbeddingToCommon12_minimalPeriod d hd hd12 P,
      hval]
    exact Q.2
  left_inv P := by
    apply Subtype.ext
    let qfix : NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalTwoModel 2 12 d :=
      ⟨degreeCurvePointEmbeddingToCommon12 d hd hd12 P.1,
        exactPeriodicPoint_iterate commonPointFrobeniusTwo
          ⟨degreeCurvePointEmbeddingToCommon12 d hd hd12 P.1, by
            rw [degreeCurvePointEmbeddingToCommon12_minimalPeriod
              d hd hd12 P.1]
            exact P.2⟩⟩
    change (degreeToCommonFixedEquiv d hd hd12).symm qfix = P.1
    apply (degreeToCommonFixedEquiv d hd hd12).injective
    rw [(degreeToCommonFixedEquiv d hd hd12).apply_symm_apply]
    exact Subtype.ext (by rfl)
  right_inv Q := by
    apply Subtype.ext
    let qfix : NormalizedProjectiveCurveFrobenius.FixedByIterate
        canonicalTwoModel 2 12 d :=
      ⟨Q.1, exactPeriodicPoint_iterate commonPointFrobeniusTwo Q⟩
    change degreeCurvePointEmbeddingToCommon12 d hd hd12
        ((degreeToCommonFixedEquiv d hd hd12).symm qfix) = Q.1
    change ((degreeToCommonFixedEquiv d hd hd12
        ((degreeToCommonFixedEquiv d hd hd12).symm qfix)).1 = Q.1)
    exact congrArg Subtype.val
      ((degreeToCommonFixedEquiv d hd hd12).apply_symm_apply qfix)

/-- The degreewise exact-period equivalence preserves and reflects the
bounded orbit relation. -/
theorem sameExactOrbit_degreeToCommon12_iff
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12)
    (P Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    SameExactOrbit commonPointFrobeniusTwo d
        (exactPeriodicPointEquivDegreeToCommon12 d hd hd12 P)
        (exactPeriodicPointEquivDegreeToCommon12 d hd hd12 Q) ↔
      SameExactOrbit (degreePointFrobeniusTwo d) d P Q := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply (degreeCurvePointEmbeddingToCommon12 d hd hd12).injective
    calc
      degreeCurvePointEmbeddingToCommon12 d hd hd12
          (((degreePointFrobeniusTwo d : _ → _)^[i.1]) P.1) =
        ((commonPointFrobeniusTwo : _ → _)^[i.1])
          (degreeCurvePointEmbeddingToCommon12 d hd hd12 P.1) := by
            exact
              (degreeCurvePointEmbeddingToCommon12_semiconj
                d hd hd12).iterate_right i.1 P.1
      _ = degreeCurvePointEmbeddingToCommon12 d hd hd12 Q.1 := hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    calc
      ((commonPointFrobeniusTwo : _ → _)^[i.1])
          (degreeCurvePointEmbeddingToCommon12 d hd hd12 P.1) =
        degreeCurvePointEmbeddingToCommon12 d hd hd12
          (((degreePointFrobeniusTwo d : _ → _)^[i.1]) P.1) := by
            exact
              ((degreeCurvePointEmbeddingToCommon12_semiconj
                d hd hd12).iterate_right i.1 P.1).symm
      _ = degreeCurvePointEmbeddingToCommon12 d hd hd12 Q.1 := by
        rw [hi]

/-- Exact Frobenius orbit classes over the degree-`d` field agree with
degree-`d` orbit classes inside the common degree-twelve field. -/
noncomputable def orbitClassEquivDegreeToCommon12
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    OrbitClass (degreePointFrobeniusTwo d) d hd ≃
      OrbitClass commonPointFrobeniusTwo d hd := by
  let E := exactPeriodicPointEquivDegreeToCommon12 d hd hd12
  let f :
      OrbitClass (degreePointFrobeniusTwo d) d hd →
        OrbitClass commonPointFrobeniusTwo d hd :=
    Quotient.map E (by
      intro P Q hPQ
      exact (sameExactOrbit_degreeToCommon12_iff
        d hd hd12 P Q).2 hPQ)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ P =>
      induction b using Quotient.inductionOn with
      | _ Q =>
        apply Quotient.sound
        exact (sameExactOrbit_degreeToCommon12_iff
          d hd hd12 P Q).1 (Quotient.exact hab)
  · intro q
    induction q using Quotient.inductionOn with
    | _ Q =>
      refine ⟨orbitClassMk (degreePointFrobeniusTwo d) d hd (E.symm Q), ?_⟩
      exact congrArg
        (orbitClassMk commonPointFrobeniusTwo d hd)
        (E.apply_symm_apply Q)

/-- For every positive degree dividing twelve, the old common-field orbit
carrier agrees with the full degreewise closed-point carrier. -/
noncomputable def closedPointEquivCommon12ToFull
    (d : ℕ) (hd : 0 < d) (hd12 : d ∣ 12) :
    frobeniusOrbitGrading25TwoLE4.Closed d ≃
      fullClosedPointGrading25Two.Closed d := by
  cases d with
  | zero => omega
  | succ d =>
      exact
        (orbitClassEquivDegreeToCommon12
          (d + 1) (Nat.succ_pos d) hd12).symm

/-- Degree-one closed points in the old and full gradings agree. -/
noncomputable def closedPointDegreeOneEquiv :
    frobeniusOrbitGrading25TwoLE4.Closed 1 ≃
      fullClosedPointGrading25Two.Closed 1 :=
  closedPointEquivCommon12ToFull 1 (by norm_num) (by norm_num)

/-- Degree-two closed points in the old and full gradings agree. -/
noncomputable def closedPointDegreeTwoEquiv :
    frobeniusOrbitGrading25TwoLE4.Closed 2 ≃
      fullClosedPointGrading25Two.Closed 2 :=
  closedPointEquivCommon12ToFull 2 (by norm_num) (by norm_num)

/-- Degree-three closed points in the old and full gradings agree. -/
noncomputable def closedPointDegreeThreeEquiv :
    frobeniusOrbitGrading25TwoLE4.Closed 3 ≃
      fullClosedPointGrading25Two.Closed 3 :=
  closedPointEquivCommon12ToFull 3 (by norm_num) (by norm_num)

/-- Degree-four closed points in the old and full gradings agree. -/
noncomputable def closedPointDegreeFourEquiv :
    frobeniusOrbitGrading25TwoLE4.Closed 4 ≃
      fullClosedPointGrading25Two.Closed 4 :=
  closedPointEquivCommon12ToFull 4 (by norm_num) (by norm_num)

/-- The pointwise closed-point comparison through degree four. -/
noncomputable def closedPointEquivCommon12ToFullLE4
    (d : Fin 5) :
    frobeniusOrbitGrading25TwoLE4.Closed d.1 ≃
      fullClosedPointGrading25Two.Closed d.1 := by
  by_cases hd : d.1 = 0
  · have hdeq : d = 0 := Fin.ext hd
    subst d
    exact Equiv.refl _
  · apply closedPointEquivCommon12ToFull d.1 (Nat.pos_of_ne_zero hd)
    have hdle : d.1 ≤ 4 := Nat.le_of_lt_succ d.2
    have hcases : d.1 = 1 ∨ d.1 = 2 ∨ d.1 = 3 ∨ d.1 = 4 := by omega
    rcases hcases with h | h | h | h <;> simp [h]

/-- The degreewise comparison at every degree bounded by `k`, when
`k ≤ 4`. -/
noncomputable def closedPointEquivCommon12ToFullLE
    (k : ℕ) (hk : k ≤ 4) (d : Fin (k + 1)) :
    frobeniusOrbitGrading25TwoLE4.Closed d.1 ≃
      fullClosedPointGrading25Two.Closed d.1 :=
  closedPointEquivCommon12ToFullLE4
    ⟨d.1, Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.2).trans hk)⟩

/-- Transport bounded atoms through degree four without changing their
degree coordinate. -/
noncomputable def atomLEEquivCommon12ToFull
    (k : ℕ) (hk : k ≤ 4) :
    frobeniusOrbitGrading25TwoLE4.AtomLE k ≃
      fullClosedPointGrading25Two.AtomLE k :=
  (frobeniusOrbitGrading25TwoLE4.atomLEEquivSigma k).trans
    ((Equiv.sigmaCongrRight fun d =>
      closedPointEquivCommon12ToFullLE k hk d).trans
        (fullClosedPointGrading25Two.atomLEEquivSigma k).symm)

set_option maxHeartbeats 1000000 in
-- Proof-erasing inversion of the nested dependent sigma needs extra
-- elaboration resources but introduces no new mathematical input.
set_option maxRecDepth 100000 in
/-- Transport intrinsic ghost slots through degree four, preserving the
closed-point degree, copy count, and residue position. -/
noncomputable def exactGhostSlotEquivCommon12ToFull
    (k : ℕ) (hk : k ≤ 4) :
    CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        frobeniusOrbitGrading25TwoLE4 k ≃
      CurveZetaMarkedDivisors.ClosedPointGrading.ExactGhostSlot
        fullClosedPointGrading25Two k where
  toFun s := by
    rcases s with ⟨x, r, t⟩
    let e := atomLEEquivCommon12ToFull k hk
    let x' := e x
    have hdegree :
        fullClosedPointGrading25Two.atomDegree x'.1 =
          frobeniusOrbitGrading25TwoLE4.atomDegree x.1 := by
      rfl
    let r' : CurveZetaMarkedDivisors.ClosedPointGrading.ExactCopies
        fullClosedPointGrading25Two k x' :=
      ⟨r.1, r.2.1, by simpa only [hdegree] using r.2.2⟩
    let t' : Fin (fullClosedPointGrading25Two.atomDegree x'.1) :=
      Fin.cast hdegree.symm t
    exact ⟨x', r', t'⟩
  invFun s := by
    rcases s with ⟨x, r, t⟩
    let e := atomLEEquivCommon12ToFull k hk
    let x' := e.symm x
    have hdegree :
        frobeniusOrbitGrading25TwoLE4.atomDegree x'.1 =
          fullClosedPointGrading25Two.atomDegree x.1 := by
      rfl
    let r' : CurveZetaMarkedDivisors.ClosedPointGrading.ExactCopies
        frobeniusOrbitGrading25TwoLE4 k x' :=
      ⟨r.1, r.2.1, by simpa only [hdegree] using r.2.2⟩
    let t' : Fin (frobeniusOrbitGrading25TwoLE4.atomDegree x'.1) :=
      Fin.cast hdegree.symm t
    exact ⟨x', r', t'⟩
  left_inv s := by
    apply CurveZetaMarkedDivisors.ClosedPointGrading.exactGhostCoordinates_injective
      frobeniusOrbitGrading25TwoLE4 k
    rcases s with ⟨x, r, t⟩
    change
      (((atomLEEquivCommon12ToFull k hk).symm
          (atomLEEquivCommon12ToFull k hk x)).1, r.1.1, t.1) =
        (x.1, r.1.1, t.1)
    rw [(atomLEEquivCommon12ToFull k hk).symm_apply_apply]
  right_inv s := by
    apply CurveZetaMarkedDivisors.ClosedPointGrading.exactGhostCoordinates_injective
      fullClosedPointGrading25Two k
    rcases s with ⟨x, r, t⟩
    change
      ((atomLEEquivCommon12ToFull k hk
          ((atomLEEquivCommon12ToFull k hk).symm x)).1, r.1.1, t.1) =
        (x.1, r.1.1, t.1)
    rw [(atomLEEquivCommon12ToFull k hk).apply_symm_apply]

/-- The semantic point-count bridge through degree four, now carried by the
full degreewise closed-point grading rather than a fixed finite field. -/
noncomputable def fullClosedPointBridge25TwoLE4 :
    ClosedPointBridge25TwoLE4 fullClosedPointGrading25Two where
  classify i :=
    (frobeniusClosedPointBridge25TwoLE4.classify i).trans
      (exactGhostSlotEquivCommon12ToFull
        (ExtensionIndex25Two.exponent i) (by
          cases i <;> norm_num [ExtensionIndex25Two.exponent]))

end MazurProof.RationalPointsN25QuotientTwoFullClosedPoints
