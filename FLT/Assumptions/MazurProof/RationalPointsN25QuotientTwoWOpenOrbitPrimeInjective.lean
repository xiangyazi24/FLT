import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointPartition

/-!
# Injectivity of W-open closed-point primes

An exact-period point on `W != 0` evaluates the fixed chart ring onto its
full residue field.  Two such evaluation kernels therefore differ by a
finite-field automorphism, hence by a Frobenius power.  Recovering the three
affine coordinates shows that equal kernels mean equal closed orbits.

Residue cardinality first recovers the degree, so this fixed-degree result
gives an injection from every nonboundary full closed-point atom to a
height-one maximal ideal of the fixed `W` chart.  Degree one is handled over
`F₂`, where the only `F₂`-algebra automorphism is the identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective

open Function
open CurveZetaFrobeniusOrbitGrading
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientF2
open RationalPointsN25QuotientWeil
open RationalPointsN25QuotientMiddleRiemannRoch
open RationalPointsN25QuotientBaseChange
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoAffineCharts
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoConormal
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenResidueDegree
open RationalPointsN25QuotientTwoWOpenOrbitPrime
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoClosedPointPartition

private theorem ringHom_surjective_of_range_natCard_eq
    {A K : Type*} [Ring A] [Ring K] [Finite K]
    (f : A →+* K) (hcard : Nat.card f.range = Nat.card K) :
    Function.Surjective f := by
  have hsub : Function.Surjective ((↑) : f.range → K) :=
    (Subtype.val_injective.bijective_of_nat_card_le (by rw [hcard])).2
  intro y
  obtain ⟨z, hz⟩ := hsub y
  rcases z.2 with ⟨x, hx⟩
  exact ⟨x, hx.trans hz⟩

/-- Exact period forces the fixed `W`-chart evaluation to generate the whole
finite residue field. -/
theorem exactPeriodicWOpen_eval_surjective
    (d : ℕ) (hd : 0 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (hW : (normalizedCoordinates25 Q.1.1).w ≠ 0) :
    Function.Surjective (wOpenChartQuotientEvalAlgHom
      (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d))) := by
  change Function.Surjective
    (wOpenChartQuotientEvalAlgHom
      (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d))).toRingHom
  apply ringHom_surjective_of_range_natCard_eq
  change Nat.card (wOpenChartQuotientEval
    (⟨Q.1, hW⟩ : CurvePointOnWOpen (CommonField 2 d))).range =
      Nat.card (CommonField 2 d)
  rw [exactPeriodicWOpen_eval_range_card d hd Q hW,
    GaloisField.card 2 d hd.ne']

/-- Two surjective algebra maps to the same field with equal kernels differ
by an algebra automorphism of that field. -/
noncomputable def algEquivOfSurjectiveEqKer
    {F A K : Type*}
    [CommRing F] [CommRing A] [Field K]
    [Algebra F A] [Algebra F K]
    (f g : A →ₐ[F] K)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (hker : RingHom.ker f.toRingHom = RingHom.ker g.toRingHom) :
    K ≃ₐ[F] K := by
  let H : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom :=
    le_of_eq hker
  let σ : K →ₐ[F] K := AlgHom.liftOfSurjective f hf g H
  have hσsurj : Function.Surjective σ :=
    AlgHom.liftOfSurjective_surjective f hf g H hg
  exact AlgEquiv.ofBijective σ
    ⟨RingHom.injective σ.toRingHom, hσsurj⟩

/-- The automorphism induced by two equal-kernel quotient presentations
intertwines the original algebra maps. -/
theorem algEquivOfSurjectiveEqKer_comp
    {F A K : Type*}
    [CommRing F] [CommRing A] [Field K]
    [Algebra F A] [Algebra F K]
    (f g : A →ₐ[F] K)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (hker : RingHom.ker f.toRingHom = RingHom.ker g.toRingHom) :
    (algEquivOfSurjectiveEqKer f g hf hg hker).toAlgHom.comp f = g := by
  let H : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom :=
    le_of_eq hker
  simpa [algEquivOfSurjectiveEqKer, H] using
    AlgHom.liftOfSurjective_comp f hf g H

/-- Every `F₂`-algebra automorphism of the common degree-`d` field is a
power of arithmetic Frobenius. -/
theorem commonFieldTwo_algEquiv_eq_frobenius_pow
    (d : ℕ) (hd : 0 < d)
    (σ : CommonField 2 d ≃ₐ[ZMod 2] CommonField 2 d) :
    ∃ n : Fin d, σ = commonFrobenius 2 d ^ n.1 := by
  have hbij :=
    FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ZMod 2) (CommonField 2 d)
  rw [GaloisField.finrank 2 hd.ne'] at hbij
  obtain ⟨n, hn⟩ := hbij.surjective σ
  exact ⟨n, by simpa [commonFrobenius] using hn.symm⟩

/-- Equality of all normalized `W`-chart coordinates recovers equality of
the underlying normalized projective points. -/
theorem normalizedProjective4_map_eq_of_wOpenCoordinates
    {K : Type} [Field K]
    (e : K ≃+* K) (P Q : CurvePointOnWOpen K)
    (hcoords : Coordinates4.map e.toRingHom (wOpenCoordinates P) =
      wOpenCoordinates Q) :
    NormalizedProjective4.map e.toRingHom P.point.1 = Q.point.1 := by
  rcases P with ⟨⟨P, hcurveP⟩, hwP⟩
  rcases Q with ⟨⟨Q, hcurveQ⟩, hwQ⟩
  cases P <;> cases Q <;>
    simp [wOpenCoordinates, normalizeAtW, scaleCoordinates4,
      normalizedCoordinates25, NormalizedProjective4.coordinates,
      fieldBinaryOperations, Coordinates4.map] at hcoords hwP hwQ ⊢
  case xChart.xChart =>
    rcases hcoords with ⟨hew, hey, hez, _⟩
    rw [hew] at hey hez
    field_simp [hwQ] at hey hez
    exact ⟨hey, hez, hew⟩
  case xChart.yChart => exact hwP hcoords.1
  case xChart.zChart => exact hwP hcoords.1
  case xChart.wChart => exact hwP hcoords.1
  case yChart.xChart => exact hwQ hcoords.1.symm
  case yChart.yChart =>
    rcases hcoords with ⟨hew, hez, _⟩
    rw [hew] at hez
    field_simp [hwQ] at hez
    exact ⟨hez, hew⟩
  case yChart.zChart => exact hwP hcoords.1
  case yChart.wChart => exact hwP hcoords.1
  case zChart.xChart => exact hwQ hcoords.1.symm
  case zChart.yChart => exact hwQ hcoords.1.symm
  case zChart.zChart => exact hcoords.1
  case zChart.wChart => exact hwP hcoords.1
  case wChart.xChart => exact hwQ hcoords.1.symm
  case wChart.yChart => exact hwQ hcoords.1.symm
  case wChart.zChart => exact hwQ hcoords.1.symm

private theorem coordinates4_ext
    {K : Type*} {P Q : Coordinates4 K}
    (hx : P.x = Q.x) (hy : P.y = Q.y)
    (hz : P.z = Q.z) (hw : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  simp_all

/-- Equal fixed-`W` evaluation kernels of exact-period points imply that the
points belong to the same Frobenius orbit. -/
theorem sameExactOrbit_of_wOpen_ker_eq
    {d : ℕ} (hd : 0 < d)
    (P Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (hPw : (normalizedCoordinates25 P.1.1).w ≠ 0)
    (hQw : (normalizedCoordinates25 Q.1.1).w ≠ 0)
    (hker :
      RingHom.ker (wOpenChartQuotientEvalAlgHom
        (⟨P.1, hPw⟩ : CurvePointOnWOpen (CommonField 2 d))).toRingHom =
      RingHom.ker (wOpenChartQuotientEvalAlgHom
        (⟨Q.1, hQw⟩ : CurvePointOnWOpen (CommonField 2 d))).toRingHom) :
    SameExactOrbit (degreePointFrobeniusTwo d) d P Q := by
  let PW : CurvePointOnWOpen (CommonField 2 d) := ⟨P.1, hPw⟩
  let QW : CurvePointOnWOpen (CommonField 2 d) := ⟨Q.1, hQw⟩
  let evP := wOpenChartQuotientEvalAlgHom PW
  let evQ := wOpenChartQuotientEvalAlgHom QW
  have hsurjP : Function.Surjective evP :=
    exactPeriodicWOpen_eval_surjective d hd P hPw
  have hsurjQ : Function.Surjective evQ :=
    exactPeriodicWOpen_eval_surjective d hd Q hQw
  have hker' : RingHom.ker evP.toRingHom = RingHom.ker evQ.toRingHom := by
    simpa [evP, evQ, PW, QW] using hker
  let σ : CommonField 2 d ≃ₐ[ZMod 2] CommonField 2 d :=
    algEquivOfSurjectiveEqKer evP evQ hsurjP hsurjQ hker'
  have hσeval (x : WChartQuotient) : σ (evP x) = evQ x := by
    have hcomp := algEquivOfSurjectiveEqKer_comp
      evP evQ hsurjP hsurjQ hker'
    exact DFunLike.congr_fun hcomp x
  obtain ⟨i, hiσ⟩ := commonFieldTwo_algEquiv_eq_frobenius_pow d hd σ
  let qx : WChartQuotient :=
    Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
      (MvPolynomial.X (⟨0, by decide⟩ : OtherCoordinate (3 : Fin 4)))
  let qy : WChartQuotient :=
    Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
      (MvPolynomial.X (⟨1, by decide⟩ : OtherCoordinate (3 : Fin 4)))
  let qz : WChartQuotient :=
    Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
      (MvPolynomial.X (⟨2, by decide⟩ : OtherCoordinate (3 : Fin 4)))
  have hcoords :
      Coordinates4.map σ.toRingEquiv.toRingHom (wOpenCoordinates PW) =
        wOpenCoordinates QW := by
    apply coordinates4_ext
    · change σ (wOpenCoordinates PW).x = (wOpenCoordinates QW).x
      have h := hσeval qx
      change σ (wOpenChartQuotientEval PW qx) =
        wOpenChartQuotientEval QW qx at h
      simpa [qx, wOpenAffineEval, coordinates4ToFun] using h
    · change σ (wOpenCoordinates PW).y = (wOpenCoordinates QW).y
      have h := hσeval qy
      change σ (wOpenChartQuotientEval PW qy) =
        wOpenChartQuotientEval QW qy at h
      simpa [qy, wOpenAffineEval, coordinates4ToFun] using h
    · change σ (wOpenCoordinates PW).z = (wOpenCoordinates QW).z
      have h := hσeval qz
      change σ (wOpenChartQuotientEval PW qz) =
        wOpenChartQuotientEval QW qz at h
      simpa [qz, wOpenAffineEval, coordinates4ToFun] using h
    · change σ (wOpenCoordinates PW).w = (wOpenCoordinates QW).w
      simp
  have hproj :
      NormalizedProjective4.map σ.toRingEquiv.toRingHom P.1.1 = Q.1.1 := by
    simpa [PW, QW] using
      normalizedProjective4_map_eq_of_wOpenCoordinates σ.toRingEquiv PW QW hcoords
  refine ⟨i, ?_⟩
  change ((pointFrobeniusFun canonicalTwoModel 2 d : _ → _)^[i.1]) P.1 = Q.1
  apply Subtype.ext
  rw [pointFrobenius_iterate_val, ← hiσ]
  exact hproj

/-- Evaluation at an `F₂`-rational point is surjective onto `F₂`. -/
theorem wOpenF2_eval_surjective (P : CurvePointOnWOpen F2) :
    Function.Surjective (wOpenChartQuotientEvalAlgHom P) := by
  intro y
  refine ⟨algebraMap (ZMod 2) WChartQuotient y, ?_⟩
  exact (wOpenChartQuotientEvalAlgHom P).commutes y

/-- On the `W` chart, two `F₂`-points with the same evaluation kernel are
equal. -/
theorem wOpenF2_eq_of_ker_eq
    (P Q : CurvePointOnWOpen F2)
    (hker : RingHom.ker (wOpenChartQuotientEval P) =
      RingHom.ker (wOpenChartQuotientEval Q)) : P = Q := by
  let evP := wOpenChartQuotientEvalAlgHom P
  let evQ := wOpenChartQuotientEvalAlgHom Q
  have hsurjP : Function.Surjective evP := wOpenF2_eval_surjective P
  have hsurjQ : Function.Surjective evQ := wOpenF2_eval_surjective Q
  have hker' : RingHom.ker evP.toRingHom = RingHom.ker evQ.toRingHom := by
    change RingHom.ker (wOpenChartQuotientEval P) =
      RingHom.ker (wOpenChartQuotientEval Q)
    exact hker
  let σ : F2 ≃ₐ[F2] F2 :=
    algEquivOfSurjectiveEqKer evP evQ hsurjP hsurjQ hker'
  have hσeval (x : WChartQuotient) : σ (evP x) = evQ x := by
    have hcomp := algEquivOfSurjectiveEqKer_comp
      evP evQ hsurjP hsurjQ hker'
    exact DFunLike.congr_fun hcomp x
  have heval (x : WChartQuotient) : evP x = evQ x := by
    have hfix : σ (evP x) = evP x := by
      simpa using σ.commutes (evP x)
    exact hfix.symm.trans (hσeval x)
  let qx : WChartQuotient :=
    Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
      (MvPolynomial.X (⟨0, by decide⟩ : OtherCoordinate (3 : Fin 4)))
  let qy : WChartQuotient :=
    Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
      (MvPolynomial.X (⟨1, by decide⟩ : OtherCoordinate (3 : Fin 4)))
  let qz : WChartQuotient :=
    Ideal.Quotient.mk (chartAffineEquationIdeal (3 : Fin 4))
      (MvPolynomial.X (⟨2, by decide⟩ : OtherCoordinate (3 : Fin 4)))
  have hcoords : wOpenCoordinates P = wOpenCoordinates Q := by
    apply coordinates4_ext
    · have h := heval qx
      change wOpenChartQuotientEval P qx =
        wOpenChartQuotientEval Q qx at h
      simpa [qx, wOpenAffineEval, coordinates4ToFun] using h
    · have h := heval qy
      change wOpenChartQuotientEval P qy =
        wOpenChartQuotientEval Q qy at h
      simpa [qy, wOpenAffineEval, coordinates4ToFun] using h
    · have h := heval qz
      change wOpenChartQuotientEval P qz =
        wOpenChartQuotientEval Q qz at h
      simpa [qz, wOpenAffineEval, coordinates4ToFun] using h
    · simp
  have hproj : P.point.1 = Q.point.1 := by
    have h := normalizedProjective4_map_eq_of_wOpenCoordinates
      (RingEquiv.refl F2) P Q (by
        have hrefl : Coordinates4.map (RingEquiv.refl F2).toRingHom
            (wOpenCoordinates P) = wOpenCoordinates P := by
          cases wOpenCoordinates P
          rfl
        exact hrefl.trans hcoords)
    simpa using h
  exact CurvePointOnWOpen.ext (Subtype.ext hproj)

/-- The fixed-`W` chart prime attached to a nonboundary full closed-point
atom. -/
noncomputable def fullNonBoundaryPrimeIdeal
    (A : FullNonBoundaryAtom25Two) : Ideal WChartQuotient :=
  (fullNonBoundaryPrimeData A).ideal

/-- The residue field at a nonboundary atom has cardinality `2^degree`. -/
theorem fullNonBoundaryPrimeIdeal_residue_card
    (A : FullNonBoundaryAtom25Two) :
    Nat.card (WChartQuotient ⧸ fullNonBoundaryPrimeIdeal A) =
      2 ^ fullClosedPointGrading25Two.atomDegree A.1 :=
  (fullNonBoundaryPrimeData A).residue_card

/-- A nonboundary degree-one atom lies on the geometric open `W != 0`. -/
theorem fullDegreeOneNonBoundary_w_ne_zero
    (c : fullClosedPointGrading25Two.Closed 1)
    (hnb : ¬ IsFullBoundaryAtom (⟨1, c⟩ : FullAtom25Two)) :
    (normalizedCoordinates25 (fullDegreeOnePointEquiv.symm c).1).w ≠ 0 := by
  let P : ExtensionIndex25Two.pointType .degreeOne :=
    fullDegreeOnePointEquiv.symm c
  have hPc : fullDegreeOnePointEquiv P = c :=
    fullDegreeOnePointEquiv.apply_symm_apply c
  intro hzero
  rcases primeFieldCurvePoint_w_eq_zero_classification P hzero with
    hX | hYZ | hZ
  · have hc : c = fullBoundaryClosedPointX :=
      hPc.symm.trans (congrArg fullDegreeOnePointEquiv hX)
    apply hnb
    apply Or.inl
    have hatom := congrArg (fun z => (⟨1, z⟩ : FullAtom25Two)) hc
    simpa [fullBoundaryAtomX] using hatom
  · have hc : c = fullBoundaryClosedPointYZ :=
      hPc.symm.trans (congrArg fullDegreeOnePointEquiv hYZ)
    apply hnb
    apply Or.inr
    apply Or.inl
    have hatom := congrArg (fun z => (⟨1, z⟩ : FullAtom25Two)) hc
    simpa [fullBoundaryAtomYZ] using hatom
  · have hc : c = fullBoundaryClosedPointZ :=
      hPc.symm.trans (congrArg fullDegreeOnePointEquiv hZ)
    apply hnb
    apply Or.inr
    apply Or.inr
    have hatom := congrArg (fun z => (⟨1, z⟩ : FullAtom25Two)) hc
    simpa [fullBoundaryAtomZ] using hatom

/-- The `W`-open point represented by a nonboundary degree-one atom. -/
noncomputable def fullDegreeOneNonBoundaryWOpenPoint
    (c : fullClosedPointGrading25Two.Closed 1)
    (hnb : ¬ IsFullBoundaryAtom (⟨1, c⟩ : FullAtom25Two)) :
    CurvePointOnWOpen F2 :=
  ⟨fullDegreeOnePointEquiv.symm c,
    fullDegreeOneNonBoundary_w_ne_zero c hnb⟩

/-- Nonboundary full atoms of degree strictly greater than one. -/
def FullHigherNonBoundaryAtom25Two :=
  {A : FullNonBoundaryAtom25Two //
    1 < fullClosedPointGrading25Two.atomDegree A.1}

/-- The fixed-`W` chart prime restricted to higher-degree nonboundary atoms. -/
noncomputable def fullHigherNonBoundaryPrimeIdeal
    (A : FullHigherNonBoundaryAtom25Two) : Ideal WChartQuotient :=
  fullNonBoundaryPrimeIdeal A.1

/-- The higher-degree fixed-chart residue cardinality formula. -/
theorem fullHigherNonBoundaryPrimeIdeal_residue_card
    (A : FullHigherNonBoundaryAtom25Two) :
    Nat.card (WChartQuotient ⧸ fullHigherNonBoundaryPrimeIdeal A) =
      2 ^ fullClosedPointGrading25Two.atomDegree A.1.1 :=
  (fullNonBoundaryPrimeData A.1).residue_card

/-- Higher-degree nonboundary atoms have distinct fixed-`W` chart primes. -/
theorem fullHigherNonBoundaryPrimeIdeal_injective :
    Function.Injective fullHigherNonBoundaryPrimeIdeal := by
  intro A B hprime
  have hpow :
      2 ^ fullClosedPointGrading25Two.atomDegree A.1.1 =
        2 ^ fullClosedPointGrading25Two.atomDegree B.1.1 := by
    calc
      2 ^ fullClosedPointGrading25Two.atomDegree A.1.1 =
          Nat.card (WChartQuotient ⧸ fullHigherNonBoundaryPrimeIdeal A) :=
        (fullHigherNonBoundaryPrimeIdeal_residue_card A).symm
      _ = Nat.card (WChartQuotient ⧸ fullHigherNonBoundaryPrimeIdeal B) := by
        rw [hprime]
      _ = 2 ^ fullClosedPointGrading25Two.atomDegree B.1.1 :=
        fullHigherNonBoundaryPrimeIdeal_residue_card B
  have hdegree := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  rcases A with ⟨⟨⟨d, c⟩, hnbA⟩, hdA⟩
  rcases B with ⟨⟨⟨e, c'⟩, hnbB⟩, hdB⟩
  change d = e at hdegree
  subst e
  change 1 < d at hdA hdB
  have hcc : c = c' := by
    cases d with
    | zero => omega
    | succ n =>
        cases n with
        | zero => omega
        | succ n =>
            change
              (wOpenOrbitPrime (n + 2) (by omega) c).asIdeal =
                (wOpenOrbitPrime (n + 2) (by omega) c').asIdeal at hprime
            induction c using Quotient.inductionOn with
            | _ P =>
                induction c' using Quotient.inductionOn with
                | _ Q =>
                    apply Quotient.sound
                    apply sameExactOrbit_of_wOpen_ker_eq (by omega) P Q
                      (exactPeriodicPoint_w_ne_zero_of_one_lt
                        (n + 2) (by omega) P)
                      (exactPeriodicPoint_w_ne_zero_of_one_lt
                        (n + 2) (by omega) Q)
                    exact hprime
  subst c'
  rfl

/-- All nonboundary full closed-point atoms have distinct fixed-`W` chart
primes. -/
theorem fullNonBoundaryPrimeIdeal_injective :
    Function.Injective fullNonBoundaryPrimeIdeal := by
  intro A B hprime
  have hpow :
      2 ^ fullClosedPointGrading25Two.atomDegree A.1 =
        2 ^ fullClosedPointGrading25Two.atomDegree B.1 := by
    calc
      2 ^ fullClosedPointGrading25Two.atomDegree A.1 =
          Nat.card (WChartQuotient ⧸ fullNonBoundaryPrimeIdeal A) :=
        (fullNonBoundaryPrimeIdeal_residue_card A).symm
      _ = Nat.card (WChartQuotient ⧸ fullNonBoundaryPrimeIdeal B) := by
        rw [hprime]
      _ = 2 ^ fullClosedPointGrading25Two.atomDegree B.1 :=
        fullNonBoundaryPrimeIdeal_residue_card B
  have hdegree := Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  rcases A with ⟨⟨d, c⟩, hnbA⟩
  rcases B with ⟨⟨e, c'⟩, hnbB⟩
  change d = e at hdegree
  subst e
  cases d with
  | zero => exact (isEmptyElim c : False).elim
  | succ n =>
      cases n with
      | zero =>
          let P : CurvePointOnWOpen F2 :=
            fullDegreeOneNonBoundaryWOpenPoint c hnbA
          let Q : CurvePointOnWOpen F2 :=
            fullDegreeOneNonBoundaryWOpenPoint c' hnbB
          have hker :
              RingHom.ker (wOpenChartQuotientEval P) =
                RingHom.ker (wOpenChartQuotientEval Q) := by
            simpa [fullNonBoundaryPrimeIdeal, fullNonBoundaryPrimeData,
              degreeOneWOpenPrimeData, P, Q,
              fullDegreeOneNonBoundaryWOpenPoint] using hprime
          have hPQ : P = Q := wOpenF2_eq_of_ker_eq P Q hker
          have hpoints : fullDegreeOnePointEquiv.symm c =
              fullDegreeOnePointEquiv.symm c' := by
            exact congrArg CurvePointOnWOpen.point hPQ
          have hcc : c = c' := fullDegreeOnePointEquiv.symm.injective hpoints
          subst c'
          rfl
      | succ n =>
          let A' : FullHigherNonBoundaryAtom25Two :=
            ⟨⟨(⟨n + 2, c⟩ : FullAtom25Two), hnbA⟩, by
              change 1 < n + 2
              omega⟩
          let B' : FullHigherNonBoundaryAtom25Two :=
            ⟨⟨(⟨n + 2, c'⟩ : FullAtom25Two), hnbB⟩, by
              change 1 < n + 2
              omega⟩
          have hprime' : fullHigherNonBoundaryPrimeIdeal A' =
              fullHigherNonBoundaryPrimeIdeal B' := by
            exact hprime
          have hAB := fullHigherNonBoundaryPrimeIdeal_injective hprime'
          exact congrArg Subtype.val hAB

end MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrimeInjective
