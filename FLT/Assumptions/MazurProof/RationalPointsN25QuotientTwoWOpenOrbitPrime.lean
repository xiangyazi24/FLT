import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoWBoundaryClosedPoints
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoPlaneChartClosedPoints

/-!
# Representative-independent primes for closed orbits on the \`W\` open

Every exact-period orbit of degree greater than one lies on \`W != 0\`.
Frobenius invariance of fixed-chart evaluation therefore descends its kernel
to the orbit quotient.  The descended ideal is nonzero, maximal, height one,
and has residue cardinality \`2^d\`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrime

open CurveZetaFrobeniusOrbitGrading
open FiniteFieldFrobeniusDescent
open NormalizedProjectiveCurveFrobenius
open RationalPointsN25QuotientSmoothF2
open RationalPointsN25QuotientTwoFullClosedPoints
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoBaseChange
open RationalPointsN25QuotientTwoWBoundaryClosedPoints
open RationalPointsN25QuotientTwoWOpenEvaluation
open RationalPointsN25QuotientTwoWOpenResidueDegree
open RationalPointsN25QuotientTwoPlaneChartClosedPoints
open Function

/-- Regard a degree-greater-than-one exact-period point as a point of the
fixed projective `W` open. -/
def exactPeriodicPointOnWOpen
    (d : ℕ) (hd : 1 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    CurvePointOnWOpen (CommonField 2 d) :=
  ⟨Q.1, exactPeriodicPoint_w_ne_zero_of_one_lt d hd Q⟩

/-- The `W`-open packaging commutes with one arithmetic Frobenius step. -/
theorem exactPeriodicPointOnWOpen_frobenius
    (d : ℕ) (hd : 1 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    exactPeriodicPointOnWOpen d hd
        ⟨degreePointFrobeniusTwo d Q.1,
          by
            rw [minimalPeriod_apply
              (exactPeriodicPoint_mem_periodicPts
                (degreePointFrobeniusTwo d) (by omega) Q)]
            exact Q.2⟩ =
      (exactPeriodicPointOnWOpen d hd Q).map
        (commonFrobenius 2 d).toRingEquiv := by
  apply CurvePointOnWOpen.ext
  rfl

/-- Exact-period points in the same Frobenius orbit have the same evaluation
kernel on the fixed `w = 1` chart. -/
theorem sameExactOrbit_wOpen_ker_eq
    (d : ℕ) (hd : 1 < d)
    (P Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d)
    (hPQ : SameExactOrbit (degreePointFrobeniusTwo d) d P Q) :
    RingHom.ker (wOpenChartQuotientEval
        (exactPeriodicPointOnWOpen d hd P)) =
      RingHom.ker (wOpenChartQuotientEval
        (exactPeriodicPointOnWOpen d hd Q)) := by
  rcases hPQ with ⟨n, hn⟩
  let e : CommonField 2 d ≃+* CommonField 2 d :=
    (commonFrobenius 2 d ^ n.1).toRingEquiv
  let PW := exactPeriodicPointOnWOpen d hd P
  let QW := exactPeriodicPointOnWOpen d hd Q
  have hn' :
      ((pointFrobeniusFun canonicalTwoModel 2 d : _ → _)^[n.1]) P.1 =
        Q.1 := by
    exact hn
  have hiter := pointFrobenius_iterate_val
    canonicalTwoModel 2 d n.1 P.1
  have hval :
      RationalPointsN25QuotientBaseChange.NormalizedProjective4.map
          e.toRingHom P.1.1 = Q.1.1 := by
    change RationalPointsN25QuotientBaseChange.NormalizedProjective4.map
        (commonFrobenius 2 d ^ n.1).toRingEquiv.toRingHom P.1.1 = Q.1.1
    exact hiter.symm.trans (congrArg Subtype.val hn')
  have hpoint : (PW.map e).point = QW.point := by
    apply Subtype.ext
    exact hval
  have hopen : PW.map e = QW := CurvePointOnWOpen.ext hpoint
  change RingHom.ker (wOpenChartQuotientEval PW) =
    RingHom.ker (wOpenChartQuotientEval QW)
  rw [← hopen]
  exact (wOpenChartQuotientEval_ker_map e PW).symm

/-- The fixed-chart prime attached to a degree-greater-than-one closed
Frobenius orbit, independent of its representative. -/
def wOpenOrbitPrime
    (d : ℕ) (hd : 1 < d)
    (c : OrbitClass (degreePointFrobeniusTwo d) d (by omega)) :
    PrimeSpectrum WChartQuotient :=
  Quotient.lift
    (fun Q => ⟨RingHom.ker (wOpenChartQuotientEval
      (exactPeriodicPointOnWOpen d hd Q)),
      RingHom.ker_isPrime (wOpenChartQuotientEval
        (exactPeriodicPointOnWOpen d hd Q))⟩)
    (by
      intro P Q hPQ
      apply PrimeSpectrum.ext
      exact sameExactOrbit_wOpen_ker_eq d hd P Q hPQ)
    c

/-- The descended orbit prime is maximal. -/
theorem wOpenOrbitPrime_isMaximal
    (d : ℕ) (hd : 1 < d)
    (c : OrbitClass (degreePointFrobeniusTwo d) d (by omega)) :
    (wOpenOrbitPrime d hd c).asIdeal.IsMaximal := by
  induction c using Quotient.inductionOn with
  | _ Q =>
      exact wOpenChartQuotientEval_ker_isMaximal
        (exactPeriodicPointOnWOpen d hd Q)

/-- The descended orbit prime is nonzero. -/
theorem wOpenOrbitPrime_ne_bot
    (d : ℕ) (hd : 1 < d)
    (c : OrbitClass (degreePointFrobeniusTwo d) d (by omega)) :
    (wOpenOrbitPrime d hd c).asIdeal ≠ ⊥ :=
  canonicalWChart_maximal_ne_bot _ (wOpenOrbitPrime_isMaximal d hd c)

/-- The descended orbit prime has height exactly one. -/
theorem wOpenOrbitPrime_height_eq_one
    (d : ℕ) (hd : 1 < d)
    (c : OrbitClass (degreePointFrobeniusTwo d) d (by omega)) :
    (wOpenOrbitPrime d hd c).asIdeal.height = 1 :=
  canonicalWChart_maximal_height_eq_one _
    (wOpenOrbitPrime_isMaximal d hd c)

/-- The representative-independent residue ring of a closed orbit on the
fixed `W` chart. -/
abbrev WOpenOrbitResidue
    (d : ℕ) (hd : 1 < d)
    (c : OrbitClass (degreePointFrobeniusTwo d) d (by omega)) :=
  WChartQuotient ⧸ (wOpenOrbitPrime d hd c).asIdeal

/-- A degree-`d` closed orbit on the `W` open has residue cardinality
exactly `2^d`. -/
theorem wOpenOrbitResidue_card
    (d : ℕ) (hd : 1 < d)
    (c : OrbitClass (degreePointFrobeniusTwo d) d (by omega)) :
    Nat.card (WOpenOrbitResidue d hd c) = 2 ^ d := by
  induction c using Quotient.inductionOn with
  | _ Q =>
      exact (Nat.card_congr
        (RingHom.quotientKerEquivRange
          (wOpenChartQuotientEval
            (exactPeriodicPointOnWOpen d hd Q))).toEquiv).trans
        (exactPeriodicWOpen_eval_range_card d (by omega) Q
          (exactPeriodicPoint_w_ne_zero_of_one_lt d hd Q))

/-! ## Interface on the full closed-point grading -/

/-- Every full closed point of degree greater than one defines a prime on
the fixed integral `W` chart. -/
noncomputable def fullClosedPointWOpenPrime :
    (d : ℕ) → 1 < d → fullClosedPointGrading25Two.Closed d →
      PrimeSpectrum WChartQuotient
  | 0, hd, _ => by omega
  | d + 1, hd, P => wOpenOrbitPrime (d + 1) hd P

/-- The fixed-chart prime attached to a full closed point of degree greater
than one is maximal. -/
theorem fullClosedPointWOpenPrime_isMaximal
    (d : ℕ) (hd : 1 < d)
    (P : fullClosedPointGrading25Two.Closed d) :
    (fullClosedPointWOpenPrime d hd P).asIdeal.IsMaximal := by
  revert hd P
  cases d with
  | zero =>
      intro hd
      omega
  | succ d =>
      intro hd P
      exact wOpenOrbitPrime_isMaximal (d + 1) hd P

/-- The fixed-chart prime attached to a full closed point of degree greater
than one is nonzero. -/
theorem fullClosedPointWOpenPrime_ne_bot
    (d : ℕ) (hd : 1 < d)
    (P : fullClosedPointGrading25Two.Closed d) :
    (fullClosedPointWOpenPrime d hd P).asIdeal ≠ ⊥ := by
  revert hd P
  cases d with
  | zero =>
      intro hd
      omega
  | succ d =>
      intro hd P
      exact wOpenOrbitPrime_ne_bot (d + 1) hd P

/-- The fixed-chart prime attached to a full closed point of degree greater
than one has height exactly one. -/
theorem fullClosedPointWOpenPrime_height_eq_one
    (d : ℕ) (hd : 1 < d)
    (P : fullClosedPointGrading25Two.Closed d) :
    (fullClosedPointWOpenPrime d hd P).asIdeal.height = 1 := by
  revert hd P
  cases d with
  | zero =>
      intro hd
      omega
  | succ d =>
      intro hd P
      exact wOpenOrbitPrime_height_eq_one (d + 1) hd P

/-- The fixed-chart residue ring of a full closed point of degree greater
than one. -/
abbrev FullClosedPointWOpenResidue
    (d : ℕ) (hd : 1 < d)
    (P : fullClosedPointGrading25Two.Closed d) :=
  WChartQuotient ⧸ (fullClosedPointWOpenPrime d hd P).asIdeal

/-- The fixed-chart residue of a full degree-`d` closed point has exactly
`2^d` elements. -/
theorem fullClosedPointWOpenResidue_card
    (d : ℕ) (hd : 1 < d)
    (P : fullClosedPointGrading25Two.Closed d) :
    Nat.card (FullClosedPointWOpenResidue d hd P) = 2 ^ d := by
  revert hd P
  cases d with
  | zero =>
      intro hd
      omega
  | succ d =>
      intro hd P
      exact wOpenOrbitResidue_card (d + 1) hd P

end MazurProof.RationalPointsN25QuotientTwoWOpenOrbitPrime
