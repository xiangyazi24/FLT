import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoAffineCanonicalDifferentials
import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoClosedPointResidueDegree
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoClosedPointKernelNonzero

open KaehlerDifferential
open CurveZetaFrobeniusOrbitGrading
open RationalPointsN25QuotientTwoAffineChartsSmooth
open RationalPointsN25QuotientTwoAffineCanonicalDifferentials
open RationalPointsN25QuotientBinaryFieldSemantics
open RationalPointsN25QuotientTwoClosedPointChart
open RationalPointsN25QuotientTwoClosedPointEvaluation
open RationalPointsN25QuotientTwoClosedPointResidueDegree
open RationalPointsN25QuotientTwoFrobeniusOrbits
open RationalPointsN25QuotientTwoFullClosedPoints

/-- A rank-one presentation of the Kahler differentials forces some
universal differential to be nonzero. -/
theorem exists_D_ne_zero_of_kaehler_equiv
    {B : Type*} [CommRing B] [Nontrivial B] [Algebra (ZMod 2) B]
    (e : Ω[B⁄ZMod 2] ≃ₗ[B] B) :
    ∃ b : B, KaehlerDifferential.D (ZMod 2) B b ≠ 0 := by
  let D := KaehlerDifferential.D (ZMod 2) B
  let ω : Ω[B⁄ZMod 2] := e.symm (1 : B)
  have hω : ω ≠ 0 := by
    intro hω0
    have h10 := congrArg (fun x => e x) hω0
    simp [ω] at h10
  by_contra h
  have hD : ∀ b : B, D b = 0 := by
    intro b
    by_contra hb
    exact h ⟨b, hb⟩
  have hspan_le : Submodule.span B (Set.range D) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    simpa using hD b
  have hωspan : ω ∈ Submodule.span B (Set.range D) := by
    rw [KaehlerDifferential.span_range_derivation]
    simp
  have hωbot : ω ∈ (⊥ : Submodule B Ω[B⁄ZMod 2]) :=
    hspan_le hωspan
  apply hω
  simpa using hωbot

/-- Over the binary prime field, a finite evaluation range of cardinality
`2^d` has nonzero kernel whenever the source has rank-one differentials and
`d` is positive. -/
theorem ker_ne_bot_of_kaehler_equiv_of_range_natCard
    {B K : Type*} [CommRing B] [Algebra (ZMod 2) B] [Field K]
    (ev : B →+* K) (e : Ω[B⁄ZMod 2] ≃ₗ[B] B)
    {d : ℕ} (hd : 0 < d) (hcard : Nat.card ev.range = 2 ^ d) :
    RingHom.ker ev ≠ ⊥ := by
  classical
  letI : Nontrivial B := ev.domain_nontrivial
  obtain ⟨b, hdb⟩ := exists_D_ne_zero_of_kaehler_equiv e
  let D := KaehlerDifferential.D (ZMod 2) B
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  have hDpow : D (b ^ (2 ^ d)) = 0 := by
    rw [D.leibniz_pow]
    change (2 ^ d) • (b ^ (2 ^ d - 1) • D b) = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have hcast : ((2 ^ d : ℕ) : ZMod 2) = 0 := by
      rw [Nat.cast_pow, CharP.cast_eq_zero (ZMod 2) 2, zero_pow hd0]
    rw [hcast, zero_smul]
  let w : B := b ^ (2 ^ d) - b
  have hw_ne : w ≠ 0 := by
    intro hw
    have hwD : D (b ^ (2 ^ d) - b) = D 0 := by
      simpa [w] using congrArg (fun x => D x) hw
    have hwD' : -D b = 0 := by
      simpa [map_sub, hDpow] using hwD
    exact hdb (neg_eq_zero.mp hwD')
  have hcard_ne : Nat.card ev.range ≠ 0 := by
    rw [hcard]
    exact pow_ne_zero d (by decide : (2 : ℕ) ≠ 0)
  letI : Finite ev.range := Nat.finite_of_card_ne_zero hcard_ne
  letI : Fintype ev.range := Fintype.ofFinite ev.range
  letI : Field ev.range := Fintype.fieldOfDomain ev.range
  have hcardF := hcard
  rw [Nat.card_eq_fintype_card] at hcardF
  have hpowRange :
      (ev.rangeRestrict b) ^ (2 ^ d) = ev.rangeRestrict b := by
    have h := FiniteField.pow_card (ev.rangeRestrict b)
    rw [hcardF] at h
    exact h
  have hpowK : ev b ^ (2 ^ d) = ev b := by
    simpa using congrArg (fun x : ev.range => (x : K)) hpowRange
  have hw_mem : w ∈ RingHom.ker ev := by
    rw [RingHom.mem_ker]
    dsimp [w]
    rw [map_sub, map_pow, hpowK, sub_self]
  intro hker
  have hinj : Function.Injective ev :=
    (RingHom.injective_iff_ker_eq_bot ev).2 hker
  apply hw_ne
  apply hinj
  simpa using RingHom.mem_ker.mp hw_mem

/-- The evaluation range of an exact-period point has the exact binary
cardinality dictated by that period. -/
theorem exactPeriodicPoint_chartEvalRange_card
    (d : ℕ) (hd : 0 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    Nat.card
        (chartQuotientEval (normalizedPivot Q.1.1) ⟨Q.1, rfl⟩).range =
      2 ^ d := by
  calc
    Nat.card
        (chartQuotientEval (normalizedPivot Q.1.1) ⟨Q.1, rfl⟩).range =
        Nat.card (chartPointCoordinateField d (normalizedPivot Q.1.1)
          ⟨Q.1, rfl⟩) :=
      Nat.card_congr
        (chartPointEvalRangeEquivCoordinateField d
          (normalizedPivot Q.1.1) ⟨Q.1, rfl⟩)
    _ = 2 ^ d := by
      rw [chartPointCoordinateField_card,
        coordinateFieldDegree_eq_exactPeriod d hd Q]

/-- Evaluation on the canonical pivot chart of every positive exact-period
point has a nonzero kernel. -/
theorem exactPeriodicPoint_chartEval_ker_ne_bot
    (d : ℕ) (hd : 0 < d)
    (Q : ExactPeriodicPoint (degreePointFrobeniusTwo d) d) :
    RingHom.ker
        (chartQuotientEval (normalizedPivot Q.1.1) ⟨Q.1, rfl⟩) ≠ ⊥ := by
  exact ker_ne_bot_of_kaehler_equiv_of_range_natCard
    (chartQuotientEval (normalizedPivot Q.1.1) ⟨Q.1, rfl⟩)
    (chartKaehlerDifferentialEquiv (normalizedPivot Q.1.1)) hd
    (exactPeriodicPoint_chartEvalRange_card d hd Q)

end MazurProof.RationalPointsN25QuotientTwoClosedPointKernelNonzero
