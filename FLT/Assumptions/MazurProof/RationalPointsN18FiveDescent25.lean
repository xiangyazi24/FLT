import FLT.Assumptions.MazurProof.RationalPointsN18FiveDescent
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Lifting the order-18 five-descent to powers of five

The preceding file leaves twelve mod-five cases.  This file proves a uniform
lifting fact that is invisible modulo five alone: in every surviving case,
the unique root among `e,f` containing `5` has exactly the same 5-adic
valuation as the unique cusp factor among `A,D,A+D` containing `5`.

Consequently divisibility by every power `5^n` is synchronized.  In
particular, each of the twelve cases splits into the three machine-checked
possibilities

* both distinguished terms have valuation exactly one;
* both have valuation exactly two;
* both are divisible by `5^3`.

This is a strict mod-25/mod-125 refinement of the previous seam; it does not
claim a local contradiction where none exists.
-/

namespace MazurProof.RationalPointsN18FiveDescent25

open RationalPointsN18
open RationalPointsN18Descent
open RationalPointsN18FiveDescent

noncomputable section

/-- Two nonzero integers have synchronized divisibility by every power of
five. -/
def SameFiveValuation (x y : ℤ) : Prop :=
  ∀ n : ℕ, (5 : ℤ) ^ n ∣ x ↔ (5 : ℤ) ^ n ∣ y

/-- The exact surviving classification through modulus `125`. -/
def FiveLiftStatus (x y : ℤ) : Prop :=
  (¬(25 : ℤ) ∣ x ∧ ¬(25 : ℤ) ∣ y) ∨
  ((25 : ℤ) ∣ x ∧ (25 : ℤ) ∣ y ∧
    ¬(125 : ℤ) ∣ x ∧ ¬(125 : ℤ) ∣ y) ∨
  ((125 : ℤ) ∣ x ∧ (125 : ℤ) ∣ y)

def FivePowerMatch (x y : ℤ) : Prop :=
  SameFiveValuation x y ∧ FiveLiftStatus x y

/-- The six possible pairings of the unique five-divisible root with the
unique five-divisible cusp factor, enhanced by all-power valuation matching. -/
def FiveValuationMatch (A D e f : ℤ) : Prop :=
  ((5 : ℤ) ∣ e ∧
    (((5 : ℤ) ∣ A ∧ FivePowerMatch e A) ∨
     ((5 : ℤ) ∣ D ∧ FivePowerMatch e D) ∨
     ((5 : ℤ) ∣ A + D ∧ FivePowerMatch e (A + D)))) ∨
  ((5 : ℤ) ∣ f ∧
    (((5 : ℤ) ∣ A ∧ FivePowerMatch f A) ∨
     ((5 : ℤ) ∣ D ∧ FivePowerMatch f D) ∨
     ((5 : ℤ) ∣ A + D ∧ FivePowerMatch f (A + D))))

/-! ## Valuation algebra -/

theorem five_valuation_balance {A D e f : ℤ}
    (hA : 0 < A) (hD : 0 < D) (he : 0 < e) (hf : 0 < f)
    (hmul : e * f = A * D * (A + D)) :
    padicValInt 5 e + padicValInt 5 f =
      padicValInt 5 A + padicValInt 5 D + padicValInt 5 (A + D) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hS0 : A + D ≠ 0 := ne_of_gt (add_pos hA hD)
  have he0 : e ≠ 0 := ne_of_gt he
  have hf0 : f ≠ 0 := ne_of_gt hf
  calc
    padicValInt 5 e + padicValInt 5 f = padicValInt 5 (e * f) :=
      (padicValInt.mul he0 hf0).symm
    _ = padicValInt 5 (A * D * (A + D)) := by rw [hmul]
    _ = padicValInt 5 (A * D) + padicValInt 5 (A + D) :=
      padicValInt.mul (mul_ne_zero hA0 hD0) hS0
    _ = padicValInt 5 A + padicValInt 5 D + padicValInt 5 (A + D) := by
      rw [padicValInt.mul hA0 hD0]

theorem sameFiveValuation_of_padicValInt_eq {x y : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hval : padicValInt 5 x = padicValInt 5 y) :
    SameFiveValuation x y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro n
  change (((5 : ℕ) : ℤ) ^ n ∣ x ↔ ((5 : ℕ) : ℤ) ^ n ∣ y)
  rw [padicValInt_dvd_iff (p := 5) n x, padicValInt_dvd_iff (p := 5) n y]
  simp only [hx, hy, false_or]
  rw [hval]

theorem fiveLiftStatus_of_sameFiveValuation {x y : ℤ}
    (hsame : SameFiveValuation x y) : FiveLiftStatus x y := by
  have h25 := hsame 2
  have h125 := hsame 3
  norm_num at h25 h125
  by_cases hx25 : (25 : ℤ) ∣ x
  · have hy25 : (25 : ℤ) ∣ y := h25.mp hx25
    by_cases hx125 : (125 : ℤ) ∣ x
    · exact Or.inr (Or.inr ⟨hx125, h125.mp hx125⟩)
    · have hy125 : ¬(125 : ℤ) ∣ y := by
        intro hy
        exact hx125 (h125.mpr hy)
      exact Or.inr (Or.inl ⟨hx25, hy25, hx125, hy125⟩)
  · have hy25 : ¬(25 : ℤ) ∣ y := by
      intro hy
      exact hx25 (h25.mpr hy)
    exact Or.inl ⟨hx25, hy25⟩

theorem fivePowerMatch_of_padicValInt_eq {x y : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hval : padicValInt 5 x = padicValInt 5 y) :
    FivePowerMatch x y := by
  have hsame := sameFiveValuation_of_padicValInt_eq hx hy hval
  exact ⟨hsame, fiveLiftStatus_of_sameFiveValuation hsame⟩

/-! ## Matching the unique root and cusp factor -/

theorem five_valuation_match_of_allocations {A D e f : ℤ}
    (hA : 0 < A) (hD : 0 < D) (he : 0 < e) (hf : 0 < f)
    (hmul : e * f = A * D * (A + D))
    (hroot :
      ((5 : ℤ) ∣ e ∧ ¬(5 : ℤ) ∣ f) ∨
      ((5 : ℤ) ∣ f ∧ ¬(5 : ℤ) ∣ e))
    (hfactor :
      ((5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ A + D) ∨
      ((5 : ℤ) ∣ A + D ∧ ¬(5 : ℤ) ∣ A ∧ ¬(5 : ℤ) ∣ D)) :
    FiveValuationMatch A D e f := by
  have hbal := five_valuation_balance hA hD he hf hmul
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hS0 : A + D ≠ 0 := ne_of_gt (add_pos hA hD)
  have he0 : e ≠ 0 := ne_of_gt he
  have hf0 : f ≠ 0 := ne_of_gt hf
  rcases hroot with hrootE | hrootF
  · have hvf : padicValInt 5 f = 0 := padicValInt.eq_zero_of_not_dvd hrootE.2
    rcases hfactor with hfactorA | hfactorD | hfactorS
    · have hvD : padicValInt 5 D = 0 := padicValInt.eq_zero_of_not_dvd hfactorA.2.1
      have hvS : padicValInt 5 (A + D) = 0 :=
        padicValInt.eq_zero_of_not_dvd hfactorA.2.2
      have hval : padicValInt 5 e = padicValInt 5 A := by omega
      exact Or.inl ⟨hrootE.1, Or.inl ⟨hfactorA.1,
        fivePowerMatch_of_padicValInt_eq he0 hA0 hval⟩⟩
    · have hvA : padicValInt 5 A = 0 := padicValInt.eq_zero_of_not_dvd hfactorD.2.1
      have hvS : padicValInt 5 (A + D) = 0 :=
        padicValInt.eq_zero_of_not_dvd hfactorD.2.2
      have hval : padicValInt 5 e = padicValInt 5 D := by omega
      exact Or.inl ⟨hrootE.1, Or.inr (Or.inl ⟨hfactorD.1,
        fivePowerMatch_of_padicValInt_eq he0 hD0 hval⟩)⟩
    · have hvA : padicValInt 5 A = 0 := padicValInt.eq_zero_of_not_dvd hfactorS.2.1
      have hvD : padicValInt 5 D = 0 := padicValInt.eq_zero_of_not_dvd hfactorS.2.2
      have hval : padicValInt 5 e = padicValInt 5 (A + D) := by omega
      exact Or.inl ⟨hrootE.1, Or.inr (Or.inr ⟨hfactorS.1,
        fivePowerMatch_of_padicValInt_eq he0 hS0 hval⟩)⟩
  · have hve : padicValInt 5 e = 0 := padicValInt.eq_zero_of_not_dvd hrootF.2
    rcases hfactor with hfactorA | hfactorD | hfactorS
    · have hvD : padicValInt 5 D = 0 := padicValInt.eq_zero_of_not_dvd hfactorA.2.1
      have hvS : padicValInt 5 (A + D) = 0 :=
        padicValInt.eq_zero_of_not_dvd hfactorA.2.2
      have hval : padicValInt 5 f = padicValInt 5 A := by omega
      exact Or.inr ⟨hrootF.1, Or.inl ⟨hfactorA.1,
        fivePowerMatch_of_padicValInt_eq hf0 hA0 hval⟩⟩
    · have hvA : padicValInt 5 A = 0 := padicValInt.eq_zero_of_not_dvd hfactorD.2.1
      have hvS : padicValInt 5 (A + D) = 0 :=
        padicValInt.eq_zero_of_not_dvd hfactorD.2.2
      have hval : padicValInt 5 f = padicValInt 5 D := by omega
      exact Or.inr ⟨hrootF.1, Or.inr (Or.inl ⟨hfactorD.1,
        fivePowerMatch_of_padicValInt_eq hf0 hD0 hval⟩)⟩
    · have hvA : padicValInt 5 A = 0 := padicValInt.eq_zero_of_not_dvd hfactorS.2.1
      have hvD : padicValInt 5 D = 0 := padicValInt.eq_zero_of_not_dvd hfactorS.2.2
      have hval : padicValInt 5 f = padicValInt 5 (A + D) := by omega
      exact Or.inr ⟨hrootF.1, Or.inr (Or.inr ⟨hfactorS.1,
        fivePowerMatch_of_padicValInt_eq hf0 hS0 hval⟩)⟩

/-! ## Lifted rational-point seam -/

/-- The twelve mod-five cases all lift with synchronized valuations.  Thus
the distinguished root and cusp factor survive mod 25 and mod 125 only in
the three statuses recorded by `FiveLiftStatus`. -/
theorem noncuspidal_point_to_lifted_five_cases {U Y : ℚ}
    (hU0 : U ≠ 0) (hU1 : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    ∃ A D C e f : ℤ,
      0 < A ∧ 0 < D ∧ 0 < e ∧ 0 < f ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧ Int.gcd D (A + D) = 1 ∧
      Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      FiveValuationMatch A D e f ∧
      ((normReal A D = e ^ 2 - 2 * f ^ 2 ∧
          |C| = e ^ 2 + 2 * f ^ 2 ∧ FiveBranchOne A D e f) ∨
       (normReal A D = 2 * e ^ 2 - f ^ 2 ∧
          |C| = 2 * e ^ 2 + f ^ 2 ∧ FiveBranchTwo A D e f)) := by
  obtain ⟨A, D, C, e, f, hA, hD, he, hf, hcop, hcopAS, hcopDS,
      hcopEF, hmul, hforms, hroot, hfactor⟩ :=
    noncuspidal_point_to_five_descent hU0 hU1 hY
  have hmatch := five_valuation_match_of_allocations hA hD he hf hmul hroot hfactor
  refine ⟨A, D, C, e, f, hA, hD, he, hf, hcop, hcopAS, hcopDS,
    hcopEF, hmul, hmatch, ?_⟩
  rcases hforms with hbranch | hbranch
  · exact Or.inl ⟨hbranch.1, hbranch.2,
      branch_one_five_split hbranch.1 hroot hfactor⟩
  · exact Or.inr ⟨hbranch.1, hbranch.2,
      branch_two_five_split hbranch.1 hroot hfactor⟩

end

end MazurProof.RationalPointsN18FiveDescent25
