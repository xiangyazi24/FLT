import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Full-cover extraction interfaces for the shifted N=12 curve

This module records the honest interface for extracting integer full-cover data
from a rational point on

`E1 : Y^2 = X * (X - 1) * (X + 3)`.

The arithmetic content is deliberately split into named residual statements:
valuation parity, squareclass extraction supported at `{2,3}`, and denominator
clearing.  The theorem in this file only assembles those residuals.
-/

namespace MazurProof.RationalPointsN12

/-- The shifted full-cover curve `Y^2 = X(X-1)(X+3)`. -/
def E1FullCoverCurve (X Y : ℚ) : Prop :=
  Y ^ 2 = X * (X - 1) * (X + 3)

/-- Integer squareclass representatives supported only at primes `2` and `3`,
including sign. -/
def S23 : List ℤ := [1, -1, 2, -2, 3, -3, 6, -6]

/-- Membership in the fixed squareclass representative list `S23`. -/
def InS23 (d : ℤ) : Prop :=
  d ∈ S23

/-- `q` lies in the squareclass represented by `d`, with nonzero square factor. -/
def SquareclassBy (q : ℚ) (d : ℤ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ q = (d : ℚ) * r ^ 2

/-- The p-adic valuation of `q` is even away from the primes `2` and `3`. -/
def EvenPadicOutside23 (q : ℚ) : Prop :=
  q ≠ 0 ∧
    ∀ p : ℕ, Fact p.Prime → p ≠ 2 → p ≠ 3 → Even (padicValRat p q)

/-- Representative form of squareclass support away from primes other than
`2` and `3`. -/
def SquareclassSupportedOn23 (q : ℚ) : Prop :=
  q ≠ 0 ∧ ∃ d : ℤ, InS23 d ∧ SquareclassBy q d

noncomputable def halfFactorization (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.mapRange (fun e => e / 2) (by simp)

/-- If every prime exponent in a nonzero natural number is even, then the
natural number is a square. -/
theorem nat_isSquare_of_factorization_even
    {n : ℕ} (hn : n ≠ 0)
    (hev : ∀ p : ℕ, p.Prime → Even (n.factorization p)) :
    IsSquare n := by
  classical
  let f : ℕ →₀ ℕ := halfFactorization n
  let a : ℕ := f.prod (fun p e => p ^ e)
  have hf_prime : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    have hfp : f p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hnfp : n.factorization p ≠ 0 := by
      intro hzero
      apply hfp
      simp [f, halfFactorization, hzero]
    have hp_mem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hnfp
    exact Nat.prime_of_mem_primeFactors hp_mem
  have hfac_a : a.factorization = f := by
    simpa [a] using (Nat.prod_pow_factorization_eq_self (f := f) hf_prime)
  have ha_ne : a ≠ 0 := by
    dsimp [a]
    exact Finsupp.prod_ne_zero_iff.mpr (by
      intro p hp
      exact pow_ne_zero _ (hf_prime p hp).ne_zero)
  refine ⟨a, ?_⟩
  suffices hsq : n = a ^ 2 by simpa [pow_two] using hsq
  apply Nat.eq_of_factorization_eq hn (pow_ne_zero 2 ha_ne)
  intro p
  by_cases hp : p.Prime
  · have he : Even (n.factorization p) := hev p hp
    rcases he with ⟨k, hk⟩
    have hpow : (a ^ 2).factorization p = 2 * a.factorization p := by
      have h := congrFun (congrArg DFunLike.coe (Nat.factorization_pow a 2)) p
      exact h.trans (by simp [Finsupp.smul_apply, two_mul])
    rw [hpow, hfac_a]
    dsimp [f, halfFactorization]
    change n.factorization p = 2 * (n.factorization p / 2)
    omega
  · have hnzero : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_prime n hp
    have hpow : (a ^ 2).factorization p = 2 * a.factorization p := by
      have h := congrFun (congrArg DFunLike.coe (Nat.factorization_pow a 2)) p
      exact h.trans (by simp [Finsupp.smul_apply, two_mul])
    rw [hnzero, hpow, hfac_a]
    dsimp [f, halfFactorization]
    change 0 = 2 * (n.factorization p / 2)
    omega

theorem int_isSquare_of_natAbs_isSquare_of_nonneg {z : ℤ}
    (hz : 0 ≤ z) (hsq : IsSquare z.natAbs) :
    IsSquare z := by
  rcases hsq with ⟨a, ha⟩
  refine ⟨(a : ℤ), ?_⟩
  calc
    z = (z.natAbs : ℤ) := (Int.natAbs_of_nonneg hz).symm
    _ = ((a * a : ℕ) : ℤ) := by rw [ha]
    _ = (a : ℤ) * (a : ℤ) := by norm_num

theorem rat_num_den_factorization_even_of_even_padicValRat
    {q : ℚ}
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p q)) :
    (∀ p : ℕ, p.Prime → Even (q.num.natAbs.factorization p)) ∧
    (∀ p : ℕ, p.Prime → Even (q.den.factorization p)) := by
  constructor
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    have hv : Even (padicValRat p q) := hval p inferInstance
    have hred : Nat.Coprime q.num.natAbs q.den := q.reduced
    by_cases hpnum : p ∣ q.num.natAbs
    · have hpden : ¬ p ∣ q.den := by
        intro hpd
        have hpgcd : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpnum hpd
        have hpone : p ∣ 1 := by
          simpa [hred.gcd_eq_one] using hpgcd
        exact hp.not_dvd_one hpone
      have hden0 : q.den.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hpden
      have hvdef :
          padicValRat p q =
            (q.num.natAbs.factorization p : ℤ) - (q.den.factorization p : ℤ) := by
        simp [padicValRat_def, padicValInt, Nat.factorization_def, hp]
      have hvnum : Even ((q.num.natAbs.factorization p : ℤ)) := by
        simpa [hvdef, hden0] using hv
      exact (Int.even_coe_nat _).mp hvnum
    · have hnum0 : q.num.natAbs.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hpnum
      simp [hnum0]
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    have hv : Even (padicValRat p q) := hval p inferInstance
    have hred : Nat.Coprime q.num.natAbs q.den := q.reduced
    by_cases hpden : p ∣ q.den
    · have hpnum : ¬ p ∣ q.num.natAbs := by
        intro hpn
        have hpgcd : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpn hpden
        have hpone : p ∣ 1 := by
          simpa [hred.gcd_eq_one] using hpgcd
        exact hp.not_dvd_one hpone
      have hnum0 : q.num.natAbs.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hpnum
      have hvdef :
          padicValRat p q =
            (q.num.natAbs.factorization p : ℤ) - (q.den.factorization p : ℤ) := by
        simp [padicValRat_def, padicValInt, Nat.factorization_def, hp]
      have hvden_neg : Even (-(q.den.factorization p : ℤ)) := by
        simpa [hvdef, hnum0] using hv
      have hvden : Even ((q.den.factorization p : ℤ)) := by
        simpa using hvden_neg.neg
      exact (Int.even_coe_nat _).mp hvden
    · have hden0 : q.den.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hpden
      simp [hden0]

theorem rat_isSquare_of_pos_even_padicValRat
    {q : ℚ}
    (hqpos : 0 < q)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p q)) :
    IsSquare q := by
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hnum_ne : q.num.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hqne)
  have hden_ne : q.den ≠ 0 := q.den_ne_zero
  rcases rat_num_den_factorization_even_of_even_padicValRat hval with
    ⟨hnumEven, hdenEven⟩
  have hnumSqNat : IsSquare q.num.natAbs :=
    nat_isSquare_of_factorization_even hnum_ne hnumEven
  have hdenSq : IsSquare q.den :=
    nat_isSquare_of_factorization_even hden_ne hdenEven
  have hnum_nonneg : 0 ≤ q.num :=
    le_of_lt (Rat.num_pos.mpr hqpos)
  have hnumSqInt : IsSquare q.num :=
    int_isSquare_of_natAbs_isSquare_of_nonneg hnum_nonneg hnumSqNat
  exact Rat.isSquare_iff.mpr ⟨hnumSqInt, hdenSq⟩

theorem rat_exists_sq_of_pos_even_padicValRat
    {q : ℚ}
    (hqpos : 0 < q)
    (hval : ∀ p : ℕ, Fact p.Prime → Even (padicValRat p q)) :
    ∃ r : ℚ, r ≠ 0 ∧ q = r ^ 2 := by
  rcases rat_isSquare_of_pos_even_padicValRat hqpos hval with ⟨r, hr⟩
  refine ⟨r, ?_, ?_⟩
  · intro hr0
    subst r
    have : q = 0 := by simpa using hr
    exact (ne_of_gt hqpos) this
  · simpa [pow_two] using hr

/-- The product of the three squareclass representatives is itself a rational
square. -/
def ProductSquareclassCondition (d0 d1 d3 : ℤ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ ((d0 * d1 * d3 : ℤ) : ℚ) = r ^ 2

/-- Integer full-cover equations after clearing a common denominator. -/
def CoverInt (d0 d1 d3 A B C T : ℤ) : Prop :=
  d0 * A ^ 2 - d1 * B ^ 2 = T ^ 2 ∧
    d3 * C ^ 2 - d0 * A ^ 2 = (3 : ℤ) * T ^ 2

/-- Primitive projective integer quadruple. -/
def PrimitiveInt4 (A B C T : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime →
    ¬ ((p : ℤ) ∣ A ∧ (p : ℤ) ∣ B ∧ (p : ℤ) ∣ C ∧ (p : ℤ) ∣ T)

/-- The common gcd of a cover quadruple, measured by absolute values.  This is
kept local to the extraction file to avoid importing the four-square AP module
back into the full-cover interface. -/
def coverGCD4 (A B C T : ℤ) : ℕ :=
  Nat.gcd A.natAbs (Nat.gcd B.natAbs (Nat.gcd C.natAbs T.natAbs))

theorem coverGCD4_dvd_left (A B C T : ℤ) :
    coverGCD4 A B C T ∣ A.natAbs := by
  unfold coverGCD4
  exact Nat.gcd_dvd_left _ _

theorem coverGCD4_dvd_second (A B C T : ℤ) :
    coverGCD4 A B C T ∣ B.natAbs := by
  unfold coverGCD4
  exact Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)

theorem coverGCD4_dvd_third (A B C T : ℤ) :
    coverGCD4 A B C T ∣ C.natAbs := by
  unfold coverGCD4
  exact Nat.dvd_trans
    (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_dvd_left _ _)

theorem coverGCD4_dvd_fourth (A B C T : ℤ) :
    coverGCD4 A B C T ∣ T.natAbs := by
  unfold coverGCD4
  exact Nat.dvd_trans
    (Nat.dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))
    (Nat.gcd_dvd_right _ _)

theorem dvd_coverGCD4 {k : ℕ} {A B C T : ℤ}
    (hA : k ∣ A.natAbs) (hB : k ∣ B.natAbs)
    (hC : k ∣ C.natAbs) (hT : k ∣ T.natAbs) :
    k ∣ coverGCD4 A B C T := by
  unfold coverGCD4
  exact Nat.dvd_gcd hA (Nat.dvd_gcd hB (Nat.dvd_gcd hC hT))

theorem coverGCD4_intCast_dvd_left (A B C T : ℤ) :
    (coverGCD4 A B C T : ℤ) ∣ A := by
  rw [Int.natCast_dvd]
  exact coverGCD4_dvd_left A B C T

theorem coverGCD4_intCast_dvd_second (A B C T : ℤ) :
    (coverGCD4 A B C T : ℤ) ∣ B := by
  rw [Int.natCast_dvd]
  exact coverGCD4_dvd_second A B C T

theorem coverGCD4_intCast_dvd_third (A B C T : ℤ) :
    (coverGCD4 A B C T : ℤ) ∣ C := by
  rw [Int.natCast_dvd]
  exact coverGCD4_dvd_third A B C T

theorem coverGCD4_intCast_dvd_fourth (A B C T : ℤ) :
    (coverGCD4 A B C T : ℤ) ∣ T := by
  rw [Int.natCast_dvd]
  exact coverGCD4_dvd_fourth A B C T

theorem coverGCD4_pos_of_fourth_ne_zero {A B C T : ℤ}
    (hT : T ≠ 0) :
    0 < coverGCD4 A B C T := by
  unfold coverGCD4
  exact Nat.gcd_pos_of_pos_right _
    (Nat.gcd_pos_of_pos_right _
      (Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr hT)))

theorem coverGCD4_eq_one_of_common_factor
    {A B C T A' B' C' T' : ℤ} {g : ℕ}
    (hgpos : 0 < g)
    (hgroot : g = coverGCD4 A B C T)
    (hA : A = (g : ℤ) * A')
    (hB : B = (g : ℤ) * B')
    (hC : C = (g : ℤ) * C')
    (hT : T = (g : ℤ) * T') :
    coverGCD4 A' B' C' T' = 1 := by
  let K : ℕ := coverGCD4 A' B' C' T'
  have hKA : K ∣ A'.natAbs := by
    dsimp [K]
    exact coverGCD4_dvd_left A' B' C' T'
  have hKB : K ∣ B'.natAbs := by
    dsimp [K]
    exact coverGCD4_dvd_second A' B' C' T'
  have hKC : K ∣ C'.natAbs := by
    dsimp [K]
    exact coverGCD4_dvd_third A' B' C' T'
  have hKT : K ∣ T'.natAbs := by
    dsimp [K]
    exact coverGCD4_dvd_fourth A' B' C' T'
  have hKg_A : K * g ∣ A.natAbs := by
    have hAa : A.natAbs = g * A'.natAbs := by
      rw [hA, Int.natAbs_mul]
      simp
    rcases hKA with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hAa, ht]
    ring
  have hKg_B : K * g ∣ B.natAbs := by
    have hBa : B.natAbs = g * B'.natAbs := by
      rw [hB, Int.natAbs_mul]
      simp
    rcases hKB with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hBa, ht]
    ring
  have hKg_C : K * g ∣ C.natAbs := by
    have hCa : C.natAbs = g * C'.natAbs := by
      rw [hC, Int.natAbs_mul]
      simp
    rcases hKC with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hCa, ht]
    ring
  have hKg_T : K * g ∣ T.natAbs := by
    have hTa : T.natAbs = g * T'.natAbs := by
      rw [hT, Int.natAbs_mul]
      simp
    rcases hKT with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hTa, ht]
    ring
  have hKg_root : K * g ∣ coverGCD4 A B C T :=
    dvd_coverGCD4 hKg_A hKg_B hKg_C hKg_T
  have hKg_g : K * g ∣ g := by
    simpa [← hgroot] using hKg_root
  rcases hKg_g with ⟨t, ht⟩
  have hKt : 1 = K * t := by
    have hmul : g * 1 = g * (K * t) := by
      calc
        g * 1 = g := by ring
        _ = (K * g) * t := ht
        _ = g * (K * t) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos hmul
  have hK_dvd_one : K ∣ 1 := ⟨t, hKt⟩
  have hK_one : K = 1 := Nat.dvd_one.mp hK_dvd_one
  simpa [K] using hK_one

theorem primitiveInt4_of_coverGCD4_eq_one {A B C T : ℤ}
    (hgcd : coverGCD4 A B C T = 1) :
    PrimitiveInt4 A B C T := by
  intro p hp hcommon
  rcases hcommon with ⟨hA, hB, hC, hT⟩
  have hAn : p ∣ A.natAbs := Int.natCast_dvd.mp hA
  have hBn : p ∣ B.natAbs := Int.natCast_dvd.mp hB
  have hCn : p ∣ C.natAbs := Int.natCast_dvd.mp hC
  have hTn : p ∣ T.natAbs := Int.natCast_dvd.mp hT
  have hp_gcd : p ∣ coverGCD4 A B C T :=
    dvd_coverGCD4 hAn hBn hCn hTn
  have hp_one : p ∣ 1 := by
    simpa [hgcd] using hp_gcd
  exact hp.not_dvd_one hp_one

/-- Integer full-cover data attached to a nonzero-`Y` point on `E1`. -/
def E1FullCoverIntData (X _Y : ℚ) : Prop :=
  ∃ d0 d1 d3 : ℤ,
    InS23 d0 ∧ InS23 d1 ∧ InS23 d3 ∧
    ProductSquareclassCondition d0 d1 d3 ∧
    ∃ A B C T : ℤ,
      T ≠ 0 ∧ A ≠ 0 ∧ B ≠ 0 ∧ C ≠ 0 ∧
      PrimitiveInt4 A B C T ∧
      X = (d0 : ℚ) * (((A : ℚ) / (T : ℚ)) ^ 2) ∧
      X - 1 = (d1 : ℚ) * (((B : ℚ) / (T : ℚ)) ^ 2) ∧
      X + 3 = (d3 : ℚ) * (((C : ℚ) / (T : ℚ)) ^ 2) ∧
      CoverInt d0 d1 d3 A B C T

/-- Hard p-adic/gcd layer: the three factors have even valuation outside
`{2,3}`. -/
def E1FactorEvenPadicOutside23Statement : Prop :=
  ∀ {X Y : ℚ}, E1FullCoverCurve X Y → Y ≠ 0 →
    EvenPadicOutside23 X ∧
      EvenPadicOutside23 (X - 1) ∧
        EvenPadicOutside23 (X + 3)

/-- Squarefree/UFD extraction layer for rational squareclasses. -/
def SquareclassSupportedOn23OfEvenPadicOutside23Statement : Prop :=
  ∀ {q : ℚ}, EvenPadicOutside23 q → SquareclassSupportedOn23 q

/-- Denominator-clearing layer from three supported squareclasses to primitive
integer full-cover data. -/
def E1FullCoverIntDataOfFactorSquareclassesStatement : Prop :=
  ∀ {X Y : ℚ}, E1FullCoverCurve X Y → Y ≠ 0 →
    SquareclassSupportedOn23 X →
    SquareclassSupportedOn23 (X - 1) →
    SquareclassSupportedOn23 (X + 3) →
    E1FullCoverIntData X Y

/-- Final full-cover extraction statement, split into the residuals above. -/
def E1FullCoverSquareclassExtractionIntStatement : Prop :=
  ∀ {X Y : ℚ}, E1FullCoverCurve X Y → Y ≠ 0 → E1FullCoverIntData X Y

/-- A more concrete denominator-clearing residual once squareclass
representatives have already been chosen. -/
def CommonDenomSquareclassRepsToPrimitiveCoverIntStatement : Prop :=
  ∀ {X Y : ℚ} {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ},
    E1FullCoverCurve X Y → Y ≠ 0 →
    InS23 d0 → InS23 d1 → InS23 d3 →
    r0 ≠ 0 → r1 ≠ 0 → r3 ≠ 0 →
    X = (d0 : ℚ) * r0 ^ 2 →
    X - 1 = (d1 : ℚ) * r1 ^ 2 →
    X + 3 = (d3 : ℚ) * r3 ^ 2 →
    E1FullCoverIntData X Y

/-- A nonzero-`Y` point on `E1` has all three full-cover factors nonzero. -/
theorem e1FullCoverCurve_factors_ne_zero
    {X Y : ℚ}
    (hE : E1FullCoverCurve X Y) (hY : Y ≠ 0) :
    X ≠ 0 ∧ X - 1 ≠ 0 ∧ X + 3 ≠ 0 := by
  have hprod_ne : X * (X - 1) * (X + 3) ≠ 0 := by
    rw [← hE]
    exact pow_ne_zero 2 hY
  refine ⟨?_, ?_, ?_⟩
  · intro hX
    exact hprod_ne (by simp [hX])
  · intro hXm1
    exact hprod_ne (by simp [hXm1])
  · intro hXp3
    exact hprod_ne (by simp [hXp3])

/-- A lightweight replacement for the missing ultrametric equality lemma in
the current Mathlib API. -/
theorem padicValRat_add_eq_left_of_lt
    {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (ha : a ≠ 0) (hab : a + b ≠ 0)
    (h : padicValRat p a < padicValRat p b) :
    padicValRat p (a + b) = padicValRat p a := by
  let va : ℤ := padicValRat p a
  let vb : ℤ := padicValRat p b
  let vc : ℤ := padicValRat p (a + b)
  have hle_left : va ≤ vc := by
    have hmin := padicValRat.min_le_padicValRat_add (p := p) hab
    have hmin_eq : min va vb = va := min_eq_left (le_of_lt h)
    simpa [va, vb, vc, hmin_eq] using hmin
  have hsum : (a + b) + (-b) ≠ 0 := by
    simpa [add_assoc] using ha
  have hle_back : min vc vb ≤ va := by
    have hmin := padicValRat.min_le_padicValRat_add
      (p := p) (q := a + b) (r := -b) hsum
    simpa [va, vb, vc, add_assoc] using hmin
  have hvc_le : vc ≤ va := by
    by_contra hnot
    have hva_lt_vc : va < vc := lt_of_not_ge hnot
    have hmin_gt : va < min vc vb := lt_min hva_lt_vc h
    exact not_lt_of_ge hle_back hmin_gt
  exact le_antisymm hvc_le hle_left

theorem padicValRat_add_eq_right_of_lt
    {p : ℕ} [Fact p.Prime] {a b : ℚ}
    (hb : b ≠ 0) (hab : a + b ≠ 0)
    (h : padicValRat p b < padicValRat p a) :
    padicValRat p (a + b) = padicValRat p b := by
  rw [add_comm]
  exact padicValRat_add_eq_left_of_lt hb (by simpa [add_comm] using hab) h

/-- If `a-b` is a `p`-adic unit and `v(a)<v(b)`, then `v(a)=0`. -/
theorem padicValRat_left_eq_zero_of_lt_of_sub_val_zero
    {p : ℕ} [Fact p.Prime] {a b c : ℚ}
    (hsub : a - b = c) (hc0 : c ≠ 0) (hc : padicValRat p c = 0)
    (h : padicValRat p a < padicValRat p b) :
    padicValRat p a = 0 := by
  by_cases ha : a = 0
  · simp [ha]
  have hab : a + -b ≠ 0 := by
    intro hzero
    apply hc0
    rw [← hsub]
    simpa [sub_eq_add_neg] using hzero
  have hval :
      padicValRat p (a + -b) = padicValRat p a := by
    exact padicValRat_add_eq_left_of_lt ha hab (by simpa using h)
  calc
    padicValRat p a = padicValRat p (a + -b) := hval.symm
    _ = padicValRat p c := by rw [show a + -b = c by simpa [sub_eq_add_neg] using hsub]
    _ = 0 := hc

/-- If `a-b` is a `p`-adic unit, two positive valuations are impossible. -/
theorem padicValRat_not_both_pos_of_sub_val_zero
    {p : ℕ} [Fact p.Prime] {a b c : ℚ}
    (hsub : a - b = c) (hc0 : c ≠ 0) (hc : padicValRat p c = 0) :
    ¬ (0 < padicValRat p a ∧ 0 < padicValRat p b) := by
  intro hpos
  have hab : a + -b ≠ 0 := by
    intro hzero
    apply hc0
    rw [← hsub]
    simpa [sub_eq_add_neg] using hzero
  have hmin := padicValRat.min_le_padicValRat_add
    (p := p) (q := a) (r := -b) hab
  have hmin_pos :
      0 < min (padicValRat p a) (padicValRat p (-b)) := by
    rw [padicValRat.neg]
    exact lt_min hpos.1 hpos.2
  have hc_pos : 0 < padicValRat p c := by
    have hdiff :
        padicValRat p (a + -b) = padicValRat p c := by
      rw [show a + -b = c by simpa [sub_eq_add_neg] using hsub]
    rw [← hdiff]
    exact lt_of_lt_of_le hmin_pos hmin
  rw [hc] at hc_pos
  norm_num at hc_pos

theorem padicValRat_two_of_prime_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    padicValRat p (2 : ℚ) = 0 := by
  change padicValRat p ((2 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast (padicValNat.eq_zero_of_not_dvd (p := p) (n := 2) (by
    intro hdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p)
      Nat.prime_two).mp hdiv)))

theorem padicValRat_three_of_prime_ne_three
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    padicValRat p (3 : ℚ) = 0 := by
  change padicValRat p ((3 : ℕ) : ℚ) = 0
  rw [padicValRat.of_nat]
  exact_mod_cast (padicValNat.eq_zero_of_not_dvd (p := p) (n := 3) (by
    intro hdiv
    exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p)
      Nat.prime_three).mp hdiv)))

theorem padicValRat_four_of_prime_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    padicValRat p (4 : ℚ) = 0 := by
  have h2 : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_two_of_prime_ne_two hp2
  calc
    padicValRat p (4 : ℚ) = padicValRat p ((2 : ℚ) ^ 2) := by norm_num
    _ = (2 : ℤ) * padicValRat p (2 : ℚ) :=
      padicValRat.pow (p := p) (q := (2 : ℚ)) (by norm_num) (k := 2)
    _ = 0 := by rw [h2]; norm_num

def sqclass23Rep (q : ℚ) : ℤ :=
  (if q < 0 then (-1 : ℤ) else 1) *
  (if Even (padicValRat 2 q) then (1 : ℤ) else 2) *
  (if Even (padicValRat 3 q) then (1 : ℤ) else 3)

private theorem even_sub_one_of_not_even {z : ℤ} (hz : ¬ Even z) :
    Even (z - 1) := by
  rcases (Int.not_even_iff_odd.mp hz) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  omega

private theorem even_sub_of_even {a b : ℤ} (ha : Even a) (hb : Even b) :
    Even (a - b) := by
  rcases ha with ⟨x, rfl⟩
  rcases hb with ⟨y, rfl⟩
  refine ⟨x - y, ?_⟩
  ring

private theorem sqclass23Rep_mem (q : ℚ) : InS23 (sqclass23Rep q) := by
  unfold sqclass23Rep InS23 S23
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hq, h2, h3]

private theorem sqclass23Rep_ne_zero (q : ℚ) : sqclass23Rep q ≠ 0 := by
  unfold sqclass23Rep
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  norm_num [hq, h2, h3]

private theorem sqclass23Rep_rat_ne_zero (q : ℚ) :
    ((sqclass23Rep q : ℤ) : ℚ) ≠ 0 := by
  exact_mod_cast sqclass23Rep_ne_zero q

private theorem sqclass23Rep_rat_pos_of_not_neg {q : ℚ} (hq : ¬ q < 0) :
    0 < ((sqclass23Rep q : ℤ) : ℚ) := by
  unfold sqclass23Rep
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  norm_num [hq, h2, h3]

private theorem sqclass23Rep_rat_neg_of_neg {q : ℚ} (hq : q < 0) :
    ((sqclass23Rep q : ℤ) : ℚ) < 0 := by
  unfold sqclass23Rep
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  norm_num [hq, h2, h3]

private theorem div_sqclass23Rep_pos {q : ℚ} (hq0 : q ≠ 0) :
    0 < q / ((sqclass23Rep q : ℤ) : ℚ) := by
  by_cases hqneg : q < 0
  · exact div_pos_of_neg_of_neg hqneg (sqclass23Rep_rat_neg_of_neg hqneg)
  · have hqpos : 0 < q := lt_of_le_of_ne (le_of_not_gt hqneg) (Ne.symm hq0)
    exact div_pos hqpos (sqclass23Rep_rat_pos_of_not_neg hqneg)

private theorem padicValRat_sqclass23Rep_at_two (q : ℚ) :
    padicValRat 2 (((sqclass23Rep q : ℤ) : ℚ)) =
      if Even (padicValRat 2 q) then 0 else 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hself : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (p := 2) (by norm_num)
  have hthree : padicValRat 2 (3 : ℚ) = 0 :=
    padicValRat_three_of_prime_ne_three (p := 2) (by norm_num)
  have hsix : padicValRat 2 (6 : ℚ) = 1 := by
    calc
      padicValRat 2 (6 : ℚ) = padicValRat 2 ((2 : ℚ) * (3 : ℚ)) := by norm_num
      _ = padicValRat 2 (2 : ℚ) + padicValRat 2 (3 : ℚ) :=
        padicValRat.mul (p := 2) (q := (2 : ℚ)) (r := (3 : ℚ)) (by norm_num) (by norm_num)
      _ = 1 := by rw [hself, hthree]; norm_num
  unfold sqclass23Rep
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hq, h2, h3, padicValRat.neg, hself, hthree, hsix]

private theorem padicValRat_sqclass23Rep_at_three (q : ℚ) :
    padicValRat 3 (((sqclass23Rep q : ℤ) : ℚ)) =
      if Even (padicValRat 3 q) then 0 else 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hself : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (p := 3) (by norm_num)
  have htwo : padicValRat 3 (2 : ℚ) = 0 :=
    padicValRat_two_of_prime_ne_two (p := 3) (by norm_num)
  have hsix : padicValRat 3 (6 : ℚ) = 1 := by
    calc
      padicValRat 3 (6 : ℚ) = padicValRat 3 ((2 : ℚ) * (3 : ℚ)) := by norm_num
      _ = padicValRat 3 (2 : ℚ) + padicValRat 3 (3 : ℚ) :=
        padicValRat.mul (p := 3) (q := (2 : ℚ)) (r := (3 : ℚ)) (by norm_num) (by norm_num)
      _ = 1 := by rw [hself, htwo]; norm_num
  unfold sqclass23Rep
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hq, h2, h3, padicValRat.neg, hself, htwo, hsix]

private theorem padicValRat_sqclass23Rep_outside23
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (q : ℚ) :
    padicValRat p (((sqclass23Rep q : ℤ) : ℚ)) = 0 := by
  have htwo : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_two_of_prime_ne_two (p := p) hp2
  have hthree : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_three_of_prime_ne_three (p := p) hp3
  have hsix : padicValRat p (6 : ℚ) = 0 := by
    calc
      padicValRat p (6 : ℚ) = padicValRat p ((2 : ℚ) * (3 : ℚ)) := by norm_num
      _ = padicValRat p (2 : ℚ) + padicValRat p (3 : ℚ) :=
        padicValRat.mul (p := p) (q := (2 : ℚ)) (r := (3 : ℚ)) (by norm_num) (by norm_num)
      _ = 0 := by rw [htwo, hthree]; norm_num
  unfold sqclass23Rep
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hq, h2, h3, padicValRat.neg, htwo, hthree, hsix]

private theorem even_padicValRat_div_sqclass23Rep_all
    {q : ℚ} (hq : EvenPadicOutside23 q) :
    ∀ p : ℕ, Fact p.Prime →
      Even (padicValRat p (q / (((sqclass23Rep q : ℤ) : ℚ)))) := by
  intro p hp
  letI : Fact p.Prime := hp
  rcases hq with ⟨hq0, hout⟩
  have hd0 : (((sqclass23Rep q : ℤ) : ℚ)) ≠ 0 := sqclass23Rep_rat_ne_zero q
  rw [padicValRat.div hq0 hd0]
  by_cases hp2 : p = 2
  · subst p
    rw [padicValRat_sqclass23Rep_at_two]
    by_cases h2 : Even (padicValRat 2 q)
    · simp [h2]
    · simpa [h2] using even_sub_one_of_not_even h2
  · by_cases hp3 : p = 3
    · subst p
      rw [padicValRat_sqclass23Rep_at_three]
      by_cases h3 : Even (padicValRat 3 q)
      · simp [h3]
      · simpa [h3] using even_sub_one_of_not_even h3
    · have hqeven : Even (padicValRat p q) := hout p hp hp2 hp3
      have hdeven : Even (padicValRat p (((sqclass23Rep q : ℤ) : ℚ))) := by
        rw [padicValRat_sqclass23Rep_outside23 hp2 hp3]
        exact ⟨0, by norm_num⟩
      exact even_sub_of_even hqeven hdeven

theorem squareclassSupportedOn23_of_evenPadicOutside23_checked :
    SquareclassSupportedOn23OfEvenPadicOutside23Statement := by
  intro q hq
  rcases hq with ⟨hq0, hout⟩
  let d : ℤ := sqclass23Rep q
  have hdmem : InS23 d := by
    simpa [d] using sqclass23Rep_mem q
  have hd0 : ((d : ℤ) : ℚ) ≠ 0 := by
    simpa [d] using sqclass23Rep_rat_ne_zero q
  have htpos : 0 < q / ((d : ℤ) : ℚ) := by
    simpa [d] using div_sqclass23Rep_pos (q := q) hq0
  have hval : ∀ p : ℕ, Fact p.Prime →
      Even (padicValRat p (q / ((d : ℤ) : ℚ))) := by
    intro p hp
    simpa [d] using
      even_padicValRat_div_sqclass23Rep_all (q := q) ⟨hq0, hout⟩ p hp
  rcases rat_exists_sq_of_pos_even_padicValRat htpos hval with ⟨r, hr0, hsq⟩
  refine ⟨hq0, d, hdmem, ?_⟩
  refine ⟨r, hr0, ?_⟩
  calc
    q = ((d : ℤ) : ℚ) * (q / ((d : ℤ) : ℚ)) := by
      field_simp [hd0]
    _ = ((d : ℤ) : ℚ) * r ^ 2 := by rw [hsq]

theorem even_each_of_sum_even_of_pairwise_unit_val
    {a b c : ℤ}
    (hsum : Even (a + b + c))
    (hab_lt : a < b → a = 0) (hba_lt : b < a → b = 0)
    (hac_lt : a < c → a = 0) (hca_lt : c < a → c = 0)
    (hbc_lt : b < c → b = 0) (hcb_lt : c < b → c = 0)
    (hab_pos : ¬ (0 < a ∧ 0 < b))
    (hac_pos : ¬ (0 < a ∧ 0 < c))
    (hbc_pos : ¬ (0 < b ∧ 0 < c)) :
    Even a ∧ Even b ∧ Even c := by
  rcases hsum with ⟨k, hk⟩
  by_cases ha_neg : a < 0
  · have hba : b = a := by
      rcases lt_trichotomy b a with hlt | heq | hgt
      · have hb0 := hba_lt hlt
        omega
      · exact heq
      · have ha0 := hab_lt hgt
        omega
    have hca : c = a := by
      rcases lt_trichotomy c a with hlt | heq | hgt
      · have hc0 := hca_lt hlt
        omega
      · exact heq
      · have ha0 := hac_lt hgt
        omega
    have ha_even : Even a := by
      refine ⟨k - a, ?_⟩
      omega
    exact ⟨ha_even, by simpa [hba] using ha_even, by simpa [hca] using ha_even⟩
  by_cases hb_neg : b < 0
  · have hab : a = b := by
      rcases lt_trichotomy a b with hlt | heq | hgt
      · have ha0 := hab_lt hlt
        omega
      · exact heq
      · have hb0 := hba_lt hgt
        omega
    have hcb : c = b := by
      rcases lt_trichotomy c b with hlt | heq | hgt
      · have hc0 := hcb_lt hlt
        omega
      · exact heq
      · have hb0 := hbc_lt hgt
        omega
    have hb_even : Even b := by
      refine ⟨k - b, ?_⟩
      omega
    exact ⟨by simpa [hab] using hb_even, hb_even, by simpa [hcb] using hb_even⟩
  by_cases hc_neg : c < 0
  · have hac : a = c := by
      rcases lt_trichotomy a c with hlt | heq | hgt
      · have ha0 := hac_lt hlt
        omega
      · exact heq
      · have hc0 := hca_lt hgt
        omega
    have hbc : b = c := by
      rcases lt_trichotomy b c with hlt | heq | hgt
      · have hb0 := hbc_lt hlt
        omega
      · exact heq
      · have hc0 := hcb_lt hgt
        omega
    have hc_even : Even c := by
      refine ⟨k - c, ?_⟩
      omega
    exact ⟨by simpa [hac] using hc_even, by simpa [hbc] using hc_even, hc_even⟩
  have ha_nonneg : 0 ≤ a := le_of_not_gt ha_neg
  have hb_nonneg : 0 ≤ b := le_of_not_gt hb_neg
  have hc_nonneg : 0 ≤ c := le_of_not_gt hc_neg
  have hab_zero : a = 0 ∨ b = 0 := by
    by_contra hnot
    push Not at hnot
    exact hab_pos ⟨lt_of_le_of_ne ha_nonneg hnot.1.symm,
      lt_of_le_of_ne hb_nonneg hnot.2.symm⟩
  have hac_zero : a = 0 ∨ c = 0 := by
    by_contra hnot
    push Not at hnot
    exact hac_pos ⟨lt_of_le_of_ne ha_nonneg hnot.1.symm,
      lt_of_le_of_ne hc_nonneg hnot.2.symm⟩
  have hbc_zero : b = 0 ∨ c = 0 := by
    by_contra hnot
    push Not at hnot
    exact hbc_pos ⟨lt_of_le_of_ne hb_nonneg hnot.1.symm,
      lt_of_le_of_ne hc_nonneg hnot.2.symm⟩
  constructor
  · rcases hab_zero with ha0 | hb0
    · exact ⟨0, by omega⟩
    · rcases hac_zero with ha0 | hc0
      · exact ⟨0, by omega⟩
      · refine ⟨k, ?_⟩
        omega
  constructor
  · rcases hab_zero with ha0 | hb0
    · rcases hbc_zero with hb0 | hc0
      · exact ⟨0, by omega⟩
      · refine ⟨k, ?_⟩
        omega
    · exact ⟨0, by omega⟩
  · rcases hac_zero with ha0 | hc0
    · rcases hbc_zero with hb0 | hc0
      · refine ⟨k, ?_⟩
        omega
      · exact ⟨0, by omega⟩
    · exact ⟨0, by omega⟩

/-- Checked p-adic parity layer for the shifted full-cover curve.  Away from
`2` and `3`, the pairwise differences of `X`, `X-1`, and `X+3` are units, and
the curve equation makes the sum of the three valuations even. -/
theorem e1FactorEvenPadicOutside23_checked :
    E1FactorEvenPadicOutside23Statement := by
  intro X Y hE hY
  rcases e1FullCoverCurve_factors_ne_zero hE hY with ⟨hX, hXm1, hXp3⟩
  have hParity :
      ∀ p : ℕ, Fact p.Prime → p ≠ 2 → p ≠ 3 →
        Even (padicValRat p X) ∧
          Even (padicValRat p (X - 1)) ∧
            Even (padicValRat p (X + 3)) := by
    intro p hpFact hp2 hp3
    letI : Fact p.Prime := hpFact
    let a : ℤ := padicValRat p X
    let b : ℤ := padicValRat p (X - 1)
    let c : ℤ := padicValRat p (X + 3)
    have hprod12 : X * (X - 1) ≠ 0 := mul_ne_zero hX hXm1
    have hval_prod :
        padicValRat p (X * (X - 1) * (X + 3)) = a + b + c := by
      dsimp [a, b, c]
      rw [padicValRat.mul hprod12 hXp3, padicValRat.mul hX hXm1]
    have hval_y :
        padicValRat p (Y ^ 2) = (2 : ℤ) * padicValRat p Y := by
      simpa using (padicValRat.pow (p := p) (q := Y) hY (k := 2))
    have hsum_eq : a + b + c = (2 : ℤ) * padicValRat p Y := by
      calc
        a + b + c = padicValRat p (X * (X - 1) * (X + 3)) := hval_prod.symm
        _ = padicValRat p (Y ^ 2) := by rw [← hE]
        _ = (2 : ℤ) * padicValRat p Y := hval_y
    have hsum : Even (a + b + c) := by
      refine ⟨padicValRat p Y, ?_⟩
      omega
    have hval_one : padicValRat p (1 : ℚ) = 0 := by simp
    have hval_neg_one : padicValRat p (-1 : ℚ) = 0 := by simp
    have hval_three : padicValRat p (3 : ℚ) = 0 :=
      padicValRat_three_of_prime_ne_three hp3
    have hval_neg_three : padicValRat p (-3 : ℚ) = 0 := by
      rw [padicValRat.neg]
      exact hval_three
    have hval_four : padicValRat p (4 : ℚ) = 0 :=
      padicValRat_four_of_prime_ne_two hp2
    have hval_neg_four : padicValRat p (-4 : ℚ) = 0 := by
      rw [padicValRat.neg]
      exact hval_four
    have hab_lt : a < b → a = 0 := by
      intro hlt
      dsimp [a, b] at hlt ⊢
      exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
        (p := p) (a := X) (b := X - 1) (c := 1)
        (by ring) (by norm_num) hval_one hlt
    have hba_lt : b < a → b = 0 := by
      intro hlt
      dsimp [a, b] at hlt ⊢
      exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
        (p := p) (a := X - 1) (b := X) (c := -1)
        (by ring) (by norm_num) hval_neg_one hlt
    have hac_lt : a < c → a = 0 := by
      intro hlt
      dsimp [a, c] at hlt ⊢
      exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
        (p := p) (a := X) (b := X + 3) (c := -3)
        (by ring) (by norm_num) hval_neg_three hlt
    have hca_lt : c < a → c = 0 := by
      intro hlt
      dsimp [a, c] at hlt ⊢
      exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
        (p := p) (a := X + 3) (b := X) (c := 3)
        (by ring) (by norm_num) hval_three hlt
    have hbc_lt : b < c → b = 0 := by
      intro hlt
      dsimp [b, c] at hlt ⊢
      exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
        (p := p) (a := X - 1) (b := X + 3) (c := -4)
        (by ring) (by norm_num) hval_neg_four hlt
    have hcb_lt : c < b → c = 0 := by
      intro hlt
      dsimp [b, c] at hlt ⊢
      exact padicValRat_left_eq_zero_of_lt_of_sub_val_zero
        (p := p) (a := X + 3) (b := X - 1) (c := 4)
        (by ring) (by norm_num) hval_four hlt
    have hab_pos : ¬ (0 < a ∧ 0 < b) := by
      dsimp [a, b]
      exact padicValRat_not_both_pos_of_sub_val_zero
        (p := p) (a := X) (b := X - 1) (c := 1)
        (by ring) (by norm_num) hval_one
    have hac_pos : ¬ (0 < a ∧ 0 < c) := by
      dsimp [a, c]
      exact padicValRat_not_both_pos_of_sub_val_zero
        (p := p) (a := X) (b := X + 3) (c := -3)
        (by ring) (by norm_num) hval_neg_three
    have hbc_pos : ¬ (0 < b ∧ 0 < c) := by
      dsimp [b, c]
      exact padicValRat_not_both_pos_of_sub_val_zero
        (p := p) (a := X - 1) (b := X + 3) (c := -4)
        (by ring) (by norm_num) hval_neg_four
    exact even_each_of_sum_even_of_pairwise_unit_val
      hsum hab_lt hba_lt hac_lt hca_lt hbc_lt hcb_lt
      hab_pos hac_pos hbc_pos
  refine ⟨⟨hX, ?_⟩, ⟨hXm1, ?_⟩, ⟨hXp3, ?_⟩⟩
  · intro p hp hp2 hp3
    exact (hParity p hp hp2 hp3).1
  · intro p hp hp2 hp3
    exact (hParity p hp hp2 hp3).2.1
  · intro p hp hp2 hp3
    exact (hParity p hp hp2 hp3).2.2

/-- The curve equation forces the product of the three selected squareclass
representatives to be a rational square. -/
theorem productSquareclassCondition_of_E1_squareclasses
    {X Y : ℚ} {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ}
    (hE : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    (hr0 : r0 ≠ 0) (hr1 : r1 ≠ 0) (hr3 : r3 ≠ 0)
    (hX : X = (d0 : ℚ) * r0 ^ 2)
    (hXm1 : X - 1 = (d1 : ℚ) * r1 ^ 2)
    (hXp3 : X + 3 = (d3 : ℚ) * r3 ^ 2) :
    ProductSquareclassCondition d0 d1 d3 := by
  let R : ℚ := r0 * r1 * r3
  have hR : R ≠ 0 := by
    dsimp [R]
    exact mul_ne_zero (mul_ne_zero hr0 hr1) hr3
  refine ⟨Y / R, div_ne_zero hY hR, ?_⟩
  have hprod :
      Y ^ 2 = ((d0 * d1 * d3 : ℤ) : ℚ) * R ^ 2 := by
    unfold E1FullCoverCurve at hE
    rw [hXm1, hXp3, hX] at hE
    dsimp [R]
    rw [hE]
    norm_num
    ring
  apply mul_right_cancel₀ (pow_ne_zero 2 hR)
  calc
    ((d0 * d1 * d3 : ℤ) : ℚ) * R ^ 2 = Y ^ 2 := hprod.symm
    _ = (Y / R) ^ 2 * R ^ 2 := by
      field_simp [hR]

/-- A common nonzero integer scaling of three rationals. -/
structure RatIntScale3 (r0 r1 r3 : ℚ) where
  T : ℤ
  hT : T ≠ 0
  A : ℤ
  B : ℤ
  C : ℤ
  hA : (A : ℚ) = (T : ℚ) * r0
  hB : (B : ℚ) = (T : ℚ) * r1
  hC : (C : ℚ) = (T : ℚ) * r3

private lemma rat_scale_by_three_den_product
    (q r s : ℚ) :
    ((q.num * (r.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ)
      = ((((q.den * r.den * s.den : ℕ) : ℤ) : ℚ) * q) := by
  calc
    ((q.num * (r.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ)
        = (q.num : ℚ) * (r.den : ℚ) * (s.den : ℚ) := by
          norm_cast
    _ = ((q.den : ℚ) * q) * (r.den : ℚ) * (s.den : ℚ) := by
          rw [← Rat.den_mul_eq_num q]
    _ = ((((q.den * r.den * s.den : ℕ) : ℤ) : ℚ) * q) := by
          simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
          ring

/-- Denominator-clearing object for three rationals. -/
theorem rat_int_scale3_nonempty (r0 r1 r3 : ℚ) :
    Nonempty (RatIntScale3 r0 r1 r3) := by
  refine ⟨
    { T := ((r0.den * r1.den * r3.den : ℕ) : ℤ)
      hT := by
        exact Int.ofNat_ne_zero.2
          (mul_ne_zero
            (mul_ne_zero (Rat.den_ne_zero r0) (Rat.den_ne_zero r1))
            (Rat.den_ne_zero r3))
      A := r0.num * (r1.den : ℤ) * (r3.den : ℤ)
      B := r1.num * (r0.den : ℤ) * (r3.den : ℤ)
      C := r3.num * (r0.den : ℤ) * (r1.den : ℤ)
      hA := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_three_den_product r0 r1 r3
      hB := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_three_den_product r1 r0 r3
      hC := by
        simpa [mul_assoc, mul_left_comm, mul_comm]
          using rat_scale_by_three_den_product r3 r0 r1 }⟩

private lemma ratIntScale3_sq_sub_cast
    {A B T : ℤ} {a b : ℚ}
    (hA : (A : ℚ) = (T : ℚ) * a)
    (hB : (B : ℚ) = (T : ℚ) * b) :
    ((A ^ 2 - B ^ 2 : ℤ) : ℚ) = (T : ℚ) ^ 2 * (a ^ 2 - b ^ 2) := by
  calc
    ((A ^ 2 - B ^ 2 : ℤ) : ℚ) = (A : ℚ) ^ 2 - (B : ℚ) ^ 2 := by
      norm_cast
    _ = ((T : ℚ) * a) ^ 2 - ((T : ℚ) * b) ^ 2 := by
      rw [hA, hB]
    _ = (T : ℚ) ^ 2 * (a ^ 2 - b ^ 2) := by
      ring

/-- A common integer scale of the three rational square roots gives the raw
integer cover equations. -/
theorem coverInt_of_ratIntScale3
    {X : ℚ} {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ}
    (s : RatIntScale3 r0 r1 r3)
    (hX : X = (d0 : ℚ) * r0 ^ 2)
    (hXm1 : X - 1 = (d1 : ℚ) * r1 ^ 2)
    (hXp3 : X + 3 = (d3 : ℚ) * r3 ^ 2) :
    CoverInt d0 d1 d3 s.A s.B s.C s.T := by
  have hleftQ : (d0 : ℚ) * r0 ^ 2 - (d1 : ℚ) * r1 ^ 2 = 1 := by
    nlinarith
  have hrightQ : (d3 : ℚ) * r3 ^ 2 - (d0 : ℚ) * r0 ^ 2 = 3 := by
    nlinarith
  constructor
  · exact Rat.intCast_injective (by
      calc
        ((d0 * s.A ^ 2 - d1 * s.B ^ 2 : ℤ) : ℚ)
            = (d0 : ℚ) * (s.A : ℚ) ^ 2 - (d1 : ℚ) * (s.B : ℚ) ^ 2 := by
              norm_cast
        _ = (s.T : ℚ) ^ 2 *
              ((d0 : ℚ) * r0 ^ 2 - (d1 : ℚ) * r1 ^ 2) := by
              rw [s.hA, s.hB]
              ring
        _ = (s.T : ℚ) ^ 2 := by rw [hleftQ]; ring
        _ = ((s.T ^ 2 : ℤ) : ℚ) := by norm_cast)
  · exact Rat.intCast_injective (by
      calc
        ((d3 * s.C ^ 2 - d0 * s.A ^ 2 : ℤ) : ℚ)
            = (d3 : ℚ) * (s.C : ℚ) ^ 2 - (d0 : ℚ) * (s.A : ℚ) ^ 2 := by
              norm_cast
        _ = (s.T : ℚ) ^ 2 *
              ((d3 : ℚ) * r3 ^ 2 - (d0 : ℚ) * r0 ^ 2) := by
              rw [s.hC, s.hA]
              ring
        _ = (s.T : ℚ) ^ 2 * 3 := by rw [hrightQ]
        _ = (((3 : ℤ) * s.T ^ 2 : ℤ) : ℚ) := by norm_cast; ring)

private lemma ratIntScale3_ratio_eq
    {T A : ℤ} {r : ℚ}
    (hT : T ≠ 0)
    (hA : (A : ℚ) = (T : ℚ) * r) :
    (A : ℚ) / (T : ℚ) = r := by
  have hTQ : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  field_simp [hTQ]
  exact hA

private lemma ratIntScale3_scaled_ne_zero
    {T A : ℤ} {r : ℚ}
    (hT : T ≠ 0)
    (hr : r ≠ 0)
    (hA : (A : ℚ) = (T : ℚ) * r) :
    A ≠ 0 := by
  intro hAz
  have hTQ : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  have hAq : (A : ℚ) = 0 := by exact_mod_cast hAz
  have hmul : (T : ℚ) * r = 0 := by
    rw [← hA, hAq]
  exact (mul_ne_zero hTQ hr) hmul

/-- Divide a common integer scale by its four-coordinate gcd to make it
primitive without changing the represented rationals. -/
theorem primitive_ratIntScale3_of_ratIntScale3
    {r0 r1 r3 : ℚ} (s : RatIntScale3 r0 r1 r3) :
    ∃ s' : RatIntScale3 r0 r1 r3, PrimitiveInt4 s'.A s'.B s'.C s'.T := by
  let g : ℕ := coverGCD4 s.A s.B s.C s.T
  have hgpos : 0 < g := by
    dsimp [g]
    exact coverGCD4_pos_of_fourth_ne_zero s.hT
  rcases coverGCD4_intCast_dvd_left s.A s.B s.C s.T with ⟨A', hAraw⟩
  rcases coverGCD4_intCast_dvd_second s.A s.B s.C s.T with ⟨B', hBraw⟩
  rcases coverGCD4_intCast_dvd_third s.A s.B s.C s.T with ⟨C', hCraw⟩
  rcases coverGCD4_intCast_dvd_fourth s.A s.B s.C s.T with ⟨T', hTraw⟩
  have hArawg : s.A = (g : ℤ) * A' := by simpa [g] using hAraw
  have hBrawg : s.B = (g : ℤ) * B' := by simpa [g] using hBraw
  have hCrawg : s.C = (g : ℤ) * C' := by simpa [g] using hCraw
  have hTrawg : s.T = (g : ℤ) * T' := by simpa [g] using hTraw
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hgpos)
  have hT'ne : T' ≠ 0 := by
    intro hT'0
    apply s.hT
    rw [hTrawg, hT'0]
    ring
  have hA' : (A' : ℚ) = (T' : ℚ) * r0 := by
    apply mul_left_cancel₀ hgQ
    calc
      (g : ℚ) * (A' : ℚ) = (s.A : ℚ) := by
        rw [hArawg]
        norm_cast
      _ = (s.T : ℚ) * r0 := s.hA
      _ = ((g : ℚ) * (T' : ℚ)) * r0 := by
        rw [hTrawg]
        norm_cast
      _ = (g : ℚ) * ((T' : ℚ) * r0) := by ring
  have hB' : (B' : ℚ) = (T' : ℚ) * r1 := by
    apply mul_left_cancel₀ hgQ
    calc
      (g : ℚ) * (B' : ℚ) = (s.B : ℚ) := by
        rw [hBrawg]
        norm_cast
      _ = (s.T : ℚ) * r1 := s.hB
      _ = ((g : ℚ) * (T' : ℚ)) * r1 := by
        rw [hTrawg]
        norm_cast
      _ = (g : ℚ) * ((T' : ℚ) * r1) := by ring
  have hC' : (C' : ℚ) = (T' : ℚ) * r3 := by
    apply mul_left_cancel₀ hgQ
    calc
      (g : ℚ) * (C' : ℚ) = (s.C : ℚ) := by
        rw [hCrawg]
        norm_cast
      _ = (s.T : ℚ) * r3 := s.hC
      _ = ((g : ℚ) * (T' : ℚ)) * r3 := by
        rw [hTrawg]
        norm_cast
      _ = (g : ℚ) * ((T' : ℚ) * r3) := by ring
  have hgcd :
      coverGCD4 A' B' C' T' = 1 := by
    exact coverGCD4_eq_one_of_common_factor
      (A := s.A) (B := s.B) (C := s.C) (T := s.T)
      (A' := A') (B' := B') (C' := C') (T' := T')
      (g := g) hgpos (by rfl) hArawg hBrawg hCrawg hTrawg
  refine ⟨
    { T := T'
      hT := hT'ne
      A := A'
      B := B'
      C := C'
      hA := hA'
      hB := hB'
      hC := hC' },
    primitiveInt4_of_coverGCD4_eq_one hgcd⟩

/-- Once a common scale is primitive, it packages the selected squareclass roots
as full integer cover data. -/
theorem e1FullCoverIntData_of_primitive_ratIntScale3
    {X Y : ℚ} {d0 d1 d3 : ℤ} {r0 r1 r3 : ℚ}
    (hE : E1FullCoverCurve X Y) (hY : Y ≠ 0)
    (hd0 : InS23 d0) (hd1 : InS23 d1) (hd3 : InS23 d3)
    (hr0 : r0 ≠ 0) (hr1 : r1 ≠ 0) (hr3 : r3 ≠ 0)
    (hX : X = (d0 : ℚ) * r0 ^ 2)
    (hXm1 : X - 1 = (d1 : ℚ) * r1 ^ 2)
    (hXp3 : X + 3 = (d3 : ℚ) * r3 ^ 2)
    (s : RatIntScale3 r0 r1 r3)
    (hprim : PrimitiveInt4 s.A s.B s.C s.T) :
    E1FullCoverIntData X Y := by
  refine ⟨d0, d1, d3, hd0, hd1, hd3,
    productSquareclassCondition_of_E1_squareclasses hE hY
      hr0 hr1 hr3 hX hXm1 hXp3,
    s.A, s.B, s.C, s.T, s.hT, ?_, ?_, ?_, hprim, ?_, ?_, ?_, ?_⟩
  · exact ratIntScale3_scaled_ne_zero s.hT hr0 s.hA
  · exact ratIntScale3_scaled_ne_zero s.hT hr1 s.hB
  · exact ratIntScale3_scaled_ne_zero s.hT hr3 s.hC
  · rw [hX, ratIntScale3_ratio_eq s.hT s.hA]
  · rw [hXm1, ratIntScale3_ratio_eq s.hT s.hB]
  · rw [hXp3, ratIntScale3_ratio_eq s.hT s.hC]
  · exact coverInt_of_ratIntScale3 s hX hXm1 hXp3

/-- The concrete common-denominator clearing layer is fully checked: choose a
common integer scale for the three rational square roots and divide by its
four-coordinate gcd. -/
theorem commonDenomSquareclassRepsToPrimitiveCoverInt_checked :
    CommonDenomSquareclassRepsToPrimitiveCoverIntStatement := by
  intro X Y d0 d1 d3 r0 r1 r3 hE hY hd0 hd1 hd3 hr0 hr1 hr3 hX hXm1 hXp3
  rcases rat_int_scale3_nonempty r0 r1 r3 with ⟨s⟩
  rcases primitive_ratIntScale3_of_ratIntScale3 s with ⟨s', hprim⟩
  exact e1FullCoverIntData_of_primitive_ratIntScale3
    hE hY hd0 hd1 hd3 hr0 hr1 hr3 hX hXm1 hXp3 s' hprim

/-- The abstract squareclass-supported denominator-clearing residual is reduced
to the concrete common-denominator clearing residual. -/
theorem e1FullCoverIntDataOfFactorSquareclasses_of_commonDenom
    (hcommon : CommonDenomSquareclassRepsToPrimitiveCoverIntStatement) :
    E1FullCoverIntDataOfFactorSquareclassesStatement := by
  intro X Y hE hY hX hXm1 hXp3
  rcases hX with ⟨_hXne, d0, hd0, r0, hr0, hXsq⟩
  rcases hXm1 with ⟨_hXm1ne, d1, hd1, r1, hr1, hXm1sq⟩
  rcases hXp3 with ⟨_hXp3ne, d3, hd3, r3, hr3, hXp3sq⟩
  exact hcommon hE hY hd0 hd1 hd3 hr0 hr1 hr3 hXsq hXm1sq hXp3sq

/-- Checked denominator-clearing layer from supported squareclasses to primitive
integer full-cover data. -/
theorem e1FullCoverIntDataOfFactorSquareclasses_checked :
    E1FullCoverIntDataOfFactorSquareclassesStatement :=
  e1FullCoverIntDataOfFactorSquareclasses_of_commonDenom
    commonDenomSquareclassRepsToPrimitiveCoverInt_checked

/-- The full-cover extraction theorem follows formally from the three split
residual layers. -/
theorem e1_full_cover_extraction_from_split_residuals
    (hval : E1FactorEvenPadicOutside23Statement)
    (hsq : SquareclassSupportedOn23OfEvenPadicOutside23Statement)
    (hclear : E1FullCoverIntDataOfFactorSquareclassesStatement) :
    E1FullCoverSquareclassExtractionIntStatement := by
  intro X Y hE hY
  rcases hval hE hY with ⟨hX, hXm1, hXp3⟩
  exact hclear hE hY (hsq hX) (hsq hXm1) (hsq hXp3)

end MazurProof.RationalPointsN12
