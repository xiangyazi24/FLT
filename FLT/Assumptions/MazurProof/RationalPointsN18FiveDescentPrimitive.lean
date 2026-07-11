import FLT.Assumptions.MazurProof.RationalPointsN18FiveDescent25

/-!
# Primitive reduction of the order-18 five-descent

The previous layer proves that the unique five-divisible norm root and the
unique five-divisible cusp factor have the same 5-adic valuation.  Here we
remove their common factor `5^(k-1)`, leaving a positive pair of valuation
exactly one.  When `k ≥ 3`, both new terms are strictly smaller.

The six possible root/cusp pairings are then rewritten after this common
factor is cancelled from `e*f = A*D*(A+D)`.  The two integral norm equations
are retained after the same substitution.
-/

namespace MazurProof.RationalPointsN18FiveDescentPrimitive

open RationalPointsN18
open RationalPointsN18Descent
open RationalPointsN18FiveDescent
open RationalPointsN18FiveDescent25

noncomputable section

/-- Data obtained by removing all but one common factor of five from two
positive integers with equal positive 5-adic valuation. -/
structure FivePeel (x y : ℤ) where
  k : ℕ
  q : ℤ
  x0 : ℤ
  y0 : ℤ
  k_eq : k = padicValInt 5 x
  one_le_k : 1 ≤ k
  q_eq : q = (5 : ℤ) ^ (k - 1)
  x_eq : x = q * x0
  y_eq : y = q * y0
  x0_pos : 0 < x0
  y0_pos : 0 < y0
  x0_val : padicValInt 5 x0 = 1
  y0_val : padicValInt 5 y0 = 1
  strict_of_three_le : 3 ≤ k → x0 < x ∧ y0 < y

theorem padicValInt_eq_of_sameFiveValuation {x y : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hsame : SameFiveValuation x y) :
    padicValInt 5 x = padicValInt 5 y := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply le_antisymm
  · have hdx : (((5 : ℕ) : ℤ) ^ padicValInt 5 x) ∣ x :=
      padicValInt_dvd (p := 5) x
    have hdy : (((5 : ℕ) : ℤ) ^ padicValInt 5 x) ∣ y :=
      (hsame (padicValInt 5 x)).mp hdx
    rcases (padicValInt_dvd_iff (p := 5) (padicValInt 5 x) y).mp hdy with
        hyzero | hle
    · exact (hy hyzero).elim
    · exact hle
  · have hdy : (((5 : ℕ) : ℤ) ^ padicValInt 5 y) ∣ y :=
      padicValInt_dvd (p := 5) y
    have hdx : (((5 : ℕ) : ℤ) ^ padicValInt 5 y) ∣ x :=
      (hsame (padicValInt 5 y)).mpr hdy
    rcases (padicValInt_dvd_iff (p := 5) (padicValInt 5 y) x).mp hdx with
        hxzero | hle
    · exact (hx hxzero).elim
    · exact hle

theorem peel_common_five_power {x y : ℤ}
    (hx : 0 < x) (hy : 0 < y)
    (hx5 : (5 : ℤ) ∣ x) (_hy5 : (5 : ℤ) ∣ y)
    (hsame : SameFiveValuation x y) :
    Nonempty (FivePeel x y) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy
  let k : ℕ := padicValInt 5 x
  have hvalxy : padicValInt 5 x = padicValInt 5 y :=
    padicValInt_eq_of_sameFiveValuation hxne hyne hsame
  have hyval : padicValInt 5 y = k := by
    simpa [k] using hvalxy.symm
  have hk : 1 ≤ k := by
    have hxpow : (((5 : ℕ) : ℤ) ^ 1) ∣ x := by simpa using hx5
    rcases (padicValInt_dvd_iff (p := 5) 1 x).mp hxpow with hxzero | hle
    · exact (hxne hxzero).elim
    · exact hle
  let q : ℤ := (5 : ℤ) ^ (k - 1)
  have hqx : q ∣ x := by
    apply (padicValInt_dvd_iff (p := 5) (k - 1) x).mpr
    exact Or.inr (by dsimp [k]; exact Nat.sub_le _ _)
  have hqy : q ∣ y := by
    exact (hsame (k - 1)).mp hqx
  obtain ⟨x0, hx0eq⟩ := hqx
  obtain ⟨y0, hy0eq⟩ := hqy
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hx0pos : 0 < x0 := by
    have hp : 0 < q * x0 := by simpa [hx0eq] using hx
    exact pos_of_mul_pos_right hp hqpos.le
  have hy0pos : 0 < y0 := by
    have hp : 0 < q * y0 := by simpa [hy0eq] using hy
    exact pos_of_mul_pos_right hp hqpos.le
  have hx0ne : x0 ≠ 0 := ne_of_gt hx0pos
  have hy0ne : y0 ≠ 0 := ne_of_gt hy0pos
  have hqval : padicValInt 5 q = k - 1 := by
    dsimp [q]
    have hcast : ((5 : ℤ) ^ (k - 1)) = (((5 : ℕ) ^ (k - 1) : ℕ) : ℤ) := by
      norm_cast
    rw [hcast, padicValInt.of_nat, padicValNat.prime_pow]
  have hx0val : padicValInt 5 x0 = 1 := by
    have hmul := padicValInt.mul (p := 5) hqne hx0ne
    rw [← hx0eq, hqval] at hmul
    change k = k - 1 + padicValInt 5 x0 at hmul
    omega
  have hy0val : padicValInt 5 y0 = 1 := by
    have hmul := padicValInt.mul (p := 5) hqne hy0ne
    rw [← hy0eq, hqval, hyval] at hmul
    omega
  have hstrict : 3 ≤ k → x0 < x ∧ y0 < y := by
    intro hk3
    have hexp : k - 1 ≠ 0 := by omega
    have hqgt : 1 < q := by
      dsimp [q]
      exact one_lt_pow₀ (by norm_num : (1 : ℤ) < 5) hexp
    constructor
    · calc
        x0 = 1 * x0 := by ring
        _ < q * x0 := mul_lt_mul_of_pos_right hqgt hx0pos
        _ = x := hx0eq.symm
    · calc
        y0 = 1 * y0 := by ring
        _ < q * y0 := mul_lt_mul_of_pos_right hqgt hy0pos
        _ = y := hy0eq.symm
  exact ⟨
    { k := k
      q := q
      x0 := x0
      y0 := y0
      k_eq := rfl
      one_le_k := hk
      q_eq := rfl
      x_eq := hx0eq
      y_eq := hy0eq
      x0_pos := hx0pos
      y0_pos := hy0pos
      x0_val := hx0val
      y0_val := hy0val
      strict_of_three_le := hstrict }⟩

/-- If the common valuation is at least three, removing all but one factor of
five strictly decreases both members of the matched pair. -/
theorem peel_common_five_power_strict {x y : ℤ}
    (hx : 0 < x) (hy : 0 < y)
    (hx5 : (5 : ℤ) ∣ x) (hy5 : (5 : ℤ) ∣ y)
    (hsame : SameFiveValuation x y)
    (hthree : 3 ≤ padicValInt 5 x) :
    ∃ p : FivePeel x y, p.x0 < x ∧ p.y0 < y := by
  obtain ⟨p⟩ := peel_common_five_power hx hy hx5 hy5 hsame
  refine ⟨p, p.strict_of_three_le ?_⟩
  simpa only [p.k_eq] using hthree

/-! ## Integral systems after cancellation -/

def NormBranches (P e f : ℤ) : Prop :=
  P = e ^ 2 - 2 * f ^ 2 ∨ P = 2 * e ^ 2 - f ^ 2

/-- The six possible primitive systems after cancelling the common power of
five. -/
def PrimitiveFiveReduction (A D e f : ℤ) : Prop :=
  ((5 : ℤ) ∣ e ∧ (5 : ℤ) ∣ A ∧
    ∃ p : FivePeel e A,
      p.x0 * f = p.y0 * D * (p.q * p.y0 + D) ∧
      NormBranches (normReal (p.q * p.y0) D) (p.q * p.x0) f) ∨
  ((5 : ℤ) ∣ e ∧ (5 : ℤ) ∣ D ∧
    ∃ p : FivePeel e D,
      p.x0 * f = A * p.y0 * (A + p.q * p.y0) ∧
      NormBranches (normReal A (p.q * p.y0)) (p.q * p.x0) f) ∨
  ((5 : ℤ) ∣ e ∧ (5 : ℤ) ∣ A + D ∧
    ∃ p : FivePeel e (A + D),
      p.x0 * f = A * D * p.y0 ∧
      NormBranches (normReal A D) (p.q * p.x0) f) ∨
  ((5 : ℤ) ∣ f ∧ (5 : ℤ) ∣ A ∧
    ∃ p : FivePeel f A,
      e * p.x0 = p.y0 * D * (p.q * p.y0 + D) ∧
      NormBranches (normReal (p.q * p.y0) D) e (p.q * p.x0)) ∨
  ((5 : ℤ) ∣ f ∧ (5 : ℤ) ∣ D ∧
    ∃ p : FivePeel f D,
      e * p.x0 = A * p.y0 * (A + p.q * p.y0) ∧
      NormBranches (normReal A (p.q * p.y0)) e (p.q * p.x0)) ∨
  ((5 : ℤ) ∣ f ∧ (5 : ℤ) ∣ A + D ∧
    ∃ p : FivePeel f (A + D),
      e * p.x0 = A * D * p.y0 ∧
      NormBranches (normReal A D) e (p.q * p.x0))

theorem primitive_reduction_of_match {A D e f : ℤ}
    (hA : 0 < A) (hD : 0 < D) (he : 0 < e) (hf : 0 < f)
    (hmul : e * f = A * D * (A + D))
    (hnorm : NormBranches (normReal A D) e f)
    (hmatch : FiveValuationMatch A D e f) :
    PrimitiveFiveReduction A D e f := by
  rcases hmatch with ⟨he5, hpairA | hpairD | hpairS⟩ |
      ⟨hf5, hpairA | hpairD | hpairS⟩
  · obtain ⟨p⟩ := peel_common_five_power he hA he5 hpairA.1 hpairA.2.1
    have hqne : p.q ≠ 0 := by rw [p.q_eq]; positivity
    have hprod : p.x0 * f = p.y0 * D * (p.q * p.y0 + D) := by
      apply mul_left_cancel₀ hqne
      calc
        p.q * (p.x0 * f) = (p.q * p.x0) * f := by ring
        _ = e * f := (congrArg (fun z : ℤ => z * f) p.x_eq).symm
        _ = A * D * (A + D) := hmul
        _ = (p.q * p.y0) * D * (p.q * p.y0 + D) :=
          congrArg (fun z : ℤ => z * D * (z + D)) p.y_eq
        _ = p.q * (p.y0 * D * (p.q * p.y0 + D)) := by ring
    have hnorm' :
        NormBranches (normReal (p.q * p.y0) D) (p.q * p.x0) f := by
      rcases hnorm with hbranch | hbranch
      · exact Or.inl (by simpa only [p.y_eq, p.x_eq] using hbranch)
      · exact Or.inr (by simpa only [p.y_eq, p.x_eq] using hbranch)
    exact Or.inl ⟨he5, hpairA.1, p, hprod, hnorm'⟩
  · obtain ⟨p⟩ := peel_common_five_power he hD he5 hpairD.1 hpairD.2.1
    have hqne : p.q ≠ 0 := by rw [p.q_eq]; positivity
    have hprod : p.x0 * f = A * p.y0 * (A + p.q * p.y0) := by
      apply mul_left_cancel₀ hqne
      calc
        p.q * (p.x0 * f) = (p.q * p.x0) * f := by ring
        _ = e * f := (congrArg (fun z : ℤ => z * f) p.x_eq).symm
        _ = A * D * (A + D) := hmul
        _ = A * (p.q * p.y0) * (A + p.q * p.y0) :=
          congrArg (fun z : ℤ => A * z * (A + z)) p.y_eq
        _ = p.q * (A * p.y0 * (A + p.q * p.y0)) := by ring
    have hnorm' :
        NormBranches (normReal A (p.q * p.y0)) (p.q * p.x0) f := by
      rcases hnorm with hbranch | hbranch
      · exact Or.inl (by simpa only [p.y_eq, p.x_eq] using hbranch)
      · exact Or.inr (by simpa only [p.y_eq, p.x_eq] using hbranch)
    exact Or.inr (Or.inl ⟨he5, hpairD.1, p, hprod, hnorm'⟩)
  · obtain ⟨p⟩ := peel_common_five_power he (add_pos hA hD)
      he5 hpairS.1 hpairS.2.1
    have hqne : p.q ≠ 0 := by rw [p.q_eq]; positivity
    have hprod : p.x0 * f = A * D * p.y0 := by
      apply mul_left_cancel₀ hqne
      calc
        p.q * (p.x0 * f) = (p.q * p.x0) * f := by ring
        _ = e * f := (congrArg (fun z : ℤ => z * f) p.x_eq).symm
        _ = A * D * (A + D) := hmul
        _ = A * D * (p.q * p.y0) :=
          congrArg (fun z : ℤ => A * D * z) p.y_eq
        _ = p.q * (A * D * p.y0) := by ring
    have hnorm' : NormBranches (normReal A D) (p.q * p.x0) f := by
      rcases hnorm with hbranch | hbranch
      · exact Or.inl (by simpa only [p.x_eq] using hbranch)
      · exact Or.inr (by simpa only [p.x_eq] using hbranch)
    exact Or.inr (Or.inr (Or.inl ⟨he5, hpairS.1, p, hprod, hnorm'⟩))
  · obtain ⟨p⟩ := peel_common_five_power hf hA hf5 hpairA.1 hpairA.2.1
    have hqne : p.q ≠ 0 := by rw [p.q_eq]; positivity
    have hprod : e * p.x0 = p.y0 * D * (p.q * p.y0 + D) := by
      apply mul_left_cancel₀ hqne
      calc
        p.q * (e * p.x0) = e * (p.q * p.x0) := by ring
        _ = e * f := (congrArg (fun z : ℤ => e * z) p.x_eq).symm
        _ = A * D * (A + D) := hmul
        _ = (p.q * p.y0) * D * (p.q * p.y0 + D) :=
          congrArg (fun z : ℤ => z * D * (z + D)) p.y_eq
        _ = p.q * (p.y0 * D * (p.q * p.y0 + D)) := by ring
    have hnorm' :
        NormBranches (normReal (p.q * p.y0) D) e (p.q * p.x0) := by
      rcases hnorm with hbranch | hbranch
      · exact Or.inl (by simpa only [p.y_eq, p.x_eq] using hbranch)
      · exact Or.inr (by simpa only [p.y_eq, p.x_eq] using hbranch)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hf5, hpairA.1, p, hprod, hnorm'⟩)))
  · obtain ⟨p⟩ := peel_common_five_power hf hD hf5 hpairD.1 hpairD.2.1
    have hqne : p.q ≠ 0 := by rw [p.q_eq]; positivity
    have hprod : e * p.x0 = A * p.y0 * (A + p.q * p.y0) := by
      apply mul_left_cancel₀ hqne
      calc
        p.q * (e * p.x0) = e * (p.q * p.x0) := by ring
        _ = e * f := (congrArg (fun z : ℤ => e * z) p.x_eq).symm
        _ = A * D * (A + D) := hmul
        _ = A * (p.q * p.y0) * (A + p.q * p.y0) :=
          congrArg (fun z : ℤ => A * z * (A + z)) p.y_eq
        _ = p.q * (A * p.y0 * (A + p.q * p.y0)) := by ring
    have hnorm' :
        NormBranches (normReal A (p.q * p.y0)) e (p.q * p.x0) := by
      rcases hnorm with hbranch | hbranch
      · exact Or.inl (by simpa only [p.y_eq, p.x_eq] using hbranch)
      · exact Or.inr (by simpa only [p.y_eq, p.x_eq] using hbranch)
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hf5, hpairD.1, p, hprod, hnorm'⟩))))
  · obtain ⟨p⟩ := peel_common_five_power hf (add_pos hA hD)
      hf5 hpairS.1 hpairS.2.1
    have hqne : p.q ≠ 0 := by rw [p.q_eq]; positivity
    have hprod : e * p.x0 = A * D * p.y0 := by
      apply mul_left_cancel₀ hqne
      calc
        p.q * (e * p.x0) = e * (p.q * p.x0) := by ring
        _ = e * f := (congrArg (fun z : ℤ => e * z) p.x_eq).symm
        _ = A * D * (A + D) := hmul
        _ = A * D * (p.q * p.y0) :=
          congrArg (fun z : ℤ => A * D * z) p.y_eq
        _ = p.q * (A * D * p.y0) := by ring
    have hnorm' : NormBranches (normReal A D) e (p.q * p.x0) := by
      rcases hnorm with hbranch | hbranch
      · exact Or.inl (by simpa only [p.x_eq] using hbranch)
      · exact Or.inr (by simpa only [p.x_eq] using hbranch)
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨hf5, hpairS.1, p, hprod, hnorm'⟩))))

/-! ## Primitive rational-point seam -/

theorem noncuspidal_point_to_primitive_five_reduction {U Y : ℚ}
    (hU0 : U ≠ 0) (hU1 : U ≠ 1)
    (hY : Y ^ 2 = hyperellipticF18 U) :
    ∃ A D C e f : ℤ,
      0 < A ∧ 0 < D ∧ 0 < e ∧ 0 < f ∧
      Int.gcd A D = 1 ∧ Int.gcd A (A + D) = 1 ∧ Int.gcd D (A + D) = 1 ∧
      Int.gcd e f = 1 ∧ e * f = A * D * (A + D) ∧
      PrimitiveFiveReduction A D e f ∧
      ((normReal A D = e ^ 2 - 2 * f ^ 2 ∧
          |C| = e ^ 2 + 2 * f ^ 2 ∧ FiveBranchOne A D e f) ∨
       (normReal A D = 2 * e ^ 2 - f ^ 2 ∧
          |C| = 2 * e ^ 2 + f ^ 2 ∧ FiveBranchTwo A D e f)) := by
  obtain ⟨A, D, C, e, f, hA, hD, he, hf, hcop, hcopAS, hcopDS,
      hcopEF, hmul, hmatch, hforms⟩ :=
    noncuspidal_point_to_lifted_five_cases hU0 hU1 hY
  have hnorm : NormBranches (normReal A D) e f := by
    rcases hforms with hbranch | hbranch
    · exact Or.inl hbranch.1
    · exact Or.inr hbranch.1
  have hreduce := primitive_reduction_of_match hA hD he hf hmul hnorm hmatch
  exact ⟨A, D, C, e, f, hA, hD, he, hf, hcop, hcopAS, hcopDS,
    hcopEF, hmul, hreduce, hforms⟩

end

end MazurProof.RationalPointsN18FiveDescentPrimitive
