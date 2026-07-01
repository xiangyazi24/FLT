# Q2840 (dm-codex1): `sqclass23Rep` wrapper for the squareclass-on-23 residual

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic

namespace MazurProof.RationalPointsN12

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

/-- Valuation of the chosen representative at `2`: it is `0` or `1` according
as the original `2`-valuation was even or odd. -/
private theorem padicValRat_sqclass23Rep_at_two (q : ℚ) :
    padicValRat 2 (((sqclass23Rep q : ℤ) : ℚ)) =
      if Even (padicValRat 2 q) then 0 else 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hself : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (p := 2) (by norm_num)
  have hthree : padicValRat 2 (3 : ℚ) = 0 :=
    padicValRat_three_of_prime_ne_three (p := 2) (by norm_num)
  unfold sqclass23Rep
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hq, h2, h3, padicValRat.mul, padicValRat.neg, hself, hthree]

/-- Valuation of the chosen representative at `3`. -/
private theorem padicValRat_sqclass23Rep_at_three (q : ℚ) :
    padicValRat 3 (((sqclass23Rep q : ℤ) : ℚ)) =
      if Even (padicValRat 3 q) then 0 else 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hself : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (p := 3) (by norm_num)
  have htwo : padicValRat 3 (2 : ℚ) = 0 :=
    padicValRat_two_of_prime_ne_two (p := 3) (by norm_num)
  unfold sqclass23Rep
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hq, h2, h3, padicValRat.mul, padicValRat.neg, hself, htwo]

/-- Outside `{2,3}`, the chosen representative has valuation zero. -/
private theorem padicValRat_sqclass23Rep_outside23
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) (q : ℚ) :
    padicValRat p (((sqclass23Rep q : ℤ) : ℚ)) = 0 := by
  have htwo : padicValRat p (2 : ℚ) = 0 :=
    padicValRat_two_of_prime_ne_two (p := p) hp2
  have hthree : padicValRat p (3 : ℚ) = 0 :=
    padicValRat_three_of_prime_ne_three (p := p) hp3
  unfold sqclass23Rep
  by_cases hq : q < 0 <;>
  by_cases h2 : Even (padicValRat 2 q) <;>
  by_cases h3 : Even (padicValRat 3 q) <;>
  simp [hq, h2, h3, padicValRat.mul, padicValRat.neg, htwo, hthree]

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
    · simpa [h2] using h2
    · simpa [h2] using even_sub_one_of_not_even h2
  · by_cases hp3 : p = 3
    · subst p
      rw [padicValRat_sqclass23Rep_at_three]
      by_cases h3 : Even (padicValRat 3 q)
      · simpa [h3] using h3
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

end MazurProof.RationalPointsN12
```

API notes:

* If `simp [padicValRat.mul]` leaves nonzero side goals in the three valuation helper lemmas, add `norm_num` side proofs by rewriting products one factor at a time with `rw [padicValRat.mul (by norm_num) (by norm_num)]`.
* If the local theorem names for constants differ, replace only:
  `padicValRat_two_of_prime_ne_two` and `padicValRat_three_of_prime_ne_three`.
* The parity helper `even_sub_one_of_not_even` uses `Int.not_even_iff_odd`; if that lemma is not imported, add `import Mathlib.Algebra.Ring.Int.Parity`.
