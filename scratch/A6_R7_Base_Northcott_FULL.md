
═══ BRIDGE  Q21 →dm2  SUBMITTED ═══
     "A6-HEIGHT design R7 (about the BASE projective-height Northcott over ℚ…"
     ↳ debug: task 5abbb89f

[ask-gpt Q21 dm2 tid=5abbb89f +0s] dispatched, waiting for answer
[ask-gpt Q21 dm2 tid=5abbb89f +90s] waiting (status=processing)
[ask-gpt Q21 dm2 tid=5abbb89f +180s] waiting (status=processing)
[ask-gpt Q21 dm2 tid=5abbb89f +270s] waiting (status=processing)
[ask-gpt Q21 dm2 tid=5abbb89f +360s] waiting (status=processing)
[ask-gpt Q21 dm2 tid=5abbb89f +450s] waiting (status=processing)
[ask-gpt Q21 dm2 tid=5abbb89f +540s] waiting (status=processing)
[ask-gpt Q21 dm2 tid=5abbb89f +630s] waiting (status=processing)
[ask-gpt Q21 dm2 tid=5abbb89f +668s] terminal: status=completed

═══ BRIDGE  Q21 →dm2  ✅ COMPLETE (10.0KB, 11m08s) ═══
     "A6-HEIGHT design R7 (about the BASE projective-height Northcott over ℚ…"
     ↳ debug: task 5abbb89f

I’ll first verify the exact height and projectivization APIs, especially Projectivization.logHeight_mk and the rational logHeight₁ normalization, before committing to the proof.

Mathlib appears to have the rational height formulas but not the projective Northcott instance, so I’ll build the missing base theorem through a small ℙ¹(ℚ) ≃ Option ℚ chart layer.

Mathlib has the right height API for the proof, but not the final instance: Projectivization.logHeight_mk is available, Northcott is exactly the finite-sublevel-set class, and the file Height.Northcott explicitly marks projective Northcott instances as TODO. The rational-number height formulas you need are Rat.mulHeight_self_one_eq_mulHeight_num_den, Rat.mulHeight₁_eq_max, and Rat.logHeight₁_eq_log_max. 
Lean Community

Here is the full intended Lean block. It proves the base theorem by using the chart ℙ¹(ℚ) ≃ Option ℚ, where none = [1:0] and some q = [q:1].

lean
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.Northcott
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Order.Northcott

noncomputable section

open scoped Matrix
open Real
open Height

namespace RatP1Northcott

abbrev P1 : Type := Projectivization ℚ (Fin 2 → ℚ)

private lemma vec_one_zero_ne_zero : ![(1 : ℚ), 0] ≠ 0 := by
  intro h
  have h0 := congr_fun h 0
  norm_num at h0

private lemma vec_self_one_ne_zero (q : ℚ) : ![q, (1 : ℚ)] ≠ 0 := by
  intro h
  have h1 := congr_fun h 1
  norm_num at h1

/-- The point at infinity `[1:0] ∈ ℙ¹(ℚ)`. -/
def infinity : P1 :=
  Projectivization.mk ℚ ![(1 : ℚ), 0] vec_one_zero_ne_zero

/-- The affine chart point `[q:1] ∈ ℙ¹(ℚ)`. -/
def affine (q : ℚ) : P1 :=
  Projectivization.mk ℚ ![q, (1 : ℚ)] (vec_self_one_ne_zero q)

/-- The affine chart map `ℙ¹(ℚ) → Option ℚ`. -/
def toOption : P1 → Option ℚ :=
  Projectivization.lift
    (K := ℚ) (V := Fin 2 → ℚ)
    (fun v =>
      if h : (v : Fin 2 → ℚ) 1 = 0 then
        none
      else
        some ((v : Fin 2 → ℚ) 0 / (v : Fin 2 → ℚ) 1))
    (by
      intro a b t ht
      have ht0 : t ≠ 0 := by
        intro ht0
        exact a.2 (by
          rw [ht, ht0, zero_smul])
      by_cases hb : (b : Fin 2 → ℚ) 1 = 0
      · have ha : (a : Fin 2 → ℚ) 1 = 0 := by
          rw [ht]
          simp [Pi.smul_apply, hb]
        simp [ha, hb]
      · have ha : (a : Fin 2 → ℚ) 1 ≠ 0 := by
          rw [ht]
          simp [Pi.smul_apply, ht0, hb]
        have h0 : (a : Fin 2 → ℚ) 0 = t * (b : Fin 2 → ℚ) 0 := by
          simpa [Pi.smul_apply] using congr_fun ht 0
        have h1 : (a : Fin 2 → ℚ) 1 = t * (b : Fin 2 → ℚ) 1 := by
          simpa [Pi.smul_apply] using congr_fun ht 1
        simp [ha, hb]
        calc
          (a : Fin 2 → ℚ) 0 / (a : Fin 2 → ℚ) 1
              = (t * (b : Fin 2 → ℚ) 0) / (t * (b : Fin 2 → ℚ) 1) := by
                  rw [h0, h1]
          _ = (b : Fin 2 → ℚ) 0 / (b : Fin 2 → ℚ) 1 := by
                  field_simp [ht0, hb])

@[simp] lemma toOption_infinity : toOption infinity = none := by
  unfold toOption infinity
  rw [Projectivization.lift_mk]
  simp

@[simp] lemma toOption_affine (q : ℚ) : toOption (affine q) = some q := by
  unfold toOption affine
  rw [Projectivization.lift_mk]
  simp

/-- The inverse chart map `Option ℚ → ℙ¹(ℚ)`. -/
def ofOption : Option ℚ → P1
  | none => infinity
  | some q => affine q

@[simp] lemma ofOption_none : ofOption none = infinity := rfl
@[simp] lemma ofOption_some (q : ℚ) : ofOption (some q) = affine q := rfl

lemma ofOption_toOption (z : P1) : ofOption (toOption z) = z := by
  induction z using Projectivization.ind with
  | h v hv =>
      unfold toOption
      rw [Projectivization.lift_mk]
      by_cases h1 : v 1 = 0
      · simp [h1, ofOption, infinity]
        symm
        rw [Projectivization.mk_eq_mk_iff']
        refine ⟨v 0, ?_⟩
        ext i
        fin_cases i <;> simp [Pi.smul_apply, h1]
      · simp [h1, ofOption, affine]
        symm
        rw [Projectivization.mk_eq_mk_iff']
        refine ⟨v 1, ?_⟩
        ext i
        fin_cases i
        · simp [Pi.smul_apply, h1]
          field_simp [h1]
        · simp [Pi.smul_apply]

@[simp] lemma toOption_ofOption (z : Option ℚ) : toOption (ofOption z) = z := by
  cases z <;> simp [ofOption]

/-- The equivalence `ℙ¹(ℚ) ≃ Option ℚ`. -/
def equivOption : P1 ≃ Option ℚ where
  toFun := toOption
  invFun := ofOption
  left_inv := ofOption_toOption
  right_inv := toOption_ofOption

private lemma finite_int_natAbs_le (N : ℕ) :
    {z : ℤ | z.natAbs ≤ N}.Finite := by
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro z hz
  rw [Set.mem_Icc]
  have hzN : (z.natAbs : ℤ) ≤ (N : ℤ) := by
    exact_mod_cast hz
  constructor
  · exact (neg_le_neg hzN).trans (Int.neg_natAbs_le z)
  · exact (Int.le_natAbs z).trans hzN

private lemma finite_nat_le (N : ℕ) :
    {n : ℕ | n ≤ N}.Finite := by
  simpa using (Set.finite_Icc 0 N)

/-- Finitely many rationals have bounded numerator and denominator. -/
private lemma finite_rat_num_den_le (N : ℕ) :
    {q : ℚ | max q.num.natAbs q.den ≤ N}.Finite := by
  classical
  let S : Set (ℤ × ℕ) := {p | p.1.natAbs ≤ N ∧ p.2 ≤ N}
  have hS : S.Finite := by
    simpa [S, Set.setOf_and] using
      (finite_int_natAbs_le N).prod (finite_nat_le N)
  refine (hS.image fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ)).subset ?_
  intro q hq
  refine ⟨(q.num, q.den), ?_, ?_⟩
  · exact ⟨le_trans (le_max_left _ _) hq, le_trans (le_max_right _ _) hq⟩
  · exact Rat.num_div_den q

/-- Bounded rational logarithmic height gives bounded numerator and denominator. -/
private lemma rat_logHeight₁_bound (B : ℝ) :
    ∃ N : ℕ, ∀ q : ℚ,
      Height.logHeight₁ q ≤ B →
        max q.num.natAbs q.den ≤ N := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp B)
  refine ⟨N, ?_⟩
  intro q hq
  have hlog :
      Real.log ((max q.num.natAbs q.den : ℕ) : ℝ) ≤ B := by
    simpa [Rat.logHeight₁_eq_log_max] using hq
  have hle_exp :
      ((max q.num.natAbs q.den : ℕ) : ℝ) ≤ Real.exp B :=
    le_exp_of_log_le hlog
  have hlt : ((max q.num.natAbs q.den : ℕ) : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt hle_exp hN
  exact_mod_cast le_of_lt hlt

/-- Northcott for the affine logarithmic height on `ℚ`. -/
theorem rat_logHeight₁_northcott :
    Northcott (Height.logHeight₁ (K := ℚ)) where
  finite_le B := by
    obtain ⟨N, hN⟩ := rat_logHeight₁_bound B
    exact (finite_rat_num_den_le N).subset (by
      intro q hq
      exact hN q hq)

/-- Height on the `Option ℚ` chart of `ℙ¹(ℚ)`. -/
def optionLogHeight : Option ℚ → ℝ
  | none => 0
  | some q => Height.logHeight₁ q

/-- Northcott on the `Option ℚ` chart. -/
private theorem optionLogHeight_northcott :
    Northcott optionLogHeight where
  finite_le B := by
    classical
    have hq : {q : ℚ | Height.logHeight₁ q ≤ B}.Finite :=
      Northcott.finite_le (h := Height.logHeight₁ (K := ℚ)) B
    have h :
        {o : Option ℚ | optionLogHeight o ≤ B}
          =
        {none} ∪ (Option.some '' {q : ℚ | Height.logHeight₁ q ≤ B}) := by
      ext o
      cases o <;> simp [optionLogHeight]
    rw [h]
    exact (Set.finite_singleton none).union (hq.image Option.some)

private lemma rat_gcd_num_den_vec (q : ℚ) :
    Finset.univ.gcd ![q.num, (q.den : ℤ)] = 1 := by
  have hred : Nat.gcd q.num.natAbs q.den = 1 := by
    simpa [Nat.Coprime] using q.reduced
  simpa [Finset.univ_fin_two, hred, Int.natAbs_natCast]

/-- `Height.logHeight ![q,1] = Height.logHeight₁ q`. -/
private lemma Rat.logHeight_pair_self_one (q : ℚ) :
    Height.logHeight ![q, (1 : ℚ)] = Height.logHeight₁ q := by
  rw [Height.logHeight_eq_log_mulHeight, Height.logHeight₁_eq_log_mulHeight₁]
  rw [Rat.mulHeight_self_one_eq_mulHeight_num_den, Rat.mulHeight₁_eq_max]
  have htuple :=
    Rat.mulHeight_eq_max_abs_of_gcd_eq_one
      (x := ![q.num, (q.den : ℤ)])
      (rat_gcd_num_den_vec q)
  simpa [Fin.forall_fin_two, Int.natAbs_natCast, max_comm] using htuple

private lemma logHeight_vec_one_zero :
    Height.logHeight ![(1 : ℚ), 0] = 0 := by
  have hgcd : Finset.univ.gcd ![(1 : ℤ), 0] = 1 := by
    norm_num [Finset.univ_fin_two]
  have h :=
    Rat.logHeight_eq_max_abs_of_gcd_eq_one
      (x := ![(1 : ℤ), 0])
      hgcd
  simpa [Fin.forall_fin_two] using h

/-- Projective log-height transported to the `Option ℚ` chart. -/
lemma logHeight_ofOption (o : Option ℚ) :
    Projectivization.logHeight (ofOption o) = optionLogHeight o := by
  cases o with
  | none =>
      simp [ofOption, infinity, optionLogHeight,
        Projectivization.logHeight_mk, logHeight_vec_one_zero]
  | some q =>
      simp [ofOption, affine, optionLogHeight,
        Projectivization.logHeight_mk, Rat.logHeight_pair_self_one q]

/-- Projective log-height equals the chart height under `equivOption`. -/
lemma logHeight_eq_optionLogHeight (z : P1) :
    Projectivization.logHeight z = optionLogHeight (equivOption z) := by
  calc
    Projectivization.logHeight z
        = Projectivization.logHeight (ofOption (toOption z)) := by
            rw [ofOption_toOption]
    _ = optionLogHeight (toOption z) := logHeight_ofOption (toOption z)

end RatP1Northcott

open RatP1Northcott

/-- Northcott for logarithmic height on `ℙ¹(ℚ)`. -/
theorem rat_P1_logHeight_northcott :
    Northcott (Projectivization.logHeight
      (K := ℚ) (ι := Fin 2)) where
  finite_le B := by
    classical
    have hopt :
        {o : Option ℚ | optionLogHeight o ≤ B}.Finite :=
      Northcott.finite_le (h := optionLogHeight) B
    refine (hopt.image equivOption.symm).subset ?_
    intro z hz
    refine ⟨equivOption z, ?_, ?_⟩
    · simpa [RatP1Northcott.logHeight_eq_optionLogHeight z] using hz
    · simp

A couple of implementation notes matter.

First, this uses the Projectivization.lift API rather than choosing arbitrary representatives and proving chart formulas afterward; this is the right way to build ℙ¹(ℚ) ≃ Option ℚ. The equality criterion used under the hood is Projectivization.mk_eq_mk_iff', which says two nonzero vectors represent the same projective point iff one is a scalar multiple of the other.

Second, the rational finiteness step does not use coprimality for enumeration: it just injects every rational into the finite box of numerator/denominator pairs via Rat.num_div_den. Coprimality only enters the height computation through Mathlib’s rational height lemmas.
