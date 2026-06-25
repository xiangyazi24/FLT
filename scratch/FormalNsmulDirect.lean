import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution

namespace FormalNsmulDirect

variable {R : Type*} [CommRing R]

noncomputable def addF (F : MvPowerSeries (Fin 2) R) (f g : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst (fun i : Fin 2 => (![f, g] i : PowerSeries R)) F

theorem hasSubst_pair {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff (R := R) f = 0) (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    MvPowerSeries.HasSubst (fun i : Fin 2 => (![f, g] i : PowerSeries R)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> assumption)

private theorem coeff_one_pow_mul_pow_eq_zero {f g : PowerSeries R}
    (hf : PowerSeries.X ∣ f) (hg : PowerSeries.X ∣ g) {a b : ℕ} (hab : 2 ≤ a + b) :
    PowerSeries.coeff (R := R) 1 (f ^ a * g ^ b) = 0 := by
  obtain ⟨f', rfl⟩ := hf
  obtain ⟨g', rfl⟩ := hg
  have hdvd : (PowerSeries.X * f') ^ a * (PowerSeries.X * g') ^ b
      = PowerSeries.X ^ (a + b) * (f' ^ a * g' ^ b) := by
    rw [mul_pow, mul_pow, pow_add]; ring
  rw [hdvd, PowerSeries.coeff_X_pow_mul']; rw [if_neg]; omega

theorem addF_constantCoeff (F : MvPowerSeries (Fin 2) R)
    (hF : MvPowerSeries.constantCoeff (σ := Fin 2) F = 0)
    {f g : PowerSeries R} (hf : PowerSeries.constantCoeff (R := R) f = 0)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.constantCoeff (R := R) (addF F f g) = 0 := by
  simp only [PowerSeries.constantCoeff_eq, addF]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hf hg)
    (fun i => by fin_cases i <;> assumption) hF

theorem addF_coeff_one (F : MvPowerSeries (Fin 2) R)
    (hF : MvPowerSeries.constantCoeff (σ := Fin 2) F = 0)
    (hX : (MvPowerSeries.coeff (R := R) (Finsupp.single 0 1)) F = 1)
    (hY : (MvPowerSeries.coeff (R := R) (Finsupp.single 1 1)) F = 1)
    {f g : PowerSeries R} (hf : PowerSeries.constantCoeff (R := R) f = 0)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.coeff (R := R) 1 (addF F f g) =
      PowerSeries.coeff (R := R) 1 f + PowerSeries.coeff (R := R) 1 g := by
  have hfX : PowerSeries.X ∣ f := PowerSeries.X_dvd_iff.mpr hf
  have hgX : PowerSeries.X ∣ g := PowerSeries.X_dvd_iff.mpr hg
  have hcoe : (PowerSeries.coeff (R := R) 1) = MvPowerSeries.coeff (Finsupp.single () 1) := rfl
  rw [addF, hcoe, MvPowerSeries.coeff_subst (hasSubst_pair hf hg)]
  have hinner : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s e => (fun i : Fin 2 => (![f, g] i : PowerSeries R)) s ^ e) =
        f ^ (d 0) * g ^ (d 1) := by
    intro d; rw [Finsupp.prod_fintype]
    · rw [Fin.prod_univ_two]; simp
    · intro i; simp
  simp_rw [hinner]
  set T : (Fin 2 →₀ ℕ) → R := fun d =>
    MvPowerSeries.coeff d F •
      MvPowerSeries.coeff (Finsupp.single () (1 : ℕ)) (f ^ (d 0) * g ^ (d 1)) with hT
  have hval : ∀ d : Fin 2 →₀ ℕ, d ≠ Finsupp.single 0 1 → d ≠ Finsupp.single 1 1 →
      MvPowerSeries.coeff (Finsupp.single () (1 : ℕ)) (f ^ (d 0) * g ^ (d 1)) = 0 := by
    intro d hd0 hd1
    rcases Nat.lt_or_ge (d 0 + d 1) 2 with hlt | hge
    · have key0 : d 0 = 0 ∨ d 0 = 1 := by omega
      have key1 : d 1 = 0 ∨ d 1 = 1 := by omega
      rcases key0 with h0 | h0 <;> rcases key1 with h1 | h1
      · rw [h0, h1]; simp only [pow_zero, one_mul]
        have h1c : MvPowerSeries.coeff (Finsupp.single () (1 : ℕ)) (1 : PowerSeries R)
             = PowerSeries.coeff (R := R) 1 1 := rfl
        rw [h1c]; simp [PowerSeries.coeff_one]
      · exact absurd (by ext i; fin_cases i <;> simp [h0, h1]) hd1
      · exact absurd (by ext i; fin_cases i <;> simp [h0, h1]) hd0
      · omega
    · exact coeff_one_pow_mul_pow_eq_zero hfX hgX hge
  have hsupp : Function.support T ⊆
      ({Finsupp.single 0 1, Finsupp.single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    intro d hd
    simp only [Function.mem_support, hT] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    push_neg at hcon
    exact hd (by rw [hval d hcon.1 hcon.2, smul_zero])
  rw [finsum_eq_finsetSum_of_support_subset T hsupp]
  have hne : (Finsupp.single (0 : Fin 2) 1) ≠ (Finsupp.single (1 : Fin 2) 1) := by
    intro h; have := DFunLike.congr_fun h 0; simp [Finsupp.single_apply] at this
  rw [Finset.sum_pair hne, hT]
  simp only
  have e00 : (Finsupp.single (0 : Fin 2) 1) 0 = 1 := by simp
  have e01 : (Finsupp.single (0 : Fin 2) 1) 1 = 0 := by simp [Finsupp.single_apply]
  have e10 : (Finsupp.single (1 : Fin 2) 1) 0 = 0 := by simp [Finsupp.single_apply]
  have e11 : (Finsupp.single (1 : Fin 2) 1) 1 = 1 := by simp
  rw [e00, e01, e10, e11]
  simp only [pow_one, pow_zero, mul_one, one_mul]
  rw [hX, hY]
  simp only [one_smul]

noncomputable def formalNsmulF (F : MvPowerSeries (Fin 2) R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => addF F (formalNsmulF F n) PowerSeries.X

theorem formalNsmulF_constantCoeff (F : MvPowerSeries (Fin 2) R)
    (hF : MvPowerSeries.constantCoeff (σ := Fin 2) F = 0)
    (n : ℕ) : PowerSeries.constantCoeff (R := R) (formalNsmulF F n) = 0 := by
  induction n with
  | zero => simp [formalNsmulF]
  | succ n ih => exact addF_constantCoeff F hF ih (by simp)

theorem formalNsmulF_coeff_one (F : MvPowerSeries (Fin 2) R)
    (hF : MvPowerSeries.constantCoeff (σ := Fin 2) F = 0)
    (hX : (MvPowerSeries.coeff (R := R) (Finsupp.single 0 1)) F = 1)
    (hY : (MvPowerSeries.coeff (R := R) (Finsupp.single 1 1)) F = 1)
    (n : ℕ) : PowerSeries.coeff (R := R) 1 (formalNsmulF F n) = (n : R) := by
  induction n with
  | zero => simp [formalNsmulF]
  | succ n ih =>
      show PowerSeries.coeff (R := R) 1 (addF F (formalNsmulF F n) PowerSeries.X) = _
      rw [addF_coeff_one F hF hX hY (formalNsmulF_constantCoeff F hF n) (by simp),
        ih, PowerSeries.coeff_one_X, Nat.cast_succ]

end FormalNsmulDirect
