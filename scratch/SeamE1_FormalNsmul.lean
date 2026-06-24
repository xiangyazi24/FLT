module

public import Mathlib.RingTheory.FormalGroup.Basic
public import Mathlib.RingTheory.PowerSeries.Order

/-! # SEAM1 / E1 — formal `[n]` linear coefficient: `[n]'(0) = n`

The genuine mathematical heart of the SEAM1 rootwise crux: over ANY one-dimensional formal group
law `F` over a commutative ring `R`, the formal multiplication-by-`n` series `[n](T)` has its
linear coefficient equal to `(n : R)` and zero constant coefficient, i.e. `[n](T) = nT + O(T²)`.

This is exactly the statement that "the tangent of `[n]` at the origin is scalar `n`", phrased
intrinsically on the formal group (NOT via the field-only point group). It is fully self-contained
(0 sorry, 0 custom axiom) and reusable: it depends only on the two linear-coefficient fields of
`FormalGroup` plus the power-series substitution coefficient formula.

The remaining SEAM1 gap (linking the Weierstrass `σ`-formal group's `[n]` to the division
polynomial `preΨ'`) is isolated elsewhere; this file lands the formal-group core. -/

@[expose] public section

open MvPowerSeries Finsupp PowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R]

/-- Formal addition of two one-variable series `f, g` via the bivariate group law `F`:
substitute `X₀ ↦ f`, `X₁ ↦ g`. -/
noncomputable def addSeries (F : FormalGroup R) (f g : PowerSeries R) : PowerSeries R :=
  MvPowerSeries.subst (fun i : Fin 2 => ![f, g] i) F.toPowerSeries

/-- The substitution map used by `addSeries` is admissible when both inputs have zero
constant coefficient. -/
theorem hasSubst_pair {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff (R := R) f = 0)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    MvPowerSeries.HasSubst (fun i : Fin 2 => ![f, g] i) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro s
  fin_cases s
  · exact hf
  · exact hg

/-- Constant coefficient of a formal addition vanishes (origin is the identity to lowest order). -/
theorem addSeries_constantCoeff (F : FormalGroup R) {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff (R := R) f = 0)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.constantCoeff (R := R) (F.addSeries f g) = 0 := by
  rw [PowerSeries.constantCoeff_eq, addSeries]
  apply MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_pair hf hg)
  · intro s
    fin_cases s
    · exact hf
    · exact hg
  · exact F.zero_constantCoeff

/-- Degree-1 coefficient of `f^a · g^b` vanishes when `a + b ≥ 2` and `X` divides both `f, g`. -/
theorem coeff_one_pow_mul_pow_eq_zero {f g : PowerSeries R}
    (hf : PowerSeries.X ∣ f) (hg : PowerSeries.X ∣ g) {a b : ℕ} (hab : 2 ≤ a + b) :
    PowerSeries.coeff (R := R) 1 (f ^ a * g ^ b) = 0 := by
  obtain ⟨f', rfl⟩ := hf
  obtain ⟨g', rfl⟩ := hg
  have hdvd : (PowerSeries.X * f') ^ a * (PowerSeries.X * g') ^ b
      = PowerSeries.X ^ (a + b) * (f' ^ a * g' ^ b) := by
    rw [mul_pow, mul_pow, pow_add]; ring
  rw [hdvd, PowerSeries.coeff_X_pow_mul']; rw [if_neg]; omega

/-- The linear coefficient of a formal addition is additive: this is where the two
`FormalGroup` linear-coefficient fields `lin_coeff_X`, `lin_coeff_Y` are consumed. -/
theorem addSeries_coeff_one (F : FormalGroup R) {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff (R := R) f = 0)
    (hg : PowerSeries.constantCoeff (R := R) g = 0) :
    PowerSeries.coeff (R := R) 1 (F.addSeries f g) =
      PowerSeries.coeff (R := R) 1 f + PowerSeries.coeff (R := R) 1 g := by
  have hfX : PowerSeries.X ∣ f := PowerSeries.X_dvd_iff.mpr hf
  have hgX : PowerSeries.X ∣ g := PowerSeries.X_dvd_iff.mpr hg
  have hcoe : (PowerSeries.coeff (R := R) 1) = MvPowerSeries.coeff (single () 1) := rfl
  rw [addSeries, hcoe, MvPowerSeries.coeff_subst (hasSubst_pair hf hg)]
  have hinner : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s e => (fun i : Fin 2 => ![f, g] i) s ^ e) = f ^ (d 0) * g ^ (d 1) := by
    intro d; rw [Finsupp.prod_fintype]
    · rw [Fin.prod_univ_two]; simp
    · intro i; simp
  simp_rw [hinner]
  set T : (Fin 2 →₀ ℕ) → R := fun d =>
    MvPowerSeries.coeff d F.toPowerSeries •
      MvPowerSeries.coeff (single () (1 : ℕ)) (f ^ (d 0) * g ^ (d 1)) with hT
  have hval : ∀ d : Fin 2 →₀ ℕ, d ≠ single 0 1 → d ≠ single 1 1 →
      MvPowerSeries.coeff (single () (1 : ℕ)) (f ^ (d 0) * g ^ (d 1)) = 0 := by
    intro d hd0 hd1
    rcases Nat.lt_or_ge (d 0 + d 1) 2 with hlt | hge
    · have key0 : d 0 = 0 ∨ d 0 = 1 := by omega
      have key1 : d 1 = 0 ∨ d 1 = 1 := by omega
      rcases key0 with h0 | h0 <;> rcases key1 with h1 | h1
      · rw [h0, h1]; simp only [pow_zero, one_mul]
        have h1c : MvPowerSeries.coeff (single () (1 : ℕ)) (1 : PowerSeries R)
             = PowerSeries.coeff (R := R) 1 1 := rfl
        rw [h1c]; simp [PowerSeries.coeff_one]
      · exact absurd (by ext i; fin_cases i <;> simp [h0, h1]) hd1
      · exact absurd (by ext i; fin_cases i <;> simp [h0, h1]) hd0
      · omega
    · exact coeff_one_pow_mul_pow_eq_zero hfX hgX hge
  have hsupp : Function.support T ⊆ ({single 0 1, single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    intro d hd
    simp only [Function.mem_support, hT] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    push_neg at hcon
    exact hd (by rw [hval d hcon.1 hcon.2, smul_zero])
  rw [finsum_eq_finsetSum_of_support_subset T hsupp]
  have hne : (single (0 : Fin 2) 1) ≠ (single (1 : Fin 2) 1) := by
    intro h; have := DFunLike.congr_fun h 0; simp [single_apply] at this
  rw [Finset.sum_pair hne, hT]
  simp only
  have e00 : (single (0 : Fin 2) 1) 0 = 1 := by simp
  have e01 : (single (0 : Fin 2) 1) 1 = 0 := by simp [single_apply]
  have e10 : (single (1 : Fin 2) 1) 0 = 0 := by simp [single_apply]
  have e11 : (single (1 : Fin 2) 1) 1 = 1 := by simp
  rw [e00, e01, e10, e11]
  simp only [pow_one, pow_zero, mul_one, one_mul]
  rw [F.lin_coeff_X, F.lin_coeff_Y]
  simp only [one_smul]

/-- Formal multiplication-by-`n` series `[n](T)`, defined by `[0] = 0`, `[n+1] = F(·, T)`. -/
noncomputable def formalNsmul (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => F.addSeries (F.formalNsmul n) PowerSeries.X

@[simp] lemma formalNsmul_zero (F : FormalGroup R) : F.formalNsmul 0 = 0 := rfl

@[simp] lemma formalNsmul_succ (F : FormalGroup R) (n : ℕ) :
    F.formalNsmul (n + 1) = F.addSeries (F.formalNsmul n) PowerSeries.X := rfl

/-- `[n](T)` has zero constant coefficient. -/
theorem formalNsmul_constantCoeff (F : FormalGroup R) (n : ℕ) :
    PowerSeries.constantCoeff (R := R) (F.formalNsmul n) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [formalNsmul_succ]
      exact addSeries_constantCoeff F ih (by simp)

/-- **`[n]'(0) = n`**: the linear coefficient of the formal `[n]` series is `(n : R)`.
This is the formal-group tangent-at-origin fact, the intrinsic version of
`TangentO.nsmul₁ n 1 = (n : K)`. -/
theorem formalNsmul_coeff_one (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff (R := R) 1 (F.formalNsmul n) = (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [formalNsmul_succ,
        addSeries_coeff_one F (formalNsmul_constantCoeff F n) (by simp),
        ih, PowerSeries.coeff_one_X, Nat.cast_succ]

end FormalGroup
