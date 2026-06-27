# Q1492 (dm2): coprime factorization of `5 * C^4`

## Status

I cannot run Lean in this connector-only workflow, so this should still be checked in the target tree.  The proof below is written to be pasteable Lean and uses the helper you said already exists:

```lean
theorem pos_fourth_of_coprime_mul_fourth {a b c : ℤ} (hab : Int.gcd a b = 1)
    (heq : a * b = c ^ 4) (ha : 0 < a) (hb : 0 < b) :
    ∃ α : ℤ, 0 < α ∧ a = α ^ 4
```

The main tactic is not to do explicit prime-exponent bookkeeping.  Instead, split on whether `5 ∣ F₁` or `5 ∣ F₂`, cancel the single `5`, and apply `pos_fourth_of_coprime_mul_fourth` twice.

## Lean code

```lean
import Mathlib

namespace Q1492

/-- Positive fourth powers are injective on positive integers. -/
private lemma eq_of_pos_fourth_eq {x y : ℤ} (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 4 = y ^ 4) : x = y := by
  have hsq : (x ^ 2) ^ 2 = (y ^ 2) ^ 2 := by
    calc
      (x ^ 2) ^ 2 = x ^ 4 := by ring
      _ = y ^ 4 := h
      _ = (y ^ 2) ^ 2 := by ring
  have hxy2 : x ^ 2 = y ^ 2 := by
    have hor := (Commute.all (x ^ 2) (y ^ 2)).sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rcases hor with hpos | hneg
    · exact hpos
    · exfalso
      have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero x (ne_of_gt hx)
      have hy2nonneg : 0 ≤ y ^ 2 := sq_nonneg y
      nlinarith
  have hxy := (Commute.all x y).sq_eq_sq_iff_eq_or_eq_neg.mp hxy2
  rcases hxy with hxy | hxyneg
  · exact hxy
  · exfalso
    nlinarith

private lemma gcd_eq_one_of_isCoprime {x y : ℤ} (h : IsCoprime x y) :
    Int.gcd x y = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp h

private lemma isCoprime_of_gcd_eq_one {x y : ℤ} (h : Int.gcd x y = 1) :
    IsCoprime x y :=
  Int.isCoprime_iff_gcd_eq_one.mpr h

/-- The branch where `5 ∣ F₂`. -/
private lemma coprime_factor_5_fourth_right
    {F₁ F₂ C G : ℤ}
    (hprod : F₁ * F₂ = 5 * C ^ 4)
    (hcop : Int.gcd F₁ F₂ = 1)
    (hF₁ : 0 < F₁) (hF₂ : 0 < F₂) (hC : 0 < C)
    (hF₂eq : F₂ = 5 * G) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ C = a * b ∧
      (F₁ = a ^ 4 ∧ F₂ = 5 * b ^ 4) := by
  have hG : 0 < G := by
    nlinarith

  have hprodFG : F₁ * G = C ^ 4 := by
    have hmul : (5 : ℤ) * (F₁ * G) = 5 * C ^ 4 := by
      calc
        (5 : ℤ) * (F₁ * G) = F₁ * (5 * G) := by ring
        _ = F₁ * F₂ := by rw [hF₂eq]
        _ = 5 * C ^ 4 := hprod
    exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hmul

  have hcopI : IsCoprime F₁ F₂ := isCoprime_of_gcd_eq_one hcop
  have hcopF₁5G : IsCoprime F₁ (5 * G) := by
    simpa [hF₂eq] using hcopI
  have hcopF₁G_I : IsCoprime F₁ G := hcopF₁5G.of_mul_right_right
  have hcopF₁G : Int.gcd F₁ G = 1 := gcd_eq_one_of_isCoprime hcopF₁G_I

  obtain ⟨a, ha_pos, hF₁a⟩ :=
    pos_fourth_of_coprime_mul_fourth hcopF₁G hprodFG hF₁ hG

  have hprodGF₁ : G * F₁ = C ^ 4 := by
    simpa [mul_comm] using hprodFG
  have hcopGF₁ : Int.gcd G F₁ = 1 := by
    exact gcd_eq_one_of_isCoprime hcopF₁G_I.symm

  obtain ⟨b, hb_pos, hGb⟩ :=
    pos_fourth_of_coprime_mul_fourth hcopGF₁ hprodGF₁ hG hF₁

  have hcop_ab_I : IsCoprime a b := by
    have hcop_pow : IsCoprime (a ^ 4) (b ^ 4) := by
      simpa [hF₁a, hGb] using hcopF₁G_I
    exact (IsCoprime.pow_iff (R := ℤ) (x := a) (y := b) (m := 4) (n := 4)
      (by norm_num) (by norm_num)).mp hcop_pow
  have hcop_ab : Int.gcd a b = 1 := gcd_eq_one_of_isCoprime hcop_ab_I

  have hab_pos : 0 < a * b := mul_pos ha_pos hb_pos
  have hCpow : C ^ 4 = (a * b) ^ 4 := by
    calc
      C ^ 4 = F₁ * G := hprodFG.symm
      _ = a ^ 4 * b ^ 4 := by rw [hF₁a, hGb]
      _ = (a * b) ^ 4 := by ring
  have hCeq : C = a * b := eq_of_pos_fourth_eq hC hab_pos hCpow

  refine ⟨a, b, ha_pos, hb_pos, hcop_ab, hCeq, ?_⟩
  constructor
  · exact hF₁a
  · calc
      F₂ = 5 * G := hF₂eq
      _ = 5 * b ^ 4 := by rw [hGb]

/-- The branch where `5 ∣ F₁`. -/
private lemma coprime_factor_5_fourth_left
    {F₁ F₂ C G : ℤ}
    (hprod : F₁ * F₂ = 5 * C ^ 4)
    (hcop : Int.gcd F₁ F₂ = 1)
    (hF₁ : 0 < F₁) (hF₂ : 0 < F₂) (hC : 0 < C)
    (hF₁eq : F₁ = 5 * G) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ C = a * b ∧
      (F₁ = 5 * a ^ 4 ∧ F₂ = b ^ 4) := by
  have hG : 0 < G := by
    nlinarith

  have hprodGF₂ : G * F₂ = C ^ 4 := by
    have hmul : (5 : ℤ) * (G * F₂) = 5 * C ^ 4 := by
      calc
        (5 : ℤ) * (G * F₂) = (5 * G) * F₂ := by ring
        _ = F₁ * F₂ := by rw [hF₁eq]
        _ = 5 * C ^ 4 := hprod
    exact mul_left_cancel₀ (show (5 : ℤ) ≠ 0 by norm_num) hmul

  have hcopI : IsCoprime F₁ F₂ := isCoprime_of_gcd_eq_one hcop
  have hcop5GF₂ : IsCoprime (5 * G) F₂ := by
    simpa [hF₁eq] using hcopI
  have hcopGF₂_I : IsCoprime G F₂ := hcop5GF₂.of_mul_left_right
  have hcopGF₂ : Int.gcd G F₂ = 1 := gcd_eq_one_of_isCoprime hcopGF₂_I

  obtain ⟨a, ha_pos, hGa⟩ :=
    pos_fourth_of_coprime_mul_fourth hcopGF₂ hprodGF₂ hG hF₂

  have hprodF₂G : F₂ * G = C ^ 4 := by
    simpa [mul_comm] using hprodGF₂
  have hcopF₂G : Int.gcd F₂ G = 1 := gcd_eq_one_of_isCoprime hcopGF₂_I.symm

  obtain ⟨b, hb_pos, hF₂b⟩ :=
    pos_fourth_of_coprime_mul_fourth hcopF₂G hprodF₂G hF₂ hG

  have hcop_ab_I : IsCoprime a b := by
    have hcop_pow : IsCoprime (a ^ 4) (b ^ 4) := by
      simpa [hGa, hF₂b] using hcopGF₂_I
    exact (IsCoprime.pow_iff (R := ℤ) (x := a) (y := b) (m := 4) (n := 4)
      (by norm_num) (by norm_num)).mp hcop_pow
  have hcop_ab : Int.gcd a b = 1 := gcd_eq_one_of_isCoprime hcop_ab_I

  have hab_pos : 0 < a * b := mul_pos ha_pos hb_pos
  have hCpow : C ^ 4 = (a * b) ^ 4 := by
    calc
      C ^ 4 = G * F₂ := hprodGF₂.symm
      _ = a ^ 4 * b ^ 4 := by rw [hGa, hF₂b]
      _ = (a * b) ^ 4 := by ring
  have hCeq : C = a * b := eq_of_pos_fourth_eq hC hab_pos hCpow

  refine ⟨a, b, ha_pos, hb_pos, hcop_ab, hCeq, ?_⟩
  constructor
  · calc
      F₁ = 5 * G := hF₁eq
      _ = 5 * a ^ 4 := by rw [hGa]
  · exact hF₂b

/-- Coprime factorization of `5·C⁴`: if `F₁·F₂ = 5·C⁴` with `gcd(F₁,F₂)=1`
and `F₁,F₂,C > 0`, then exactly one side carries the single factor `5`, and the
remaining coprime factors are fourth powers. -/
theorem coprime_factor_5_fourth {F₁ F₂ C : ℤ} (hprod : F₁ * F₂ = 5 * C ^ 4)
    (hcop : Int.gcd F₁ F₂ = 1) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂) (hC : 0 < C) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ Int.gcd a b = 1 ∧ C = a * b ∧
      ((F₁ = a ^ 4 ∧ F₂ = 5 * b ^ 4) ∨ (F₁ = 5 * a ^ 4 ∧ F₂ = b ^ 4)) := by
  have h5prod : (5 : ℤ) ∣ F₁ * F₂ := by
    rw [hprod]
    exact dvd_mul_right 5 (C ^ 4)

  have h5_or : (5 : ℤ) ∣ F₁ ∨ (5 : ℤ) ∣ F₂ :=
    Int.Prime.dvd_mul' (by norm_num : Nat.Prime 5) h5prod

  rcases h5_or with h5F₁ | h5F₂
  · rcases h5F₁ with ⟨G, hF₁eq⟩
    obtain ⟨a, b, ha, hb, hcopab, hCab, hcase⟩ :=
      coprime_factor_5_fourth_left hprod hcop hF₁ hF₂ hC hF₁eq
    exact ⟨a, b, ha, hb, hcopab, hCab, Or.inr hcase⟩
  · rcases h5F₂ with ⟨G, hF₂eq⟩
    obtain ⟨a, b, ha, hb, hcopab, hCab, hcase⟩ :=
      coprime_factor_5_fourth_right hprod hcop hF₁ hF₂ hC hF₂eq
    exact ⟨a, b, ha, hb, hcopab, hCab, Or.inl hcase⟩

end Q1492
```

## Likely API-sensitive lines

The two most likely lines to need tiny edits are:

```lean
exact hcopF₁5G.of_mul_right_right
exact hcop5GF₂.of_mul_left_right
```

These names are present in Mathlib’s coprime API. If projection notation does not resolve in your namespace, use the fully qualified forms:

```lean
exact IsCoprime.of_mul_right_right hcopF₁5G
exact IsCoprime.of_mul_left_right hcop5GF₂
```

The other key API is exactly:

```lean
Int.isCoprime_iff_gcd_eq_one
IsCoprime.pow_iff
Int.Prime.dvd_mul'
```

so you should not need to go through `Nat.Coprime` manually.
