import Mathlib
import scratch.FermatFourthDifferenceN16

set_option autoImplicit false

namespace MazurProof.CyclicExclusion16

def CoprimeRectangle (r s m n : ℤ) : Prop :=
  ∃ α β γ δ : ℤ,
    r = α * β ∧ s = γ * δ ∧ m = α * γ ∧ n = β * δ ∧
      IsCoprime α δ ∧ IsCoprime β γ

lemma coprime_rectangle
    {r s m n : ℤ}
    (hrs : IsCoprime r s)
    (hr0 : r ≠ 0)
    (hm0 : m ≠ 0)
    (hprod : r * s = m * n) :
    CoprimeRectangle r s m n := by
  have hg0 : Int.gcd r m ≠ 0 := by
    intro hg
    have hzero := Int.gcd_eq_zero_iff.mp hg
    exact hr0 hzero.1
  have hgpos : 0 < Int.gcd r m := Nat.pos_of_ne_zero hg0
  obtain ⟨β, γ, hβγgcd, hr, hm⟩ := Int.exists_gcd_one hgpos
  let α : ℤ := Int.gcd r m
  have hα0 : α ≠ 0 := by
    dsimp [α]
    exact_mod_cast hg0
  have hr' : r = α * β := by
    calc
      r = β * (Int.gcd r m : ℤ) := hr
      _ = α * β := by dsimp [α]; ring
  have hm' : m = α * γ := by
    calc
      m = γ * (Int.gcd r m : ℤ) := hm
      _ = α * γ := by dsimp [α]; ring
  have hβ0 : β ≠ 0 := by
    intro hβ
    apply hr0
    rw [hr', hβ]
    ring
  have hγ0 : γ ≠ 0 := by
    intro hγ
    apply hm0
    rw [hm', hγ]
    ring
  have hβsγn : β * s = γ * n := by
    apply (mul_left_inj' hα0).mp
    calc
      (β * s) * α = r * s := by rw [hr']; ring
      _ = m * n := hprod
      _ = (γ * n) * α := by rw [hm']; ring
  have hβdvdn : β ∣ n := by
    apply (Int.isCoprime_iff_gcd_eq_one.mpr hβγgcd).dvd_of_dvd_mul_right
    refine ⟨s, ?_⟩
    calc
      n * γ = γ * n := by ring
      _ = β * s := hβsγn.symm
  have hγdvds : γ ∣ s := by
    apply (Int.isCoprime_iff_gcd_eq_one.mpr hβγgcd).symm.dvd_of_dvd_mul_right
    refine ⟨n, ?_⟩
    calc
      s * β = β * s := by ring
      _ = γ * n := hβsγn
  obtain ⟨δ, hn'⟩ := hβdvdn
  obtain ⟨ε, hs'⟩ := hγdvds
  have hεδ : ε = δ := by
    apply (mul_left_inj' (mul_ne_zero hβ0 hγ0)).mp
    calc
      ε * (β * γ) = β * s := by rw [hs']; ring
      _ = γ * n := hβsγn
      _ = δ * (β * γ) := by rw [hn']; ring
  subst ε
  have hαδ : IsCoprime α δ := by
    have hp : IsCoprime (α * β) (γ * δ) := by
      simpa [hr', hs'] using hrs
    exact (hp.of_mul_left_left).of_mul_right_right
  exact ⟨α, β, γ, δ, hr', hs', hm', hn', hαδ,
    Int.isCoprime_iff_gcd_eq_one.mpr hβγgcd⟩

lemma odd_sum_opposite {r s : ℤ} (hodd : Odd (r + s)) :
    (Even r ∧ Odd s) ∨ (Odd r ∧ Even s) := by
  rcases Int.even_or_odd r with hre | hro
  · left
    refine ⟨hre, ?_⟩
    by_contra hso
    have hse : Even s := Int.not_odd_iff_even.mp hso
    have he : Even (r + s) := hre.add hse
    exact (Int.not_even_iff_odd.mpr hodd) he
  · right
    refine ⟨hro, ?_⟩
    by_contra hse
    have hso : Odd s := Int.not_even_iff_odd.mp hse
    have he : Even (r + s) := hro.add_odd hso
    exact (Int.not_even_iff_odd.mpr hodd) he

lemma square_sum_odd_of_odd_sum {r s : ℤ} (hodd : Odd (r + s)) :
    Odd (r ^ 2 + s ^ 2) := by
  rcases odd_sum_opposite hodd with ⟨hre, hso⟩ | ⟨hro, hse⟩
  · exact (hre.pow_of_ne_zero (by decide)).add_odd hso.pow
  · exact hro.pow.add_even (hse.pow_of_ne_zero (by decide))

lemma coprime_square_sum_twice_product {r s : ℤ}
    (hrs : IsCoprime r s) (hodd : Odd (r + s)) :
    IsCoprime (r ^ 2 + s ^ 2) (2 * r * s) := by
  have hXodd : Odd (r ^ 2 + s ^ 2) := square_sum_odd_of_odd_sum hodd
  have hX2 : IsCoprime (r ^ 2 + s ^ 2) 2 :=
    Int.isCoprime_two_right.mpr hXodd
  have hXrs : IsCoprime (r ^ 2 + s ^ 2) (r * s) :=
    Int.isCoprime_of_sq_sum' hrs
  have hcp := hX2.mul_right hXrs
  convert hcp using 1
  ring

lemma fourth_difference_from_rectangle
    {r s m n : ℤ}
    (hrs : IsCoprime r s)
    (hr0 : r ≠ 0)
    (hs0 : s ≠ 0)
    (hm0 : m ≠ 0)
    (hprod : r * s = m * n)
    (hsum : r ^ 2 + s ^ 2 = m ^ 2 - n ^ 2) : False := by
  rcases coprime_rectangle hrs hr0 hm0 hprod with
    ⟨α, β, γ, δ, hr, hs, hm, hn, hαδ, hβγ⟩
  have hα0 : α ≠ 0 := by
    intro hα
    apply hr0
    rw [hr, hα]
    ring
  have hδ0 : δ ≠ 0 := by
    intro hδ
    apply hs0
    rw [hs, hδ]
    ring
  have hβ0 : β ≠ 0 := by
    intro hβ
    apply hr0
    rw [hr, hβ]
    ring
  have hγ0 : γ ≠ 0 := by
    intro hγ
    apply hm0
    rw [hm, hγ]
    ring
  have hkey : α ^ 2 * (γ ^ 2 - β ^ 2) =
      δ ^ 2 * (γ ^ 2 + β ^ 2) := by
    rw [hr, hs, hm, hn] at hsum
    nlinarith [hsum]
  have hpowcp : IsCoprime (α ^ 2) (δ ^ 2) := hαδ.pow
  have hδdvd : δ ^ 2 ∣ γ ^ 2 - β ^ 2 := by
    apply hpowcp.symm.dvd_of_dvd_mul_right
    refine ⟨γ ^ 2 + β ^ 2, ?_⟩
    calc
      (γ ^ 2 - β ^ 2) * α ^ 2 = α ^ 2 * (γ ^ 2 - β ^ 2) := by ring
      _ = δ ^ 2 * (γ ^ 2 + β ^ 2) := hkey
  have hαdvd : α ^ 2 ∣ γ ^ 2 + β ^ 2 := by
    apply hpowcp.dvd_of_dvd_mul_right
    refine ⟨γ ^ 2 - β ^ 2, ?_⟩
    calc
      (γ ^ 2 + β ^ 2) * δ ^ 2 = δ ^ 2 * (γ ^ 2 + β ^ 2) := by ring
      _ = α ^ 2 * (γ ^ 2 - β ^ 2) := hkey.symm
  obtain ⟨h₁, hminus⟩ := hδdvd
  obtain ⟨h₂, hplus⟩ := hαdvd
  have hh : h₁ = h₂ := by
    apply (mul_left_inj'
      (mul_ne_zero (pow_ne_zero 2 hα0) (pow_ne_zero 2 hδ0))).mp
    calc
      h₁ * (α ^ 2 * δ ^ 2) = α ^ 2 * (γ ^ 2 - β ^ 2) := by rw [hminus]; ring
      _ = δ ^ 2 * (γ ^ 2 + β ^ 2) := hkey
      _ = h₂ * (α ^ 2 * δ ^ 2) := by rw [hplus]; ring
  subst h₂
  have hdiff : (α * δ * h₁) ^ 2 = γ ^ 4 - β ^ 4 := by
    calc
      (α * δ * h₁) ^ 2 = (δ ^ 2 * h₁) * (α ^ 2 * h₁) := by ring
      _ = (γ ^ 2 - β ^ 2) * (γ ^ 2 + β ^ 2) := by rw [hminus, hplus]
      _ = γ ^ 4 - β ^ 4 := by ring
  exact no_coprime_fourth_difference
    { X := γ
      Y := β
      Z := α * δ * h₁
      hXY := hβγ.symm
      hX := hγ0
      hY := hβ0
      hEq := hdiff }

/-- Explicit quartic-mean descent. -/
theorem quarticMean_explicit {a b c : ℤ}
    (hab : IsCoprime a b) (ha : Odd a) (hb : Odd b)
    (h : a ^ 4 + b ^ 4 = 2 * c ^ 2) : a ^ 2 = b ^ 2 := by
  rcases ha with ⟨p, hp⟩
  rcases hb with ⟨q, hq⟩
  let r : ℤ := p + q + 1
  let s : ℤ := p - q
  have ha_rs : a = r + s := by
    dsimp [r, s]
    rw [hp]
    ring
  have hb_rs : b = r - s := by
    dsimp [r, s]
    rw [hq]
    ring
  by_contra habsq
  have hr0 : r ≠ 0 := by
    intro hr
    apply habsq
    rw [ha_rs, hb_rs, hr]
    ring
  have hs0 : s ≠ 0 := by
    intro hs
    apply habsq
    rw [ha_rs, hb_rs, hs]
    ring
  have hrs : IsCoprime r s := by
    rcases hab with ⟨u, v, huv⟩
    refine ⟨u + v, u - v, ?_⟩
    rw [ha_rs, hb_rs] at huv
    nlinarith [huv]
  let X : ℤ := r ^ 2 + s ^ 2
  let Y : ℤ := 2 * r * s
  have htrip : PythagoreanTriple X Y c := by
    unfold PythagoreanTriple
    dsimp [X, Y]
    rw [ha_rs, hb_rs] at h
    nlinarith [h]
  have hXYcp : IsCoprime X Y := by
    dsimp [X, Y]
    apply coprime_square_sum_twice_product hrs
    rw [← ha_rs]
    exact ⟨p, hp⟩
  obtain ⟨m, n, hmnform, _hc, hmngcd, _hmnparity⟩ :=
    PythagoreanTriple.coprime_classification.mp
      ⟨htrip, Int.isCoprime_iff_gcd_eq_one.mp hXYcp⟩
  have hXodd : Odd X := by
    dsimp [X]
    apply square_sum_odd_of_odd_sum
    rw [← ha_rs]
    exact ⟨p, hp⟩
  have hform : X = m ^ 2 - n ^ 2 ∧ Y = 2 * m * n := by
    rcases hmnform with hfirst | hsecond
    · exact hfirst
    · exfalso
      have hXeven : Even X := by
        refine ⟨m * n, ?_⟩
        rw [hsecond.1]
        ring
      exact (Int.not_even_iff_odd.mpr hXodd) hXeven
  have hrs_mn : r * s = m * n := by
    dsimp [Y] at hform
    nlinarith [hform.2]
  have hmn0 : m * n ≠ 0 := by
    rw [← hrs_mn]
    exact mul_ne_zero hr0 hs0
  have hm0 : m ≠ 0 := left_ne_zero_of_mul hmn0
  have hsum : r ^ 2 + s ^ 2 = m ^ 2 - n ^ 2 := by
    simpa [X] using hform.1
  exact fourth_difference_from_rectangle hrs hr0 hs0 hm0 hrs_mn hsum

end MazurProof.CyclicExclusion16
