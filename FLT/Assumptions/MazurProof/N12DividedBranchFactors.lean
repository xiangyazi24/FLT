import FLT.Assumptions.MazurProof.N12QuarticEisenstein

/-!
# Divided N=12 Eisenstein square branch factor packages

This downstream file extracts the honest square-factor packages from the
divided-by-`3` square branch.  It deliberately stops before the final
unit/impossibility argument.
-/

namespace MazurProof.RationalPointsN12

/-- Divided branch factor package in the `m` even case. -/
def DividedSqBranchMEvenFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = a ^ 2 ∧
    m + n = 3 * b ^ 2 ∧
    n = c ^ 2 ∧
    2 * m - n = 3 * d ^ 2

/-- Divided branch factor package in the `m` odd case. -/
def DividedSqBranchMOddFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = 2 * a ^ 2 ∧
    m + n = 6 * b ^ 2 ∧
    n = c ^ 2 ∧
    2 * m - n = 3 * d ^ 2

/-- Honest divided-branch factorization by the parity of `m`. -/
def DividedSqBranchFactorizationStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
      (Even m ∧ DividedSqBranchMEvenFactors m n) ∨
      (Odd m ∧ DividedSqBranchMOddFactors m n)

/-- The visible divided-branch factors are positive. -/
theorem dividedSquareBranch_factor_pos {A N S m n : ℤ}
    (h : DividedSquareBranch A N S m n) :
    0 < m - n ∧ 0 < m + n ∧ 0 < n ∧ 0 < 2 * m - n := by
  rcases h with ⟨hnpos, hnltm, _hcop, _h3, _hA, _hN, _hS⟩
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · exact hnpos
  · nlinarith

private lemma odd_of_even_coprime_right {m n : ℤ}
    (hcop : IsCoprime m n) (hn : Even n) :
    Odd m := by
  rcases Int.even_or_odd m with hm | hm
  · exfalso
    rcases hcop with ⟨r, s, hrs⟩
    rcases hm with ⟨m0, hm0⟩
    rcases hn with ⟨n0, hn0⟩
    have htwo : (2 : ℤ) ∣ 1 := by
      refine ⟨r * m0 + s * n0, ?_⟩
      rw [← hrs, hm0, hn0]
      ring
    norm_num at htwo
  · exact hm

private lemma divided_branch_n_odd
    {A m n : ℤ} (hcop : IsCoprime m n)
    (hA : 3 * A ^ 2 = (m - n) * (m + n)) :
    Odd n := by
  rcases Int.even_or_odd n with hn | hn
  · exfalso
    have hm : Odd m := odd_of_even_coprime_right hcop hn
    rcases hm with ⟨m0, hm0⟩
    rcases hn with ⟨n0, hn0⟩
    rcases Int.even_or_odd A with hAe | hAo
    · rcases hAe with ⟨a0, ha0⟩
      rw [hm0, hn0, ha0] at hA
      ring_nf at hA
      omega
    · rcases hAo with ⟨a0, ha0⟩
      rw [hm0, hn0, ha0] at hA
      ring_nf at hA
      omega
  · exact hn

private lemma odd_sub_of_even_odd {m n : ℤ}
    (hm : Even m) (hn : Odd n) :
    Odd (m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a - b - 1, ?_⟩
  rw [ha, hb]
  ring

private lemma even_sub_of_odd_odd {m n : ℤ}
    (hm : Odd m) (hn : Odd n) :
    Even (m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  rw [ha, hb]
  ring

private lemma even_add_of_odd_odd {m n : ℤ}
    (hm : Odd m) (hn : Odd n) :
    Even (m + n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a + b + 1, ?_⟩
  rw [ha, hb]
  ring

private lemma isCoprime_two_of_dvd_odd {d x : ℤ}
    (hx : Odd x) (hdx : d ∣ x) :
    IsCoprime d (2 : ℤ) :=
  ((Int.isCoprime_two_right).mpr hx).of_isCoprime_of_dvd_left hdx

private lemma dvd_of_dvd_two_mul_of_coprime_two {d x : ℤ}
    (hd2 : IsCoprime d (2 : ℤ)) (h : d ∣ 2 * x) :
    d ∣ x :=
  hd2.dvd_of_dvd_mul_left h

private lemma isCoprime_of_dvd_right {x y z : ℤ}
    (hcop : IsCoprime x y) (hzy : z ∣ y) :
    IsCoprime x z := by
  apply IsRelPrime.isCoprime
  intro d hdx hdz
  exact hcop.isUnit_of_dvd' hdx (hdz.trans hzy)

private lemma isCoprime_m_sub_n_m_add_n_of_sub_odd
    {m n : ℤ} (hcop : IsCoprime m n) (hsub : Odd (m - n)) :
    IsCoprime (m - n) (m + n) := by
  apply IsRelPrime.isCoprime
  intro d hdsub hdadd
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd hsub hdsub
  have hsum : d ∣ (m - n) + (m + n) := dvd_add hdsub hdadd
  have hsum_eq : (m - n) + (m + n) = 2 * m := by ring
  have hdm : d ∣ m := by
    apply dvd_of_dvd_two_mul_of_coprime_two hd2
    rwa [← hsum_eq]
  have hdiff : d ∣ (m + n) - (m - n) := dvd_sub hdadd hdsub
  have hdiff_eq : (m + n) - (m - n) = 2 * n := by ring
  have hdn : d ∣ n := by
    apply dvd_of_dvd_two_mul_of_coprime_two hd2
    rwa [← hdiff_eq]
  exact hcop.isUnit_of_dvd' hdm hdn

private lemma isCoprime_n_two_mul_m_sub_n_of_odd_n
    {m n : ℤ} (hcop : IsCoprime m n) (hn : Odd n) :
    IsCoprime n (2 * m - n) := by
  apply IsRelPrime.isCoprime
  intro d hdn hd2mn
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd hn hdn
  have hsum : d ∣ n + (2 * m - n) := dvd_add hdn hd2mn
  have hsum_eq : n + (2 * m - n) = 2 * m := by ring
  have hdm : d ∣ m := by
    apply dvd_of_dvd_two_mul_of_coprime_two hd2
    rwa [← hsum_eq]
  exact hcop.isUnit_of_dvd' hdm hdn

private lemma isCoprime_halves_m_sub_m_add
    {m n x y : ℤ} (hcop : IsCoprime m n)
    (hx : m - n = 2 * x) (hy : m + n = 2 * y) :
    IsCoprime x y := by
  rcases hcop with ⟨r, s, hrs⟩
  use r - s, r + s
  have hm : m = x + y := by omega
  have hn : n = y - x := by omega
  calc
    (r - s) * x + (r + s) * y = r * (x + y) + s * (y - x) := by ring
    _ = r * m + s * n := by rw [hm, hn]
    _ = 1 := hrs

private lemma three_dvd_two_mul_sub_of_three_dvd_add {m n : ℤ}
    (h3 : (3 : ℤ) ∣ m + n) :
    (3 : ℤ) ∣ 2 * m - n := by
  rcases h3 with ⟨k, hk⟩
  refine ⟨2 * k - n, ?_⟩
  have hm : m = 3 * k - n := by omega
  rw [hm]
  ring

private lemma posSqOfCoprimeMulThreeSq_right
    {x y y0 z : ℤ}
    (hx : 0 < x) (hy0 : 0 < y0)
    (hcop : IsCoprime x y0)
    (hy : y = 3 * y0)
    (hz : 3 * z ^ 2 = x * y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = 3 * b ^ 2 := by
  have hz' : z ^ 2 = x * y0 := by
    rw [hy] at hz
    nlinarith
  rcases posSqOfCoprimeMulSq hx hy0 hcop hz' with
    ⟨a, b, ha, hb, hxa, hyb⟩
  exact ⟨a, b, ha, hb, hxa, by rw [hy, hyb]⟩

private lemma even_of_three_sq_eq_four_mul
    {A u v : ℤ} (h : 3 * A ^ 2 = (2 * u) * (2 * v)) :
    Even A := by
  rcases Int.even_or_odd A with hAe | hAo
  · exact hAe
  · exfalso
    rcases hAo with ⟨a0, ha0⟩
    rw [ha0] at h
    ring_nf at h
    omega

private lemma split_three_on_m_add
    {m n A : ℤ}
    (hcop : IsCoprime (m - n) (m + n))
    (h3 : (3 : ℤ) ∣ m + n)
    (hsub_pos : 0 < m - n)
    (hadd_pos : 0 < m + n)
    (hA : 3 * A ^ 2 = (m - n) * (m + n)) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧
      m - n = a ^ 2 ∧ m + n = 3 * b ^ 2 := by
  rcases h3 with ⟨y0, hy0⟩
  have hy0_pos : 0 < y0 := by nlinarith
  have hy0_dvd : y0 ∣ m + n := ⟨3, by rw [hy0]; ring⟩
  have hcop_y0 : IsCoprime (m - n) y0 :=
    isCoprime_of_dvd_right hcop hy0_dvd
  exact posSqOfCoprimeMulThreeSq_right
    hsub_pos hy0_pos hcop_y0 hy0 hA

private lemma split_three_on_two_mul_sub
    {m n N : ℤ}
    (hcop : IsCoprime n (2 * m - n))
    (h3 : (3 : ℤ) ∣ 2 * m - n)
    (hn_pos : 0 < n)
    (hsub_pos : 0 < 2 * m - n)
    (hN : 3 * N ^ 2 = n * (2 * m - n)) :
    ∃ c d : ℤ, 0 < c ∧ 0 < d ∧
      n = c ^ 2 ∧ 2 * m - n = 3 * d ^ 2 := by
  rcases h3 with ⟨y0, hy0⟩
  have hy0_pos : 0 < y0 := by nlinarith
  have hy0_dvd : y0 ∣ 2 * m - n := ⟨3, by rw [hy0]; ring⟩
  have hcop_y0 : IsCoprime n y0 :=
    isCoprime_of_dvd_right hcop hy0_dvd
  exact posSqOfCoprimeMulThreeSq_right
    hn_pos hy0_pos hcop_y0 hy0 hN

private lemma split_three_on_halves_m_add
    {m n A u v : ℤ}
    (hcop : IsCoprime u v)
    (hv3 : (3 : ℤ) ∣ v)
    (hu_pos : 0 < u)
    (hv_pos : 0 < v)
    (hu : m - n = 2 * u)
    (hv : m + n = 2 * v)
    (hA : 3 * A ^ 2 = (m - n) * (m + n)) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧
      m - n = 2 * a ^ 2 ∧ m + n = 6 * b ^ 2 := by
  have hA_even : Even A := by
    apply even_of_three_sq_eq_four_mul
    rwa [hu, hv] at hA
  rcases hA_even with ⟨A0, hA0⟩
  have hA0 : 3 * A0 ^ 2 = u * v := by
    rw [hu, hv, hA0] at hA
    ring_nf at hA ⊢
    nlinarith
  rcases hv3 with ⟨v0, hv0⟩
  have hv0_pos : 0 < v0 := by nlinarith
  have hv0_dvd : v0 ∣ v := ⟨3, by rw [hv0]; ring⟩
  have hcop_v0 : IsCoprime u v0 :=
    isCoprime_of_dvd_right hcop hv0_dvd
  rcases posSqOfCoprimeMulThreeSq_right
      hu_pos hv0_pos hcop_v0 hv0 hA0 with
    ⟨a, b, ha, hb, hua, hvb⟩
  exact ⟨a, b, ha, hb, by rw [hu, hua], by rw [hv, hvb]; ring⟩

theorem dividedSqBranchFactorizationStatement :
    DividedSqBranchFactorizationStatement := by
  intro A N S m n hbranch
  rcases hbranch with ⟨hnpos, hnltm, hcop, h3add, hA, hN, hS⟩
  have hbranch' : DividedSquareBranch A N S m n :=
    ⟨hnpos, hnltm, hcop, h3add, hA, hN, hS⟩
  rcases dividedSquareBranch_factor_pos hbranch' with
    ⟨h_m_sub_n_pos, h_m_add_n_pos, hn_pos, h_two_m_sub_n_pos⟩
  have hnOdd : Odd n := divided_branch_n_odd hcop hA
  have h3_two_sub : (3 : ℤ) ∣ 2 * m - n :=
    three_dvd_two_mul_sub_of_three_dvd_add h3add
  have hcopN : IsCoprime n (2 * m - n) :=
    isCoprime_n_two_mul_m_sub_n_of_odd_n hcop hnOdd
  rcases split_three_on_two_mul_sub hcopN h3_two_sub
      hn_pos h_two_m_sub_n_pos hN with
    ⟨c, d, hc_pos, hd_pos, hnc, h2md⟩
  rcases Int.even_or_odd m with hmEven | hmOdd
  · left
    refine ⟨hmEven, ?_⟩
    have hcopA : IsCoprime (m - n) (m + n) :=
      isCoprime_m_sub_n_m_add_n_of_sub_odd hcop
        (odd_sub_of_even_odd hmEven hnOdd)
    rcases split_three_on_m_add hcopA h3add h_m_sub_n_pos h_m_add_n_pos hA with
      ⟨a, b, ha_pos, hb_pos, hma, hmb⟩
    exact ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos,
      hma, hmb, hnc, h2md⟩
  · right
    refine ⟨hmOdd, ?_⟩
    have hmnEven : Even (m - n) := even_sub_of_odd_odd hmOdd hnOdd
    have hmpEven : Even (m + n) := even_add_of_odd_odd hmOdd hnOdd
    rcases hmnEven with ⟨u, hu'⟩
    rcases hmpEven with ⟨v, hv'⟩
    have hu : m - n = 2 * u := by rw [hu']; ring
    have hv : m + n = 2 * v := by rw [hv']; ring
    have hcopUV : IsCoprime u v :=
      isCoprime_halves_m_sub_m_add hcop hu hv
    have hu_pos : 0 < u := by nlinarith
    have hv_pos : 0 < v := by nlinarith
    have h3v : (3 : ℤ) ∣ v := by
      have h3_two_v : (3 : ℤ) ∣ 2 * v := by
        rcases h3add with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        omega
      exact dvd_of_dvd_two_mul_of_coprime_two (by norm_num : IsCoprime (3 : ℤ) (2 : ℤ))
        h3_two_v
    rcases split_three_on_halves_m_add hcopUV h3v hu_pos hv_pos
        hu hv hA with
      ⟨a, b, ha_pos, hb_pos, hma, hmb⟩
    exact ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos,
      hma, hmb, hnc, h2md⟩

theorem dividedMEvenFactors_AP_identities
    {m n a b c d : ℤ}
    (hma : m - n = a ^ 2)
    (hmb : m + n = 3 * b ^ 2)
    (hnc : n = c ^ 2)
    (h2md : 2 * m - n = 3 * d ^ 2) :
    c ^ 2 + d ^ 2 = 2 * b ^ 2 ∧
      b ^ 2 + a ^ 2 = 2 * d ^ 2 := by
  constructor <;> nlinarith

theorem dividedMOddFactors_core_identities
    {m n a b c d : ℤ}
    (hma : m - n = 2 * a ^ 2)
    (hmb : m + n = 6 * b ^ 2)
    (hnc : n = c ^ 2)
    (h2md : 2 * m - n = 3 * d ^ 2) :
    a ^ 2 + c ^ 2 = 3 * b ^ 2 ∧
      4 * a ^ 2 + c ^ 2 = 3 * d ^ 2 := by
  constructor <;> nlinarith

end MazurProof.RationalPointsN12
