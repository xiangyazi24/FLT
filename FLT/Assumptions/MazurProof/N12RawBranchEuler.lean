import FLT.Assumptions.MazurProof.N12QuarticEisenstein
import FLT.Assumptions.MazurProof.N12FourSquaresAP

/-!
# Raw N=12 Eisenstein square branch to Euler square-pair contradiction

This downstream bridge keeps `N12QuarticEisenstein` independent from the
four-square AP/Euler descent development.  The raw branch factor packages are
converted into the already-checked `EulerSquarePair` shape, and the checked
Euler-pair descent rules out such a pair by a minimal-product argument.
-/

namespace MazurProof.RationalPointsN12

private lemma int_natAbs_lt_natAbs_of_pos_lt {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b) (h : a < b) :
    a.natAbs < b.natAbs := by
  have haAbs : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg (le_of_lt ha)
  have hbAbs : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg (le_of_lt hb)
  have hcast : (a.natAbs : ℤ) < (b.natAbs : ℤ) := by
    simpa [haAbs, hbAbs] using h
  exact_mod_cast hcast

private lemma eulerSquarePair_product_pos (E : EulerSquarePair) :
    0 < E.A * E.D :=
  mul_pos E.hApos E.hDpos

/-- A strict descent on the positive Euler product rules out Euler square
pairs. -/
theorem no_eulerSquarePair_of_descent
    (hdesc : EulerSquarePairDescent) :
    ¬ Nonempty EulerSquarePair := by
  intro hne
  classical
  let P : ℕ → Prop := fun k => ∃ E : EulerSquarePair, (E.A * E.D).natAbs = k
  have hP : ∃ k, P k := by
    rcases hne with ⟨E⟩
    exact ⟨(E.A * E.D).natAbs, E, rfl⟩
  let k0 := Nat.find hP
  have hk0 : P k0 := Nat.find_spec hP
  rcases hk0 with ⟨E, hE⟩
  rcases hdesc E with ⟨F, hFE⟩
  have hposF : 0 < F.A * F.D := eulerSquarePair_product_pos F
  have hposE : 0 < E.A * E.D := eulerSquarePair_product_pos E
  have hltAbs : (F.A * F.D).natAbs < (E.A * E.D).natAbs :=
    int_natAbs_lt_natAbs_of_pos_lt hposF hposE hFE
  have hF : P (F.A * F.D).natAbs := ⟨F, rfl⟩
  have hmin : k0 ≤ (F.A * F.D).natAbs :=
    Nat.find_min' hP hF
  have hltFind : (F.A * F.D).natAbs < k0 := by
    simpa [hE] using hltAbs
  exact (not_lt_of_ge hmin) hltFind

private lemma odd_sub_even_int {m n : ℤ}
    (hm : Odd m) (hn : Even n) :
    Odd (m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  rw [ha, hb]
  ring

private lemma sq_eq_four_mul_of_even {n : ℤ} (hn : Even n) :
    ∃ k : ℤ, n ^ 2 = 4 * k := by
  rcases hn with ⟨t, rfl⟩
  refine ⟨t ^ 2, ?_⟩
  ring

private lemma sq_eq_eight_mul_add_one_of_odd {n : ℤ} (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  rcases Int.two_dvd_mul_add_one t with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    (2 * t + 1) ^ 2 = 4 * (t * (t + 1)) + 1 := by ring
    _ = 4 * (2 * u) + 1 := by rw [hu]
    _ = 8 * u + 1 := by ring

private lemma sq_eq_eight_mul_add_four_of_two_mul_odd
    {n k : ℤ} (hn : n = 2 * k) (hk : Odd k) :
    ∃ q : ℤ, n ^ 2 = 8 * q + 4 := by
  rcases hk with ⟨t, ht⟩
  refine ⟨2 * t ^ 2 + 2 * t, ?_⟩
  rw [hn, ht]
  ring

private lemma four_dvd_of_odd_sq_add_sq_eq_sq {x y z : ℤ}
    (hx : Odd x) (h : y ^ 2 = x ^ 2 + z ^ 2) :
    (4 : ℤ) ∣ z := by
  rcases Int.even_or_odd z with hzEven | hzOdd
  · rcases hzEven with ⟨k, hk⟩
    rcases Int.even_or_odd k with hkEven | hkOdd
    · rcases hkEven with ⟨l, hl⟩
      refine ⟨l, ?_⟩
      rw [hk, hl]
      ring
    · exfalso
      rcases sq_eq_eight_mul_add_one_of_odd hx with ⟨X, hX⟩
      have hk2 : z = 2 * k := by
        rw [hk]
        ring
      rcases sq_eq_eight_mul_add_four_of_two_mul_odd hk2 hkOdd with ⟨Z, hZ⟩
      rcases Int.even_or_odd y with hyEven | hyOdd
      · rcases hyEven with ⟨v, hv⟩
        rcases sq_eq_four_mul_of_even ⟨v, hv⟩ with ⟨Y, hY⟩
        rw [hY, hX, hZ] at h
        omega
      · rcases hyOdd with ⟨v, hv⟩
        rcases sq_eq_eight_mul_add_one_of_odd ⟨v, hv⟩ with ⟨Y, hY⟩
        rw [hY, hX, hZ] at h
        omega
  · exfalso
    rcases sq_eq_eight_mul_add_one_of_odd hx with ⟨X, hX⟩
    rcases sq_eq_eight_mul_add_one_of_odd hzOdd with ⟨Z, hZ⟩
    have hYcases :
        (∃ Y : ℤ, y ^ 2 = 4 * Y) ∨
        (∃ Y : ℤ, y ^ 2 = 8 * Y + 1) := by
      rcases Int.even_or_odd y with hyEven | hyOdd
      · left
        exact sq_eq_four_mul_of_even hyEven
      · right
        exact sq_eq_eight_mul_add_one_of_odd hyOdd
    rcases hYcases with hYeven | hYodd
    · rcases hYeven with ⟨Y, hY⟩
      rw [hY, hX, hZ] at h
      omega
    · rcases hYodd with ⟨Y, hY⟩
      rw [hY, hX, hZ] at h
      omega

private lemma isCoprime_factor_roots_even
    {m n a c : ℤ}
    (hcop : IsCoprime m n)
    (hma : m - n = a ^ 2)
    (hnc : n = 2 * c ^ 2) :
    IsCoprime c a := by
  apply IsRelPrime.isCoprime
  intro t htc hta
  have htc2 : t ∣ c ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left htc c
  have htn : t ∣ n := by
    rw [hnc]
    exact dvd_mul_of_dvd_right htc2 2
  have hta2 : t ∣ a ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hta a
  have htmn : t ∣ m - n := by
    rwa [hma]
  have htm : t ∣ m := by
    have hsum : t ∣ (m - n) + n := dvd_add htmn htn
    simpa using hsum
  exact hcop.isUnit_of_dvd' htm htn

private lemma isCoprime_factor_roots_odd
    {m n a c : ℤ}
    (hcop : IsCoprime m n)
    (hma : m - n = 2 * a ^ 2)
    (hnc : n = c ^ 2) :
    IsCoprime a c := by
  apply IsRelPrime.isCoprime
  intro t hta htc
  have hta2 : t ∣ a ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left hta a
  have htmn : t ∣ m - n := by
    rw [hma]
    exact dvd_mul_of_dvd_right hta2 2
  have htc2 : t ∣ c ^ 2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left htc c
  have htn : t ∣ n := by
    rwa [hnc]
  have htm : t ∣ m := by
    have hsum : t ∣ (m - n) + n := dvd_add htmn htn
    simpa using hsum
  exact hcop.isUnit_of_dvd' htm htn

private theorem rawEvenFactors_core_identities
    {m n a b c r : ℤ}
    (hma : m - n = a ^ 2)
    (hmb : m + n = b ^ 2)
    (hnc : n = 2 * c ^ 2)
    (h2mr : 2 * m - n = 2 * r ^ 2) :
    m = c ^ 2 + r ^ 2 ∧
      a ^ 2 = r ^ 2 - c ^ 2 ∧
      b ^ 2 = a ^ 2 + 4 * c ^ 2 ∧
      r ^ 2 = a ^ 2 + c ^ 2 := by
  have hm : m = c ^ 2 + r ^ 2 := by
    nlinarith
  refine ⟨hm, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

private theorem rawOddFactors_core_identities
    {m n a b c r : ℤ}
    (hma : m - n = 2 * a ^ 2)
    (hmb : m + n = 2 * b ^ 2)
    (hnc : n = c ^ 2)
    (h2mr : 2 * m - n = r ^ 2) :
    m = a ^ 2 + b ^ 2 ∧
      b ^ 2 = a ^ 2 + c ^ 2 ∧
      r ^ 2 = 4 * a ^ 2 + c ^ 2 := by
  have hm : m = a ^ 2 + b ^ 2 := by
    nlinarith
  refine ⟨hm, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem eulerSquarePair_of_rawSqBranchEvenFactors
    {A N S m n : ℤ}
    (hbranch : EisensteinSqBranch A N S m n)
    (hnEven : Even n)
    (hfac : RawSqBranchEvenFactors m n) :
    Nonempty EulerSquarePair := by
  rcases hbranch with ⟨_hnpos, _hnltm, hcop, _hA, _hN, _hS⟩
  rcases hfac with
    ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos, hma, hmb, hnc, h2md⟩
  rcases rawEvenFactors_core_identities hma hmb hnc h2md with
    ⟨_hm, _ha2, hb_sq, hd_sq⟩
  have hbranch' : EisensteinSqBranch A N S m n :=
    ⟨_hnpos, _hnltm, hcop, _hA, _hN, _hS⟩
  have hmOdd : Odd m := rawSqBranchMParityStatement hbranch'
  have hmnOdd : Odd (m - n) := odd_sub_even_int hmOdd hnEven
  have haSqOdd : Odd (a ^ 2) := by
    simpa [hma] using hmnOdd
  have haOdd : Odd a :=
    (Int.odd_pow' (m := a) (n := 2) (by norm_num)).mp haSqOdd
  have h4c : (4 : ℤ) ∣ c :=
    four_dvd_of_odd_sq_add_sq_eq_sq haOdd hd_sq
  rcases h4c with ⟨k, hc4⟩
  have hk_pos : 0 < k := by nlinarith
  have hc_as_two_A : c = 2 * (2 * k) := by
    rw [hc4]
    ring
  have hca : IsCoprime c a :=
    isCoprime_factor_roots_even hcop hma hnc
  have hADcop : IsCoprime (2 * k) a := by
    have htwoA : IsCoprime (2 * (2 * k)) a := by
      simpa [← hc_as_two_A] using hca
    exact htwoA.of_mul_left_right
  refine ⟨{
    A := 2 * k
    D := a
    B := b
    C := d
    hApos := by nlinarith
    hDpos := ha_pos
    hDodd := haOdd
    hAeven := ⟨k, by ring⟩
    hADcop := hADcop
    hBpos := hb_pos
    hCpos := hd_pos
    hB := ?_
    hC := ?_ }⟩
  · calc
      b ^ 2 = a ^ 2 + 4 * c ^ 2 := hb_sq
      _ = 16 * (2 * k) ^ 2 + a ^ 2 := by
        rw [hc4]
        ring
  · calc
      d ^ 2 = a ^ 2 + c ^ 2 := hd_sq
      _ = 4 * (2 * k) ^ 2 + a ^ 2 := by
        rw [hc4]
        ring

theorem eulerSquarePair_of_rawSqBranchOddFactors
    {A N S m n : ℤ}
    (hbranch : EisensteinSqBranch A N S m n)
    (hnOdd : Odd n)
    (hfac : RawSqBranchOddFactors m n) :
    Nonempty EulerSquarePair := by
  rcases hbranch with ⟨_hnpos, _hnltm, hcop, _hA, _hN, _hS⟩
  rcases hfac with
    ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos, hma, hmb, hnc, h2md⟩
  rcases rawOddFactors_core_identities hma hmb hnc h2md with
    ⟨_hm, hb_sq, hd_sq⟩
  have hcSqOdd : Odd (c ^ 2) := by
    simpa [hnc] using hnOdd
  have hcOdd : Odd c :=
    (Int.odd_pow' (m := c) (n := 2) (by norm_num)).mp hcSqOdd
  have h4a : (4 : ℤ) ∣ a :=
    four_dvd_of_odd_sq_add_sq_eq_sq hcOdd (by
      rw [hb_sq]
      ring)
  rcases h4a with ⟨k, ha4⟩
  have hk_pos : 0 < k := by nlinarith
  have ha_as_two_A : a = 2 * (2 * k) := by
    rw [ha4]
    ring
  have hac : IsCoprime a c :=
    isCoprime_factor_roots_odd hcop hma hnc
  have hADcop : IsCoprime (2 * k) c := by
    have htwoA : IsCoprime (2 * (2 * k)) c := by
      simpa [← ha_as_two_A] using hac
    exact htwoA.of_mul_left_right
  refine ⟨{
    A := 2 * k
    D := c
    B := d
    C := b
    hApos := by nlinarith
    hDpos := hc_pos
    hDodd := hcOdd
    hAeven := ⟨k, by ring⟩
    hADcop := hADcop
    hBpos := hd_pos
    hCpos := hb_pos
    hB := ?_
    hC := ?_ }⟩
  · calc
      d ^ 2 = 4 * a ^ 2 + c ^ 2 := hd_sq
      _ = 16 * (2 * k) ^ 2 + c ^ 2 := by
        rw [ha4]
        ring
  · calc
      b ^ 2 = a ^ 2 + c ^ 2 := hb_sq
      _ = 4 * (2 * k) ^ 2 + c ^ 2 := by
        rw [ha4]
        ring

theorem rawSqBranchDescentFromFactorsStatement :
    RawSqBranchDescentFromFactorsStatement := by
  intro A N S m n hbranch hcases
  have hno : ¬ Nonempty EulerSquarePair :=
    no_eulerSquarePair_of_descent eulerSquarePairDescent
  rcases hcases with hEven | hOdd
  · exact hno (eulerSquarePair_of_rawSqBranchEvenFactors hbranch hEven.1 hEven.2)
  · exact hno (eulerSquarePair_of_rawSqBranchOddFactors hbranch hOdd.1 hOdd.2)

/-- Since the checked raw factorization theorem produces one of the impossible
factor packages, the raw branch is impossible, and hence implies the older
descent interface by contradiction. -/
theorem descentFromBranchUnordered_of_rawSqBranchFactorization :
    DescentFromBranchUnorderedStatement := by
  intro A N S m n _hbad hbranch
  exact False.elim
    (rawSqBranchDescentFromFactorsStatement hbranch
      (rawSqBranchFactorizationStatement hbranch))

theorem rawSqBranchNonunitDescendsStatement_of_rawSqBranchFactorization :
    RawSqBranchNonunitDescendsStatement := by
  intro A N S m n _hbad _hunit hbranch
  exact False.elim
    (rawSqBranchDescentFromFactorsStatement hbranch
      (rawSqBranchFactorizationStatement hbranch))

end MazurProof.RationalPointsN12
