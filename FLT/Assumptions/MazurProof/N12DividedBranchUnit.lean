import FLT.Assumptions.MazurProof.N12DividedBranchFactors
import FLT.Assumptions.MazurProof.N12FourSquaresAP

/-!
# Divided N=12 branch collapses to the unit case

The divided-by-`3` square branch does not produce a new descent object.  After
the honest factorization, the `m` even branch is a four-square AP and the `m`
odd branch is impossible modulo `4`.
-/

namespace MazurProof.RationalPointsN12

def DividedSquareBranchUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    A = 1 ∧ N = 1 ∧ S = 1

def DividedMEvenFactorsUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    Even m →
    DividedSqBranchMEvenFactors m n →
    A = 1 ∧ N = 1 ∧ S = 1

def DividedMOddFactorsImpossibleStatement : Prop :=
  ∀ {A N S m n : ℤ},
    DividedSquareBranch A N S m n →
    Odd m →
    DividedSqBranchMOddFactors m n →
    False

private lemma int_pos_eq_one_of_mul_eq_one {x y : ℤ}
    (hx : 0 < x) (hxy : x * y = 1) :
    x = 1 := by
  have hypos : 0 < y := by
    by_contra hy_not
    have hy_nonpos : y ≤ 0 := le_of_not_gt hy_not
    have hprod_nonpos : x * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx) hy_nonpos
    nlinarith [hxy, hprod_nonpos]
  have hxle : x ≤ 1 := by
    by_contra hx_not
    have hx_ge_two : (2 : ℤ) ≤ x := by omega
    have hy_ge_one : (1 : ℤ) ≤ y := by omega
    have hprod_ge_two : (2 : ℤ) ≤ x * y := by
      calc
        (2 : ℤ) = 2 * 1 := by ring
        _ ≤ x * y := by
          exact mul_le_mul hx_ge_two hy_ge_one (by norm_num) (by omega)
    nlinarith [hxy, hprod_ge_two]
  omega

private lemma int_pos_sq_eq_one {x : ℤ} (hx : 0 < x) (hsq : x ^ 2 = 1) :
    x = 1 := by
  apply int_pos_eq_one_of_mul_eq_one hx
  simpa [pow_two] using hsq

theorem no_oddC_three_square_sum {a b c : ℤ}
    (hc : Odd c) (h : a ^ 2 + c ^ 2 = 3 * b ^ 2) :
    False := by
  rcases hc with ⟨c0, hc0⟩
  rcases Int.even_or_odd a with ha | ha
  · rcases ha with ⟨a0, ha0⟩
    rcases Int.even_or_odd b with hb | hb
    · rcases hb with ⟨b0, hb0⟩
      rw [ha0, hb0, hc0] at h
      ring_nf at h
      omega
    · rcases hb with ⟨b0, hb0⟩
      rw [ha0, hb0, hc0] at h
      ring_nf at h
      omega
  · rcases ha with ⟨a0, ha0⟩
    rcases Int.even_or_odd b with hb | hb
    · rcases hb with ⟨b0, hb0⟩
      rw [ha0, hb0, hc0] at h
      ring_nf at h
      omega
    · rcases hb with ⟨b0, hb0⟩
      rw [ha0, hb0, hc0] at h
      ring_nf at h
      omega

theorem dividedMOddFactorsImpossibleStatement :
    DividedMOddFactorsImpossibleStatement := by
  intro A N S m n hbranch hmOdd hfac
  rcases hfac with
    ⟨a, b, c, d, _ha_pos, _hb_pos, _hc_pos, _hd_pos, hma, hmb, hnc, h2md⟩
  have hnOdd : Odd n := by
    rcases hmOdd with ⟨m0, hm0⟩
    refine ⟨m0 - a ^ 2, ?_⟩
    omega
  have hcSqOdd : Odd (c ^ 2) := by
    simpa [hnc] using hnOdd
  have hcOdd : Odd c :=
    (Int.odd_pow' (m := c) (n := 2) (by norm_num)).mp hcSqOdd
  have hcore := dividedMOddFactors_core_identities hma hmb hnc h2md
  exact no_oddC_three_square_sum hcOdd hcore.1

theorem dividedMEvenFactorsUnitStatement :
    DividedMEvenFactorsUnitStatement := by
  intro A N S m n hbad hbranch _hmEven hfac
  rcases hbad with ⟨hApos, hNpos, hSpos, _hcopAN, _hsqne, _hquartic⟩
  rcases hbranch with ⟨hnpos, _hnltm, hcopmn, _h3, hAeq, hNeq, hSeq⟩
  rcases hfac with
    ⟨a, b, c, d, _ha_pos, _hb_pos, _hc_pos, _hd_pos, hma, hmb, hnc, h2md⟩
  rcases dividedMEvenFactors_AP_identities hma hmb hnc h2md with
    ⟨hcb_mid, hba_mid⟩
  have hAP : IntFourSqAP c b d a := by
    unfold IntFourSqAP
    constructor
    · nlinarith
    · nlinarith
  have hconst : FourSqAPConst c b d a :=
    fourIntSquaresAPConst_checked hAP
  rcases hconst with ⟨hcb, hbd, hda⟩
  have hac : a ^ 2 = c ^ 2 := by
    calc
      a ^ 2 = d ^ 2 := hda.symm
      _ = b ^ 2 := hbd.symm
      _ = c ^ 2 := hcb.symm
  have hm_two_n : m = 2 * n := by
    nlinarith
  rcases hcopmn with ⟨r, s, hrs⟩
  have hn_mul : n * (2 * r + s) = 1 := by
    rw [← hrs, hm_two_n]
    ring
  have hn_one : n = 1 :=
    int_pos_eq_one_of_mul_eq_one hnpos hn_mul
  have hm_two : m = 2 := by
    rw [hm_two_n, hn_one]
    norm_num
  have hA_sq : A ^ 2 = 1 := by
    rw [hm_two, hn_one] at hAeq
    ring_nf at hAeq
    nlinarith
  have hN_sq : N ^ 2 = 1 := by
    rw [hm_two, hn_one] at hNeq
    ring_nf at hNeq
    nlinarith
  have hS_one : S = 1 := by
    rw [hm_two, hn_one] at hSeq
    omega
  exact ⟨int_pos_sq_eq_one hApos hA_sq,
    int_pos_sq_eq_one hNpos hN_sq, hS_one⟩

theorem dividedSquareBranchUnitStatement :
    DividedSquareBranchUnitStatement := by
  intro A N S m n hbad hbranch
  rcases dividedSqBranchFactorizationStatement hbranch with hEven | hOdd
  · exact dividedMEvenFactorsUnitStatement hbad hbranch hEven.1 hEven.2
  · exact False.elim
      (dividedMOddFactorsImpossibleStatement hbranch hOdd.1 hOdd.2)

theorem dividedSquareBranchUnitOrDescendsStatement_of_unit :
    DividedSquareBranchUnitOrDescendsStatement := by
  intro A N S m n hbad hbranch
  exact Or.inl (dividedSquareBranchUnitStatement hbad hbranch)

end MazurProof.RationalPointsN12
