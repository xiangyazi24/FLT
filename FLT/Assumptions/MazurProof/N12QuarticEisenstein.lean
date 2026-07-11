import Mathlib.Tactic
import Mathlib.RingTheory.Int.Basic

/-!
# Independent Eisenstein quartic residual for N=12

This file contains only the quartic residual interface and the rational-to-
integer denominator-clearing layer.  It deliberately does not import the E1
finite-point theorem or full-cover files.
-/

namespace MazurProof.RationalPointsN12

/-- Independent rational Eisenstein quartic obstruction. -/
def RatQuarticEisensteinDegenerate : Prop :=
  ∀ {t s : ℚ},
    s ^ 2 = t ^ 4 - t ^ 2 + 1 →
    t = 0 ∨ t ^ 2 = 1

/-- Rational affine Eisenstein quartic. -/
def RatQuarticEisensteinLocal (t s : ℚ) : Prop :=
  s ^ 2 = t ^ 4 - t ^ 2 + 1

/-- If an integer is a rational square, then it is an integer square. -/
def IntSquareOfRatSquareInt : Prop :=
  ∀ {q : ℚ} {m : ℤ},
    q ^ 2 = (m : ℚ) →
    ∃ z : ℤ, z ^ 2 = m

/-- Denominator-cleared primitive integer point from a rational quartic point. -/
def RatQuarticToPrimitiveInt : Prop :=
  ∀ {t s : ℚ},
    s ^ 2 = t ^ 4 - t ^ 2 + 1 →
    ∃ A N S : ℤ,
      IsCoprime A N ∧
      N ≠ 0 ∧
      t = (A : ℚ) / (N : ℚ) ∧
      S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Eisenstein norm equation in integer coordinates. -/
def EisensteinTriple (X Y Z : ℤ) : Prop :=
  Z ^ 2 = X ^ 2 - X * Y + Y ^ 2

/-- One of the two symmetric Eisenstein parametrizations. -/
def EisensteinParam (X Y Z m n : ℤ) : Prop :=
  Z = m ^ 2 - m * n + n ^ 2 ∧
  ((X = m ^ 2 - n ^ 2 ∧ Y = 2 * m * n - n ^ 2) ∨
   (Y = m ^ 2 - n ^ 2 ∧ X = 2 * m * n - n ^ 2))

/-- The full primitive Eisenstein-triple parametrization branch.  The raw
sector and the divided-by-`3` sector are intentionally distinct. -/
def EisensteinFullParam (X Y Z m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧
  ((¬ (3 : ℤ) ∣ m + n ∧ EisensteinParam X Y Z m n) ∨
    ((3 : ℤ) ∣ m + n ∧
      3 * Z = m ^ 2 - m * n + n ^ 2 ∧
      ((3 * X = m ^ 2 - n ^ 2 ∧ 3 * Y = 2 * m * n - n ^ 2) ∨
       (3 * Y = m ^ 2 - n ^ 2 ∧ 3 * X = 2 * m * n - n ^ 2))))

/-- Positive primitive Eisenstein-triple classification target.  The unit
triple `(1,1,1)` must be kept as an explicit exceptional branch. -/
def EisensteinTripleParamOrUnit (X Y Z : ℤ) : Prop :=
  (X = 1 ∧ Y = 1 ∧ Z = 1) ∨
  ∃ m n : ℤ, EisensteinFullParam X Y Z m n

/-- Lean target for a positive primitive Eisenstein-triple parametrization,
with the necessary unit exception. -/
def EisensteinTriplePrimitiveParamOrUnit : Prop :=
  ∀ {X Y Z : ℤ},
    0 < X → 0 < Y → 0 < Z →
    IsCoprime X Y →
    EisensteinTriple X Y Z →
    EisensteinTripleParamOrUnit X Y Z

/-- Homogeneous integer Eisenstein quartic obstruction. -/
def IntQuarticEisensteinDegenerate : Prop :=
  ∀ {A N S : ℤ},
    N ≠ 0 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    A = 0 ∨ A ^ 2 = N ^ 2

/-- Primitive homogeneous integer Eisenstein quartic obstruction; this is the
natural target for an independent Ljunggren/Eisenstein descent. -/
def IntQuarticEisensteinPrimitive : Prop :=
  ∀ {A N S : ℤ},
    IsCoprime A N →
    N ≠ 0 →
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 →
    A = 0 ∨ A ^ 2 = N ^ 2

/-- A non-degenerate primitive integer solution to the Eisenstein quartic. -/
def EisensteinQuarticBad (A N S : ℤ) : Prop :=
  IsCoprime A N ∧
  A ≠ 0 ∧ N ≠ 0 ∧ A ^ 2 ≠ N ^ 2 ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Positive ordered primitive bad solution. -/
def NormalizedEisensteinBad (A N S : ℤ) : Prop :=
  0 < A ∧ A < N ∧ 0 < S ∧ IsCoprime A N ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- Positive unordered primitive bad solution, used by a single parametrized
branch before reordering the smaller output. -/
def PositivePrimitiveEisensteinBadUnordered (A N S : ℤ) : Prop :=
  0 < A ∧ 0 < N ∧ 0 < S ∧ IsCoprime A N ∧ A ^ 2 ≠ N ^ 2 ∧
  S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4

/-- A square-sided branch of the Eisenstein conic parametrization. -/
def EisensteinSqBranch (A N S m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧
  A ^ 2 = (m - n) * (m + n) ∧
  N ^ 2 = n * (2 * m - n) ∧
  S = m ^ 2 - m * n + n ^ 2

/-- The divided-by-`3` square-sided branch that occurs in the full primitive
Eisenstein-triple parametrization.  This cannot be silently merged into the raw
branch. -/
def DividedSquareBranch (A N S m n : ℤ) : Prop :=
  0 < n ∧ n < m ∧ IsCoprime m n ∧ (3 : ℤ) ∣ m + n ∧
  3 * A ^ 2 = (m - n) * (m + n) ∧
  3 * N ^ 2 = n * (2 * m - n) ∧
  3 * S = m ^ 2 - m * n + n ^ 2

/-- A descent step on bad primitive Eisenstein quartic solutions. -/
def EisensteinQuarticDescentStep : Prop :=
  ∀ {A N S : ℤ},
    EisensteinQuarticBad A N S →
    ∃ A' N' S' : ℤ,
      EisensteinQuarticBad A' N' S' ∧
      A'.natAbs + N'.natAbs < A.natAbs + N.natAbs

/-- A primitive theorem is enough once a separate primitive-reduction layer has
been proved.  This is kept explicit because reducing a nonprimitive homogeneous
solution is part of the hard arithmetic, not denominator bookkeeping. -/
def IntQuarticEisensteinPrimitiveReduction : Prop :=
  IntQuarticEisensteinPrimitive → IntQuarticEisensteinDegenerate

/-- Sign/order normalization frontier for the primitive quartic. -/
def NormalizedOfBadStatement : Prop :=
  ∀ {A N S : ℤ},
    EisensteinQuarticBad A N S →
    ∃ A0 N0 S0 : ℤ, NormalizedEisensteinBad A0 N0 S0

/-- Correct parametrization frontier for a normalized bad solution.  Besides
the two raw square-sided orientations, the divided-by-`3` sector must be kept
explicit. -/
def NormalizedBadParamStatement : Prop :=
  ∀ {A N S : ℤ},
    NormalizedEisensteinBad A N S →
    ∃ m n : ℤ,
      EisensteinSqBranch A N S m n ∨
        EisensteinSqBranch N A S m n ∨
        DividedSquareBranch A N S m n ∨
        DividedSquareBranch N A S m n

/-- Positive coprime product-square splitting. -/
def PosSqOfCoprimeMulSqStatement : Prop :=
  ∀ {x y z : ℤ},
    0 < x →
    0 < y →
    IsCoprime x y →
    z ^ 2 = x * y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2

/-- Positive product-square splitting when both factors carry one factor `2`. -/
def PosTwoSqOfGcdTwoMulSqStatement : Prop :=
  ∀ {x y z : ℤ},
    0 < x →
    0 < y →
    2 ∣ x →
    2 ∣ y →
    IsCoprime (x / 2) (y / 2) →
    z ^ 2 = x * y →
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2 * a ^ 2 ∧ y = 2 * b ^ 2

/-- The `n` even branch of the explicit Eisenstein descent. -/
def DescentBranchNEvenStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    2 ∣ n →
    ∃ e f d : ℤ,
      0 < e ∧ e < f ∧ 0 < d ∧ IsCoprime e f ∧
      d ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 ∧ f < N

/-- The `n` odd, `m` even branch is impossible. -/
def BranchNOddMEvenImpossibleStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ¬ 2 ∣ n →
    2 ∣ m →
    False

/-- The `n` odd, `m` odd branch of the explicit Eisenstein descent. -/
def DescentBranchNOddMOddStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ¬ 2 ∣ n →
    ¬ 2 ∣ m →
    ∃ e f b : ℤ,
      0 < e ∧ e < f ∧ 0 < b ∧ IsCoprime e f ∧
      b ^ 2 = e ^ 4 - e ^ 2 * f ^ 2 + f ^ 4 ∧ f < N

/-- Combined branch descent, decreasing the second coordinate of the branch. -/
def DescentFromBranchUnorderedStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Raw square branch cannot be the unit solution.  This keeps the current raw
descent residual from being forced to descend below `N = 1`. -/
def RawSqBranchNoUnitStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1)

/-- Safer raw-branch target: descent only after the unit case is excluded. -/
def RawSqBranchNonunitDescendsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) →
    EisensteinSqBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Unit-or-descent version of the raw square branch, parallel to the divided
branch residual. -/
def RawSqBranchUnitOrDescendsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    EisensteinSqBranch A N S m n →
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      ∃ A' N' S' : ℤ,
        NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Compatibility wrapper for retaining the current raw descent residual. -/
def RawSqBranchBridgeToCurrentStatement : Prop :=
  RawSqBranchNoUnitStatement →
  RawSqBranchNonunitDescendsStatement →
  DescentFromBranchUnorderedStatement

/-- The divided-by-`3` sector either is the unit solution or descends.  For a
normalized bad solution the unit branch is impossible, so this is sufficient for
global descent once the full parametrization is available. -/
def DividedSquareBranchUnitOrDescendsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    DividedSquareBranch A N S m n →
    (A = 1 ∧ N = 1 ∧ S = 1) ∨
      ∃ A' N' S' : ℤ,
        NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Nonunit version of the divided-branch residual. -/
def DividedSquareBranchNonunitDescendsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    PositivePrimitiveEisensteinBadUnordered A N S →
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) →
    DividedSquareBranch A N S m n →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- Bridge from the nonunit divided-branch target to the current unit-or-
descent statement. -/
def DividedSquareBranchBridgeStatement : Prop :=
  DividedSquareBranchNonunitDescendsStatement →
  DividedSquareBranchUnitOrDescendsStatement

/-- Proof graph for the raw branch from the explicit parity sub-branches. -/
def RawSqBranchDescentFromParityPiecesStatement : Prop :=
  DescentBranchNEvenStatement →
  BranchNOddMEvenImpossibleStatement →
  DescentBranchNOddMOddStatement →
  DescentFromBranchUnorderedStatement

/-- Factors obtained from the raw branch in the `n` even case. -/
def RawSqBranchEvenFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = a ^ 2 ∧
    m + n = b ^ 2 ∧
    n = 2 * c ^ 2 ∧
    2 * m - n = 2 * d ^ 2

/-- Factors obtained from the raw branch in the `n` odd case. -/
def RawSqBranchOddFactors (m n : ℤ) : Prop :=
  ∃ a b c d : ℤ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    m - n = 2 * a ^ 2 ∧
    m + n = 2 * b ^ 2 ∧
    n = c ^ 2 ∧
    2 * m - n = d ^ 2

/-- Parity frontier for the raw branch before applying the gcd-one/gcd-two
square splitting lemmas. -/
def RawSqBranchMParityStatement : Prop :=
  ∀ {A N S m n : ℤ},
    EisensteinSqBranch A N S m n →
    Odd m

/-- Honest raw-branch factorization frontier: split only the products already
known to be squares. -/
def RawSqBranchFactorizationStatement : Prop :=
  ∀ {A N S m n : ℤ},
    EisensteinSqBranch A N S m n →
      (Even n ∧ RawSqBranchEvenFactors m n) ∨
      (Odd n ∧ RawSqBranchOddFactors m n)

/-- The remaining descent/contradiction after the honest raw-branch factors
have been extracted. -/
def RawSqBranchDescentFromFactorsStatement : Prop :=
  ∀ {A N S m n : ℤ},
    EisensteinSqBranch A N S m n →
      ((Even n ∧ RawSqBranchEvenFactors m n) ∨
       (Odd n ∧ RawSqBranchOddFactors m n)) →
    False

/-- Normalized infinite descent step. -/
def NormalizedDescentStatement : Prop :=
  ∀ {A N S : ℤ},
    NormalizedEisensteinBad A N S →
    ∃ A' N' S' : ℤ,
      NormalizedEisensteinBad A' N' S' ∧ N' < N

/-- No normalized bad solution exists. -/
def NotNormalizedBadStatement : Prop :=
  ¬ ∃ A N S : ℤ, NormalizedEisensteinBad A N S

/-- Final assembly frontier for proving the primitive quartic theorem from
normalization, branch parametrization, and branch descent. -/
def IntQuarticEisensteinPrimitiveFromDescentStatement : Prop :=
  NormalizedOfBadStatement →
  NormalizedBadParamStatement →
  DescentFromBranchUnorderedStatement →
  DividedSquareBranchUnitOrDescendsStatement →
  IntQuarticEisensteinPrimitive

/-- A tiny integer helper avoiding fragile unit-normalization API. -/
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

theorem rawSqBranchNoUnitStatement :
    RawSqBranchNoUnitStatement := by
  intro A N S m n _hbad hbranch hunit
  rcases hbranch with ⟨hnpos, hnltm, _hcop, _hA, hN, _hS⟩
  rcases hunit with ⟨_hAunit, hNunit, _hSunit⟩
  have hprod : n * (2 * m - n) = 1 := by
    calc
      n * (2 * m - n) = N ^ 2 := hN.symm
      _ = 1 := by
        rw [hNunit]
        norm_num
  have hn_one : n = 1 :=
    int_pos_eq_one_of_mul_eq_one hnpos hprod
  have hm_one : m = 1 := by
    nlinarith
  nlinarith

theorem descentFromBranchUnordered_of_rawSqBranchNonunitDescends
    (hNonunit : RawSqBranchNonunitDescendsStatement) :
    DescentFromBranchUnorderedStatement := by
  intro A N S m n hbad hbranch
  exact hNonunit hbad (rawSqBranchNoUnitStatement hbad hbranch) hbranch

/-- The four visible raw-branch factors are positive. -/
theorem eisensteinSqBranch_factor_pos {A N S m n : ℤ}
    (h : EisensteinSqBranch A N S m n) :
    0 < m - n ∧ 0 < m + n ∧ 0 < n ∧ 0 < 2 * m - n := by
  rcases h with ⟨hnpos, hnltm, _hcop, _hA, _hN, _hS⟩
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · exact hnpos
  · nlinarith

private lemma int_square_ne_four_mul_sub_one (x q : ℤ) :
    x ^ 2 ≠ 4 * q - 1 := by
  intro h
  rcases Int.even_or_odd x with hx | hx
  · rcases hx with ⟨r, rfl⟩
    ring_nf at h
    omega
  · rcases hx with ⟨r, rfl⟩
    ring_nf at h
    omega

private lemma even_sq_sub_odd_sq_eq_four_mul_sub_one
    {U V : ℤ} (hU : Even U) (hV : Odd V) :
    ∃ q : ℤ, U ^ 2 - V ^ 2 = 4 * q - 1 := by
  rcases hU with ⟨u, rfl⟩
  rcases hV with ⟨v, rfl⟩
  refine ⟨u ^ 2 - v ^ 2 - v, ?_⟩
  ring

theorem rawSqBranchMParityStatement :
    RawSqBranchMParityStatement := by
  intro A N S m n hbranch
  by_contra hm_not_odd
  have hm_even : Even m := Int.not_odd_iff_even.mp hm_not_odd
  rcases hbranch with ⟨_hnpos, _hnltm, hcop, hA, _hN, _hS⟩
  have hn_odd : Odd n := by
    by_contra hn_not_odd
    have hn_even : Even n := Int.not_odd_iff_even.mp hn_not_odd
    rcases hcop with ⟨u, v, huv⟩
    rcases hm_even with ⟨m0, hm0⟩
    rcases hn_even with ⟨n0, hn0⟩
    have htwo : (2 : ℤ) ∣ 1 := by
      refine ⟨u * m0 + v * n0, ?_⟩
      rw [← huv, hm0, hn0]
      ring
    norm_num at htwo
  have hmn : (m - n) * (m + n) = m ^ 2 - n ^ 2 := by ring
  rcases even_sq_sub_odd_sq_eq_four_mul_sub_one hm_even hn_odd with ⟨q, hq⟩
  exact int_square_ne_four_mul_sub_one A q (by
    calc
      A ^ 2 = (m - n) * (m + n) := hA
      _ = m ^ 2 - n ^ 2 := hmn
      _ = 4 * q - 1 := hq)

private lemma odd_sub_even_int {m n : ℤ}
    (hm : Odd m) (hn : Even n) :
    Odd (m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  rw [ha, hb]
  ring

private lemma even_sub_odd_odd_int {m n : ℤ}
    (hm : Odd m) (hn : Odd n) :
    Even (m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  rw [ha, hb]
  ring

private lemma even_add_odd_odd_int {m n : ℤ}
    (hm : Odd m) (hn : Odd n) :
    Even (m + n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨a + b + 1, ?_⟩
  rw [ha, hb]
  ring

private lemma even_two_mul_sub_of_odd_even_int {m n : ℤ}
    (hm : Odd m) (hn : Even n) :
    Even (2 * m - n) := by
  rcases hm with ⟨a, ha⟩
  rcases hn with ⟨b, hb⟩
  refine ⟨2 * a + 1 - b, ?_⟩
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

private lemma isCoprime_m_sub_n_m_add_n_of_even_n
    {m n : ℤ} (hcop : IsCoprime m n) (hm : Odd m) (hn : Even n) :
    IsCoprime (m - n) (m + n) := by
  apply IsRelPrime.isCoprime
  intro d hdsub hdadd
  have hsub_odd : Odd (m - n) := odd_sub_even_int hm hn
  have hd2 : IsCoprime d (2 : ℤ) :=
    isCoprime_two_of_dvd_odd hsub_odd hdsub
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

private lemma isCoprime_halves_n_two_mul_sub
    {m n x y : ℤ} (hcop : IsCoprime m n)
    (hx : n = 2 * x) (hy : 2 * m - n = 2 * y) :
    IsCoprime x y := by
  rcases hcop with ⟨r, s, hrs⟩
  use r + 2 * s, r
  have hm : m = x + y := by omega
  calc
    (r + 2 * s) * x + r * y = r * (x + y) + s * (2 * x) := by ring
    _ = r * m + s * n := by rw [hm, hx]
    _ = 1 := hrs

/-- The parametrization identities satisfy the Eisenstein norm equation. -/
theorem eisensteinParam_triple {X Y Z m n : ℤ}
    (h : EisensteinParam X Y Z m n) :
    EisensteinTriple X Y Z := by
  rcases h with ⟨hZ, hcases⟩
  rcases hcases with hXY | hYX
  · rcases hXY with ⟨hX, hY⟩
    unfold EisensteinTriple
    rw [hZ, hX, hY]
    ring
  · rcases hYX with ⟨hY, hX⟩
    unfold EisensteinTriple
    rw [hZ, hX, hY]
    ring

/-- The Eisenstein norm equation is symmetric in `X` and `Y`. -/
theorem eisensteinTriple_symm {X Y Z : ℤ}
    (h : EisensteinTriple X Y Z) :
    EisensteinTriple Y X Z := by
  unfold EisensteinTriple at h ⊢
  rw [h]
  ring

/-- The parametrization predicate is symmetric in `X` and `Y`. -/
theorem eisensteinParam_symm {X Y Z m n : ℤ}
    (h : EisensteinParam X Y Z m n) :
    EisensteinParam Y X Z m n := by
  rcases h with ⟨hZ, hcases⟩
  refine ⟨hZ, ?_⟩
  rcases hcases with hXY | hYX
  · rcases hXY with ⟨hX, hY⟩
    exact Or.inr ⟨hX, hY⟩
  · rcases hYX with ⟨hY, hX⟩
    exact Or.inl ⟨hY, hX⟩

/-- If a positive primitive Eisenstein triple has `X = Y`, it is the unit
triple. -/
theorem eisensteinTriple_unit_of_eq {X Y Z : ℤ}
    (hXpos : 0 < X) (hZpos : 0 < Z)
    (hcop : IsCoprime X Y)
    (htri : EisensteinTriple X Y Z)
    (hXY : X = Y) :
    X = 1 ∧ Y = 1 ∧ Z = 1 := by
  subst Y
  rcases hcop with ⟨r, s, hrs⟩
  have hXmul : X * (r + s) = 1 := by
    rw [← hrs]
    ring
  have hXone : X = 1 := int_pos_eq_one_of_mul_eq_one hXpos hXmul
  have hZpow : Z ^ 2 = 1 := by
    unfold EisensteinTriple at htri
    calc
      Z ^ 2 = X ^ 2 - X * X + X ^ 2 := htri
      _ = 1 := by
        rw [hXone]
        norm_num
  have hZmul : Z * Z = 1 := by
    simpa [pow_two] using hZpow
  have hZone : Z = 1 := int_pos_eq_one_of_mul_eq_one hZpos hZmul
  exact ⟨hXone, hXone, hZone⟩

/-- Factor identity with `P = 2*Z - (2*X-Y)` and
`Q = 2*Z + (2*X-Y)`. -/
theorem eisensteinTriple_factor_identity {X Y Z : ℤ}
    (h : EisensteinTriple X Y Z) :
    (2 * Z - (2 * X - Y)) * (2 * Z + (2 * X - Y)) = 3 * Y ^ 2 := by
  unfold EisensteinTriple at h
  calc
    (2 * Z - (2 * X - Y)) * (2 * Z + (2 * X - Y))
        = 4 * Z ^ 2 - (2 * X - Y) ^ 2 := by ring
    _ = 3 * Y ^ 2 := by
      rw [h]
      ring

/-- The affine branch formulas satisfy the Eisenstein conic identity. -/
theorem eisenstein_param_identity (m n : ℤ) :
    (m ^ 2 - m * n + n ^ 2) ^ 2 =
      ((m - n) * (m + n)) ^ 2
        - ((m - n) * (m + n)) * (n * (2 * m - n))
        + (n * (2 * m - n)) ^ 2 := by
  ring

/-- A square-sided branch gives an Eisenstein triple. -/
theorem eisensteinSqBranch_triple {A N S m n : ℤ}
    (h : EisensteinSqBranch A N S m n) :
    EisensteinTriple (A ^ 2) (N ^ 2) S := by
  rcases h with ⟨_, _, _, hA, hN, hS⟩
  unfold EisensteinTriple
  rw [hS, hA, hN]
  exact eisenstein_param_identity m n

/-- The raw branch controls the sum of the two known squares; no sign choice
for `A * N` is involved. -/
theorem eisensteinSqBranch_A_sq_add_N_sq_eq_S {A N S m n : ℤ}
    (h : EisensteinSqBranch A N S m n) :
    A ^ 2 + N ^ 2 = S + 3 * m * n - 3 * n ^ 2 := by
  rcases h with ⟨_, _, _, hA, hN, hS⟩
  rw [hA, hN, hS]
  ring

/-- The raw branch controls `(A*N)^2`, not a linear formula for `A*N`. -/
theorem eisensteinSqBranch_A_mul_N_sq {A N S m n : ℤ}
    (h : EisensteinSqBranch A N S m n) :
    (A * N) ^ 2 = ((m - n) * (m + n)) * (n * (2 * m - n)) := by
  rcases h with ⟨_, _, _, hA, hN, _⟩
  rw [mul_pow, hA, hN]

/-- A homogeneous Eisenstein-quartic solution is an Eisenstein triple with
coordinates `A²,N²,S`. -/
theorem eisensteinTriple_of_quartic {A N S : ℤ}
    (h : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
    EisensteinTriple (A ^ 2) (N ^ 2) S := by
  unfold EisensteinTriple
  rw [h]
  ring

/-- In the quartic application, the unit branch of the triple classification is
exactly the degenerate conclusion `A²=N²`. -/
theorem quartic_unit_branch_forces_degenerate {A N S : ℤ}
    (hunit : A ^ 2 = 1 ∧ N ^ 2 = 1 ∧ S = 1) :
    A ^ 2 = N ^ 2 := by
  exact hunit.1.trans hunit.2.1.symm

private lemma q2670_quartic_pos {A N : ℤ}
    (hA : A ≠ 0) (hN : N ≠ 0) :
    0 < A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 := by
  have hA2pos : 0 < A ^ 2 := sq_pos_of_ne_zero hA
  have hN2pos : 0 < N ^ 2 := sq_pos_of_ne_zero hN
  have hprod : 0 < A ^ 2 * N ^ 2 := mul_pos hA2pos hN2pos
  have hsq : 0 ≤ (A ^ 2 - N ^ 2) ^ 2 := sq_nonneg _
  have hid :
      A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 =
        (A ^ 2 - N ^ 2) ^ 2 + A ^ 2 * N ^ 2 := by
    ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos hsq hprod

private lemma q2670_abs_quartic {A N S : ℤ}
    (hS : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4) :
    |S| ^ 2 = |A| ^ 4 - |A| ^ 2 * |N| ^ 2 + |N| ^ 4 := by
  have hS2 : |S| ^ 2 = S ^ 2 := sq_abs S
  have hA2 : |A| ^ 2 = A ^ 2 := sq_abs A
  have hN2 : |N| ^ 2 = N ^ 2 := sq_abs N
  have hA4 : |A| ^ 4 = A ^ 4 := by
    calc
      |A| ^ 4 = (|A| ^ 2) ^ 2 := by ring
      _ = (A ^ 2) ^ 2 := by rw [hA2]
      _ = A ^ 4 := by ring
  have hN4 : |N| ^ 4 = N ^ 4 := by
    calc
      |N| ^ 4 = (|N| ^ 2) ^ 2 := by ring
      _ = (N ^ 2) ^ 2 := by rw [hN2]
      _ = N ^ 4 := by ring
  calc
    |S| ^ 2 = S ^ 2 := hS2
    _ = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 := hS
    _ = |A| ^ 4 - |A| ^ 2 * |N| ^ 2 + |N| ^ 4 := by
      rw [hA4, hA2, hN2, hN4]

private lemma q2670_abs_coprime {A N : ℤ}
    (hcop : IsCoprime A N) :
    IsCoprime |A| |N| := by
  exact hcop.abs_abs

private lemma q2670_abs_ne_of_sq_ne {A N : ℤ}
    (hneq : A ^ 2 ≠ N ^ 2) :
    |A| ≠ |N| := by
  intro hAbs
  have hsq : A ^ 2 = N ^ 2 := by
    calc
      A ^ 2 = |A| ^ 2 := (sq_abs A).symm
      _ = |N| ^ 2 := by rw [hAbs]
      _ = N ^ 2 := sq_abs N
  exact hneq hsq

/-- Every bad primitive Eisenstein quartic counterexample can be normalized to
positive ordered coordinates. -/
theorem normalizedOfBadStatement : NormalizedOfBadStatement := by
  intro A N S hbad
  rcases hbad with ⟨hcop, hAne, hNne, hsq_ne, hS⟩
  have hAabspos : 0 < |A| := abs_pos.mpr hAne
  have hNabspos : 0 < |N| := abs_pos.mpr hNne
  have hSsqpos : 0 < S ^ 2 := by
    rw [hS]
    exact q2670_quartic_pos hAne hNne
  have hSne : S ≠ 0 := by
    intro h0
    rw [h0] at hSsqpos
    norm_num at hSsqpos
  have hSabspos : 0 < |S| := abs_pos.mpr hSne
  have hquartAbs :
      |S| ^ 2 = |A| ^ 4 - |A| ^ 2 * |N| ^ 2 + |N| ^ 4 :=
    q2670_abs_quartic hS
  have hcopAbs : IsCoprime |A| |N| := q2670_abs_coprime hcop
  have hAbs_ne : |A| ≠ |N| := q2670_abs_ne_of_sq_ne hsq_ne
  rcases lt_or_gt_of_ne hAbs_ne with hlt | hgt
  · refine ⟨|A|, |N|, |S|, ?_⟩
    exact ⟨hAabspos, hlt, hSabspos, hcopAbs, hquartAbs⟩
  · refine ⟨|N|, |A|, |S|, ?_⟩
    have hquartSwap :
        |S| ^ 2 = |N| ^ 4 - |N| ^ 2 * |A| ^ 2 + |A| ^ 4 := by
      rw [hquartAbs]
      ring
    exact ⟨hNabspos, hgt, hSabspos, hcopAbs.symm, hquartSwap⟩

private lemma exists_pos_sq_of_pos_eq_sq {x a0 : ℤ}
    (hx : 0 < x) (hxa : x = a0 ^ 2) :
    ∃ a : ℤ, 0 < a ∧ x = a ^ 2 := by
  by_cases ha_pos : 0 < a0
  · exact ⟨a0, ha_pos, hxa⟩
  · have ha0_ne : a0 ≠ 0 := by
      intro ha0
      have hx0 : x = 0 := by
        simpa [ha0] using hxa
      linarith
    have ha_le : a0 ≤ 0 := le_of_not_gt ha_pos
    have ha_lt : a0 < 0 := lt_of_le_of_ne ha_le ha0_ne
    refine ⟨-a0, by linarith, ?_⟩
    calc
      x = a0 ^ 2 := hxa
      _ = (-a0) ^ 2 := by ring

/-- Positive coprime factors of an integer square are positive squares. -/
theorem posSqOfCoprimeMulSq
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y)
    (hcop : IsCoprime x y) (hz : z ^ 2 = x * y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = a ^ 2 ∧ y = b ^ 2 := by
  have hmul : x * y = z ^ 2 := hz.symm
  rcases Int.sq_of_isCoprime hcop hmul with ⟨a0, hx_sq | hx_neg_sq⟩
  · have hmul_yx : y * x = z ^ 2 := by
      simpa [mul_comm] using hmul
    rcases Int.sq_of_isCoprime hcop.symm hmul_yx with ⟨b0, hy_sq | hy_neg_sq⟩
    · rcases exists_pos_sq_of_pos_eq_sq hx hx_sq with ⟨a, ha, hxa⟩
      rcases exists_pos_sq_of_pos_eq_sq hy hy_sq with ⟨b, hb, hyb⟩
      exact ⟨a, b, ha, hb, hxa, hyb⟩
    · exfalso
      have hyneg : 0 < -(b0 ^ 2) := by
        simpa [hy_neg_sq] using hy
      have hb_nonneg : 0 ≤ b0 ^ 2 := sq_nonneg b0
      nlinarith
  · exfalso
    have hxneg : 0 < -(a0 ^ 2) := by
      simpa [hx_neg_sq] using hx
    have ha_nonneg : 0 ≤ a0 ^ 2 := sq_nonneg a0
    nlinarith

theorem posSqOfCoprimeMulSqStatement :
    PosSqOfCoprimeMulSqStatement := by
  intro x y z hx hy hcop hz
  exact posSqOfCoprimeMulSq hx hy hcop hz

/-- If both factors carry exactly the visible factor `2`, the remaining
coprime product-square splitting makes both halves positive squares. -/
theorem posTwoSqOfGcdTwoMulSq
    {x y z : ℤ} (hx : 0 < x) (hy : 0 < y)
    (hx2 : (2 : ℤ) ∣ x) (hy2 : (2 : ℤ) ∣ y)
    (hcop : IsCoprime (x / 2) (y / 2))
    (hz : z ^ 2 = x * y) :
    ∃ a b : ℤ, 0 < a ∧ 0 < b ∧ x = 2 * a ^ 2 ∧ y = 2 * b ^ 2 := by
  rcases hx2 with ⟨u, rfl⟩
  rcases hy2 with ⟨v, rfl⟩
  have hu_pos : 0 < u := by
    nlinarith
  have hv_pos : 0 < v := by
    nlinarith
  have h2_ne : (2 : ℤ) ≠ 0 := by norm_num
  have hdiv_u : ((2 : ℤ) * u) / 2 = u := by
    exact Int.mul_ediv_cancel_left u h2_ne
  have hdiv_v : ((2 : ℤ) * v) / 2 = v := by
    exact Int.mul_ediv_cancel_left v h2_ne
  have hcop_uv : IsCoprime u v := by
    simpa [hdiv_u, hdiv_v] using hcop
  have hz2_dvd : (2 : ℤ) ∣ z ^ 2 := by
    rw [hz]
    exact ⟨u * (2 * v), by ring⟩
  have hz_dvd : (2 : ℤ) ∣ z :=
    Int.Prime.dvd_pow' (p := 2) (n := z) (k := 2) Nat.prime_two hz2_dvd
  rcases hz_dvd with ⟨w, rfl⟩
  have h4 : 4 * (w ^ 2) = 4 * (u * v) := by
    calc
      4 * (w ^ 2) = (2 * w) ^ 2 := by ring
      _ = (2 * u) * (2 * v) := hz
      _ = 4 * (u * v) := by ring
  have hw : w ^ 2 = u * v := by
    nlinarith
  rcases posSqOfCoprimeMulSq hu_pos hv_pos hcop_uv hw with
    ⟨a, b, ha, hb, hu_sq, hv_sq⟩
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rw [hu_sq]
  · rw [hv_sq]

theorem posTwoSqOfGcdTwoMulSqStatement :
    PosTwoSqOfGcdTwoMulSqStatement := by
  intro x y z hx hy hx2 hy2 hcop hz
  exact posTwoSqOfGcdTwoMulSq hx hy hx2 hy2 hcop hz

theorem rawSqBranchFactorizationStatement :
    RawSqBranchFactorizationStatement := by
  intro A N S m n hbranch
  rcases hbranch with ⟨hnpos, hnltm, hcop, hA, hN, hS⟩
  have hbranch' : EisensteinSqBranch A N S m n :=
    ⟨hnpos, hnltm, hcop, hA, hN, hS⟩
  have hmOdd : Odd m := rawSqBranchMParityStatement hbranch'
  rcases eisensteinSqBranch_factor_pos hbranch' with
    ⟨h_m_sub_n_pos, h_m_add_n_pos, hn_pos, h_two_m_sub_n_pos⟩
  have h2_ne : (2 : ℤ) ≠ 0 := by norm_num
  rcases Int.even_or_odd n with hnEven | hnOdd
  · refine Or.inl ⟨hnEven, ?_⟩
    have hcopA : IsCoprime (m - n) (m + n) :=
      isCoprime_m_sub_n_m_add_n_of_even_n hcop hmOdd hnEven
    rcases posSqOfCoprimeMulSq h_m_sub_n_pos h_m_add_n_pos hcopA hA with
      ⟨a, b, ha_pos, hb_pos, hma, hmb⟩
    have h2mnEven : Even (2 * m - n) :=
      even_two_mul_sub_of_odd_even_int hmOdd hnEven
    have hn2 : (2 : ℤ) ∣ n := even_iff_two_dvd.mp hnEven
    have h2mn2 : (2 : ℤ) ∣ (2 * m - n) := even_iff_two_dvd.mp h2mnEven
    rcases hnEven with ⟨u, hu⟩
    rcases h2mnEven with ⟨v, hv⟩
    have hu2 : n = 2 * u := by
      rw [hu]
      ring
    have hv2 : 2 * m - n = 2 * v := by
      rw [hv]
      ring
    have hcopUV : IsCoprime u v :=
      isCoprime_halves_n_two_mul_sub hcop hu2 hv2
    have hdivu : n / 2 = u := by
      rw [hu2]
      exact Int.mul_ediv_cancel_left u h2_ne
    have hdivv : (2 * m - n) / 2 = v := by
      rw [hv2]
      exact Int.mul_ediv_cancel_left v h2_ne
    have hcopDiv : IsCoprime (n / 2) ((2 * m - n) / 2) := by
      simpa [hdivu, hdivv] using hcopUV
    rcases posTwoSqOfGcdTwoMulSq hn_pos h_two_m_sub_n_pos
        hn2 h2mn2 hcopDiv hN with
      ⟨c, d, hc_pos, hd_pos, hnc, h2md⟩
    exact ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos, hma, hmb, hnc, h2md⟩
  · refine Or.inr ⟨hnOdd, ?_⟩
    have hmnEven : Even (m - n) := even_sub_odd_odd_int hmOdd hnOdd
    have hmpEven : Even (m + n) := even_add_odd_odd_int hmOdd hnOdd
    have hmn2 : (2 : ℤ) ∣ (m - n) := even_iff_two_dvd.mp hmnEven
    have hmp2 : (2 : ℤ) ∣ (m + n) := even_iff_two_dvd.mp hmpEven
    rcases hmnEven with ⟨u, hu⟩
    rcases hmpEven with ⟨v, hv⟩
    have hu2 : m - n = 2 * u := by
      rw [hu]
      ring
    have hv2 : m + n = 2 * v := by
      rw [hv]
      ring
    have hcopUV : IsCoprime u v :=
      isCoprime_halves_m_sub_m_add hcop hu2 hv2
    have hdivu : (m - n) / 2 = u := by
      rw [hu2]
      exact Int.mul_ediv_cancel_left u h2_ne
    have hdivv : (m + n) / 2 = v := by
      rw [hv2]
      exact Int.mul_ediv_cancel_left v h2_ne
    have hcopDiv : IsCoprime ((m - n) / 2) ((m + n) / 2) := by
      simpa [hdivu, hdivv] using hcopUV
    rcases posTwoSqOfGcdTwoMulSq h_m_sub_n_pos h_m_add_n_pos
        hmn2 hmp2 hcopDiv hA with
      ⟨a, b, ha_pos, hb_pos, hma, hmb⟩
    have hcopN : IsCoprime n (2 * m - n) :=
      isCoprime_n_two_mul_m_sub_n_of_odd_n hcop hnOdd
    rcases posSqOfCoprimeMulSq hn_pos h_two_m_sub_n_pos hcopN hN with
      ⟨c, d, hc_pos, hd_pos, hnc, h2md⟩
    exact ⟨a, b, c, d, ha_pos, hb_pos, hc_pos, hd_pos, hma, hmb, hnc, h2md⟩

theorem rawSqBranchBridgeToCurrentStatement :
    RawSqBranchBridgeToCurrentStatement := by
  intro hNoUnit hNonunit A N S m n hbad hbranch
  exact hNonunit hbad (hNoUnit hbad hbranch) hbranch

theorem rawSqBranchUnitOrDescends_of_nonunitDescends
    (hNonunit : RawSqBranchNonunitDescendsStatement) :
    RawSqBranchUnitOrDescendsStatement := by
  intro A N S m n hbad hbranch
  by_cases hunit : A = 1 ∧ N = 1 ∧ S = 1
  · exact Or.inl hunit
  · exact Or.inr (hNonunit hbad hunit hbranch)

theorem dividedSquareBranchBridgeStatement :
    DividedSquareBranchBridgeStatement := by
  intro hNonunit A N S m n hbad hbranch
  by_cases hunit : A = 1 ∧ N = 1 ∧ S = 1
  · exact Or.inl hunit
  · exact Or.inr (hNonunit hbad hunit hbranch)

theorem rawSqBranchDescentFromParityPiecesStatement :
    RawSqBranchDescentFromParityPiecesStatement := by
  intro hEven hOddEvenImpossible hOddOdd A N S m n hbad hbranch
  by_cases hn : 2 ∣ n
  · rcases hEven hbad hbranch hn with
      ⟨e, f, d, hepos, he_lt_f, hdpos, hcop, hquartic, hf_lt_N⟩
    exact ⟨e, f, d, ⟨hepos, he_lt_f, hdpos, hcop, hquartic⟩, hf_lt_N⟩
  · by_cases hm : 2 ∣ m
    · exact False.elim (hOddEvenImpossible hbad hbranch hn hm)
    · rcases hOddOdd hbad hbranch hn hm with
        ⟨e, f, b, hepos, he_lt_f, hbpos, hcop, hquartic, hf_lt_N⟩
      exact ⟨e, f, b, ⟨hepos, he_lt_f, hbpos, hcop, hquartic⟩, hf_lt_N⟩

private lemma normalizedEisensteinBad_second_pos {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    0 < N :=
  lt_trans h.1 h.2.1

private lemma normalizedEisensteinBad_sq_ne {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    A ^ 2 ≠ N ^ 2 := by
  have hApos : 0 < A := h.1
  have hAltN : A < N := h.2.1
  have hdiffpos : 0 < N - A := by
    linarith
  have hsumpos : 0 < N + A := by
    have hNpos : 0 < N := lt_trans hApos hAltN
    linarith
  intro hsq
  have hfactor : N ^ 2 - A ^ 2 = (N - A) * (N + A) := by
    ring
  have hdiffsqpos : 0 < N ^ 2 - A ^ 2 := by
    rw [hfactor]
    exact mul_pos hdiffpos hsumpos
  have hzero : N ^ 2 - A ^ 2 = 0 := by
    rw [hsq]
    ring
  linarith

/-- A normalized bad triple is a positive primitive unordered bad triple. -/
theorem positivePrimitiveEisensteinBadUnordered_of_normalized {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    PositivePrimitiveEisensteinBadUnordered A N S := by
  have hsqne : A ^ 2 ≠ N ^ 2 := normalizedEisensteinBad_sq_ne h
  rcases h with ⟨hApos, hAltN, hSpos, hcop, heq⟩
  have hNpos : 0 < N := lt_trans hApos hAltN
  exact ⟨hApos, hNpos, hSpos, hcop, hsqne, heq⟩

/-- Swapping the two square sides preserves the unordered bad condition. -/
theorem positivePrimitiveEisensteinBadUnordered_swap_of_normalized {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    PositivePrimitiveEisensteinBadUnordered N A S := by
  have hsqne : A ^ 2 ≠ N ^ 2 := normalizedEisensteinBad_sq_ne h
  rcases h with ⟨hApos, hAltN, hSpos, hcop, heq⟩
  have hNpos : 0 < N := lt_trans hApos hAltN
  refine ⟨hNpos, hApos, hSpos, hcop.symm, ?_, ?_⟩
  · intro hsqswap
    exact hsqne hsqswap.symm
  · calc
      S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 := heq
      _ = N ^ 4 - N ^ 2 * A ^ 2 + A ^ 4 := by ring

private lemma normalizedEisensteinBad_not_unit {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    ¬ (A = 1 ∧ N = 1 ∧ S = 1) := by
  intro hunit
  rcases hunit with ⟨hA, hN, _hS⟩
  have hlt : A < N := h.2.1
  rw [hA, hN] at hlt
  exact (lt_irrefl (1 : ℤ)) hlt

private lemma normalizedEisensteinBad_not_swap_unit {A N S : ℤ}
    (h : NormalizedEisensteinBad A N S) :
    ¬ (N = 1 ∧ A = 1 ∧ S = 1) := by
  intro hunit
  rcases hunit with ⟨hN, hA, _hS⟩
  have hlt : A < N := h.2.1
  rw [hA, hN] at hlt
  exact (lt_irrefl (1 : ℤ)) hlt

/-- Assemble normalized descent from the parametrization and branch residuals. -/
theorem normalizedDescentStatement_from_branches
    (hParam : NormalizedBadParamStatement)
    (hSqDesc : DescentFromBranchUnorderedStatement)
    (hDivDesc : DividedSquareBranchUnitOrDescendsStatement) :
    NormalizedDescentStatement := by
  intro A N S hnorm
  have hAltN : A < N := hnorm.2.1
  have hunord : PositivePrimitiveEisensteinBadUnordered A N S :=
    positivePrimitiveEisensteinBadUnordered_of_normalized hnorm
  have hswap : PositivePrimitiveEisensteinBadUnordered N A S :=
    positivePrimitiveEisensteinBadUnordered_swap_of_normalized hnorm
  rcases hParam hnorm with ⟨m, n, hcases⟩
  rcases hcases with hSq | hSqSwap | hDiv | hDivSwap
  · exact hSqDesc hunord hSq
  · rcases hSqDesc hswap hSqSwap with ⟨A', N', S', hnorm', hlt⟩
    exact ⟨A', N', S', hnorm', lt_trans hlt hAltN⟩
  · rcases hDivDesc hunord hDiv with hunit | hdescent
    · exact False.elim (normalizedEisensteinBad_not_unit hnorm hunit)
    · exact hdescent
  · rcases hDivDesc hswap hDivSwap with hunit | hdescent
    · exact False.elim (normalizedEisensteinBad_not_swap_unit hnorm hunit)
    · rcases hdescent with ⟨A', N', S', hnorm', hlt⟩
      exact ⟨A', N', S', hnorm', lt_trans hlt hAltN⟩

/-- Infinite descent on the positive second coordinate, implemented via
`Nat.find`. -/
theorem notNormalizedBad_of_descent
    (hDescent : NormalizedDescentStatement) :
    NotNormalizedBadStatement := by
  classical
  rintro ⟨A, N, S, hnorm⟩
  let P : ℕ → Prop := fun k =>
    ∃ A N S : ℤ, NormalizedEisensteinBad A N S ∧ N.natAbs = k
  have hExists : ∃ k : ℕ, P k := by
    refine ⟨N.natAbs, ?_⟩
    dsimp [P]
    exact ⟨A, N, S, hnorm, rfl⟩
  have hFindSpec : P (Nat.find hExists) := Nat.find_spec hExists
  dsimp [P] at hFindSpec
  rcases hFindSpec with ⟨A0, N0, S0, hnorm0, hN0_find⟩
  rcases hDescent hnorm0 with ⟨A1, N1, S1, hnorm1, hlt⟩
  have hN0pos : 0 < N0 := normalizedEisensteinBad_second_pos hnorm0
  have hN1pos : 0 < N1 := normalizedEisensteinBad_second_pos hnorm1
  have hnatlt : N1.natAbs < N0.natAbs := by
    exact Int.natAbs_lt_natAbs_of_nonneg_of_lt (le_of_lt hN1pos) hlt
  have hPsmaller : P N1.natAbs := by
    dsimp [P]
    exact ⟨A1, N1, S1, hnorm1, rfl⟩
  have hmin_le : Nat.find hExists ≤ N1.natAbs :=
    Nat.find_min' hExists hPsmaller
  have hlt_find : N1.natAbs < Nat.find hExists := by
    rw [hN0_find] at hnatlt
    exact hnatlt
  exact (not_lt_of_ge hmin_le) hlt_find

/-- Final assembly: normalized bad reduction plus branch descent imply the
primitive theorem. -/
theorem intQuarticEisensteinPrimitiveFromDescentStatement :
    IntQuarticEisensteinPrimitiveFromDescentStatement := by
  intro hNormalizedOfBad hParam hSqDesc hDivDesc
  have hNormDesc : NormalizedDescentStatement :=
    normalizedDescentStatement_from_branches hParam hSqDesc hDivDesc
  have hNoNorm : NotNormalizedBadStatement :=
    notNormalizedBad_of_descent hNormDesc
  intro A N S hcop hNne heq
  by_cases hA0 : A = 0
  · exact Or.inl hA0
  · by_cases hsq : A ^ 2 = N ^ 2
    · exact Or.inr hsq
    · exfalso
      have hbad : EisensteinQuarticBad A N S :=
        ⟨hcop, hA0, hNne, hsq, heq⟩
      exact hNoNorm (hNormalizedOfBad hbad)

/-- A rational square that is an integer is an integer square. -/
theorem intSquare_of_ratSquare_int : IntSquareOfRatSquareInt := by
  intro q m h
  have hsQ : IsSquare (m : ℚ) := by
    rw [← h]
    exact ⟨q, by ring⟩
  have hsZ : IsSquare m := Rat.isSquare_intCast_iff.mp hsQ
  rcases hsZ with ⟨z, hz⟩
  exact ⟨z, by simpa [sq] using hz.symm⟩

/-- Represent a rational pair as `t=A/N`, `s=S/N²` with a common nonzero
integer denominator. -/
theorem rat_pair_as_num_over_common_square_den
    (t s : ℚ) :
    ∃ A N S : ℤ,
      N ≠ 0 ∧
      t = (A : ℚ) / (N : ℚ) ∧
      s = (S : ℚ) / (N : ℚ) ^ 2 := by
  let N : ℤ := (t.den : ℤ) * (s.den : ℤ)
  let A : ℤ := t.num * (s.den : ℤ)
  let S : ℤ := s.num * (t.den : ℤ) ^ 2 * (s.den : ℤ)
  refine ⟨A, N, S, ?_, ?_, ?_⟩
  · dsimp [N]
    exact mul_ne_zero
      (Int.natCast_ne_zero.mpr t.den_ne_zero)
      (Int.natCast_ne_zero.mpr s.den_ne_zero)
  · dsimp [A, N]
    calc
      t = (t.num : ℚ) / (t.den : ℚ) := (Rat.num_div_den t).symm
      _ = ((t.num * (s.den : ℤ) : ℤ) : ℚ) /
          (((t.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ) := by
        field_simp
          [Int.natCast_ne_zero.mpr t.den_ne_zero,
           Int.natCast_ne_zero.mpr s.den_ne_zero]
        push_cast
        ring
  · dsimp [S, N]
    calc
      s = (s.num : ℚ) / (s.den : ℚ) := (Rat.num_div_den s).symm
      _ = ((s.num * (t.den : ℤ) ^ 2 * (s.den : ℤ) : ℤ) : ℚ) /
          ((((t.den : ℤ) * (s.den : ℤ) : ℤ) : ℚ) ^ 2) := by
        field_simp
          [Int.natCast_ne_zero.mpr t.den_ne_zero,
           Int.natCast_ne_zero.mpr s.den_ne_zero]
        push_cast
        ring

/-- Clear denominators in the rational Eisenstein quartic once a common
square-denominator representation has been chosen. -/
theorem int_eisenstein_eq_of_rat_repr {A N S : ℤ}
    (hN : N ≠ 0)
    {t s : ℚ}
    (ht : t = (A : ℚ) / (N : ℚ))
    (hs : s = (S : ℚ) / (N : ℚ) ^ 2)
    (h : s ^ 2 = t ^ 4 - t ^ 2 + 1) :
    S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 := by
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hq :
      (S : ℚ) ^ 2 =
        (A : ℚ) ^ 4 - (A : ℚ) ^ 2 * (N : ℚ) ^ 2 + (N : ℚ) ^ 4 := by
    rw [ht, hs] at h
    field_simp [hNq] at h
    ring_nf at h ⊢
    exact h
  exact_mod_cast hq

/-- Clear a rational Eisenstein quartic point to a primitive integer
homogeneous point using `t.num/t.den`. -/
theorem ratQuartic_to_primitive_int : RatQuarticToPrimitiveInt := by
  intro t s h
  let A : ℤ := t.num
  let N : ℤ := (t.den : ℤ)
  let P : ℤ := A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4
  have hN : N ≠ 0 := by
    dsimp [N]
    exact Int.natCast_ne_zero.mpr t.den_ne_zero
  have ht : t = (A : ℚ) / (N : ℚ) := by
    dsimp [A, N]
    have hden : (((t.den : ℤ) : ℚ) = (t.den : ℚ)) := by norm_num
    rw [hden]
    exact (Rat.num_div_den t).symm
  have hq : (s * (N : ℚ) ^ 2) ^ 2 = (P : ℚ) := by
    dsimp [A, N, P]
    have hNq : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
    have hden : (((t.den : ℤ) : ℚ) = (t.den : ℚ)) := by norm_num
    have hq_nat :
        (s * (t.den : ℚ) ^ 2) ^ 2 =
          (t.num : ℚ) ^ 4 - (t.num : ℚ) ^ 2 * (t.den : ℚ) ^ 2 +
            (t.den : ℚ) ^ 4 := by
      rw [← Rat.num_div_den t] at h
      calc
        (s * (t.den : ℚ) ^ 2) ^ 2 =
            (s ^ 2) * (t.den : ℚ) ^ 4 := by ring
        _ = (((t.num : ℚ) / (t.den : ℚ)) ^ 4 -
              ((t.num : ℚ) / (t.den : ℚ)) ^ 2 + 1) *
            (t.den : ℚ) ^ 4 := by rw [h]
        _ = (t.num : ℚ) ^ 4 - (t.num : ℚ) ^ 2 * (t.den : ℚ) ^ 2 +
            (t.den : ℚ) ^ 4 := by
          field_simp [hNq]
    simpa [hden] using hq_nat
  obtain ⟨S, hS⟩ := intSquare_of_ratSquare_int hq
  refine ⟨A, N, S, ?_, hN, ht, hS⟩
  rw [Int.isCoprime_iff_nat_coprime]
  dsimp [A, N]
  simpa [Int.natAbs_natCast] using t.reduced

/-- The homogeneous integer obstruction implies the rational Eisenstein
quartic obstruction. -/
theorem ratQuarticEisensteinDegenerate_of_int
    (hZ : IntQuarticEisensteinDegenerate) :
    RatQuarticEisensteinDegenerate := by
  intro t s h
  obtain ⟨A, N, S, hN, ht, hs⟩ := rat_pair_as_num_over_common_square_den t s
  have hInt : S ^ 2 = A ^ 4 - A ^ 2 * N ^ 2 + N ^ 4 :=
    int_eisenstein_eq_of_rat_repr hN ht hs h
  rcases hZ hN hInt with hA0 | hA2
  · left
    have hA0q : (A : ℚ) = 0 := by exact_mod_cast hA0
    rw [ht, hA0q]
    simp
  · right
    have hA2q : (A : ℚ) ^ 2 = (N : ℚ) ^ 2 := by exact_mod_cast hA2
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    rw [ht]
    calc
      ((A : ℚ) / (N : ℚ)) ^ 2 = (A : ℚ) ^ 2 / (N : ℚ) ^ 2 := by ring
      _ = (N : ℚ) ^ 2 / (N : ℚ) ^ 2 := by rw [hA2q]
      _ = 1 := div_self (pow_ne_zero 2 hNq)

/-- The primitive homogeneous integer obstruction already implies the rational
Eisenstein quartic obstruction, because rational points clear to primitive
integer points via `t.num/t.den`. -/
theorem ratQuarticEisensteinDegenerate_of_primitive
    (hZ : IntQuarticEisensteinPrimitive) :
    RatQuarticEisensteinDegenerate := by
  intro t s h
  obtain ⟨A, N, S, hcop, hN, ht, hInt⟩ := ratQuartic_to_primitive_int h
  rcases hZ hcop hN hInt with hA0 | hA2
  · left
    have hA0q : (A : ℚ) = 0 := by exact_mod_cast hA0
    rw [ht, hA0q]
    simp
  · right
    have hA2q : (A : ℚ) ^ 2 = (N : ℚ) ^ 2 := by exact_mod_cast hA2
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    rw [ht]
    calc
      ((A : ℚ) / (N : ℚ)) ^ 2 = (A : ℚ) ^ 2 / (N : ℚ) ^ 2 := by ring
      _ = (N : ℚ) ^ 2 / (N : ℚ) ^ 2 := by rw [hA2q]
      _ = 1 := div_self (pow_ne_zero 2 hNq)

end MazurProof.RationalPointsN12
