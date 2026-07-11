import FLT.Assumptions.MazurProof.RationalPointsN12
import FLT.Assumptions.MazurProof.N12E1CoverResiduals
import FLT.Assumptions.MazurProof.N12E1FullCoverExtraction

/-!
# Downstream bridge from E1 full-cover data to N=12 rational boundaries

This file keeps the full-cover extraction interface separate from the
Eisenstein quartic descent.  The only remaining arithmetic input here is the
elimination of nonzero-`Y` full-cover integer data.
-/

namespace MazurProof.RationalPointsN12

/-- Residual full-cover enumeration/elimination layer: once a nonzero-`Y`
point on `E1` has full-cover integer data, its `X`-coordinate is one of the
two non-torsion affine `X`-coordinates in the final list. -/
def E1FullCoverIntDataEliminationStatement : Prop :=
  ∀ {X Y : ℚ},
    E1FullCoverCurve X Y →
    Y ≠ 0 →
    E1FullCoverIntData X Y →
    X = -1 ∨ X = 3

/-- Core residual form of the nonzero-`Y` full-cover elimination.  This is the
target left after unpacking `E1FullCoverIntData`. -/
def E1CoverIntDataEliminationCoreStatement : Prop :=
  ∀ {X : ℚ} {d0 d1 d3 A B C T : ℤ},
    InS23 d0 →
    InS23 d1 →
    InS23 d3 →
    ProductSquareclassCondition d0 d1 d3 →
    T ≠ 0 →
    A ≠ 0 →
    B ≠ 0 →
    C ≠ 0 →
    PrimitiveInt4 A B C T →
    X = (d0 : ℚ) * (((A : ℚ) / (T : ℚ)) ^ 2) →
    X - 1 = (d1 : ℚ) * (((B : ℚ) / (T : ℚ)) ^ 2) →
    X + 3 = (d3 : ℚ) * (((C : ℚ) / (T : ℚ)) ^ 2) →
    CoverInt d0 d1 d3 A B C T →
    X = -1 ∨ X = 3

/-- Finite squareclass/local-obstruction residual: any primitive integer
full-cover data must lie in one of the four global residual cover classes. -/
def E1CoverIntSurvivingTriplesStatement : Prop :=
  ∀ {d0 d1 d3 A B C T : ℤ},
    InS23 d0 →
    InS23 d1 →
    InS23 d3 →
    ProductSquareclassCondition d0 d1 d3 →
    T ≠ 0 →
    A ≠ 0 →
    B ≠ 0 →
    C ≠ 0 →
    PrimitiveInt4 A B C T →
    CoverInt d0 d1 d3 A B C T →
    (d0 = 3 ∧ d1 = 2 ∧ d3 = 6) ∨
      (d0 = -1 ∧ d1 = -2 ∧ d3 = 2) ∨
        (d0 = 1 ∧ d1 = 1 ∧ d3 = 1) ∨
          (d0 = -3 ∧ d1 = -1 ∧ d3 = 3)

/-- The finite `2`-adic enumeration layer before real-sign cleanup. -/
def E1CoverIntTwoAdicSurvivorsStatement : Prop :=
  ∀ {d0 d1 d3 A B C T : ℤ},
    InS23 d0 →
    InS23 d1 →
    InS23 d3 →
    ProductSquareclassCondition d0 d1 d3 →
    T ≠ 0 →
    A ≠ 0 →
    B ≠ 0 →
    C ≠ 0 →
    PrimitiveInt4 A B C T →
    CoverInt d0 d1 d3 A B C T →
    (d0 = 1 ∧ d1 = 1 ∧ d3 = 1) ∨
      (d0 = 1 ∧ d1 = -3 ∧ d3 = -3) ∨
        (d0 = -1 ∧ d1 = -2 ∧ d3 = 2) ∨
          (d0 = -1 ∧ d1 = 6 ∧ d3 = -6) ∨
            (d0 = 3 ∧ d1 = 2 ∧ d3 = 6) ∨
              (d0 = 3 ∧ d1 = -6 ∧ d3 = -2) ∨
                (d0 = -3 ∧ d1 = -1 ∧ d3 = 3) ∨
                  (d0 = -3 ∧ d1 = 3 ∧ d3 = -1)

/-- Computable S23 list used by the finite certificate check. -/
def S23CertList : List ℤ := [1, -1, 2, -2, 3, -3, 6, -6]

def productSquareclassBool (d0 d1 d3 : ℤ) : Bool :=
  let p := d0 * d1 * d3
  p == 1 || p == 4 || p == 9 || p == 36

def twoAdicSurvivorBool (d0 d1 d3 : ℤ) : Bool :=
  (d0 == 1 && d1 == 1 && d3 == 1) ||
    (d0 == 1 && d1 == -3 && d3 == -3) ||
      (d0 == -1 && d1 == -2 && d3 == 2) ||
        (d0 == -1 && d1 == 6 && d3 == -6) ||
          (d0 == 3 && d1 == 2 && d3 == 6) ||
            (d0 == 3 && d1 == -6 && d3 == -2) ||
              (d0 == -3 && d1 == -1 && d3 == 3) ||
                (d0 == -3 && d1 == 3 && d3 == -1)

/-- The four quadratic residues modulo `16`.  Every integer square is congruent
mod `16` to one of these. -/
def sqRes16 : List ℤ := [0, 1, 4, 9]

/-- Computable primitive mod-`16` cover solubility test.  The full-cover
equations constrain `A, B, C, T` only through their squares modulo `16`, and
every square is `≡ 0, 1, 4, 9 [ZMOD 16]`, so it is enough to quantify the square
residues `a, b, c, t` over `sqRes16`, recording the parity of the underlying
value through `· % 2`.  This is a kernel-checkable reformulation of the full
`16 ^ 4` residue scan: with only `4 ^ 4` residue quadruples per triple it is
small enough for `decide`, so the certificate needs no `native_decide`. -/
def coverResidueSolBool (d0 d1 d3 : ℤ) : Bool :=
  sqRes16.any fun a =>
  sqRes16.any fun b =>
  sqRes16.any fun c =>
  sqRes16.any fun t =>
    (!(decide (a % 2 = 0) && decide (b % 2 = 0) &&
        decide (c % 2 = 0) && decide (t % 2 = 0))) &&
      decide ((d0 * a - d1 * b - t) % 16 = 0) &&
        decide ((d3 * c - d0 * a - 3 * t) % 16 = 0)

def twoAdicCertificateCheck : Bool :=
  S23CertList.all fun d0 =>
  S23CertList.all fun d1 =>
  S23CertList.all fun d3 =>
    if productSquareclassBool d0 d1 d3 then
      (! coverResidueSolBool d0 d1 d3) || twoAdicSurvivorBool d0 d1 d3
    else
      true

/- Kernel-checked finite certificate: among the `S23` triples with trivial
product squareclass, primitive mod-`16` solubility (quantified over the four
square residues) leaves only the eight listed two-adic survivors.  The whole
finite check is discharged by `decide`, i.e. by kernel reduction, so — unlike
the previous `native_decide` — no compiler sits in the trusted base. -/
set_option maxHeartbeats 0 in
-- `decide` reduces the finite check (`8 ^ 3` squareclass triples, each scanning
-- `4 ^ 4` square-residue quadruples) entirely in the kernel; this modest
-- computation still exceeds the default heartbeat budget during elaboration.
theorem twoAdicCertificateCheck_true :
    twoAdicCertificateCheck = true := by
  decide

set_option linter.flexible false in
set_option maxHeartbeats 800000 in
-- The proof is a finite split over the 512 S23 triples; the default heartbeat
-- limit is too low for the generated ground `norm_num` subgoals.
theorem productSquareclassBool_true_of_condition {d0 d1 d3 : ℤ}
    (hd0 : InS23 d0) (hd1 : InS23 d1) (hd3 : InS23 d3)
    (hprod : ProductSquareclassCondition d0 d1 d3) :
    productSquareclassBool d0 d1 d3 = true := by
  have hsquare : IsSquare (d0 * d1 * d3 : ℤ) := by
    rcases hprod with ⟨r, _hr, hsq⟩
    rw [← Rat.isSquare_intCast_iff]
    exact ⟨r, by simpa [sq] using hsq⟩
  simp [InS23, S23] at hd0 hd1 hd3
  rcases hd0 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hd1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hd3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | norm_num [productSquareclassBool]
          done
        | exfalso
          norm_num [IsSquare] at hsquare

theorem twoAdicSurvivorBool_true {d0 d1 d3 : ℤ}
    (h : twoAdicSurvivorBool d0 d1 d3 = true) :
      (d0 = 1 ∧ d1 = 1 ∧ d3 = 1) ∨
      (d0 = 1 ∧ d1 = -3 ∧ d3 = -3) ∨
      (d0 = -1 ∧ d1 = -2 ∧ d3 = 2) ∨
      (d0 = -1 ∧ d1 = 6 ∧ d3 = -6) ∨
      (d0 = 3 ∧ d1 = 2 ∧ d3 = 6) ∨
      (d0 = 3 ∧ d1 = -6 ∧ d3 = -2) ∨
      (d0 = -3 ∧ d1 = -1 ∧ d3 = 3) ∨
      (d0 = -3 ∧ d1 = 3 ∧ d3 = -1) := by
  unfold twoAdicSurvivorBool at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | h8
  · rcases h with h | h7
    · rcases h with h | h6
      · rcases h with h | h5
        · rcases h with h | h4
          · rcases h with h | h3
            · rcases h with h1 | h2
              · left
                exact ⟨h1.1.1, h1.1.2, h1.2⟩
              · right
                left
                exact ⟨h2.1.1, h2.1.2, h2.2⟩
            · right
              right
              left
              exact ⟨h3.1.1, h3.1.2, h3.2⟩
          · right
            right
            right
            left
            exact ⟨h4.1.1, h4.1.2, h4.2⟩
        · right
          right
          right
          right
          left
          exact ⟨h5.1.1, h5.1.2, h5.2⟩
      · right
        right
        right
        right
        right
        left
        exact ⟨h6.1.1, h6.1.2, h6.2⟩
    · right
      right
      right
      right
      right
      right
      left
      exact ⟨h7.1.1, h7.1.2, h7.2⟩
  · right
    right
    right
    right
    right
    right
    right
    exact ⟨h8.1.1, h8.1.2, h8.2⟩

/-- Every integer square is congruent modulo `16` to one of the four residues in
`sqRes16 = [0, 1, 4, 9]`. -/
theorem sq_emod16_mem_sqRes16 (x : ℤ) : x ^ 2 % 16 ∈ sqRes16 := by
  have hcong : (x % 16) ^ 2 % 16 = x ^ 2 % 16 := by
    have h := Int.ModEq.pow 2 (Int.mod_modEq x 16)
    unfold Int.ModEq at h
    exact h
  rw [← hcong]
  have hcases : x % 16 = 0 ∨ x % 16 = 1 ∨ x % 16 = 2 ∨ x % 16 = 3 ∨
      x % 16 = 4 ∨ x % 16 = 5 ∨ x % 16 = 6 ∨ x % 16 = 7 ∨ x % 16 = 8 ∨
      x % 16 = 9 ∨ x % 16 = 10 ∨ x % 16 = 11 ∨ x % 16 = 12 ∨ x % 16 = 13 ∨
      x % 16 = 14 ∨ x % 16 = 15 := by omega
  rcases hcases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] <;> decide

/-- If the square residue `x ^ 2 % 16` is even, then `x` itself is even.  This
transports the primitivity (not-all-even) hypothesis across the square-residue
reformulation of `coverResidueSolBool`. -/
theorem even_of_sq_emod16_emod2_zero {x : ℤ}
    (h : x ^ 2 % 16 % 2 = 0) : (2 : ℤ) ∣ x := by
  rw [Int.emod_emod_of_dvd (x ^ 2) (by norm_num : (2 : ℤ) ∣ 16)] at h
  exact Int.prime_two.dvd_of_dvd_pow (Int.dvd_of_emod_eq_zero h)

theorem coverResidueSolBool_true_of_coverInt_16
    {d0 d1 d3 A B C T : ℤ}
    (hprim : PrimitiveInt4 A B C T)
    (hcover : CoverInt d0 d1 d3 A B C T) :
    coverResidueSolBool d0 d1 d3 = true := by
  unfold coverResidueSolBool
  apply List.any_eq_true.mpr
  refine ⟨A ^ 2 % 16, sq_emod16_mem_sqRes16 A, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨B ^ 2 % 16, sq_emod16_mem_sqRes16 B, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨C ^ 2 % 16, sq_emod16_mem_sqRes16 C, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨T ^ 2 % 16, sq_emod16_mem_sqRes16 T, ?_⟩
  rcases hcover with ⟨h1, h2⟩
  have h1zero : d0 * A ^ 2 - d1 * B ^ 2 - T ^ 2 = 0 := by linarith
  have h2zero : d3 * C ^ 2 - d0 * A ^ 2 - 3 * T ^ 2 = 0 := by linarith
  have hAm : A ^ 2 % 16 ≡ A ^ 2 [ZMOD 16] := Int.mod_modEq _ _
  have hBm : B ^ 2 % 16 ≡ B ^ 2 [ZMOD 16] := Int.mod_modEq _ _
  have hCm : C ^ 2 % 16 ≡ C ^ 2 [ZMOD 16] := Int.mod_modEq _ _
  have hTm : T ^ 2 % 16 ≡ T ^ 2 [ZMOD 16] := Int.mod_modEq _ _
  have he1 :
      (d0 * (A ^ 2 % 16) - d1 * (B ^ 2 % 16) - T ^ 2 % 16) % 16 = 0 := by
    have hcong :
        d0 * (A ^ 2 % 16) - d1 * (B ^ 2 % 16) - T ^ 2 % 16
          ≡ d0 * A ^ 2 - d1 * B ^ 2 - T ^ 2 [ZMOD 16] :=
      ((hAm.mul_left d0).sub (hBm.mul_left d1)).sub hTm
    rw [h1zero] at hcong
    exact Int.dvd_iff_emod_eq_zero.mp (Int.modEq_zero_iff_dvd.mp hcong)
  have he2 :
      (d3 * (C ^ 2 % 16) - d0 * (A ^ 2 % 16) - 3 * (T ^ 2 % 16)) % 16 = 0 := by
    have hcong :
        d3 * (C ^ 2 % 16) - d0 * (A ^ 2 % 16) - 3 * (T ^ 2 % 16)
          ≡ d3 * C ^ 2 - d0 * A ^ 2 - 3 * T ^ 2 [ZMOD 16] :=
      ((hCm.mul_left d3).sub (hAm.mul_left d0)).sub (hTm.mul_left 3)
    rw [h2zero] at hcong
    exact Int.dvd_iff_emod_eq_zero.mp (Int.modEq_zero_iff_dvd.mp hcong)
  have hodd :
      (!(decide (A ^ 2 % 16 % 2 = 0) && decide (B ^ 2 % 16 % 2 = 0) &&
          decide (C ^ 2 % 16 % 2 = 0) && decide (T ^ 2 % 16 % 2 = 0))) = true := by
    rw [Bool.not_eq_true_eq_eq_false]
    apply Bool.eq_false_of_not_eq_true
    intro hall
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
    obtain ⟨⟨⟨hA, hB⟩, hC⟩, hT⟩ := hall
    exact hprim 2 Nat.prime_two
      ⟨even_of_sq_emod16_emod2_zero hA, even_of_sq_emod16_emod2_zero hB,
        even_of_sq_emod16_emod2_zero hC, even_of_sq_emod16_emod2_zero hT⟩
  rw [hodd, decide_eq_true he1, decide_eq_true he2]
  rfl

theorem s23_product_twoAdic_survivor_or_bad {d0 d1 d3 : ℤ}
    (hd0 : InS23 d0) (hd1 : InS23 d1) (hd3 : InS23 d3)
    (hprod : ProductSquareclassCondition d0 d1 d3) :
    twoAdicSurvivorBool d0 d1 d3 = true ∨
      coverResidueSolBool d0 d1 d3 = false := by
  have hmem0 : d0 ∈ S23CertList := by
    simpa [InS23, S23, S23CertList] using hd0
  have hmem1 : d1 ∈ S23CertList := by
    simpa [InS23, S23, S23CertList] using hd1
  have hmem3 : d3 ∈ S23CertList := by
    simpa [InS23, S23, S23CertList] using hd3
  have hprodBool := productSquareclassBool_true_of_condition hd0 hd1 hd3 hprod
  have h0 := (List.all_eq_true.mp twoAdicCertificateCheck_true) d0 hmem0
  have h1 := (List.all_eq_true.mp h0) d1 hmem1
  have h3 := (List.all_eq_true.mp h1) d3 hmem3
  rw [hprodBool] at h3
  simp only [ite_true, Bool.or_eq_true, Bool.not_eq_true_eq_eq_false] at h3
  rcases h3 with hbad | hsurv
  · right
    exact hbad
  · left
    exact hsurv

theorem e1CoverIntTwoAdicSurvivorsStatement_checked :
    E1CoverIntTwoAdicSurvivorsStatement := by
  intro d0 d1 d3 A B C T hd0 hd1 hd3 hprod _hT _hA _hB _hC hprim hcover
  have hloc : coverResidueSolBool d0 d1 d3 = true :=
    coverResidueSolBool_true_of_coverInt_16 hprim hcover
  rcases s23_product_twoAdic_survivor_or_bad hd0 hd1 hd3 hprod with hsurv | hbad
  · exact twoAdicSurvivorBool_true hsurv
  · rw [hloc] at hbad
    cases hbad

/-- The core integer-cover elimination residual implies the packaged
`E1FullCoverIntData` elimination residual. -/
theorem e1FullCoverIntDataElimination_of_core
    (hcore : E1CoverIntDataEliminationCoreStatement) :
    E1FullCoverIntDataEliminationStatement := by
  intro X Y _hcurve _hY hdata
  rcases hdata with
    ⟨d0, d1, d3, hd0, hd1, hd3, hprod, A, B, C, T,
      hT, hA, hB, hC, hprim, hX, hXm1, hXp3, hcover⟩
  exact hcore hd0 hd1 hd3 hprod hT hA hB hC hprim hX hXm1 hXp3 hcover

/-- Cast an integer full-cover equation to the rational cover interface used by
the residual cover wrappers. -/
theorem coverQ_of_coverInt {d0 d1 d3 A B C T : ℤ}
    (h : CoverInt d0 d1 d3 A B C T) :
    CoverQ d0 d1 d3 (A : ℚ) (B : ℚ) (C : ℚ) (T : ℚ) := by
  unfold CoverInt at h
  unfold CoverQ
  rcases h with ⟨h1, h2⟩
  constructor
  · exact_mod_cast h1
  · exact_mod_cast h2

/-- Integer form of the `(3,2,6)` residual cover collapse. -/
theorem coverInt_3_2_6_forces_X_eq_three
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℤ} {X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (3 : ℚ) * ((A : ℚ) / (T : ℚ)) ^ 2)
    (hcover : CoverInt 3 2 6 A B C T) :
    X = 3 := by
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  exact coverQ_3_2_6_forces_X_eq_three hAP hTq hX
    (coverQ_of_coverInt hcover)

/-- Integer form of the `(-1,-2,2)` residual cover collapse. -/
theorem coverInt_neg1_neg2_2_forces_X_eq_neg_one
    (hAP : FourRatSquaresAPConst)
    {A B C T : ℤ} {X : ℚ}
    (hT : T ≠ 0)
    (hX : X = (-1 : ℚ) * ((A : ℚ) / (T : ℚ)) ^ 2)
    (hcover : CoverInt (-1) (-2) 2 A B C T) :
    X = -1 := by
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  exact coverQ_neg1_neg2_2_forces_X_eq_neg_one hAP hTq hX
    (coverQ_of_coverInt hcover)

/-- Integer form of the `(1,1,1)` degenerate cover obstruction. -/
theorem coverInt_1_1_1_no_nonzero_of_doubleLeg
    (hDL : DoubleLegCoverDegenerate)
    {A B C T : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (hcover : CoverInt 1 1 1 A B C T) :
    False := by
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hCq : (C : ℚ) ≠ 0 := by exact_mod_cast hC
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  exact coverQ_1_1_1_no_nonzero_of_doubleLeg hDL hAq hBq hCq hTq
    (coverQ_of_coverInt hcover)

/-- Integer form of the `(-3,-1,3)` degenerate cover obstruction. -/
theorem coverInt_neg3_neg1_3_no_nonzero_of_doubleLeg
    (hDL : DoubleLegCoverDegenerate)
    {A B C T : ℤ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0)
    (hcover : CoverInt (-3) (-1) 3 A B C T) :
    False := by
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hCq : (C : ℚ) ≠ 0 := by exact_mod_cast hC
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT
  exact coverQ_neg3_neg1_3_no_nonzero_of_doubleLeg hDL hAq hBq hCq hTq
    (coverQ_of_coverInt hcover)

theorem coverInt_1_neg3_neg3_no_solution {A B C T : ℤ}
    (hT : T ≠ 0)
    (hcover : CoverInt 1 (-3) (-3) A B C T) :
    False := by
  unfold CoverInt at hcover
  rcases hcover with ⟨_, h2⟩
  ring_nf at h2
  nlinarith [sq_nonneg A, sq_nonneg C, sq_pos_of_ne_zero hT]

theorem coverInt_neg1_6_neg6_no_solution {A B C T : ℤ}
    (hT : T ≠ 0)
    (hcover : CoverInt (-1) 6 (-6) A B C T) :
    False := by
  unfold CoverInt at hcover
  rcases hcover with ⟨h1, _⟩
  ring_nf at h1
  nlinarith [sq_nonneg A, sq_nonneg B, sq_pos_of_ne_zero hT]

theorem coverInt_3_neg6_neg2_no_solution {A B C T : ℤ}
    (hT : T ≠ 0)
    (hcover : CoverInt 3 (-6) (-2) A B C T) :
    False := by
  unfold CoverInt at hcover
  rcases hcover with ⟨_, h2⟩
  ring_nf at h2
  nlinarith [sq_nonneg A, sq_nonneg C, sq_pos_of_ne_zero hT]

theorem coverInt_neg3_3_neg1_no_solution {A B C T : ℤ}
    (hT : T ≠ 0)
    (hcover : CoverInt (-3) 3 (-1) A B C T) :
    False := by
  unfold CoverInt at hcover
  rcases hcover with ⟨h1, _⟩
  ring_nf at h1
  nlinarith [sq_nonneg A, sq_nonneg B, sq_pos_of_ne_zero hT]

/-- The `2`-adic survivor list plus real-sign cleanup leaves exactly the four
global residual cover triples. -/
theorem e1CoverIntSurvivingTriples_of_twoAdicSurvivors
    (h2 : E1CoverIntTwoAdicSurvivorsStatement) :
    E1CoverIntSurvivingTriplesStatement := by
  intro d0 d1 d3 A B C T hd0 hd1 hd3 hprod hT hA hB hC hprim hcover
  rcases h2 hd0 hd1 hd3 hprod hT hA hB hC hprim hcover with
    h111 | h1m3m3 | hm1m22 | hm16m6 | h326 | h3m6m2 | hm3m13 | hm33m1
  · right
    right
    left
    exact h111
  · rcases h1m3m3 with ⟨rfl, rfl, rfl⟩
    exact False.elim (coverInt_1_neg3_neg3_no_solution hT hcover)
  · right
    left
    exact hm1m22
  · rcases hm16m6 with ⟨rfl, rfl, rfl⟩
    exact False.elim (coverInt_neg1_6_neg6_no_solution hT hcover)
  · left
    exact h326
  · rcases h3m6m2 with ⟨rfl, rfl, rfl⟩
    exact False.elim (coverInt_3_neg6_neg2_no_solution hT hcover)
  · right
    right
    right
    exact hm3m13
  · rcases hm33m1 with ⟨rfl, rfl, rfl⟩
    exact False.elim (coverInt_neg3_3_neg1_no_solution hT hcover)

theorem e1CoverIntSurvivingTriples_checked :
    E1CoverIntSurvivingTriplesStatement :=
  e1CoverIntSurvivingTriples_of_twoAdicSurvivors
    e1CoverIntTwoAdicSurvivorsStatement_checked

/-- The surviving-triples residual plus the two already-isolated arithmetic
inputs, four-square AP and double-leg, implies the core full-cover
elimination statement. -/
theorem e1CoverIntDataEliminationCore_of_survivingTriples
    (hAP : FourRatSquaresAPConst)
    (hDL : DoubleLegCoverDegenerate)
    (hsurv : E1CoverIntSurvivingTriplesStatement) :
    E1CoverIntDataEliminationCoreStatement := by
  intro X d0 d1 d3 A B C T hd0 hd1 hd3 hprod hT hA hB hC hprim hX
    _hXm1 _hXp3 hcover
  rcases hsurv hd0 hd1 hd3 hprod hT hA hB hC hprim hcover with
    h326 | hneg122 | h111 | hneg313
  · rcases h326 with ⟨rfl, rfl, rfl⟩
    exact Or.inr (coverInt_3_2_6_forces_X_eq_three hAP hT hX hcover)
  · rcases hneg122 with ⟨rfl, rfl, rfl⟩
    exact Or.inl (coverInt_neg1_neg2_2_forces_X_eq_neg_one hAP hT hX hcover)
  · rcases h111 with ⟨rfl, rfl, rfl⟩
    exact False.elim
      (coverInt_1_1_1_no_nonzero_of_doubleLeg hDL hA hB hC hT hcover)
  · rcases hneg313 with ⟨rfl, rfl, rfl⟩
    exact False.elim
      (coverInt_neg3_neg1_3_no_nonzero_of_doubleLeg hDL hA hB hC hT hcover)

/-- Finite surviving-triples enumeration, four-square AP, and double-leg imply
the packaged full-cover-data elimination residual. -/
theorem e1FullCoverIntDataElimination_of_survivingTriples
    (hAP : FourRatSquaresAPConst)
    (hDL : DoubleLegCoverDegenerate)
    (hsurv : E1CoverIntSurvivingTriplesStatement) :
    E1FullCoverIntDataEliminationStatement :=
  e1FullCoverIntDataElimination_of_core
    (e1CoverIntDataEliminationCore_of_survivingTriples hAP hDL hsurv)

theorem e1FullCoverIntDataElimination_checked
    (hAP : FourRatSquaresAPConst)
    (hDL : DoubleLegCoverDegenerate) :
    E1FullCoverIntDataEliminationStatement :=
  e1FullCoverIntDataElimination_of_survivingTriples hAP hDL
    e1CoverIntSurvivingTriples_checked

theorem e1FullCoverCurve_of_E1 {X Y : ℚ} (h : E1 X Y) :
    E1FullCoverCurve X Y := by
  simpa [E1, E1FullCoverCurve] using h

theorem E1_of_e1FullCoverCurve {X Y : ℚ} (h : E1FullCoverCurve X Y) :
    E1 X Y := by
  simpa [E1, E1FullCoverCurve] using h

private theorem e1_x_coordinate_of_y_zero {X Y : ℚ}
    (h : E1 X Y) (hY : Y = 0) :
    X = -3 ∨ X = 0 ∨ X = 1 := by
  have hprod : X * (X - 1) * (X + 3) = 0 := by
    simpa [E1, hY] using h.symm
  rcases mul_eq_zero.mp hprod with hleft | hneg3
  · rcases mul_eq_zero.mp hleft with hzero | hone
    · right
      left
      exact hzero
    · right
      right
      linarith
  · left
    linarith

/-- Full-cover extraction plus the nonzero-`Y` cover-data elimination residual
gives the finite `X`-coordinate classification on `E1`. -/
theorem e1XCoordinateClassification_of_fullCover
    (hextract : E1FullCoverSquareclassExtractionIntStatement)
    (helim : E1FullCoverIntDataEliminationStatement) :
    E1XCoordinateClassification := by
  intro X Y hE1
  by_cases hY : Y = 0
  · rcases e1_x_coordinate_of_y_zero hE1 hY with hneg3 | hzero | hone
    · left
      exact hneg3
    · right
      left
      exact hzero
    · right
      right
      left
      exact hone
  · have hcurve : E1FullCoverCurve X Y := e1FullCoverCurve_of_E1 hE1
    have hdata : E1FullCoverIntData X Y := hextract hcurve hY
    rcases helim hcurve hY hdata with hneg1 | hthree
    · right
      right
      right
      left
      exact hneg1
    · right
      right
      right
      right
      exact hthree

/-- Convert an `E1` `X`-coordinate classification into the `F_N12` boundary
form consumed by the Kubert bridge. -/
theorem F_N12_boundary_of_e1XCoordinateClassification
    (hE1x : E1XCoordinateClassification)
    {X Y : ℚ}
    (hF : F_N12_AffineEquation X Y) :
    F_N12_XBoundary X := by
  have hE1 : E1 X Y := by
    simpa [E1] using (F_N12_AffineEquation_factor_iff X Y).mp hF
  exact hE1x hE1

/-- Full-cover extraction plus cover-data elimination gives the `F_N12`
boundary directly. -/
theorem F_N12_boundary_of_fullCover
    (hextract : E1FullCoverSquareclassExtractionIntStatement)
    (helim : E1FullCoverIntDataEliminationStatement)
    {X Y : ℚ}
    (hF : F_N12_AffineEquation X Y) :
    F_N12_XBoundary X :=
  F_N12_boundary_of_e1XCoordinateClassification
    (e1XCoordinateClassification_of_fullCover hextract helim) hF

/-- Full-cover extraction plus cover-data elimination gives the original N=12
obstruction-curve degenerate boundary. -/
theorem E_N12_degenerate_boundary_of_fullCover
    (hextract : E1FullCoverSquareclassExtractionIntStatement)
    (helim : E1FullCoverIntDataEliminationStatement)
    (u w : ℚ)
    (h : MazurProof.E_N12_AffineEquation u w) :
    MazurProof.E_N12_DegenerateParameter u :=
  E_N12_degenerate_boundary_of_F_N12_boundary
    (F_N12_boundary_of_fullCover hextract helim) u w h

/-- The same full-cover boundary kills nontrivial square denominators on the
original N=12 obstruction curve. -/
theorem N12NoNontrivialSquareDenominatorResidual_of_fullCover
    (hextract : E1FullCoverSquareclassExtractionIntStatement)
    (helim : E1FullCoverIntDataEliminationStatement) :
    N12NoNontrivialSquareDenominatorResidual :=
  N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    (E_N12_degenerate_boundary_of_fullCover hextract helim)

/-- The same full-cover boundary gives the rational Eisenstein quartic
classification through the checked `E1`/`E24`/`C12` maps. -/
theorem ratQuarticEisensteinXClassification_of_fullCover
    (hextract : E1FullCoverSquareclassExtractionIntStatement)
    (helim : E1FullCoverIntDataEliminationStatement) :
    RatQuarticEisensteinXClassification :=
  ratQuarticEisensteinXClassification_of_e24_x
    (e24XCoordinateClassification_of_e1X
      (e1XCoordinateClassification_of_fullCover hextract helim))

end MazurProof.RationalPointsN12
