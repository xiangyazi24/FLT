import FLT.Assumptions.MazurProof.N13Jacobian
import FLT.Assumptions.MazurProof.SexticMumfordCantorReduction


set_option autoImplicit false
set_option relaxedAutoImplicit false


noncomputable section


open Polynomial
open scoped LaurentSeries nonZeroDivisors


namespace MazurProof.N13Arithmetic


private abbrev M13 : SexticMumford.Model ℚ :=
  N13Mumford.model ℚ


private abbrev H13 :
    Subgroup (SexticMumford.OrientedFrac M13) :=
  (SexticMumford.principalOriented M13
    (N13Infinity.positiveInfinityOrder ℚ)).range


private abbrev Q13 : Type :=
  SexticMumford.OrientedFrac M13 ⧸ H13


/-- The cubic polynomial part of the positive infinity branch. -/
private def s13 : ℚ[X] :=
  N13MumfordInfinityBalance.sqrtInfinity


/-- The explicit rational function `Y - s(X)`. -/
def dbFn13 : RatFun13ˣ :=
  SexticMumford.ySubFunctionUnit M13 s13


private def dM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint D)


private def bM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint B)


private def tM13 : SexticMumford.Mumford M13 :=
  SexticMumford.pointMumford M13 (point13EquivCurvePoint T)


@[simp] private theorem dM13_u :
    dM13.u = (X : ℚ[X]) := by
  change X - Polynomial.C (0 : ℚ) = X
  simp


@[simp] private theorem dM13_v :
    dM13.v = (-1 : ℚ[X]) := by
  change Polynomial.C (-1 : ℚ) = (-1 : ℚ[X])
  norm_num


@[simp] private theorem dM13_nInf :
    dM13.nInf = 0 := by
  rfl


@[simp] private theorem bM13_u :
    bM13.u = (X + 1 : ℚ[X]) := by
  change X - Polynomial.C (-1 : ℚ) = X + 1
  simp


@[simp] private theorem bM13_v :
    bM13.v = (-1 : ℚ[X]) := by
  change Polynomial.C (-1 : ℚ) = (-1 : ℚ[X])
  norm_num


@[simp] private theorem bM13_nInf :
    bM13.nInf = 0 := by
  rfl


@[simp] private theorem tM13_u :
    tM13.u = (1 : ℚ[X]) := by
  rfl


@[simp] private theorem tM13_v :
    tM13.v = (0 : ℚ[X]) := by
  rfl


@[simp] private theorem tM13_nInf :
    tM13.nInf = 0 := by
  rfl


/-! ## The finite principal ideal -/


private def quarter13 : ℚ[X] :=
  Polynomial.C (1 / 4 : ℚ)


private theorem four_mul_quarter13 :
    (4 : ℚ[X]) * quarter13 = 1 := by
  change Polynomial.C (4 : ℚ) * Polynomial.C (1 / 4 : ℚ) = Polynomial.C (1 : ℚ)
  rw [← C_mul]
  norm_num


private theorem X_dvd_s13_sub_neg_one :
    (X : ℚ[X]) ∣ s13 - (-1 : ℚ[X]) := by
  refine ⟨(X + 1) ^ 2, ?_⟩
  unfold s13 N13MumfordInfinityBalance.sqrtInfinity
  ring


private theorem X_add_one_dvd_s13_sub_neg_one :
    (X + 1 : ℚ[X]) ∣ s13 - (-1 : ℚ[X]) := by
  refine ⟨X * (X + 1), ?_⟩
  unfold s13 N13MumfordInfinityBalance.sqrtInfinity
  ring


private theorem scaled_B_ideal :
    SexticMumford.mumfordIdeal M13
        (4 * (X + 1 : ℚ[X])) s13 =
      SexticMumford.mumfordIdeal M13
        (X + 1 : ℚ[X]) s13 := by
  apply SexticMumford.mumfordIdeal_eq_of_dvd_dvd
  · refine ⟨quarter13, ?_⟩
    calc
      (X + 1 : ℚ[X]) = 1 * (X + 1) := by ring
      _ = ((4 : ℚ[X]) * quarter13) * (X + 1) := by
        rw [four_mul_quarter13]
      _ = (4 * (X + 1)) * quarter13 := by ring
  · refine ⟨(4 : ℚ[X]), ?_⟩
    ring


private theorem db_curve_factor :
    M13.f - s13 ^ 2 =
      (X : ℚ[X]) * (4 * (X + 1 : ℚ[X])) := by
  rw [N13Mumford.model_f]
  rw [show s13 =
      (N13MumfordInfinityBalance.sqrtInfinity : ℚ[X]) from rfl,
    N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq]
  ring


private theorem db_bezout :
    ∃ a b c : ℚ[X],
      a * X + b * (2 * s13) +
          c * (4 * (X + 1)) = 1 := by
  have hq :
      quarter13 * (4 : ℚ[X]) = 1 := by
    simpa [mul_comm] using four_mul_quarter13
  refine ⟨-1, 0, quarter13, ?_⟩
  calc
    (-1 : ℚ[X]) * X + 0 * (2 * s13) +
          quarter13 * (4 * (X + 1)) =
        -X + (quarter13 * 4) * (X + 1) := by
          ring
    _ = -X + (X + 1) := by
      rw [hq, one_mul]
    _ = 1 := by ring


private theorem db_point_ideal_mul :
    SexticMumford.mumfordIdeal M13
          dM13.toSemi.u dM13.toSemi.v *
        SexticMumford.mumfordIdeal M13
          bM13.toSemi.u bM13.toSemi.v =
      Ideal.span
        ({SexticMumford.ySubClass M13 s13} :
          Set (N13Mumford.CoordinateRing ℚ)) := by
  simp only [SexticMumford.toSemi_u, SexticMumford.toSemi_v,
    dM13_u, dM13_v, bM13_u, bM13_v]
  calc
    SexticMumford.mumfordIdeal M13 X (-1) *
          SexticMumford.mumfordIdeal M13 (X + 1) (-1) =
        SexticMumford.mumfordIdeal M13 X s13 *
          SexticMumford.mumfordIdeal M13 (X + 1) s13 := by
            rw [← SexticMumford.mumfordIdeal_eq_of_dvd_sub
                  M13 X (-1) s13 X_dvd_s13_sub_neg_one,
              ← SexticMumford.mumfordIdeal_eq_of_dvd_sub
                  M13 (X + 1) (-1) s13
                    X_add_one_dvd_s13_sub_neg_one]
    _ =
        SexticMumford.mumfordIdeal M13 X s13 *
          SexticMumford.mumfordIdeal M13
            (4 * (X + 1)) s13 := by
              rw [scaled_B_ideal]
    _ =
        Ideal.span
          ({SexticMumford.ySubClass M13 s13} :
            Set (N13Mumford.CoordinateRing ℚ)) := by
              exact SexticMumford.mumfordIdeal_mul_cantor
                M13
                (X : ℚ[X])
                (4 * (X + 1 : ℚ[X]))
                s13
                db_curve_factor
                db_bezout


private theorem dbFn13_finite_principal :
    SexticMumford.mumfordIdealUnit M13 dM13.toSemi *
        SexticMumford.mumfordIdealUnit M13 bM13.toSemi =
      toPrincipalIdeal
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ) dbFn13 := by
  apply Units.ext
  simp only [Units.val_mul,
    SexticMumford.coe_mumfordIdealUnit,
    coe_toPrincipalIdeal, dbFn13,
    SexticMumford.coe_ySubFunctionUnit]
  rw [← FractionalIdeal.coeIdeal_mul,
    db_point_ideal_mul,
    FractionalIdeal.coeIdeal_span_singleton]


/-! ## Exact orders at the two infinity branches -/


private def z13 : N13Mumford.SemiMumford ℚ :=
  (SexticMumford.zero M13).toSemi


private theorem z13_deg :
    z13.u.natDegree ≤ 2 := by
  simp [z13]


private theorem plusLift_z13 :
    N13MumfordInfinityBalance.plusLift z13 = s13 := by
  simp [z13, s13,
    N13MumfordInfinityBalance.plusLift,
    N13MumfordInfinityBalance.plusRemainder]


private theorem plusFactor_z13 :
    N13MumfordInfinityBalance.plusFactor z13 =
      (4 * X * (X + 1) : ℚ[X]) := by
  have h :=
    N13MumfordInfinityBalance.plusFactor_spec z13
  rw [plusLift_z13] at h
  simp only [z13, SexticMumford.toSemi_u,
    SexticMumford.zero_u, one_mul] at h
  have hs :
      N13Mumford.f ℚ - s13 ^ 2 =
        (4 * X * (X + 1) : ℚ[X]) := by
    simpa [s13] using
      (N13MumfordInfinityBalance.f_sub_sqrtInfinity_sq
        (K := ℚ))
  exact h.symm.trans hs


private theorem plusFactor_z13_natDegree :
    (N13MumfordInfinityBalance.plusFactor z13).natDegree = 2 := by
  rw [plusFactor_z13]
  compute_degree!


private theorem db_positive_order :
    (N13Infinity.coordinateToLaurent ℚ
      (SexticMumford.ySubClass M13 s13)).order = 1 := by
  have h :=
    N13MumfordInfinityBalance.plusYSub_plus_order
      z13 z13_deg
  rw [plusLift_z13, plusFactor_z13_natDegree] at h
  simpa [z13] using h


private theorem db_negative_order :
    (N13InfinityMinus.coordinateToLaurentMinus ℚ
      (SexticMumford.ySubClass M13 s13)).order = -3 := by
  have h :=
    N13MumfordInfinityBalance.plusYSub_minus_order
      z13 z13_deg
  rw [plusLift_z13] at h
  exact h


private theorem dbFn13_ordPlus :
    Multiplicative.toAdd
        ((N13Infinity.positiveInfinityOrder ℚ).ordPlus dbFn13) =
      1 := by
  rw [dbFn13,
    N13MumfordInfinityBalance.ordPlus_ySubFunctionUnit]
  exact db_positive_order


private theorem dbFn13_ordMinus :
    Multiplicative.toAdd
        ((N13InfinityMinus.negativeInfinityOrder ℚ).ordPlus dbFn13) =
      -3 := by
  change
    (N13InfinityMinus.functionFieldToLaurentMinus ℚ
      (algebraMap
        (N13Mumford.CoordinateRing ℚ)
        (N13Mumford.FunctionField ℚ)
        (SexticMumford.ySubClass M13 s13))).order = -3
  rw [N13InfinityMinus.functionFieldToLaurentMinus_algebraMap]
  exact db_negative_order


/-! ## Pass the principal divisor to the oriented Picard quotient -/


private theorem tM13_idealUnit_one :
    SexticMumford.mumfordIdealUnit M13 tM13.toSemi = 1 := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal M13 1 0 :
        FractionalIdeal
          (N13Mumford.CoordinateRing ℚ)⁰
          (N13Mumford.FunctionField ℚ)) = 1
  have hz := SexticMumford.zero_mumfordIdeal M13
  change SexticMumford.mumfordIdeal M13 1 0 = ⊤ at hz
  rw [hz]
  rfl


private theorem db_mumfordRaw_relation :
    SexticMumford.mumfordRaw M13 dM13 *
        SexticMumford.mumfordRaw M13 bM13 =
      SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) dbFn13 *
        (SexticMumford.mumfordRaw M13 tM13) ^ 3 := by
  apply Prod.ext
  · change
      SexticMumford.mumfordIdealUnit M13 dM13.toSemi *
          SexticMumford.mumfordIdealUnit M13 bM13.toSemi =
        toPrincipalIdeal
            (N13Mumford.CoordinateRing ℚ)
            (N13Mumford.FunctionField ℚ) dbFn13 *
          (SexticMumford.mumfordIdealUnit M13 tM13.toSemi) ^ 3
    rw [tM13_idealUnit_one, one_pow, mul_one]
    exact dbFn13_finite_principal
  · have hOrd :
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus dbFn13 =
          Multiplicative.ofAdd (1 : ℤ) := by
      simpa using
        congrArg Multiplicative.ofAdd dbFn13_ordPlus
    change
      Multiplicative.ofAdd ((dM13.nInf : ℤ) - 1) *
          Multiplicative.ofAdd ((bM13.nInf : ℤ) - 1) =
        (N13Infinity.positiveInfinityOrder ℚ).ordPlus dbFn13 *
          (Multiplicative.ofAdd ((tM13.nInf : ℤ) - 1)) ^ 3
    rw [hOrd, dM13_nInf, bM13_nInf, tM13_nInf]
    change
      (-1 : ℤ) + (-1) =
        1 + (3 : ℕ) • (-1 : ℤ)
    norm_num


private def raw13 (P : Point13) :
    SexticMumford.OrientedFrac M13 :=
  SexticMumford.mumfordRaw M13
    (SexticMumford.pointMumford M13
      (point13EquivCurvePoint P))


private theorem db_raw_relation :
    raw13 D * raw13 B =
      SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) dbFn13 *
        (raw13 T) ^ 3 := by
  change
    SexticMumford.mumfordRaw M13 dM13 *
        SexticMumford.mumfordRaw M13 bM13 =
      SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) dbFn13 *
        (SexticMumford.mumfordRaw M13 tM13) ^ 3
  exact db_mumfordRaw_relation


private theorem db_principal_mk_eq_one :
    QuotientGroup.mk' H13
        (SexticMumford.principalOriented M13
          (N13Infinity.positiveInfinityOrder ℚ) dbFn13) =
      1 := by
  rw [QuotientGroup.mk'_apply]
  exact
    (QuotientGroup.eq_one_iff
      (SexticMumford.principalOriented M13
        (N13Infinity.positiveInfinityOrder ℚ) dbFn13)).2
      (MonoidHom.mem_range.mpr ⟨dbFn13, rfl⟩)


private theorem db_quotient_relation :
    QuotientGroup.mk' H13 (raw13 D) *
        QuotientGroup.mk' H13 (raw13 B) =
      (QuotientGroup.mk' H13 (raw13 T)) ^ 3 := by
  rw [← map_mul, db_raw_relation, map_mul,
    db_principal_mk_eq_one, map_pow]
  exact one_mul (M := Q13) _


private theorem AJ13_eq_raw (P : Point13) :
    AJ13 P =
      Additive.ofMul (QuotientGroup.mk' H13 (raw13 P)) := by
  rfl


private theorem ofMul_add13 (a b : Q13) :
    (Additive.ofMul a : J13) + Additive.ofMul b =
      Additive.ofMul (a * b) := by
  rfl


private theorem three_nsmul_ofMul13 (a : Q13) :
    3 • (Additive.ofMul a : J13) =
      Additive.ofMul (a ^ 3) := by
  rfl


/-- The cusp relation supplied by the principal divisor
    `div(Y-s)=D+B+O-3T`. -/
theorem AJ13_D_add_B_eq_three_T :
    AJ13 D + AJ13 B = 3 • AJ13 T := by
  rw [AJ13_eq_raw D, AJ13_eq_raw B, AJ13_eq_raw T]
  simpa only [ofMul_add13, three_nsmul_ofMul13] using
    congrArg Additive.ofMul db_quotient_relation


end MazurProof.N13Arithmetic
