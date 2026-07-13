import FLT.Assumptions.MazurProof.N18RouteC_DualSurvivor
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The quadratic cyclotomic splitting field for the forward N18 descent

The constant-kernel isogeny becomes a Kummer isogeny over
`M = Q(zeta_9) = L(sqrt(-3))`.  This file fixes the embedding of the real
cubic field, complex conjugation, and the explicit quadratic basis.
-/

open Polynomial Module
open scoped NumberField

namespace MazurProof.N18RouteC.Cyclotomic

open FieldArithmetic

noncomputable section

instance : NeZero (9 : ℕ) := ⟨by norm_num⟩
instance : NeZero (9 : ℚ) := ⟨by norm_num⟩

abbrev M := CyclotomicField 9 ℚ
abbrev OM := NumberField.RingOfIntegers M

instance cycloM : IsCyclotomicExtension {9} ℚ M := by
  change IsCyclotomicExtension {9} ℚ (CyclotomicField 9 ℚ)
  exact CyclotomicField.isCyclotomicExtension (n := 9) (K := ℚ)

instance cmM : NumberField.IsCMField M :=
  IsCyclotomicExtension.Rat.isCMField (S := {9}) M
    ⟨9, Set.mem_singleton 9, by norm_num⟩

noncomputable def zeta : M := IsCyclotomicExtension.zeta 9 ℚ M

theorem zeta_primitive : IsPrimitiveRoot zeta 9 :=
  IsCyclotomicExtension.zeta_spec 9 ℚ M

theorem zeta_ne_zero : zeta ≠ 0 :=
  zeta_primitive.ne_zero (by norm_num)

theorem zeta_cubic_sum : zeta ^ 6 + zeta ^ 3 + 1 = 0 := by
  have hfac : (zeta ^ 3 - 1) * (zeta ^ 6 + zeta ^ 3 + 1) = 0 := by
    calc
      (zeta ^ 3 - 1) * (zeta ^ 6 + zeta ^ 3 + 1) = zeta ^ 9 - 1 := by ring
      _ = 0 := by rw [zeta_primitive.pow_eq_one]; ring
  exact (mul_eq_zero.mp hfac).resolve_left
    (sub_ne_zero.mpr <| zeta_primitive.pow_ne_one_of_pos_of_lt
      (by norm_num) (by norm_num))

noncomputable def aM : M := -(zeta + zeta⁻¹)
noncomputable def piM : M := aM - 1

theorem aM_cubic : aM ^ 3 = 3 * aM + 1 := by
  rw [aM]
  have hsum := zeta_cubic_sum
  have hz9 := zeta_primitive.pow_eq_one
  field_simp [zeta_ne_zero]
  ring_nf at hsum hz9 ⊢
  linear_combination -zeta ^ 3 * hsum + hz9

theorem piM_root : aeval piM cubicPoly = 0 := by
  rw [cubicPoly_eq]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
  unfold piM
  linear_combination aM_cubic

noncomputable def embedL : L →ₐ[ℚ] M :=
  AdjoinRoot.liftAlgHom cubicPoly (Algebra.ofId ℚ M) piM <| by
    simpa [aeval_def] using piM_root

local instance algebraLM : Algebra L M := embedL.toRingHom.toAlgebra

local instance scalarTowerQLM : IsScalarTower ℚ L M :=
  IsScalarTower.of_algebraMap_eq fun x ↦ (embedL.commutes x).symm

@[simp] theorem algebraMap_L_eq (x : L) : algebraMap L M x = embedL x := rfl

@[simp] theorem embedL_pi : embedL pi = piM := by
  change AdjoinRoot.liftAlgHom cubicPoly (Algebra.ofId ℚ M) piM _
      (AdjoinRoot.root cubicPoly) = piM
  rw [AdjoinRoot.liftAlgHom_root]

noncomputable def qM : M := 2 * zeta ^ 3 + 1

theorem qM_sq : qM ^ 2 = -3 := by
  unfold qM
  have hsum := zeta_cubic_sum
  ring_nf at hsum ⊢
  linear_combination 4 * hsum

theorem qM_ne_zero : qM ≠ 0 := by
  intro hq
  have hs := qM_sq
  rw [hq] at hs
  norm_num at hs

noncomputable def zetaUnit : OMˣ :=
  (IsPrimitiveRoot.isUnit
    zeta_primitive.toInteger_isPrimitiveRoot (by norm_num)).unit

@[simp] theorem zetaUnit_coe_M : ((zetaUnit : OM) : M) = zeta := rfl

noncomputable def zetaTorsion : NumberField.Units.torsion M :=
  ⟨zetaUnit, by
    rw [NumberField.Units.torsion, CommGroup.mem_torsion,
      isOfFinOrder_iff_pow_eq_one]
    refine ⟨9, by norm_num, ?_⟩
    ext
    simpa using zeta_primitive.pow_eq_one⟩

theorem complexConj_zeta :
    NumberField.IsCMField.complexConj M zeta = zeta⁻¹ := by
  simpa [zetaTorsion] using
    NumberField.IsCMField.complexConj_torsion M zetaTorsion

theorem complexConj_aM :
    NumberField.IsCMField.complexConj M aM = aM := by
  rw [aM, map_neg, map_add, complexConj_zeta, map_inv₀, complexConj_zeta]
  rw [inv_inv]
  ring

theorem complexConj_piM :
    NumberField.IsCMField.complexConj M piM = piM := by
  simp [piM, complexConj_aM]

theorem complexConj_qM :
    NumberField.IsCMField.complexConj M qM = -qM := by
  rw [qM, map_add, map_mul, map_pow, map_ofNat, map_one, complexConj_zeta]
  have hinv : (zeta⁻¹) ^ 3 = zeta ^ 6 := by
    field_simp [zeta_ne_zero]
    simpa using zeta_primitive.pow_eq_one.symm
  rw [hinv]
  linear_combination 2 * zeta_cubic_sum

theorem complexConj_embedL (x : L) :
    NumberField.IsCMField.complexConj M (embedL x) = embedL x := by
  obtain ⟨c₀, c₁, c₂, rfl⟩ := FieldArithmetic.exists_ofCoords x
  simp [FieldArithmetic.ofCoords, embedL_pi, complexConj_piM]

theorem finrank_M_over_Q : Module.finrank ℚ M = 6 := by
  rw [IsCyclotomicExtension.Rat.finrank 9 M]
  decide

theorem discr_M : NumberField.discr M = -19683 := by
  letI : IsCyclotomicExtension {3 ^ 2} ℚ M := by
    norm_num
    exact cycloM
  have htot : Nat.totient 9 = 6 := by decide
  simpa [htot] using IsCyclotomicExtension.Rat.discr_prime_pow 3 2 M

theorem nrComplexPlaces_M :
    NumberField.InfinitePlace.nrComplexPlaces M = 3 := by
  rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 9 M]
  decide

theorem minkowski_lt_five :
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces M *
      ((Nat.factorial (Module.finrank ℚ M) : ℝ) /
        (Module.finrank ℚ M : ℝ) ^ (Module.finrank ℚ M) *
          √|(NumberField.discr M : ℝ)|) < 5 := by
  rw [nrComplexPlaces_M, finrank_M_over_Q, discr_M]
  norm_num
  have hsqrt : √(19683 : ℝ) < 142 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 19683 by norm_num)
    have hs0 := Real.sqrt_nonneg (19683 : ℝ)
    nlinarith
  have hratio : 4 / Real.pi < (200 / 157 : ℝ) := by
    rw [div_lt_iff₀ Real.pi_pos]
    calc
      (4 : ℝ) = (200 / 157) * (3.14 : ℝ) := by norm_num
      _ < (200 / 157) * Real.pi :=
        mul_lt_mul_of_pos_left Real.pi_gt_d2 (by norm_num)
  have hcub : (4 / Real.pi) ^ 3 < (200 / 157 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hratio (by positivity) (by norm_num)
  calc
    (4 / Real.pi) ^ 3 * (5 / 324 * √(19683 : ℝ)) <
        (200 / 157 : ℝ) ^ 3 * (5 / 324 * √(19683 : ℝ)) :=
      mul_lt_mul_of_pos_right hcub (by positivity)
    _ < (200 / 157 : ℝ) ^ 3 * (5 / 324 * 142) := by gcongr
    _ < 5 := by norm_num

theorem minkowski_floor_le_four :
    ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces M *
      ((Nat.factorial (Module.finrank ℚ M) : ℝ) /
        (Module.finrank ℚ M : ℝ) ^ (Module.finrank ℚ M) *
          √|(NumberField.discr M : ℝ)|)⌋₊ ≤ 4 :=
  Nat.lt_succ_iff.mp
    ((Nat.floor_lt' (by norm_num : (5 : ℕ) ≠ 0)).2 minkowski_lt_five)

instance ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing OM := by
  apply
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
      (K := M)
  intro p hpRange hpPrime P hP hpow
  have hpUpper : p ≤ 4 :=
    (Finset.mem_Icc.mp hpRange).2.trans minkowski_floor_le_four
  have hpCases : p = 2 ∨ p = 3 ∨ p = 4 := by
    have hpLower := (Finset.mem_Icc.mp hpRange).1
    have hpTwo : 2 ≤ p := hpPrime.two_le
    omega
  rcases hpCases with rfl | rfl | rfl
  · letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span ({(2 : ℤ)} : Set ℤ)) := hP.2
    have hf :
        (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P = 6 := by
      have hf₀ := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        (p := 2) (m := 9) (K := M) (P := P) (by norm_num)
      have hroot : IsPrimitiveRoot ((2 : ℕ) : ZMod 9) 6 := by
        apply IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by decide)
        intro l hl hlt
        interval_cases l <;> decide
      calc
        _ = orderOf ((2 : ℕ) : ZMod 9) := by simpa using hf₀
        _ = 6 := hroot.eq_orderOf.symm
    have hbad : (64 : ℕ) ≤ 4 := by
      calc
        64 = 2 ^ (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P := by
          rw [hf]
          norm_num
        _ ≤ ⌊(4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces M *
            ((Nat.factorial (Module.finrank ℚ M) : ℝ) /
              (Module.finrank ℚ M : ℝ) ^ (Module.finrank ℚ M) *
                √|(NumberField.discr M : ℝ)|)⌋₊ := hpow
        _ ≤ 4 := minkowski_floor_le_four
    omega
  · letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : P.IsPrime := hP.1
    letI : P.LiesOver (Ideal.span ({(3 : ℤ)} : Set ℤ)) := hP.2
    letI : IsCyclotomicExtension {3 ^ (1 + 1)} ℚ M := by
      norm_num
      exact cycloM
    rw [IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver
      3 1 M zeta_primitive P]
    infer_instance
  · norm_num at hpPrime

theorem classNumber_M : NumberField.classNumber M = 1 :=
  NumberField.classNumber_eq_one_iff.mpr inferInstance

theorem finrank_M_over_L : Module.finrank L M = 2 := by
  have hmul := Module.finrank_mul_finrank ℚ L M
  rw [FieldArithmetic.finrank_L, finrank_M_over_Q] at hmul
  omega

theorem qM_not_mem_range_embedL : ¬ ∃ r : L, embedL r = qM := by
  rintro ⟨r, hr⟩
  have hrsq : r ^ 2 = (-3 : L) := by
    apply embedL.injective
    change embedL (r ^ 2) = embedL (-3 : L)
    rw [map_pow, hr, qM_sq, map_neg, map_ofNat]
  have hnorm : (Algebra.norm ℚ r) ^ 2 = (-3 : ℚ) ^ 3 := by
    calc
      (Algebra.norm ℚ r) ^ 2 = Algebra.norm ℚ (r ^ 2) := by rw [map_pow]
      _ = Algebra.norm ℚ (-3 : L) := by rw [hrsq]
      _ = (-3 : ℚ) ^ Module.finrank ℚ L := by
        simpa only [map_neg, map_ofNat] using
          (Algebra.norm_algebraMap (S := L) (-3 : ℚ))
      _ = (-3 : ℚ) ^ 3 := by rw [FieldArithmetic.finrank_L]
  nlinarith [sq_nonneg (Algebra.norm ℚ r)]

theorem one_qM_linearIndependent :
    LinearIndependent L ![(1 : M), qM] := by
  rw [LinearIndependent.pair_iff' (one_ne_zero : (1 : M) ≠ 0)]
  intro r hr
  apply qM_not_mem_range_embedL
  refine ⟨r, ?_⟩
  simpa [Algebra.smul_def] using hr

noncomputable def quadraticBasis : Basis (Fin 2) L M :=
  basisOfLinearIndependentOfCardEqFinrank one_qM_linearIndependent <| by
    rw [Fintype.card_fin, finrank_M_over_L]

@[simp] theorem quadraticBasis_zero : quadraticBasis 0 = 1 := by
  rw [quadraticBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

@[simp] theorem quadraticBasis_one : quadraticBasis 1 = qM := by
  rw [quadraticBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

@[simp] theorem quadraticBasis_repr_one_zero :
    quadraticBasis.repr (1 : M) 0 = 1 := by
  rw [← quadraticBasis_zero, Basis.repr_self_apply]
  simp

@[simp] theorem quadraticBasis_repr_one_one :
    quadraticBasis.repr (1 : M) 1 = 0 := by
  rw [← quadraticBasis_zero, Basis.repr_self_apply]
  simp

@[simp] theorem quadraticBasis_repr_q_zero :
    quadraticBasis.repr qM 0 = 0 := by
  rw [← quadraticBasis_one, Basis.repr_self_apply]
  simp

@[simp] theorem quadraticBasis_repr_q_one :
    quadraticBasis.repr qM 1 = 1 := by
  rw [← quadraticBasis_one, Basis.repr_self_apply]
  simp

def realPart (x : M) : L := quadraticBasis.repr x 0
def imagPart (x : M) : L := quadraticBasis.repr x 1

theorem recompose (x : M) :
    x = embedL (realPart x) + embedL (imagPart x) * qM := by
  have h := quadraticBasis.sum_repr x
  rw [Fin.sum_univ_two] at h
  simpa [realPart, imagPart, Algebra.smul_def] using h.symm

@[simp] theorem realPart_embed_add_q (r s : L) :
    realPart (embedL r + embedL s * qM) = r := by
  rw [show embedL r = r • (1 : M) by simp [Algebra.smul_def],
    show embedL s * qM = s • qM by simp [Algebra.smul_def],
    ← quadraticBasis_zero, ← quadraticBasis_one]
  unfold realPart
  simp

@[simp] theorem imagPart_embed_add_q (r s : L) :
    imagPart (embedL r + embedL s * qM) = s := by
  rw [show embedL r = r • (1 : M) by simp [Algebra.smul_def],
    show embedL s * qM = s • qM by simp [Algebra.smul_def],
    ← quadraticBasis_zero, ← quadraticBasis_one]
  unfold imagPart
  simp

theorem complexConj_recompose (x : M) :
    NumberField.IsCMField.complexConj M x =
      embedL (realPart x) - embedL (imagPart x) * qM := by
  nth_rw 1 [recompose x]
  rw [map_add, map_mul, complexConj_embedL, complexConj_embedL,
    complexConj_qM]
  ring

end

end MazurProof.N18RouteC.Cyclotomic
