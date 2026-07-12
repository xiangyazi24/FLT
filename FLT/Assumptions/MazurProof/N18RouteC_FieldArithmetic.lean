import FLT.Assumptions.MazurProof.N18RouteC_Split
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-!
# Arithmetic of the cyclic cubic field used in the N18 descent

This file identifies `Z[pi]` with the full ring of integers of
`L = Q(pi)`, where `pi^3 + 3*pi^2 - 3 = 0`.  In particular the field
discriminant is `81`.  The explicit integral basis is the input needed by
both the global cube-class calculation and the `pi`-adic filtration.
-/

namespace MazurProof.N18RouteC.FieldArithmetic

open Polynomial Module
open NumberField.InfinitePlace
open scoped NumberField

noncomputable section

local macro "n18_ring" : tactic =>
  `(tactic|
    (ring_nf
     simp only [a_pow_fourteen, a_pow_thirteen, a_pow_twelve, a_pow_eleven,
       a_pow_ten, a_pow_nine, a_pow_eight, a_pow_seven, a_pow_six,
       a_pow_five, a_pow_four, a_cubic]
     ring))

def powerBasis : PowerBasis ℚ L :=
  AdjoinRoot.powerBasis cubicPolyIrreducibleFact.out.ne_zero

def basis : Basis (Fin 3) ℚ L :=
  powerBasis.basis.reindex
    (finCongr (by simpa [powerBasis] using cubicPoly_natDegree))

@[simp] theorem powerBasis_gen : powerBasis.gen = pi := rfl

theorem basis_apply (i : Fin 3) : basis i = pi ^ (i : ℕ) := by
  simp [basis, powerBasis, pi]

theorem finrank_L : Module.finrank ℚ L = 3 := by
  rw [PowerBasis.finrank powerBasis]
  simpa [powerBasis] using cubicPoly_natDegree

def ofCoords (c0 c1 c2 : ℚ) : L :=
  algebraMap ℚ L c0 + algebraMap ℚ L c1 * pi +
    algebraMap ℚ L c2 * pi ^ 2

private theorem ofCoords_eq_basis_sum (c0 c1 c2 : ℚ) :
    ofCoords c0 c1 c2 =
      c0 • basis (0 : Fin 3) + c1 • basis (1 : Fin 3) +
        c2 • basis (2 : Fin 3) := by
  simp [ofCoords, basis_apply, Algebra.smul_def]

@[simp] theorem basis_repr_ofCoords_zero (c0 c1 c2 : ℚ) :
    basis.repr (ofCoords c0 c1 c2) (0 : Fin 3) = c0 := by
  rw [ofCoords_eq_basis_sum]
  simp

@[simp] theorem basis_repr_ofCoords_one (c0 c1 c2 : ℚ) :
    basis.repr (ofCoords c0 c1 c2) (1 : Fin 3) = c1 := by
  rw [ofCoords_eq_basis_sum]
  simp

@[simp] theorem basis_repr_ofCoords_two (c0 c1 c2 : ℚ) :
    basis.repr (ofCoords c0 c1 c2) (2 : Fin 3) = c2 := by
  rw [ofCoords_eq_basis_sum]
  simp

theorem exists_ofCoords (u : L) :
    ∃ c0 c1 c2 : ℚ, u = ofCoords c0 c1 c2 := by
  let c0 := basis.repr u (0 : Fin 3)
  let c1 := basis.repr u (1 : Fin 3)
  let c2 := basis.repr u (2 : Fin 3)
  refine ⟨c0, c1, c2, ?_⟩
  apply basis.repr.injective
  ext i
  fin_cases i <;> simp [c0, c1, c2]

theorem pi_isIntegral : IsIntegral ℤ pi := by
  refine ⟨cubicPolyInt, ?_, ?_⟩
  · unfold cubicPolyInt
    monicity!
  · simpa [cubicPolyInt] using pi_relation

def piInteger : NumberField.RingOfIntegers L := ⟨pi, pi_isIntegral⟩

@[simp] theorem piInteger_coe_L :
    ((piInteger : NumberField.RingOfIntegers L) : L) = pi := rfl

/-! ## The power-basis discriminant -/

private theorem trace_one : Algebra.trace ℚ L 1 = 3 := by
  simpa using Algebra.trace_algebraMap_of_basis basis (1 : ℚ)

private theorem leftMulMatrix_pi_zero_zero :
    Algebra.leftMulMatrix basis pi (0 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  simpa [basis_apply, ofCoords] using basis_repr_ofCoords_zero 0 1 0

private theorem leftMulMatrix_pi_one_one :
    Algebra.leftMulMatrix basis pi (1 : Fin 3) (1 : Fin 3) = 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  convert basis_repr_ofCoords_one 0 0 1 using 1 <;>
    simp [basis_apply, ofCoords] <;> ring

private theorem leftMulMatrix_pi_two_two :
    Algebra.leftMulMatrix basis pi (2 : Fin 3) (2 : Fin 3) = -3 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  have h : pi * basis (2 : Fin 3) = ofCoords 3 0 (-3) := by
    rw [basis_apply]
    norm_num
    unfold ofCoords
    norm_num
    linear_combination pi_relation
  rw [h]
  exact basis_repr_ofCoords_two 3 0 (-3)

private theorem trace_pi : Algebra.trace ℚ L pi = -3 := by
  rw [Algebra.trace_eq_matrix_trace basis, Matrix.trace_fin_three,
    leftMulMatrix_pi_zero_zero, leftMulMatrix_pi_one_one,
    leftMulMatrix_pi_two_two]
  norm_num

private theorem leftMulMatrix_pi_sq_zero_zero :
    Algebra.leftMulMatrix basis (pi ^ 2) (0 : Fin 3) (0 : Fin 3) = 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  simpa [basis_apply, ofCoords] using basis_repr_ofCoords_zero 0 0 1

private theorem leftMulMatrix_pi_sq_one_one :
    Algebra.leftMulMatrix basis (pi ^ 2) (1 : Fin 3) (1 : Fin 3) = 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  have h : pi ^ 2 * basis (1 : Fin 3) = ofCoords 3 0 (-3) := by
    rw [basis_apply]
    norm_num
    unfold ofCoords
    norm_num
    linear_combination pi_relation
  rw [h]
  exact basis_repr_ofCoords_one 3 0 (-3)

private theorem leftMulMatrix_pi_sq_two_two :
    Algebra.leftMulMatrix basis (pi ^ 2) (2 : Fin 3) (2 : Fin 3) = 9 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  have hpi4 : pi ^ 4 = -9 + 3 * pi + 9 * pi ^ 2 := by
    linear_combination pi * pi_relation - 3 * pi_relation
  have h : pi ^ 2 * basis (2 : Fin 3) = ofCoords (-9) 3 9 := by
    rw [basis_apply]
    norm_num
    rw [show pi ^ 2 * pi ^ 2 = pi ^ 4 by ring, hpi4]
    simp [ofCoords]
  rw [h]
  exact basis_repr_ofCoords_two (-9) 3 9

private theorem trace_pi_sq : Algebra.trace ℚ L (pi ^ 2) = 9 := by
  rw [Algebra.trace_eq_matrix_trace basis, Matrix.trace_fin_three,
    leftMulMatrix_pi_sq_zero_zero, leftMulMatrix_pi_sq_one_one,
    leftMulMatrix_pi_sq_two_two]
  norm_num

private theorem trace_pi_cubed : Algebra.trace ℚ L (pi ^ 3) = -18 := by
  rw [pi_cubed]
  have hrewrite : (3 : L) - 3 * pi ^ 2 =
      (3 : ℚ) • (1 : L) - (3 : ℚ) • pi ^ 2 := by
    simp [Algebra.smul_def]
  rw [hrewrite, map_sub, map_smul, map_smul, trace_one, trace_pi_sq]
  norm_num

private theorem trace_pi_fourth : Algebra.trace ℚ L (pi ^ 4) = 45 := by
  have hpi4 : pi ^ 4 = -9 + 3 * pi + 9 * pi ^ 2 := by
    linear_combination pi * pi_relation - 3 * pi_relation
  rw [hpi4]
  have hrewrite : (-9 : L) + 3 * pi + 9 * pi ^ 2 =
      (-9 : ℚ) • (1 : L) + (3 : ℚ) • pi +
        (9 : ℚ) • pi ^ 2 := by
    simp [Algebra.smul_def]
  rw [hrewrite, map_add, map_add, map_smul, map_smul, map_smul,
    trace_one, trace_pi, trace_pi_sq]
  norm_num

private theorem traceMatrix_zero_zero :
    Algebra.traceMatrix ℚ basis 0 0 = 3 := by
  change Algebra.trace ℚ L (basis 0 * basis 0) = 3
  simpa [basis_apply] using trace_one

private theorem traceMatrix_zero_one :
    Algebra.traceMatrix ℚ basis 0 1 = -3 := by
  change Algebra.trace ℚ L (basis 0 * basis 1) = -3
  simpa [basis_apply] using trace_pi

private theorem traceMatrix_zero_two :
    Algebra.traceMatrix ℚ basis 0 2 = 9 := by
  change Algebra.trace ℚ L (basis 0 * basis 2) = 9
  simpa [basis_apply] using trace_pi_sq

private theorem traceMatrix_one_zero :
    Algebra.traceMatrix ℚ basis 1 0 = -3 := by
  change Algebra.trace ℚ L (basis 1 * basis 0) = -3
  simpa [basis_apply] using trace_pi

private theorem traceMatrix_one_one :
    Algebra.traceMatrix ℚ basis 1 1 = 9 := by
  change Algebra.trace ℚ L (basis 1 * basis 1) = 9
  simpa [basis_apply, pow_two] using trace_pi_sq

private theorem traceMatrix_one_two :
    Algebra.traceMatrix ℚ basis 1 2 = -18 := by
  change Algebra.trace ℚ L (basis 1 * basis 2) = -18
  simp only [basis_apply]
  norm_num
  convert trace_pi_cubed using 1 <;> ring

private theorem traceMatrix_two_zero :
    Algebra.traceMatrix ℚ basis 2 0 = 9 := by
  change Algebra.trace ℚ L (basis 2 * basis 0) = 9
  simpa [basis_apply] using trace_pi_sq

private theorem traceMatrix_two_one :
    Algebra.traceMatrix ℚ basis 2 1 = -18 := by
  change Algebra.trace ℚ L (basis 2 * basis 1) = -18
  simp only [basis_apply]
  norm_num
  convert trace_pi_cubed using 1 <;> ring

private theorem traceMatrix_two_two :
    Algebra.traceMatrix ℚ basis 2 2 = 45 := by
  change Algebra.trace ℚ L (basis 2 * basis 2) = 45
  rw [basis_apply]
  norm_num
  convert trace_pi_fourth using 1 <;> ring

theorem basis_discr : Algebra.discr ℚ basis = 81 := by
  rw [Algebra.discr_def, Matrix.det_fin_three,
    traceMatrix_zero_zero, traceMatrix_zero_one, traceMatrix_zero_two,
    traceMatrix_one_zero, traceMatrix_one_one, traceMatrix_one_two,
    traceMatrix_two_zero, traceMatrix_two_one, traceMatrix_two_two]
  norm_num

/-! ## The field discriminant and the full integral basis -/

def integralIndexEquiv :
    Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers L) ≃ Fin 3 :=
  Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis (NumberField.RingOfIntegers.basis L),
      NumberField.RingOfIntegers.rank, finrank_L, Fintype.card_fin])

def integralBasisFin : Basis (Fin 3) ℚ L :=
  (NumberField.integralBasis L).reindex integralIndexEquiv

theorem integralBasisFin_discr :
    Algebra.discr ℚ integralBasisFin = (NumberField.discr L : ℚ) := by
  simp only [integralBasisFin, Basis.coe_reindex]
  rw [Algebra.discr_reindex, ← NumberField.coe_discr]

def basisInteger (i : Fin 3) : NumberField.RingOfIntegers L :=
  ⟨basis i, (mem_integralClosure_iff ℤ L).mpr <| by
    rw [basis_apply]
    exact pi_isIntegral.pow i⟩

@[simp] theorem basisInteger_coe_L (i : Fin 3) :
    ((basisInteger i : NumberField.RingOfIntegers L) : L) = basis i := rfl

private theorem integralBasisFin_repr_basis (i j : Fin 3) :
    integralBasisFin.repr (basis j) i =
      algebraMap ℤ ℚ
        ((NumberField.RingOfIntegers.basis L).repr (basisInteger j)
          (integralIndexEquiv.symm i)) := by
  rw [integralBasisFin, Basis.repr_reindex_apply]
  simpa [basisInteger] using
    NumberField.integralBasis_repr_apply L (basisInteger j)
      (integralIndexEquiv.symm i)

private theorem integral_toMatrix_entries (i j : Fin 3) :
    IsIntegral ℤ (integralBasisFin.toMatrix basis i j) := by
  rw [Basis.toMatrix_apply, integralBasisFin_repr_basis]
  exact isIntegral_algebraMap

private theorem basis_discr_index_relation :
    ∃ d : ℤ, (81 : ℤ) = d ^ 2 * NumberField.discr L := by
  let A : Matrix (Fin 3) (Fin 3) ℚ := integralBasisFin.toMatrix basis
  have hdetInt : IsIntegral ℤ A.det :=
    IsIntegral.det fun i j ↦ integral_toMatrix_entries i j
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdetInt
  refine ⟨d, ?_⟩
  have hdisc := Algebra.discr_of_matrix_vecMul
    (A := ℚ) (B := L) (integralBasisFin : Fin 3 → L) A
  have hfamily :
      Matrix.vecMul (integralBasisFin : Fin 3 → L)
          (A.map (algebraMap ℚ L)) = (basis : Fin 3 → L) := by
    exact integralBasisFin.toMatrix_map_vecMul basis
  rw [hfamily, basis_discr, integralBasisFin_discr, ← hd] at hdisc
  apply Int.cast_injective (α := ℚ)
  push_cast
  exact hdisc

theorem discr_pos : 0 < NumberField.discr L := by
  obtain ⟨d, hd⟩ := basis_discr_index_relation
  have hdne : d ≠ 0 := by
    intro hd0
    rw [hd0] at hd
    norm_num at hd
  have hdsq : 0 < d ^ 2 := sq_pos_of_ne_zero hdne
  nlinarith

theorem nrComplexPlaces_eq_zero : nrComplexPlaces L = 0 := by
  have hsign := NumberField.sign_discr L
  rw [Int.sign_eq_one_of_pos discr_pos] at hsign
  have heven : Even (nrComplexPlaces L) := by
    exact (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num)).mp hsign.symm
  have hdegree := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank L
  rw [finrank_L] at hdegree
  rcases heven with ⟨r, hr⟩
  omega

theorem nrRealPlaces_eq_three : nrRealPlaces L = 3 := by
  have hdegree := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank L
  rw [finrank_L, nrComplexPlaces_eq_zero] at hdegree
  omega

theorem abs_discr_gt_twenty :
    (20 : ℝ) < |(NumberField.discr L : ℝ)| := by
  have hbound := NumberField.abs_discr_ge' L
  rw [finrank_L, nrComplexPlaces_eq_zero] at hbound
  have hrewrite :
      (((3 : ℕ) : ℝ) ^ (2 * 3) /
          ((4 / Real.pi) ^ (2 * 0) * (Nat.factorial 3 : ℝ) ^ 2)) =
        81 / 4 := by norm_num
  rw [hrewrite, Int.cast_abs] at hbound
  linarith

theorem discr_eq_eighty_one : NumberField.discr L = 81 := by
  obtain ⟨d, hd⟩ := basis_discr_index_relation
  have hdne : d ≠ 0 := by
    intro hd0
    rw [hd0] at hd
    norm_num at hd
  have hdiscLower : (20 : ℤ) < NumberField.discr L := by
    have hreal : (20 : ℝ) < (NumberField.discr L : ℝ) := by
      simpa [abs_of_pos (show (0 : ℝ) < (NumberField.discr L : ℝ) by
        exact_mod_cast discr_pos)] using abs_discr_gt_twenty
    exact_mod_cast hreal
  have hdsqLt : d ^ 2 < 4 := by
    by_contra hnot
    have hfour : (4 : ℤ) ≤ d ^ 2 := by omega
    have htwentyOne : (21 : ℤ) ≤ NumberField.discr L := by omega
    have hprod : 4 * 21 ≤ d ^ 2 * NumberField.discr L :=
      mul_le_mul hfour htwentyOne (by norm_num) (sq_nonneg d)
    rw [← hd] at hprod
    norm_num at hprod
  have hdLower : -2 < d := by nlinarith
  have hdUpper : d < 2 := by nlinarith
  have hdCases : d = -1 ∨ d = 1 := by omega
  rcases hdCases with rfl | rfl <;> norm_num at hd ⊢ <;> exact hd.symm

def ringOfIntegersBasisFin :
    Basis (Fin 3) ℤ (NumberField.RingOfIntegers L) :=
  (NumberField.RingOfIntegers.basis L).reindex integralIndexEquiv

def basisIntegerMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j ↦ ringOfIntegersBasisFin.repr (basisInteger j) i

private theorem ringOfIntegersBasisFin_repr_basisInteger (i j : Fin 3) :
    ringOfIntegersBasisFin.repr (basisInteger j) i =
      (NumberField.RingOfIntegers.basis L).repr (basisInteger j)
        (integralIndexEquiv.symm i) := by
  rw [ringOfIntegersBasisFin, Basis.repr_reindex_apply]

private theorem basisIntegerMatrix_map :
    basisIntegerMatrix.map (algebraMap ℤ ℚ) =
      integralBasisFin.toMatrix basis := by
  ext i j
  rw [Matrix.map_apply, basisIntegerMatrix, Basis.toMatrix_apply,
    ringOfIntegersBasisFin_repr_basisInteger]
  exact (integralBasisFin_repr_basis i j).symm

theorem basisIntegerMatrix_det_isUnit : IsUnit basisIntegerMatrix.det := by
  let A : Matrix (Fin 3) (Fin 3) ℚ := integralBasisFin.toMatrix basis
  have hdisc := Algebra.discr_of_matrix_vecMul
    (A := ℚ) (B := L) (integralBasisFin : Fin 3 → L) A
  have hfamily :
      Matrix.vecMul (integralBasisFin : Fin 3 → L)
          (A.map (algebraMap ℚ L)) = (basis : Fin 3 → L) := by
    exact integralBasisFin.toMatrix_map_vecMul basis
  rw [hfamily, basis_discr, integralBasisFin_discr,
    discr_eq_eighty_one] at hdisc
  norm_num at hdisc
  have hAdet : A.det ^ 2 = 1 := sq_eq_one_iff.mpr hdisc
  have hmapDet : algebraMap ℤ ℚ basisIntegerMatrix.det = A.det := by
    calc
      algebraMap ℤ ℚ basisIntegerMatrix.det =
          (basisIntegerMatrix.map (algebraMap ℤ ℚ)).det := by
            exact (algebraMap ℤ ℚ).map_det basisIntegerMatrix
      _ = A.det := by rw [basisIntegerMatrix_map]
  have hdetSq : basisIntegerMatrix.det ^ 2 = 1 := by
    apply Int.cast_injective (α := ℚ)
    change algebraMap ℤ ℚ (basisIntegerMatrix.det ^ 2) =
      algebraMap ℤ ℚ 1
    rw [map_pow, map_one, hmapDet, hAdet]
  rw [Int.isUnit_iff, ← sq_eq_one_iff]
  exact hdetSq

def integralPowerBasis :
    Basis (Fin 3) ℤ (NumberField.RingOfIntegers L) :=
  ringOfIntegersBasisFin.map
    (Matrix.toLinearEquiv ringOfIntegersBasisFin basisIntegerMatrix
      basisIntegerMatrix_det_isUnit)

@[simp] theorem integralPowerBasis_apply (i : Fin 3) :
    integralPowerBasis i = basisInteger i := by
  simp only [integralPowerBasis, Basis.map_apply]
  change Matrix.toLin ringOfIntegersBasisFin ringOfIntegersBasisFin
      basisIntegerMatrix (ringOfIntegersBasisFin i) = basisInteger i
  rw [Matrix.toLin_self]
  simpa [basisIntegerMatrix] using
    ringOfIntegersBasisFin.sum_repr (basisInteger i)

@[simp] theorem integralPowerBasis_coe_L (i : Fin 3) :
    ((integralPowerBasis i : NumberField.RingOfIntegers L) : L) = basis i := by
  rw [integralPowerBasis_apply]
  rfl

theorem ringOfIntegers_exists_integer_coords
    (u : NumberField.RingOfIntegers L) :
    ∃ c0 c1 c2 : ℤ, (u : L) = ofCoords c0 c1 c2 := by
  let c0 := integralPowerBasis.repr u (0 : Fin 3)
  let c1 := integralPowerBasis.repr u (1 : Fin 3)
  let c2 := integralPowerBasis.repr u (2 : Fin 3)
  refine ⟨c0, c1, c2, ?_⟩
  have hsum := integralPowerBasis.sum_repr u
  rw [Fin.sum_univ_three] at hsum
  have hsumL := congrArg
    (fun v : NumberField.RingOfIntegers L ↦ (v : L)) hsum
  simpa [c0, c1, c2, ofCoords, Algebra.smul_def, basis_apply] using
    hsumL.symm

theorem adjoin_piInteger_eq_top :
    Algebra.adjoin ℤ ({piInteger} : Set (NumberField.RingOfIntegers L)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨c0, c1, c2, hu⟩ := ringOfIntegers_exists_integer_coords u
  let A := Algebra.adjoin ℤ
    ({piInteger} : Set (NumberField.RingOfIntegers L))
  have hpi : piInteger ∈ A := Algebra.subset_adjoin (Set.mem_singleton piInteger)
  have hcoords :
      u = algebraMap ℤ (NumberField.RingOfIntegers L) c0 +
          algebraMap ℤ (NumberField.RingOfIntegers L) c1 * piInteger +
          algebraMap ℤ (NumberField.RingOfIntegers L) c2 * piInteger ^ 2 := by
    apply Subtype.ext
    change (u : L) =
      (c0 : L) + (c1 : L) * pi + (c2 : L) * pi ^ 2
    simpa [ofCoords] using hu
  rw [hcoords]
  exact A.add_mem
    (A.add_mem (A.algebraMap_mem c0)
      (A.mul_mem (A.algebraMap_mem c1) hpi))
    (A.mul_mem (A.algebraMap_mem c2) (A.pow_mem hpi 2))

theorem piInteger_exponent_eq_one :
    RingOfIntegers.exponent piInteger = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr adjoin_piInteger_eq_top

private theorem cubicPolyInt_monic' : cubicPolyInt.Monic := by
  unfold cubicPolyInt
  monicity!

private theorem cubicPolyInt_irreducible' : Irreducible cubicPolyInt := by
  exact
    (cubicPolyInt_monic'.isPrimitive.irreducible_iff_irreducible_map_fraction_map).mpr
      cubicPoly_irreducible

set_option maxHeartbeats 0 in
theorem minpoly_piInteger : minpoly ℤ piInteger = cubicPolyInt := by
  have hroot : aeval piInteger cubicPolyInt = 0 := by
    unfold cubicPolyInt
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X]
    apply Subtype.ext
    exact pi_relation
  let ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd piInteger.isIntegral hroot
  symm
  exact eq_of_monic_of_associated cubicPolyInt_monic'
    (minpoly.monic piInteger.isIntegral) <| by
      convert!
        Associated.mul_left (minpoly ℤ piInteger) <|
          associated_one_iff_isUnit.2 <|
            (cubicPolyInt_irreducible'.isUnit_or_isUnit hq).resolve_left <|
              minpoly.not_isUnit ℤ piInteger
      rw [mul_one]

/-! ## Explicit units used by the Selmer basis -/

theorem a_mul_inverse : a * (a ^ 2 - 3) = 1 := by
  linear_combination a_cubic

theorem aplus_mul_inverse :
    (a + 1) * (-a ^ 2 + a + 2) = 1 := by
  n18_ring

theorem changeS_mul_inverse :
    (2 - a ^ 2) * (1 + a - a ^ 2) = 1 := by
  n18_ring

def aInteger : NumberField.RingOfIntegers L :=
  ⟨a, pi_isIntegral.add isIntegral_one⟩

def aplusInteger : NumberField.RingOfIntegers L :=
  ⟨a + 1, (pi_isIntegral.add isIntegral_one).add isIntegral_one⟩

def aUnit : (NumberField.RingOfIntegers L)ˣ where
  val := aInteger
  inv := ⟨a ^ 2 - 3, (pi_isIntegral.add isIntegral_one).pow 2 |>.sub
    (isIntegral_intCast 3)⟩
  val_inv := Subtype.ext a_mul_inverse
  inv_val := Subtype.ext (by rw [mul_comm]; exact a_mul_inverse)

def aplusUnit : (NumberField.RingOfIntegers L)ˣ where
  val := aplusInteger
  inv := ⟨-a ^ 2 + a + 2,
    ((pi_isIntegral.add isIntegral_one).pow 2).neg |>.add
      (pi_isIntegral.add isIntegral_one) |>.add
        (isIntegral_intCast 2)⟩
  val_inv := Subtype.ext aplus_mul_inverse
  inv_val := Subtype.ext (by rw [mul_comm]; exact aplus_mul_inverse)

@[simp] theorem aUnit_coe_L :
    ((aUnit : NumberField.RingOfIntegers L) : L) = a := rfl

@[simp] theorem aplusUnit_coe_L :
    ((aplusUnit : NumberField.RingOfIntegers L) : L) = a + 1 := rfl

theorem unitRank_eq_two : NumberField.Units.rank L = 2 := by
  rw [NumberField.Units.rank,
    NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    nrRealPlaces_eq_three, nrComplexPlaces_eq_zero]

/-! ## The inert prime above two and class number one -/

def cubicModTwo : (ZMod 2)[X] :=
  cubicPolyInt.map (Int.castRingHom (ZMod 2))

theorem cubicModTwo_eq : cubicModTwo = X ^ 3 + X ^ 2 + 1 := by
  rw [show (1 : (ZMod 2)[X]) = C 1 by simp]
  ext n
  by_cases h0 : n = 0
  · subst n
    simp [cubicModTwo, cubicPolyInt, coeff_X_pow]
    decide
  by_cases h2 : n = 2
  · subst n
    simp [cubicModTwo, cubicPolyInt, coeff_X_pow,
      Polynomial.coeff_natCast_ite, Polynomial.coeff_one]
    change (3 : ZMod 2) = 1
    decide
  by_cases h3 : n = 3
  · subst n
    simp [cubicModTwo, cubicPolyInt, coeff_X_pow,
      Polynomial.coeff_natCast_ite, Polynomial.coeff_one]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have hm1 : m ≠ 1 := by omega
    have hm2 : m ≠ 2 := by omega
    simp [cubicModTwo, cubicPolyInt, coeff_X_pow,
      Polynomial.coeff_natCast_ite, Polynomial.coeff_one, hm1, hm2]

theorem cubicModTwo_monic : cubicModTwo.Monic := by
  rw [cubicModTwo_eq]
  monicity!

theorem cubicModTwo_irreducible : Irreducible cubicModTwo := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubicModTwo_eq]
    have hdeg : (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 3 := by
      compute_degree <;> norm_num
    rw [Finset.mem_Icc]
    omega
  · rw [cubicModTwo_eq]
    intro x
    fin_cases x
    · simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
      change (1 : ZMod 2) ≠ 0
      exact one_ne_zero
    · simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
      change (1 : ZMod 2) ≠ 0
      exact one_ne_zero

theorem monicFactorsMod_two :
    RingOfIntegers.monicFactorsMod piInteger 2 = {cubicModTwo} := by
  simp only [RingOfIntegers.monicFactorsMod, minpoly_piInteger]
  rw [show cubicPolyInt.map (Int.castRingHom (ZMod 2)) = cubicModTwo by rfl,
    UniqueFactorizationMonoid.normalizedFactors_irreducible
      cubicModTwo_irreducible]
  rw [cubicModTwo_monic.normalize_eq_self]
  rfl

theorem cubicModTwo_mem :
    cubicModTwo ∈ RingOfIntegers.monicFactorsMod piInteger 2 := by
  rw [monicFactorsMod_two]
  simp

private theorem two_not_dvd_exponent :
    ¬ (2 : ℕ) ∣ RingOfIntegers.exponent piInteger := by
  rw [piInteger_exponent_eq_one]
  norm_num

def primeAboveTwo : Ideal (NumberField.RingOfIntegers L) :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := L) (p := 2) two_not_dvd_exponent).symm
    ⟨cubicModTwo, cubicModTwo_mem⟩ : Ideal (NumberField.RingOfIntegers L))

theorem primeAboveTwo_eq_span_two :
    primeAboveTwo = Ideal.span ({(2 : NumberField.RingOfIntegers L)} : Set _) := by
  have hspan :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
      (K := L) (p := 2) (Q := cubicPolyInt) two_not_dvd_exponent
      (by simpa [cubicModTwo] using cubicModTwo_mem)
  have heval : aeval piInteger cubicPolyInt = 0 := by
    rw [← minpoly_piInteger]
    exact minpoly.aeval ℤ piInteger
  simpa [primeAboveTwo, cubicModTwo, heval] using hspan

theorem primeAboveTwo_mem :
    primeAboveTwo ∈
      Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
        (NumberField.RingOfIntegers L) :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      (K := L) (p := 2) two_not_dvd_exponent).symm
    ⟨cubicModTwo, cubicModTwo_mem⟩).property

theorem primeAboveTwo_unique
    (P : Ideal (NumberField.RingOfIntegers L))
    (hP : P ∈ Ideal.primesOver (Ideal.span ({(2 : ℤ)} : Set ℤ))
      (NumberField.RingOfIntegers L)) :
    P = primeAboveTwo := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := L) (p := 2) two_not_dvd_exponent
  have hfac : (e ⟨P, hP⟩).1 = cubicModTwo := by
    apply Finset.mem_singleton.mp
    show (e ⟨P, hP⟩).1 ∈ ({cubicModTwo} : Finset ((ZMod 2)[X]))
    rw [← monicFactorsMod_two]
    exact (e ⟨P, hP⟩).2
  have hout : e ⟨P, hP⟩ = ⟨cubicModTwo, cubicModTwo_mem⟩ :=
    Subtype.ext hfac
  have hin : ⟨P, hP⟩ = e.symm ⟨cubicModTwo, cubicModTwo_mem⟩ := by
    apply e.injective
    simpa using hout
  exact congrArg Subtype.val hin

theorem minkowski_floor :
    ⌊(4 / Real.pi) ^ nrComplexPlaces L *
      ((Nat.factorial (Module.finrank ℚ L) : ℝ) /
        (Module.finrank ℚ L : ℝ) ^ (Module.finrank ℚ L) *
          √|(NumberField.discr L : ℝ)|)⌋₊ = 2 := by
  rw [nrComplexPlaces_eq_zero, finrank_L, discr_eq_eighty_one]
  norm_num

instance ringOfIntegers_isPrincipalIdealRing :
    IsPrincipalIdealRing (NumberField.RingOfIntegers L) := by
  apply
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
      (K := L)
  intro p hpRange hpPrime P hP _hpow
  have hpLower : 1 ≤ p := (Finset.mem_Icc.mp hpRange).1
  have hpUpper : p ≤ 2 := by
    have h := (Finset.mem_Icc.mp hpRange).2
    change p ≤
      ⌊(4 / Real.pi) ^ nrComplexPlaces L *
        ((Nat.factorial (Module.finrank ℚ L) : ℝ) /
          (Module.finrank ℚ L : ℝ) ^ (Module.finrank ℚ L) *
            √|(NumberField.discr L : ℝ)|)⌋₊ at h
    rwa [minkowski_floor] at h
  have hpCases : p = 1 ∨ p = 2 := by omega
  rcases hpCases with rfl | rfl
  · norm_num at hpPrime
  · have hPeq := primeAboveTwo_unique P (by simpa using hP)
    rw [hPeq, primeAboveTwo_eq_span_two]
    infer_instance

theorem classNumber_eq_one : NumberField.classNumber L = 1 :=
  NumberField.classNumber_eq_one_iff.mpr inferInstance

end

end MazurProof.N18RouteC.FieldArithmetic
