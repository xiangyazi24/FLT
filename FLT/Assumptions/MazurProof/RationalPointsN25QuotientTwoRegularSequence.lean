import FLT.Assumptions.MazurProof.RationalPointsN25QuotientTwoConormal
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic

/-!
# Regularity of the N25 canonical equations

The canonical quadric is monic in `y`.  We therefore write the ambient ring
as `F₂[x,z,w][y]` and model the quotient by the quadric as a free quadratic
algebra.  In this model the cubic is linear in `y`; multiplication by it has a
two-by-two matrix whose determinant can be checked structurally.
-/

noncomputable section

namespace MazurProof.RationalPointsN25QuotientTwoRegularSequence

open Module Polynomial
open MazurProof.RationalPointsN25QuotientTwoConormal

/-- The coefficient ring `F₂[x,z,w]` obtained by separating the `y`
coordinate. -/
abbrev QuadricBaseRing := MvPolynomial (Fin 3) (ZMod 2)

/-- The separated base variable `x`. -/
def baseX : QuadricBaseRing := MvPolynomial.X 0

/-- The separated base variable `z`. -/
def baseZ : QuadricBaseRing := MvPolynomial.X 1

/-- The separated base variable `w`. -/
def baseW : QuadricBaseRing := MvPolynomial.X 2

/-- The constant term `xz+xw+zw` of the canonical quadric as a polynomial in
`y`. -/
def quadricConstant : QuadricBaseRing :=
  baseX * baseZ + baseX * baseW + baseZ * baseW

/-- The `y`-free part of the canonical cubic. -/
def cubicConstant : QuadricBaseRing :=
  baseX ^ 2 * baseW + baseX * baseZ * baseW +
    baseZ ^ 2 * baseW + baseZ * baseW ^ 2

/-- The canonical quadric, now written as a monic polynomial in `y`. -/
def quadricInY : QuadricBaseRing[X] :=
  X ^ 2 + C baseZ * X + C quadricConstant

/-- The canonical cubic modulo the chosen polynomial-tower decomposition.
Its coefficient of `y` is the same `quadricConstant`. -/
def cubicInY : QuadricBaseRing[X] :=
  C quadricConstant * X + C cubicConstant

/-- The tower quadric is monic, so its quotient has the basis `1,y`. -/
theorem quadricInY_monic : quadricInY.Monic := by
  exact (isMonicOfDegree_add_add_two baseZ quadricConstant).monic

/-- The monic quadric has degree exactly two. -/
theorem quadricInY_natDegree : quadricInY.natDegree = 2 := by
  exact (isMonicOfDegree_add_add_two baseZ quadricConstant).natDegree_eq

/-- The quotient by the monic quadric in the polynomial-tower model. -/
abbrev QuadricRootRing := AdjoinRoot quadricInY

/-- The class of the separated coordinate `y`. -/
def quadricRoot : QuadricRootRing := AdjoinRoot.root quadricInY

/-- The class of the canonical cubic in the quadric quotient. -/
def cubicClass : QuadricRootRing := AdjoinRoot.mk quadricInY cubicInY

/-! ## Separating the `y` coordinate -/

/-- The polynomial-tower equivalence that sends the four variables
`x,y,z,w` to `x,Y,z,w`, with `Y` the outer polynomial variable. -/
def binaryTowerEquiv :
    BinaryHomogeneousRing ≃ₐ[ZMod 2] QuadricBaseRing[X] :=
  (MvPolynomial.renameEquiv (ZMod 2)
    (finSuccEquiv' (1 : Fin 4))).trans
      (MvPolynomial.optionEquivLeft (ZMod 2) (Fin 3))

/-- The tower equivalence sends the original `x` coordinate to the first
base-ring variable. -/
@[simp]
theorem binaryTowerEquiv_x :
    binaryTowerEquiv (MvPolynomial.X (0 : Fin 4)) = C baseX := by
  simp [binaryTowerEquiv, baseX,
    show finSuccEquiv' (1 : Fin 4) 0 = some 0 by decide]

/-- The tower equivalence sends the original `y` coordinate to the outer
polynomial variable. -/
@[simp]
theorem binaryTowerEquiv_y :
    binaryTowerEquiv (MvPolynomial.X (1 : Fin 4)) = X := by
  simp [binaryTowerEquiv,
    show finSuccEquiv' (1 : Fin 4) 1 = none by decide]

/-- The tower equivalence sends the original `z` coordinate to the second
base-ring variable. -/
@[simp]
theorem binaryTowerEquiv_z :
    binaryTowerEquiv (MvPolynomial.X (2 : Fin 4)) = C baseZ := by
  simp [binaryTowerEquiv, baseZ,
    show finSuccEquiv' (1 : Fin 4) 2 = some 1 by decide]

/-- The tower equivalence sends the original `w` coordinate to the third
base-ring variable. -/
@[simp]
theorem binaryTowerEquiv_w :
    binaryTowerEquiv (MvPolynomial.X (3 : Fin 4)) = C baseW := by
  simp [binaryTowerEquiv, baseW,
    show finSuccEquiv' (1 : Fin 4) 3 = some 2 by decide]

/-- Under the tower equivalence, the canonical quadric is the monic
quadratic used to define `QuadricRootRing`. -/
theorem binaryTowerEquiv_quadric :
    binaryTowerEquiv canonicalQuadricPolynomial25Two = quadricInY := by
  simp [canonicalQuadricPolynomial25Two, quadricInY, quadricConstant]
  ring

/-- Under the tower equivalence, the canonical cubic becomes the displayed
linear polynomial in `y`. -/
theorem binaryTowerEquiv_cubic :
    binaryTowerEquiv canonicalCubicPolynomial25Two = cubicInY := by
  simp [canonicalCubicPolynomial25Two, cubicInY, cubicConstant,
    quadricConstant]
  ring

/-- Reindex the power basis by the literal two-element type used for the
matrix calculation. -/
def quadricBasis : Basis (Fin 2) QuadricBaseRing QuadricRootRing :=
  (AdjoinRoot.powerBasisAux' quadricInY_monic).reindex
    (finCongr quadricInY_natDegree)

/-- The first vector of the reindexed power basis is `1`. -/
@[simp]
theorem quadricBasis_zero : quadricBasis (0 : Fin 2) = 1 := by
  dsimp only [quadricBasis]
  rw [Basis.reindex_apply]
  change
    (AdjoinRoot.powerBasis' quadricInY_monic).basis
        ((finCongr quadricInY_natDegree).symm 0) = 1
  rw [PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
  norm_num

/-- The second vector of the reindexed power basis is the class of `y`. -/
@[simp]
theorem quadricBasis_one : quadricBasis (1 : Fin 2) = quadricRoot := by
  dsimp only [quadricBasis]
  rw [Basis.reindex_apply]
  change
    (AdjoinRoot.powerBasis' quadricInY_monic).basis
        ((finCongr quadricInY_natDegree).symm 1) =
      AdjoinRoot.root quadricInY
  rw [PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
  norm_num

/-- In the quadric quotient, the cubic class is
`(xz+xw+zw)*y + cubicConstant`. -/
theorem cubicClass_eq :
    cubicClass =
      algebraMap QuadricBaseRing QuadricRootRing quadricConstant * quadricRoot +
        algebraMap QuadricBaseRing QuadricRootRing cubicConstant := by
  simp [cubicClass, cubicInY, quadricRoot]

/-- Multiplication by the cubic in the basis `1,y` has the expected
two-by-two matrix. -/
theorem cubicClass_leftMulMatrix :
    Algebra.leftMulMatrix quadricBasis cubicClass =
      !![cubicConstant, -(quadricConstant ^ 2);
        quadricConstant, cubicConstant - baseZ * quadricConstant] := by
  have hrepr (z : QuadricRootRing) (i : Fin 2) :
      quadricBasis.repr z i =
        (AdjoinRoot.modByMonicHom quadricInY_monic z).coeff i.val := by
    dsimp only [quadricBasis]
    rw [Basis.repr_reindex_apply,
      AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
    congr 1
  have hrem0 : cubicInY %ₘ quadricInY = cubicInY := by
    apply (modByMonic_eq_self_iff quadricInY_monic).mpr
    have hdegree : quadricInY.degree = (2 : WithBot ℕ) := by
      rw [degree_eq_natDegree quadricInY_monic.ne_zero,
        quadricInY_natDegree]
      norm_num
    rw [hdegree]
    change cubicInY.degree < ((2 : ℕ) : WithBot ℕ)
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp only [cubicInY, coeff_add, coeff_C_of_ne_zero hn0,
      coeff_C_mul_X, if_neg hn1, add_zero]
  have hrem1 :
      (cubicInY * X) %ₘ quadricInY =
        C (-(quadricConstant ^ 2)) +
          C (cubicConstant - baseZ * quadricConstant) * X := by
    let r : QuadricBaseRing[X] :=
      C (-(quadricConstant ^ 2)) +
        C (cubicConstant - baseZ * quadricConstant) * X
    have hcongr : (cubicInY * X) %ₘ quadricInY =
        r %ₘ quadricInY := by
      apply modByMonic_eq_of_dvd_sub quadricInY_monic
      refine ⟨C quadricConstant, ?_⟩
      dsimp only [r]
      simp only [quadricInY, cubicInY, map_sub, map_mul, map_neg,
        map_pow]
      ring
    rw [hcongr]
    apply (modByMonic_eq_self_iff quadricInY_monic).mpr
    have hdegree : quadricInY.degree = (2 : WithBot ℕ) := by
      rw [degree_eq_natDegree quadricInY_monic.ne_zero,
        quadricInY_natDegree]
      norm_num
    rw [hdegree]
    change r.degree < ((2 : ℕ) : WithBot ℕ)
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    dsimp only [r]
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    simp only [coeff_add, coeff_C_of_ne_zero hn0,
      coeff_C_mul_X, if_neg hn1, add_zero]
  have hmulRoot :
      AdjoinRoot.mk quadricInY cubicInY * quadricRoot =
        AdjoinRoot.mk quadricInY (cubicInY * X) := by
    rw [quadricRoot, AdjoinRoot.root, map_mul]
  change Algebra.leftMulMatrix quadricBasis
      (AdjoinRoot.mk quadricInY cubicInY) = _
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  all_goals rw [Algebra.leftMulMatrix_eq_repr_mul, hrepr]
  · rw [show quadricBasis _ = 1 by simp,
      mul_one, AdjoinRoot.modByMonicHom_mk, hrem0]
    simp [cubicInY]
  · rw [show quadricBasis _ = quadricRoot by simp,
      hmulRoot, AdjoinRoot.modByMonicHom_mk, hrem1]
    simp
    rw [← map_pow]
    simp only [coeff_C]
    simp
  · rw [show quadricBasis _ = 1 by simp,
      mul_one, AdjoinRoot.modByMonicHom_mk, hrem0]
    simp [cubicInY]
  · rw [show quadricBasis _ = quadricRoot by simp,
      hmulRoot, AdjoinRoot.modByMonicHom_mk, hrem1]
    simp
    rw [← map_pow]
    simp only [coeff_C]
    simp

/-- The determinant controlling multiplication by the cubic modulo the
quadric. -/
def cubicMultiplicationDeterminant : QuadricBaseRing :=
  cubicConstant * (cubicConstant - baseZ * quadricConstant) +
    quadricConstant ^ 3

/-- The multiplication matrix determinant is the displayed polynomial. -/
theorem cubicClass_leftMulMatrix_det :
    (Algebra.leftMulMatrix quadricBasis cubicClass).det =
      cubicMultiplicationDeterminant := by
  rw [cubicClass_leftMulMatrix]
  simp [Matrix.det_fin_two, cubicMultiplicationDeterminant]
  ring

/-- Evaluation at `(x,z,w)=(0,1,1)` witnesses that the determinant is
nonzero. -/
theorem cubicMultiplicationDeterminant_ne_zero :
    cubicMultiplicationDeterminant ≠ 0 := by
  intro h
  have heval := congrArg
    (MvPolynomial.aeval ![(0 : ZMod 2), 1, 1]) h
  norm_num [cubicMultiplicationDeterminant, cubicConstant,
    quadricConstant, baseX, baseZ, baseW, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at heval
  exact (by decide : (3 : ZMod 2) ≠ 0) heval

/-- Multiplication by the cubic class is injective in the quadric quotient. -/
theorem cubicClass_mul_injective :
    Function.Injective (Algebra.lmul QuadricBaseRing QuadricRootRing cubicClass) := by
  letI : Module.Free QuadricBaseRing QuadricRootRing :=
    quadricInY_monic.free_adjoinRoot
  letI : Module.Finite QuadricBaseRing QuadricRootRing :=
    quadricInY_monic.finite_adjoinRoot
  rw [← LinearMap.ker_eq_bot]
  by_contra hker
  have hdetZero :
      LinearMap.det
          (Algebra.lmul QuadricBaseRing QuadricRootRing cubicClass) = 0 :=
    LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker
  have hmatrix :
      ((LinearMap.toMatrix quadricBasis quadricBasis)
          (Algebra.lmul QuadricBaseRing QuadricRootRing cubicClass)).det =
        cubicMultiplicationDeterminant := by
    rw [← Algebra.leftMulMatrix_apply]
    exact cubicClass_leftMulMatrix_det
  have hdet :
      LinearMap.det
          (Algebra.lmul QuadricBaseRing QuadricRootRing cubicClass) =
        cubicMultiplicationDeterminant := by
    rw [← LinearMap.det_toMatrix quadricBasis]
    exact hmatrix
  rw [hdet] at hdetZero
  exact cubicMultiplicationDeterminant_ne_zero hdetZero

/-! ## Transport back to the canonical four-variable presentation -/

/-- The tower equivalence carries the principal quadric ideal to the
principal ideal generated by `quadricInY`. -/
theorem binaryTowerEquiv_quadricIdeal :
    Ideal.span {quadricInY} =
      Ideal.map binaryTowerEquiv.toRingHom
        (Ideal.span {canonicalQuadricPolynomial25Two}) := by
  rw [Ideal.map_span, Set.image_singleton]
  have hmap :
      binaryTowerEquiv.toRingEquiv.toRingHom
          canonicalQuadricPolynomial25Two = quadricInY :=
    binaryTowerEquiv_quadric
  rw [hmap]

/-- Quotienting the original four-variable ring by the quadric is the same
as adjoining a root of the separated monic quadratic. -/
def binaryQuadricQuotientEquiv :
    (BinaryHomogeneousRing ⧸
        Ideal.span {canonicalQuadricPolynomial25Two}) ≃+* QuadricRootRing :=
  Ideal.quotientEquiv
    (Ideal.span {canonicalQuadricPolynomial25Two})
    (Ideal.span {quadricInY}) binaryTowerEquiv.toRingEquiv
      binaryTowerEquiv_quadricIdeal

/-- The quotient equivalence acts on representatives by first applying the
polynomial-tower equivalence. -/
theorem binaryQuadricQuotientEquiv_mk (p : BinaryHomogeneousRing) :
    binaryQuadricQuotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span {canonicalQuadricPolynomial25Two}) p) =
      AdjoinRoot.mk quadricInY (binaryTowerEquiv p) := by
  exact Ideal.quotientEquiv_mk
    (Ideal.span {canonicalQuadricPolynomial25Two})
    (Ideal.span {quadricInY}) binaryTowerEquiv.toRingEquiv
      binaryTowerEquiv_quadricIdeal p

/-- In particular, the class of the canonical cubic is `cubicClass`. -/
theorem binaryQuadricQuotientEquiv_cubic :
    binaryQuadricQuotientEquiv
        (Ideal.Quotient.mk
          (Ideal.span {canonicalQuadricPolynomial25Two})
            canonicalCubicPolynomial25Two) = cubicClass := by
  rw [binaryQuadricQuotientEquiv_mk, binaryTowerEquiv_cubic]
  rfl

/-- The nonzero determinant says intrinsically that the cubic class is a
regular element of the quadric quotient. -/
theorem cubicClass_isSMulRegular :
    IsSMulRegular QuadricRootRing cubicClass := by
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro p hp
  apply cubicClass_mul_injective
  simpa [Algebra.lmul, Algebra.smul_def] using hp

/-- If a product by the canonical cubic lies in the quadric ideal, then its
other factor already lies in that ideal.  This is the original-coordinate
form of the determinant calculation. -/
theorem mem_quadricIdeal_of_cubic_mul_mem
    (p : BinaryHomogeneousRing)
    (hp : canonicalCubicPolynomial25Two * p ∈
      Ideal.span {canonicalQuadricPolynomial25Two}) :
    p ∈ Ideal.span {canonicalQuadricPolynomial25Two} := by
  have hprodZero :
      (Ideal.Quotient.mk
        (Ideal.span {canonicalQuadricPolynomial25Two})
          (canonicalCubicPolynomial25Two * p)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hprodTransported := congrArg binaryQuadricQuotientEquiv hprodZero
  rw [map_zero, binaryQuadricQuotientEquiv_mk, map_mul,
    binaryTowerEquiv_cubic] at hprodTransported
  have hpRootZero :
      AdjoinRoot.mk quadricInY (binaryTowerEquiv p) = 0 := by
    apply cubicClass_mul_injective
    simpa [cubicClass] using hprodTransported
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply binaryQuadricQuotientEquiv.injective
  rw [map_zero, binaryQuadricQuotientEquiv_mk, hpRootZero]

/-- The canonical quadric is nonzero; evaluation at the `y`-axis point
`(0,1,0,0)` detects its square term. -/
theorem canonicalQuadricPolynomial25Two_ne_zero :
    canonicalQuadricPolynomial25Two ≠ 0 := by
  intro h
  have heval := congrArg
    (MvPolynomial.aeval ![(0 : ZMod 2), 1, 0, 0]) h
  norm_num [canonicalQuadricPolynomial25Two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at heval

/-- The canonical quadric is regular in the ambient polynomial domain. -/
theorem canonicalQuadricPolynomial25Two_isSMulRegular :
    IsSMulRegular BinaryHomogeneousRing canonicalQuadricPolynomial25Two :=
  IsSMulRegular.of_ne_zero canonicalQuadricPolynomial25Two_ne_zero

/-- The quadric-cubic ideal is proper because both homogeneous equations
vanish at the origin. -/
theorem canonicalQuadricCubicIdeal_ne_top :
    Ideal.ofList
      [canonicalQuadricPolynomial25Two, canonicalCubicPolynomial25Two] ≠ ⊤ := by
  let evOrigin : BinaryHomogeneousRing →+* ZMod 2 :=
    (MvPolynomial.aeval ![(0 : ZMod 2), 0, 0, 0]).toRingHom
  have hle :
      Ideal.ofList
          [canonicalQuadricPolynomial25Two, canonicalCubicPolynomial25Two] ≤
        RingHom.ker evOrigin := by
    apply Ideal.span_le.mpr
    intro p hp
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl <;>
      simp [evOrigin, canonicalQuadricPolynomial25Two,
        canonicalCubicPolynomial25Two]
  intro htop
  have hOne : (1 : BinaryHomogeneousRing) ∈ RingHom.ker evOrigin := by
    apply hle
    rw [htop]
    exact Set.mem_univ _
  exact (one_ne_zero : (1 : ZMod 2) ≠ 0) (by
    simpa [evOrigin] using RingHom.mem_ker.mp hOne)

/-- The canonical quadric and cubic form a regular sequence in
`F₂[x,y,z,w]`. -/
theorem canonicalQuadricCubic_isRegular :
    RingTheory.Sequence.IsRegular BinaryHomogeneousRing
      [canonicalQuadricPolynomial25Two, canonicalCubicPolynomial25Two] := by
  constructor
  · apply RingTheory.Sequence.IsWeaklyRegular.cons
      canonicalQuadricPolynomial25Two_isSMulRegular
    rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro p hp
    rw [Submodule.mem_smul_pointwise_iff_exists] at hp ⊢
    rcases hp with ⟨q, -, hq⟩
    have hpIdeal := mem_quadricIdeal_of_cubic_mul_mem p <|
      Ideal.mem_span_singleton.mpr ⟨q, by
        simpa [smul_eq_mul] using hq.symm⟩
    rcases Ideal.mem_span_singleton.mp hpIdeal with ⟨q, hq⟩
    exact ⟨q, Submodule.mem_top, by
      simpa [smul_eq_mul] using hq.symm⟩
  · intro htop
    apply canonicalQuadricCubicIdeal_ne_top
    apply le_antisymm le_top
    intro p hp
    have hp' : p ∈
        Ideal.ofList
          [canonicalQuadricPolynomial25Two, canonicalCubicPolynomial25Two] •
            (⊤ : Submodule BinaryHomogeneousRing BinaryHomogeneousRing) := by
      rw [← htop]
      exact Submodule.mem_top
    simpa [Ideal.ofList, Submodule.span_smul_eq,
      Submodule.set_smul_top_eq_span] using hp'

end MazurProof.RationalPointsN25QuotientTwoRegularSequence
