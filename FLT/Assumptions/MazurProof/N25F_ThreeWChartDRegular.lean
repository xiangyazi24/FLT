import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MazurProof.N25F_ThreeWChartDRegular

open Polynomial

/-! ## Literal ternary W = 1 chart -/

abbrev WChartAmbientThree := MvPolynomial (Fin 3) (ZMod 3)

def wChartQuadricThree : WChartAmbientThree :=
  -MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 0 +
    MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 2

def wChartCubicThree : WChartAmbientThree :=
  MvPolynomial.X 0 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.X 0 * MvPolynomial.X 1 -
    MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.X 2 ^ 2 - MvPolynomial.X 2

def wChartEquationIdealThree : Ideal WChartAmbientThree :=
  Ideal.span {wChartQuadricThree, wChartCubicThree}

abbrev WChartQuotientThree :=
  WChartAmbientThree ⧸ wChartEquationIdealThree

def wChartDenominatorThree : WChartQuotientThree :=
  Ideal.Quotient.mk wChartEquationIdealThree
    (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 0 +
      MvPolynomial.X 2)

/-! ## Separate z and x in the coefficient ring -/

abbrev WChartFieldThree := ZMod 3

abbrev WChartZRingThree := WChartFieldThree[X]

abbrev WChartXZRingThree := WChartZRingThree[X]

def wChartZThree : WChartZRingThree := X

def wChartDenominatorXZThree : WChartXZRingThree :=
  C (wChartZThree - 1) * X + C wChartZThree

def wChartNumeratorXZThree : WChartXZRingThree :=
  X ^ 2 - C wChartZThree * X +
    C (wChartZThree ^ 2 - wChartZThree)

def wChartQuadricConstantXZThree : WChartXZRingThree :=
  -(X * C wChartZThree) - X + C wChartZThree

theorem wChartZ_sub_one_ne_zero : wChartZThree - 1 ≠ 0 := by
  intro h
  have hcoeff :=
    congrArg (fun p : WChartZRingThree => p.coeff 1) h
  simp [wChartZThree, Polynomial.coeff_one] at hcoeff

theorem wChartZ_sub_one_isRelPrime_wChartZ :
    IsRelPrime (wChartZThree - 1) wChartZThree := by
  intro d hdD hdz
  apply isUnit_of_dvd_one
  have hdiff :
      d ∣ wChartZThree - (wChartZThree - 1) :=
    dvd_sub hdz hdD
  have hone :
      wChartZThree - (wChartZThree - 1) =
        (1 : WChartZRingThree) := by
    ring
  rwa [hone] at hdiff

theorem wChartDenominatorXZThree_irreducible :
    Irreducible wChartDenominatorXZThree := by
  exact irreducible_C_mul_X_add_C wChartZ_sub_one_ne_zero
    wChartZ_sub_one_isRelPrime_wChartZ

theorem wChartDenominatorXZThree_prime :
    Prime wChartDenominatorXZThree := by
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp
    wChartDenominatorXZThree_irreducible

theorem wChartDenominatorIdealXZThree_isPrime :
    (Ideal.span
      ({wChartDenominatorXZThree} : Set WChartXZRingThree)).IsPrime := by
  exact
    (Ideal.span_singleton_prime
      wChartDenominatorXZThree_prime.ne_zero).mpr
        wChartDenominatorXZThree_prime

/- Keep polynomial constructions over the quotient on the semiring
projection of its canonical commutative-ring structure. -/
local instance wChartDenominatorQuotient_semiring :
    Semiring
      (WChartXZRingThree ⧸
        Ideal.span
          ({wChartDenominatorXZThree} : Set WChartXZRingThree)) :=
  (Ideal.Quotient.commRing
    (Ideal.span
      ({wChartDenominatorXZThree} : Set WChartXZRingThree))).toSemiring

noncomputable instance wChartDenominatorQuotient_isDomain :
    IsDomain
      (WChartXZRingThree ⧸
        Ideal.span
          ({wChartDenominatorXZThree} : Set WChartXZRingThree)) :=
  (Ideal.Quotient.isDomain_iff_prime
    (Ideal.span
      ({wChartDenominatorXZThree} : Set WChartXZRingThree))).mpr
        wChartDenominatorIdealXZThree_isPrime

theorem wChartNumeratorXZThree_monic :
    wChartNumeratorXZThree.Monic := by
  unfold wChartNumeratorXZThree
  monicity!

theorem wChartDenominatorXZThree_leadingCoeff :
    wChartDenominatorXZThree.leadingCoeff =
      wChartZThree - 1 := by
  exact leadingCoeff_linear wChartZ_sub_one_ne_zero

theorem wChartNumeratorXZThree_not_mem_denominatorIdeal :
    wChartNumeratorXZThree ∉
      Ideal.span
        ({wChartDenominatorXZThree} : Set WChartXZRingThree) := by
  intro hmem
  have hdvd :
      wChartDenominatorXZThree ∣ wChartNumeratorXZThree :=
    Ideal.mem_span_singleton.mp hmem
  have hunit :
      IsUnit wChartDenominatorXZThree.leadingCoeff :=
    wChartNumeratorXZThree_monic.isUnit_leadingCoeff_of_dvd hdvd
  have hzunit : IsUnit (wChartZThree - 1) := by
    rwa [wChartDenominatorXZThree_leadingCoeff] at hunit
  exact
    (Polynomial.not_isUnit_X_sub_C (1 : WChartFieldThree)) (by
      simpa [wChartZThree] using hzunit)

theorem wChartNumeratorXZThree_quotient_ne_zero :
    Ideal.Quotient.mk
        (Ideal.span
          ({wChartDenominatorXZThree} : Set WChartXZRingThree))
        wChartNumeratorXZThree ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact wChartNumeratorXZThree_not_mem_denominatorIdeal

/-! ## Two-element regular-sequence swap -/

theorem isLeftRegular_quotient_swapThree
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsLeftRegular D)
    (hc : IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsLeftRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by
  apply isLeftRegular_of_non_zero_divisor
  rintro ⟨f⟩ hf
  change
    Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D *
        Ideal.Quotient.mk (Ideal.span ({c} : Set B)) f = 0 at hf
  change Ideal.Quotient.mk (Ideal.span ({c} : Set B)) f = 0
  have hDf0 :
      Ideal.Quotient.mk (Ideal.span ({c} : Set B)) (D * f) = 0 := by
    simpa only [map_mul] using hf
  have hcf : c ∣ D * f :=
    (Ideal.Quotient.eq_zero_iff_dvd c (D * f)).mp hDf0
  obtain ⟨g, hg⟩ := hcf
  have hcg0 :
      Ideal.Quotient.mk (Ideal.span ({D} : Set B)) (c * g) = 0 := by
    rw [← hg]
    simp only [map_mul, Ideal.Quotient.mk_singleton_self, zero_mul]
  have hg0 :
      Ideal.Quotient.mk (Ideal.span ({D} : Set B)) g = 0 := by
    apply hc
    simpa only [map_mul, mul_zero] using hcg0
  have hDg : D ∣ g :=
    (Ideal.Quotient.eq_zero_iff_dvd D g).mp hg0
  obtain ⟨h, hgh⟩ := hDg
  apply (Ideal.Quotient.eq_zero_iff_dvd c f).mpr
  refine ⟨h, ?_⟩
  apply hD
  calc
    D * f = c * g := hg
    _ = c * (D * h) := by rw [hgh]
    _ = D * (c * h) := by ac_rfl

theorem isRegular_quotient_swapThree
    {B : Type*} [CommRing B] {D c : B}
    (hD : IsRegular D)
    (hc : IsRegular
      (Ideal.Quotient.mk (Ideal.span ({D} : Set B)) c)) :
    IsRegular
      (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) := by
  have hleft :
      IsLeftRegular
        (Ideal.Quotient.mk (Ideal.span ({c} : Set B)) D) :=
    isLeftRegular_quotient_swapThree hD.left hc.left
  refine ⟨hleft, ?_⟩
  intro x y hxy
  apply hleft
  simpa [mul_comm] using hxy

/-! ## Regularity through a monic root extension -/

theorem isRegular_algebraMap_adjoinRoot_of_monicThree
    {A : Type*} [CommRing A] [NoZeroDivisors A]
    (p : A[X]) (hp : p.Monic) {a : A} (ha : a ≠ 0) :
    IsRegular (algebraMap A (AdjoinRoot p) a) := by
  letI : Module.Free A (AdjoinRoot p) := hp.free_adjoinRoot
  have hscalar : IsSMulRegular (AdjoinRoot p) a :=
    Module.Flat.isSMulRegular_of_isRegular
      (IsRegular.of_ne_zero' ha)
  have hleft :
      IsLeftRegular (algebraMap A (AdjoinRoot p) a) := by
    intro x y hxy
    apply hscalar
    simpa only [Algebra.smul_def] using hxy
  refine ⟨hleft, ?_⟩
  intro x y hxy
  apply hleft
  simpa only [mul_comm] using hxy

/-! ## Impose the monic quadric, then the cubic -/

def wChartQuadricInYThree : WChartXZRingThree[X] :=
  X ^ 2 + C (C wChartZThree) * X +
    C wChartQuadricConstantXZThree

theorem wChartQuadricInYThree_monic :
    wChartQuadricInYThree.Monic := by
  unfold wChartQuadricInYThree
  monicity!

abbrev WChartQuadricRootRingThree :=
  AdjoinRoot wChartQuadricInYThree

def wChartDenominatorClassThree :
    WChartQuadricRootRingThree :=
  algebraMap WChartXZRingThree WChartQuadricRootRingThree
    wChartDenominatorXZThree

def wChartCubicInYThree : WChartXZRingThree[X] :=
  C wChartDenominatorXZThree * X +
    C wChartNumeratorXZThree

def wChartCubicClassThree :
    WChartQuadricRootRingThree :=
  AdjoinRoot.mk wChartQuadricInYThree wChartCubicInYThree

theorem wChartDenominatorClassThree_isRegular :
    IsRegular wChartDenominatorClassThree := by
  exact
    isRegular_algebraMap_adjoinRoot_of_monicThree
      wChartQuadricInYThree
      wChartQuadricInYThree_monic
      wChartDenominatorXZThree_prime.ne_zero

theorem map_wChartDenominatorIdealThree :
    Ideal.map (AdjoinRoot.of wChartQuadricInYThree)
        (Ideal.span
          ({wChartDenominatorXZThree} : Set WChartXZRingThree)) =
      Ideal.span
        ({wChartDenominatorClassThree} :
          Set WChartQuadricRootRingThree) := by
  rw [Ideal.map_span, Set.image_singleton]
  rfl

def wChartBoundaryQuadricThree :
    (WChartXZRingThree ⧸
      Ideal.span
        ({wChartDenominatorXZThree} : Set WChartXZRingThree))[X] :=
  wChartQuadricInYThree.map
    (Ideal.Quotient.mk
      (Ideal.span
        ({wChartDenominatorXZThree} : Set WChartXZRingThree)))

theorem wChartBoundaryQuadricThree_monic :
    wChartBoundaryQuadricThree.Monic := by
  exact wChartQuadricInYThree_monic.map _

def wChartBoundaryNumeratorThree :
    WChartXZRingThree ⧸
      Ideal.span
        ({wChartDenominatorXZThree} : Set WChartXZRingThree) :=
  Ideal.Quotient.mk
    (Ideal.span
      ({wChartDenominatorXZThree} : Set WChartXZRingThree))
    wChartNumeratorXZThree

theorem wChartBoundaryNumeratorThree_isRegular :
    IsRegular
      (AdjoinRoot.of wChartBoundaryQuadricThree
        wChartBoundaryNumeratorThree) := by
  exact
    isRegular_algebraMap_adjoinRoot_of_monicThree
      wChartBoundaryQuadricThree
      wChartBoundaryQuadricThree_monic
      wChartNumeratorXZThree_quotient_ne_zero

/-! ## Regularity of the cubic after imposing D = 0 -/

theorem isRegular_map_ringEquivThree
    {R S : Type*} [Ring R] [Ring S]
    (e : R ≃+* S) {r : R} (hr : IsRegular r) :
    IsRegular (e r) := by
  constructor
  · intro x y hxy
    apply e.symm.injective
    apply hr.left
    have h := congrArg e.symm hxy
    simpa only [map_mul, e.symm_apply_apply] using h
  · intro x y hxy
    apply e.symm.injective
    apply hr.right
    have h := congrArg e.symm hxy
    simpa only [map_mul, e.symm_apply_apply] using h

def wChartDenominatorQuotientEquivThree :
    WChartQuadricRootRingThree ⧸
        Ideal.span
          ({wChartDenominatorClassThree} :
            Set WChartQuadricRootRingThree) ≃+*
      AdjoinRoot wChartBoundaryQuadricThree :=
  (Ideal.quotEquivOfEq map_wChartDenominatorIdealThree.symm).trans
    (AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
      (Ideal.span
        ({wChartDenominatorXZThree} : Set WChartXZRingThree))
      wChartQuadricInYThree)

theorem wChartDenominatorQuotientEquivThree_cubic :
    wChartDenominatorQuotientEquivThree
        (Ideal.Quotient.mk
          (Ideal.span
            ({wChartDenominatorClassThree} :
              Set WChartQuadricRootRingThree))
          wChartCubicClassThree) =
      AdjoinRoot.of wChartBoundaryQuadricThree
        wChartBoundaryNumeratorThree := by
  have hD :
      Ideal.Quotient.mk
          (Ideal.span
            ({wChartDenominatorXZThree} : Set WChartXZRingThree))
          wChartDenominatorXZThree = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  rw [wChartDenominatorQuotientEquivThree,
    RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
        (Ideal.span
          ({wChartDenominatorXZThree} : Set WChartXZRingThree))
        wChartQuadricInYThree
        (Ideal.Quotient.mk
          ((Ideal.span
            ({wChartDenominatorXZThree} :
              Set WChartXZRingThree)).map
                (AdjoinRoot.of wChartQuadricInYThree))
          (AdjoinRoot.mk wChartQuadricInYThree
            wChartCubicInYThree)) = _
  rw [AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of]
  simp only [wChartCubicInYThree, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    hD, Polynomial.C_0, zero_mul, zero_add,
    wChartBoundaryNumeratorThree, AdjoinRoot.of,
    RingHom.comp_apply]
  rfl

theorem wChartCubicClass_mod_denominator_isRegular :
    IsRegular
      (Ideal.Quotient.mk
        (Ideal.span
          ({wChartDenominatorClassThree} :
            Set WChartQuadricRootRingThree))
        wChartCubicClassThree) := by
  have hmapped :
      IsRegular
        (wChartDenominatorQuotientEquivThree
          (Ideal.Quotient.mk
            (Ideal.span
              ({wChartDenominatorClassThree} :
                Set WChartQuadricRootRingThree))
            wChartCubicClassThree)) := by
    rw [wChartDenominatorQuotientEquivThree_cubic]
    exact wChartBoundaryNumeratorThree_isRegular
  have hback :=
    isRegular_map_ringEquivThree
      wChartDenominatorQuotientEquivThree.symm hmapped
  simpa only [RingEquiv.symm_apply_apply] using hback

theorem wChartDenominator_mod_cubic_isRegular :
    IsRegular
      (Ideal.Quotient.mk
        (Ideal.span
          ({wChartCubicClassThree} :
            Set WChartQuadricRootRingThree))
        wChartDenominatorClassThree) :=
  isRegular_quotient_swapThree
    wChartDenominatorClassThree_isRegular
    wChartCubicClass_mod_denominator_isRegular

/-! ## Explicit equivalence with the literal Fin 3 chart -/

def wChartVariableEquivThree :
    Fin 3 ≃ Option (Fin 2) :=
  finSuccEquiv' (1 : Fin 3)

@[simp]
theorem wChartVariableEquivThree_x :
    wChartVariableEquivThree 0 = some 0 := by
  decide

@[simp]
theorem wChartVariableEquivThree_y :
    wChartVariableEquivThree 1 = none := by
  decide

@[simp]
theorem wChartVariableEquivThree_z :
    wChartVariableEquivThree 2 = some 1 := by
  decide

def wChartXZBaseEquivThree :
    MvPolynomial (Fin 2) WChartFieldThree ≃ₐ[WChartFieldThree]
      WChartXZRingThree :=
  (MvPolynomial.finSuccEquiv WChartFieldThree 1).trans
    (Polynomial.mapAlgEquiv
      (MvPolynomial.uniqueAlgEquiv WChartFieldThree (Fin 1)))

@[simp]
theorem wChartXZBaseEquivThree_x :
    wChartXZBaseEquivThree
        (MvPolynomial.X (0 : Fin 2)) = X := by
  simp [wChartXZBaseEquivThree,
    MvPolynomial.finSuccEquiv_apply]

@[simp]
theorem wChartXZBaseEquivThree_z :
    wChartXZBaseEquivThree
        (MvPolynomial.X (1 : Fin 2)) =
      C wChartZThree := by
  simp [wChartXZBaseEquivThree, wChartZThree,
    MvPolynomial.finSuccEquiv_apply,
    show
      Fin.cases X
          (fun k : Fin 1 => C (MvPolynomial.X k))
          (1 : Fin 2) =
        C (MvPolynomial.X (0 : Fin 1)) by
      rfl]

def wChartAmbientTowerEquivThree :
    WChartAmbientThree ≃ₐ[WChartFieldThree]
      WChartXZRingThree[X] :=
  (MvPolynomial.renameEquiv WChartFieldThree
      wChartVariableEquivThree).trans
    ((MvPolynomial.optionEquivLeft WChartFieldThree
      (Fin 2)).trans
        (Polynomial.mapAlgEquiv wChartXZBaseEquivThree))

@[simp]
theorem wChartAmbientTowerEquivThree_x :
    wChartAmbientTowerEquivThree
        (MvPolynomial.X (0 : Fin 3)) =
      C X := by
  simp [wChartAmbientTowerEquivThree]

@[simp]
theorem wChartAmbientTowerEquivThree_y :
    wChartAmbientTowerEquivThree
        (MvPolynomial.X (1 : Fin 3)) =
      X := by
  simp [wChartAmbientTowerEquivThree]

@[simp]
theorem wChartAmbientTowerEquivThree_z :
    wChartAmbientTowerEquivThree
        (MvPolynomial.X (2 : Fin 3)) =
      C (C wChartZThree) := by
  simp [wChartAmbientTowerEquivThree]

theorem wChartAmbientTowerEquivThree_quadric :
    wChartAmbientTowerEquivThree wChartQuadricThree =
      wChartQuadricInYThree := by
  simp [wChartQuadricThree, wChartQuadricInYThree,
    wChartQuadricConstantXZThree]
  ring

theorem wChartAmbientTowerEquivThree_cubic :
    wChartAmbientTowerEquivThree wChartCubicThree =
      wChartCubicInYThree := by
  simp [wChartCubicThree, wChartCubicInYThree,
    wChartDenominatorXZThree, wChartNumeratorXZThree,
    wChartZThree]
  ring

def wChartQuadricIdealYThree :
    Ideal WChartXZRingThree[X] :=
  Ideal.span {wChartQuadricInYThree}

def wChartCubicIdealYThree :
    Ideal WChartXZRingThree[X] :=
  Ideal.span {wChartCubicInYThree}

def wChartQuadricCubicIdealYThree :
    Ideal WChartXZRingThree[X] :=
  Ideal.span {wChartQuadricInYThree, wChartCubicInYThree}

theorem wChartQuadricIdealY_sup_wChartCubicIdealY :
    wChartQuadricIdealYThree ⊔
        wChartCubicIdealYThree =
      wChartQuadricCubicIdealYThree := by
  rw [wChartQuadricIdealYThree, wChartCubicIdealYThree,
    wChartQuadricCubicIdealYThree, Ideal.span_insert]

theorem wChartAmbientTowerEquivThree_equationIdeal :
    wChartQuadricCubicIdealYThree =
      Ideal.map wChartAmbientTowerEquivThree.toRingHom
        wChartEquationIdealThree := by
  rw [wChartQuadricCubicIdealYThree,
    wChartEquationIdealThree, Ideal.map_span]
  congr 1
  ext p
  simp [wChartAmbientTowerEquivThree_quadric,
    wChartAmbientTowerEquivThree_cubic, eq_comm]

def wChartEquationQuotientEquivThree :
    WChartQuotientThree ≃+*
      WChartXZRingThree[X] ⧸
        wChartQuadricCubicIdealYThree :=
  Ideal.quotientEquiv wChartEquationIdealThree
    wChartQuadricCubicIdealYThree
    wChartAmbientTowerEquivThree.toRingEquiv
    wChartAmbientTowerEquivThree_equationIdeal

theorem map_wChartCubicIdealYThree :
    Ideal.map (AdjoinRoot.mk wChartQuadricInYThree)
        wChartCubicIdealYThree =
      Ideal.span
        ({wChartCubicClassThree} :
          Set WChartQuadricRootRingThree) := by
  rw [wChartCubicIdealYThree, Ideal.map_span,
    Set.image_singleton]
  rfl

def wChartTowerDoubleQuotientEquivThree :
    WChartQuadricRootRingThree ⧸
        Ideal.span
          ({wChartCubicClassThree} :
            Set WChartQuadricRootRingThree) ≃+*
      WChartXZRingThree[X] ⧸
        wChartQuadricCubicIdealYThree :=
  (Ideal.quotEquivOfEq
      map_wChartCubicIdealYThree.symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup
      wChartQuadricIdealYThree
      wChartCubicIdealYThree).trans
        (Ideal.quotEquivOfEq
          wChartQuadricIdealY_sup_wChartCubicIdealY))

def wChartQuotientTowerEquivThree :
    WChartQuotientThree ≃+*
      WChartQuadricRootRingThree ⧸
        Ideal.span
          ({wChartCubicClassThree} :
            Set WChartQuadricRootRingThree) :=
  wChartEquationQuotientEquivThree.trans
    wChartTowerDoubleQuotientEquivThree.symm

theorem wChartEquationQuotientEquivThree_mk
    (p : WChartAmbientThree) :
    wChartEquationQuotientEquivThree
        (Ideal.Quotient.mk wChartEquationIdealThree p) =
      Ideal.Quotient.mk
        wChartQuadricCubicIdealYThree
        (wChartAmbientTowerEquivThree p) := by
  exact
    Ideal.quotientEquiv_mk wChartEquationIdealThree
      wChartQuadricCubicIdealYThree
      wChartAmbientTowerEquivThree.toRingEquiv
      wChartAmbientTowerEquivThree_equationIdeal p

theorem wChartTowerDoubleQuotientEquivThree_mk
    (p : WChartXZRingThree[X]) :
    wChartTowerDoubleQuotientEquivThree
        (Ideal.Quotient.mk
          (Ideal.span
            ({wChartCubicClassThree} :
              Set WChartQuadricRootRingThree))
          (AdjoinRoot.mk wChartQuadricInYThree p)) =
      Ideal.Quotient.mk
        wChartQuadricCubicIdealYThree p := by
  rfl

theorem wChartQuotientTowerEquivThree_mk
    (p : WChartAmbientThree) :
    wChartQuotientTowerEquivThree
        (Ideal.Quotient.mk wChartEquationIdealThree p) =
      Ideal.Quotient.mk
        (Ideal.span
          ({wChartCubicClassThree} :
            Set WChartQuadricRootRingThree))
        (AdjoinRoot.mk wChartQuadricInYThree
          (wChartAmbientTowerEquivThree p)) := by
  rw [wChartQuotientTowerEquivThree,
    RingEquiv.trans_apply,
    wChartEquationQuotientEquivThree_mk]
  apply wChartTowerDoubleQuotientEquivThree.injective
  rw [RingEquiv.apply_symm_apply,
    wChartTowerDoubleQuotientEquivThree_mk]

theorem wChartQuotientTowerEquivThree_denominator :
    wChartQuotientTowerEquivThree
        wChartDenominatorThree =
      Ideal.Quotient.mk
        (Ideal.span
          ({wChartCubicClassThree} :
            Set WChartQuadricRootRingThree))
        wChartDenominatorClassThree := by
  unfold wChartDenominatorThree
  rw [wChartQuotientTowerEquivThree_mk]
  simp [wChartDenominatorClassThree,
    wChartDenominatorXZThree, wChartZThree]
  ring

theorem wChartDenominatorThree_isRegular :
    IsRegular wChartDenominatorThree := by
  have hmapped :
      IsRegular
        (wChartQuotientTowerEquivThree
          wChartDenominatorThree) := by
    rw [wChartQuotientTowerEquivThree_denominator]
    exact wChartDenominator_mod_cubic_isRegular
  have hback :=
    isRegular_map_ringEquivThree
      wChartQuotientTowerEquivThree.symm hmapped
  simpa only [RingEquiv.symm_apply_apply] using hback

theorem wChartDenominatorThree_mem_nonZeroDivisors :
    wChartDenominatorThree ∈
      nonZeroDivisors WChartQuotientThree := by
  exact
    isRegular_iff_mem_nonZeroDivisors.mp
      wChartDenominatorThree_isRegular

end MazurProof.N25F_ThreeWChartDRegular
