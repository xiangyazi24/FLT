import FLT.Assumptions.MazurProof.N13TwoAdicAbelChartData
import Mathlib.RingTheory.Henselian

/-!
# Recovering the N13 two-disk divisor from an integral Mumford graph

Suppose a smooth integral generalized Mumford graph reduces to the fixed
nonspecial graph `(X² + X, 0)`.  Hensel lifting splits its monic quadratic
into one root in each of the residue disks of `0` and `-1`.  Evaluating the
curve relation at those roots and using uniqueness in the vertical Hensel
fibres identifies the graph values with the canonical disk lifts.

Consequently every such integral graph comes from a unique `DiskPair`, up
to the harmless operation of changing its graph polynomial by a multiple
of `u`.  This is the algebraic reverse of
`N13TwoAdicAbelChartData.DiskPair.smoothMumford`; no divisor enumeration or
properness shortcut is used.
-/

open Polynomial

namespace MazurProof.N13TwoAdicAbelChartRecover

noncomputable section

local instance : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev K : Type :=
  N13GoodCoordinateRingTwo.K

abbrev maximal : Ideal R₂ :=
  IsLocalRing.maximalIdeal R₂

/-- Smooth integral Mumford data whose graph has the selected nonspecial
special fibre. -/
structure NearBaseMumford
    extends N13GeneralizedMumfordReduction.SmoothMumford₂ where
  reduce_u :
    N13GeneralizedMumfordReduction.reducePoly u =
      (X ^ 2 + X : K[X])
  reduce_v :
    N13GeneralizedMumfordReduction.reducePoly v = 0

namespace NearBaseMumford

variable (D : NearBaseMumford)

/-- Every two-disk divisor gives near-base integral data. -/
def ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    NearBaseMumford where
  toSmoothMumford₂ := P.smoothMumford
  reduce_u := P.reducePoly_u
  reduce_v := P.reducePoly_v

@[simp] theorem ofDiskPair_u
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).u = P.u := rfl

@[simp] theorem ofDiskPair_v
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).v = P.v := rfl

theorem mem_maximal_iff_reduceBase_eq_zero
    (a : R₂) :
    a ∈ maximal ↔
      N13GeneralizedMumfordReduction.reduceBase a = 0 := by
  constructor
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) := by
      rw [PadicInt.ker_toZMod]
      exact ha
    exact RingHom.mem_ker.mp hker
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) :=
      RingHom.mem_ker.mpr ha
    rw [PadicInt.ker_toZMod] at hker
    exact hker

theorem isUnit_of_reduceBase_eq_one
    {a : R₂}
    (ha :
      N13GeneralizedMumfordReduction.reduceBase a = 1) :
    IsUnit a := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  apply (mem_maximal_iff_reduceBase_eq_zero (a - 1)).2
  rw [map_sub, ha, map_one, sub_self]

theorem reduceBase_eval
    (p : R₂[X]) (a : R₂) :
    N13GeneralizedMumfordReduction.reduceBase (p.eval a) =
      (N13GeneralizedMumfordReduction.reducePoly p).eval
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    Polynomial.eval_map_apply]

theorem reduceBase_derivative_eval
    (p : R₂[X]) (a : R₂) :
    N13GeneralizedMumfordReduction.reduceBase
        (p.derivative.eval a) =
      (N13GeneralizedMumfordReduction.reducePoly p).derivative.eval
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    Polynomial.derivative_map, Polynomial.eval_map_apply]

theorem u_eval_zero_mem :
    D.u.eval 0 ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]

theorem u_eval_negOne_mem :
    D.u.eval (-1) ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
  exact htwo

theorem derivative_eval_zero_isUnit :
    IsUnit (D.u.derivative.eval 0) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]

theorem derivative_eval_negOne_isUnit :
    IsUnit (D.u.derivative.eval (-1)) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
  linear_combination htwo

/-- The root of `u` in the residue disk of zero. -/
theorem exists_root_zeroDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic 0 D.u_eval_zero_mem
      (D.derivative_eval_zero_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx

/-- The root of `u` in the residue disk of `-1`. -/
theorem exists_root_negOneDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x + 1 ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic (-1) D.u_eval_negOne_mem
      (D.derivative_eval_negOne_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx

/-- The two Hensel roots, selected in their distinct residue disks. -/
def x₀ : R₂ :=
  Classical.choose D.exists_root_zeroDisk

def x₁ : R₂ :=
  Classical.choose D.exists_root_negOneDisk

theorem x₀_spec :
    D.u.eval D.x₀ = 0 ∧ D.x₀ ∈ maximal :=
  Classical.choose_spec D.exists_root_zeroDisk

theorem x₁_spec :
    D.u.eval D.x₁ = 0 ∧ D.x₁ + 1 ∈ maximal :=
  Classical.choose_spec D.exists_root_negOneDisk

/-- The disk pair cut out by the two Hensel factors of `u`. -/
def diskPair :
    N13TwoAdicAbelChartData.DiskPair where
  x₀ := D.x₀
  x₁ := D.x₁
  x₀_mem := D.x₀_spec.2
  x₁_add_one_mem := D.x₁_spec.2

@[simp] theorem diskPair_x₀ :
    D.diskPair.x₀ = D.x₀ := rfl

@[simp] theorem diskPair_x₁ :
    D.diskPair.x₁ = D.x₁ := rfl

theorem u_natDegree :
    D.u.natDegree = 2 := by
  calc
    D.u.natDegree =
        (D.u.map
          N13GeneralizedMumfordReduction.reduceBase).natDegree :=
      (D.u_monic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase).symm
    _ =
        (N13GeneralizedMumfordReduction.reducePoly D.u).natDegree := rfl
    _ = (X ^ 2 + X : K[X]).natDegree := by rw [D.reduce_u]
    _ = 2 := by
      compute_degree
      norm_num [K, N13GoodCoordinateRingTwo.K,
        N13GoodModelTwo.F2]

theorem diskPair_u_natDegree :
    D.diskPair.u.natDegree = 2 := by
  rw [N13TwoAdicAbelChartData.DiskPair.u,
    Polynomial.natDegree_mul
      (monic_X_sub_C D.diskPair.x₀).ne_zero
      (monic_X_sub_C D.diskPair.x₁).ne_zero]
  simp

theorem diskPair_u_dvd :
    D.diskPair.u ∣ D.u := by
  have h₀ : X - C D.diskPair.x₀ ∣ D.u := by
    rw [dvd_iff_isRoot, IsRoot, D.diskPair_x₀]
    exact D.x₀_spec.1
  have h₁ : X - C D.diskPair.x₁ ∣ D.u := by
    rw [dvd_iff_isRoot, IsRoot, D.diskPair_x₁]
    exact D.x₁_spec.1
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      D.diskPair.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_comm] using hprod

/-- The recovered disk pair has exactly the original monic quadratic. -/
theorem diskPair_u :
    D.diskPair.u = D.u := by
  exact
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      D.diskPair.u_monic D.u_monic D.diskPair_u_dvd
      (by rw [D.u_natDegree, D.diskPair_u_natDegree])).symm

theorem v_eval_mem_maximal
    (x : R₂) :
    D.v.eval x ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_v]
  simp

theorem v_eval_on_curve
    {x : R₂} (hx : D.u.eval x = 0) :
    N13GoodModelTwo.AffineEquation x (D.v.eval x) := by
  have h :=
    congrArg (fun p : R₂[X] => p.eval x) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at h
  rw [hx, zero_mul] at h
  rw [N13GoodModelTwo.affineEquation_iff_residual]
  simpa [N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using h

theorem v_eval_x₀ :
    D.v.eval D.diskPair.x₀ = D.diskPair.y₀ := by
  exact
    N13TwoAdicDisks.y_eq_zeroDiskY
      D.diskPair.x₀ D.diskPair.x₀_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₀]
        exact D.x₀_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₀)

theorem v_eval_x₁ :
    D.v.eval D.diskPair.x₁ = D.diskPair.y₁ := by
  exact
    N13TwoAdicDisks.y_eq_negOneDiskY
      D.diskPair.x₁ D.diskPair.x₁_add_one_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₁]
        exact D.x₁_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₁)

/-- The original graph polynomial and the recovered interpolant agree
modulo the recovered quadratic. -/
theorem diskPair_u_dvd_v_sub :
    D.diskPair.u ∣ D.v - D.diskPair.v := by
  have h₀ :
      X - C D.diskPair.x₀ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₀,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₀,
      sub_self]
  have h₁ :
      X - C D.diskPair.x₁ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₁,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₁,
      sub_self]
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      D.diskPair.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_comm] using hprod

theorem u_dvd_v_sub_diskPair_v :
    D.u ∣ D.v - D.diskPair.v := by
  rw [← D.diskPair_u]
  exact D.diskPair_u_dvd_v_sub

/-- Generalized Mumford graph ideals only depend on `v` modulo `u`. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v w : R₂[X]) (hvw : u ∣ v - w) :
    N13GeneralizedMumfordIntegral.mumfordIdeal u v =
      N13GeneralizedMumfordIntegral.mumfordIdeal u w := by
  obtain ⟨q, hq⟩ := hvw
  have hmultiple :
      N13GeneralizedMumfordIntegral.xClass (v - w) =
        N13GeneralizedMumfordIntegral.xClass u *
          N13GeneralizedMumfordIntegral.xClass q := by
    rw [hq, N13GeneralizedMumfordIntegral.xClass_mul]
  have hyw :
      N13GeneralizedMumfordIntegral.ySubClass w =
        N13GeneralizedMumfordIntegral.ySubClass v +
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    simp [N13GeneralizedMumfordIntegral.ySubClass]
  have hyv :
      N13GeneralizedMumfordIntegral.ySubClass v =
        N13GeneralizedMumfordIntegral.ySubClass w -
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    rw [hyw]
    ring
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w
    · rw [hyv, hmultiple]
      exact Ideal.sub_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u w)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u w)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v
    · rw [hyw, hmultiple]
      exact Ideal.add_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u v)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u v)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v))

/-- The recovered disk pair cuts out exactly the original integral graph
ideal. -/
theorem mumfordIdeal_diskPair :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        D.diskPair.u D.diskPair.v := by
  rw [D.diskPair_u]
  exact mumfordIdeal_eq_of_dvd_sub
    D.u D.v D.diskPair.v D.u_dvd_v_sub_diskPair_v

/-- The disk pair associated with a near-base graph is unique. -/
theorem existsUnique_diskPair :
    ∃! P : N13TwoAdicAbelChartData.DiskPair,
      P.u = D.u ∧ D.u ∣ D.v - P.v := by
  refine
    ⟨D.diskPair,
      ⟨D.diskPair_u, D.u_dvd_v_sub_diskPair_v⟩, ?_⟩
  intro P hP
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  exact hP.1.trans D.diskPair_u.symm

@[simp] theorem diskPair_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).diskPair = P := by
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  rw [(ofDiskPair P).diskPair_u]
  rfl

end NearBaseMumford

end

end MazurProof.N13TwoAdicAbelChartRecover
