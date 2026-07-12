import FLT.Assumptions.MazurProof.N18OrientedPic

/-!
# Recovering Mumford polynomials from their ideals

The kernel description of the quotient evaluation recovers the monic
polynomial `u` by contraction to `K[X]`, and then recovers the canonical
remainder `v`.
-/

open Polynomial

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem u_eq_of_mumfordIdeal_eq {D₁ D₂ : SemiMumford K}
    (h : mumfordIdeal K D₁.u D₁.v = mumfordIdeal K D₂.u D₂.v) :
    D₁.u = D₂.u := by
  have hc := congrArg (fun I : Ideal (CoordinateRing K) ↦
    I.comap (xClassHom K)) h
  rw [mumfordIdeal_comap_base K D₁, mumfordIdeal_comap_base K D₂] at hc
  exact eq_of_monic_of_associated D₁.u_monic D₂.u_monic
    (Ideal.span_singleton_eq_span_singleton.mp hc)

theorem v_eq_of_mumfordIdeal_eq_of_u_eq {D₁ D₂ : SemiMumford K}
    (hu : D₁.u = D₂.u)
    (h : mumfordIdeal K D₁.u D₁.v = mumfordIdeal K D₂.u D₂.v) :
    D₁.v = D₂.v := by
  have hy₂ : ySubClass K D₂.v ∈ mumfordIdeal K D₁.u D₁.v := by
    rw [h]
    exact ySubClass_mem_mumfordIdeal K D₂.u D₂.v
  have hker : ySubClass K D₂.v ∈ RingHom.ker (mumfordEval K D₁) := by
    rw [ker_mumfordEval K D₁]
    exact hy₂
  have heval : mumfordEval K D₁ (ySubClass K D₂.v) = 0 :=
    RingHom.mem_ker.mp hker
  have hquot : Ideal.Quotient.mk (Ideal.span ({D₁.u} : Set K[X]))
      (D₁.v - D₂.v) = 0 := by
    simpa only [ySubClass, map_sub, mumfordEval_yClass,
      mumfordEval_xClass, sub_eq_zero] using heval
  have hdvd : D₁.u ∣ D₁.v - D₂.v :=
    Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
  have hmod : D₁.v % D₁.u = D₂.v % D₁.u :=
    mod_eq_of_dvd_sub hdvd
  rw [D₁.v_reduced, hu, D₂.v_reduced] at hmod
  exact hmod

theorem uv_eq_of_mumfordIdeal_eq {D₁ D₂ : SemiMumford K}
    (h : mumfordIdeal K D₁.u D₁.v = mumfordIdeal K D₂.u D₂.v) :
    D₁.u = D₂.u ∧ D₁.v = D₂.v := by
  have hu := u_eq_of_mumfordIdeal_eq K h
  exact ⟨hu, v_eq_of_mumfordIdeal_eq_of_u_eq K hu h⟩

theorem mumford_eq_of_ideal_eq_of_nInf_eq {D₁ D₂ : Mumford K}
    (hIdeal : mumfordIdeal K D₁.u D₁.v = mumfordIdeal K D₂.u D₂.v)
    (hInf : D₁.nInf = D₂.nInf) : D₁ = D₂ := by
  obtain ⟨hu, hv⟩ := uv_eq_of_mumfordIdeal_eq K
    (D₁ := D₁.toSemi) (D₂ := D₂.toSemi) hIdeal
  cases D₁
  cases D₂
  simp_all

end

end MazurProof.N18Mumford
