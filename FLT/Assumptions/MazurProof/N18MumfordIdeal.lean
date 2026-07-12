import FLT.Assumptions.MazurProof.N18MumfordBasis

/-!
# Mumford evaluation ideals for the N18 curve

The quotient evaluation `x ↦ x mod u`, `y ↦ v mod u` has kernel exactly
`(u,y-v)`.  This recovers the canonical Mumford polynomials from their ideal
and is the algebraic core of normal-form uniqueness.
-/

open Polynomial

namespace MazurProof.N18Mumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

abbrev MumfordResidue (D : SemiMumford K) : Type u :=
  K[X] ⧸ Ideal.span ({D.u} : Set K[X])

private theorem mumford_root_relation (D : SemiMumford K) :
    (curvePoly K).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0 := by
  change (X ^ 2 - C (f K)).eval₂
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
      (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v) = 0
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
    (D.v ^ 2 - f K) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨w, hw⟩ := D.curve_dvd
  refine ⟨-w, ?_⟩
  calc
    D.v ^ 2 - f K = -(f K - D.v ^ 2) := by ring
    _ = -(D.u * w) := by rw [hw]
    _ = D.u * (-w) := by ring

def mumfordEval (D : SemiMumford K) :
    CoordinateRing K →+* MumfordResidue K D :=
  AdjoinRoot.lift
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])))
    (Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v)
    (mumford_root_relation K D)

@[simp] theorem mumfordEval_xClass (D : SemiMumford K) (p : K[X]) :
    mumfordEval K D (xClass K p) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) p := by
  change mumfordEval K D (AdjoinRoot.of (curvePoly K) p) = _
  exact AdjoinRoot.lift_of (mumford_root_relation K D)

@[simp] theorem mumfordEval_yClass (D : SemiMumford K) :
    mumfordEval K D (yClass K) =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X])) D.v := by
  exact AdjoinRoot.lift_root (mumford_root_relation K D)

@[simp] theorem mumfordEval_ySubClass (D : SemiMumford K) :
    mumfordEval K D (ySubClass K D.v) = 0 := by
  simp [ySubClass]

theorem mumfordIdeal_le_ker (D : SemiMumford K) :
    mumfordIdeal K D.u D.v ≤ RingHom.ker (mumfordEval K D) := by
  apply Ideal.span_le.2
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · change mumfordEval K D (xClass K D.u) = 0
    rw [mumfordEval_xClass,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · change mumfordEval K D (ySubClass K D.v) = 0
    rw [mumfordEval_ySubClass]

theorem ker_mumfordEval (D : SemiMumford K) :
    RingHom.ker (mumfordEval K D) = mumfordIdeal K D.u D.v := by
  apply le_antisymm
  · intro z hz
    rw [RingHom.mem_ker] at hz
    let p : K[X] := coeff0 K z
    let q : K[X] := coeffY K z
    have hz' : mumfordEval K D
        (xClass K p + xClass K q * yClass K) = 0 := by
      rw [recompose K z]
      exact hz
    have hquot : Ideal.Quotient.mk (Ideal.span ({D.u} : Set K[X]))
        (p + q * D.v) = 0 := by
      simpa only [map_add, map_mul, mumfordEval_xClass,
        mumfordEval_yClass, map_add, map_mul] using hz'
    have hdvd : D.u ∣ p + q * D.v := by
      exact Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hquot)
    obtain ⟨s, hs⟩ := hdvd
    have hu : xClass K D.u ∈ mumfordIdeal K D.u D.v :=
      xClass_mem_mumfordIdeal K D.u D.v
    have hyv : ySubClass K D.v ∈ mumfordIdeal K D.u D.v :=
      Ideal.subset_span (by simp)
    have hbase : xClass K (p + q * D.v) ∈
        mumfordIdeal K D.u D.v := by
      rw [hs, xClass_mul, mul_comm]
      exact Ideal.mul_mem_left (mumfordIdeal K D.u D.v) (xClass K s) hu
    have hgraph : xClass K q * ySubClass K D.v ∈
        mumfordIdeal K D.u D.v :=
      Ideal.mul_mem_left (mumfordIdeal K D.u D.v) (xClass K q) hyv
    rw [← recompose K z]
    have hdecomp :
        xClass K p + xClass K q * yClass K =
          xClass K (p + q * D.v) + xClass K q * ySubClass K D.v := by
      simp only [xClass_add, xClass_mul, ySubClass]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hbase hgraph
  · exact mumfordIdeal_le_ker K D

theorem mumfordIdeal_comap_base (D : SemiMumford K) :
    (mumfordIdeal K D.u D.v).comap (xClassHom K) =
      Ideal.span ({D.u} : Set K[X]) := by
  rw [← ker_mumfordEval]
  ext p
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply,
    xClassHom_apply, mumfordEval_xClass,
    Ideal.Quotient.eq_zero_iff_mem]

end

end MazurProof.N18Mumford
