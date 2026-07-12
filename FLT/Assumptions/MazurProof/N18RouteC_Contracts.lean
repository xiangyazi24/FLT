import FLT.Assumptions.MazurProof.TorsionDefs
import Mathlib.Data.ZMod.Basic

/-!
# Integration contracts for N18 Route C

The final contradiction is intentionally representation-free.  Every
geometric or arithmetic input is an explicit field of one block certificate.
-/

set_option autoImplicit false

namespace MazurProof.N18RouteC.Contracts

structure Types where
  CQ : Type
  CL : Type
  E0L : Type
  EhatL : Type
  JQ : Type
  JL : Type

structure CurveData (T : Types) where
  baseChangePoint : T.CQ → T.CL
  baseChangePoint_injective : Function.Injective baseChangePoint
  IsCusp : T.CQ → Prop

structure SplitData (T : Types) where
  sigma : T.CL ≃ T.CL
  tau : T.CL ≃ T.CL
  qPlus : T.CL → T.E0L
  qMinus : T.CL → T.EhatL
  qPlus_sigma : ∀ P, qPlus (sigma P) = qPlus P
  qMinus_tau : ∀ P, qMinus (tau P) = qMinus P
  qPlus_fiber_finite : ∀ Q : T.E0L, Set.Finite {P : T.CL | qPlus P = Q}
  qPlus_fiber_card_le_two :
    ∀ Q : T.E0L, Nat.card {P : T.CL // qPlus P = Q} ≤ 2

structure PicData
    (T : Types) [AddCommGroup T.JQ] [AddCommGroup T.JL]
    (C : CurveData T) where
  baseChangePic : T.JQ →+ T.JL
  baseChangePic_injective : Function.Injective baseChangePic
  abelJacobiQ : T.CQ → T.JQ
  abelJacobiQ_injective : Function.Injective abelJacobiQ
  abelJacobiL : T.CL → T.JL
  abelJacobi_baseChange : ∀ P : T.CQ,
    baseChangePic (abelJacobiQ P) = abelJacobiL (C.baseChangePoint P)

structure PushPullData
    (T : Types)
    [AddCommGroup T.E0L] [AddCommGroup T.EhatL] [AddCommGroup T.JL] where
  Phi : T.JL →+ T.E0L × T.EhatL
  Psi : T.E0L × T.EhatL →+ T.JL
  psi_phi : ∀ D : T.JL, Psi (Phi D) = 2 • D

structure ThreeDescentData
    (T : Types) [AddCommGroup T.E0L] [AddCommGroup T.EhatL] where
  H3 : AddSubgroup T.E0L
  T3 : H3
  order_T3 : addOrderOf (T3 : T.E0L) = 3
  card_H3 : Nat.card H3 = 3
  H3_annihilated : ∀ t : H3, 3 • (t : T.E0L) = 0
  phi : T.E0L →+ T.EhatL
  phiHat : T.EhatL →+ T.E0L
  ker_phi : phi.ker = H3
  phi_surjective : Function.Surjective phi
  phiHat_injective : Function.Injective phiHat
  phiHat_phi : ∀ P : T.E0L, phiHat (phi P) = 3 • P
  phi_phiHat : ∀ Q : T.EhatL, phi (phiHat Q) = 3 • Q
  weak_three_descent : ∀ P : T.E0L,
    ∃ t : H3, ∃ Q : T.E0L, P = (t : T.E0L) + 3 • Q

structure SeparatedData
    (T : Types)
    [AddCommGroup T.E0L] [AddCommGroup T.EhatL] [AddCommGroup T.JL] where
  e0_annihilated_21 : ∀ P : T.E0L, 21 • P = 0
  ehat_annihilated_21 : ∀ Q : T.EhatL, 21 • Q = 0
  pic_annihilated_42 : ∀ D : T.JL, 42 • D = 0

structure EnumerationData
    (T : Types)
    [AddCommGroup T.E0L] [AddCommGroup T.JL]
    [DecidableEq T.CL]
    (C : CurveData T) where
  e0EquivZMod21 : ZMod 21 ≃+ T.E0L
  pic0L_finite : Finite T.JL
  rationalPoints_finite : Set.Finite (Set.univ : Set T.CQ)
  candidates : Finset T.CL
  candidates_card_le_42 : candidates.card ≤ 42
  rational_point_mem_candidates :
    ∀ P : T.CQ, C.baseChangePoint P ∈ candidates
  rational_candidate_is_cusp :
    ∀ P : T.CQ, C.baseChangePoint P ∈ candidates → C.IsCusp P

theorem EnumerationData.all_rational_points_are_cusps
    {T : Types}
    [AddCommGroup T.E0L] [AddCommGroup T.JL]
    [DecidableEq T.CL]
    {C : CurveData T}
    (cert : EnumerationData T C) :
    ∀ P : T.CQ, C.IsCusp P := by
  intro P
  exact cert.rational_candidate_is_cusp P
    (cert.rational_point_mem_candidates P)

def TateProducesNoncusp (T : Types) (C : CurveData T) : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    HasRationalPointOfOrder E 18 → ∃ P : T.CQ, ¬ C.IsCusp P

theorem assemble_no_order_18
    (T : Types) (C : CurveData T)
    (modular : TateProducesNoncusp T C)
    (allCusps : ∀ P : T.CQ, C.IsCusp P)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 18 := by
  intro h18
  obtain ⟨P, hP⟩ := modular E h18
  exact hP (allCusps P)

end MazurProof.N18RouteC.Contracts
