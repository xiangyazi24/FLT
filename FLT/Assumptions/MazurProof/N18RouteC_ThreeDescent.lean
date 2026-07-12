import FLT.Assumptions.MazurProof.N18RouteC_Separated
import FLT.Assumptions.MazurProof.N18RouteC_LocalThree

/-!
# The finite `3`-isogeny descent chase for N18 Route C

The `84` candidate calculation is kept separate from the arithmetic Kummer
soundness certificate.  Given exact kernels and localization soundness, the
survivor tables imply `E₀(L)=⟨T⟩+3E₀(L)` by a direct group chase.
-/

namespace MazurProof.N18RouteC.ThreeDescent

noncomputable section

abbrev F3 := Fin 3
abbrev DualClass := Fin 4 → F3
abbrev PhiClass := F3

def mkDual (i j k l : F3) : DualClass := ![i, j, k, l]

def dualTClass : DualClass := mkDual 0 0 2 0

abbrev DualLocal2 := F3
abbrev DualLocal3 := DualClass
abbrev PhiLocal2 := F3
abbrev PhiLocal3 := Fin 4 → F3

def locDual2 (c : DualClass) : DualLocal2 := c 2
def locDual3 (c : DualClass) : DualLocal3 := c
def locPhi2 (r : PhiClass) : PhiLocal2 := r
def locPhi3 (r : PhiClass) : PhiLocal3 := ![r, 0, 0, 0]

def inDualImage2b (_ : DualLocal2) : Bool := true

def inDualImage3b (c : DualLocal3) : Bool :=
  decide (LocalThree.PassDual3Finite (c 0) (c 1) (c 2) (c 3))

def inPhiImage2b (r : PhiLocal2) : Bool := decide (r = 0)
def inPhiImage3b (v : PhiLocal3) : Bool := decide (v 0 = 0)

def passDualb (c : DualClass) : Bool :=
  inDualImage2b (locDual2 c) && inDualImage3b (locDual3 c)

def passPhib (r : PhiClass) : Bool :=
  inPhiImage2b (locPhi2 r) && inPhiImage3b (locPhi3 r)

def inDualImage2 (c : DualLocal2) : Prop := inDualImage2b c = true
def inDualImage3 (c : DualLocal3) : Prop := inDualImage3b c = true
def inPhiImage2 (r : PhiLocal2) : Prop := inPhiImage2b r = true
def inPhiImage3 (v : PhiLocal3) : Prop := inPhiImage3b v = true
def passDual (c : DualClass) : Prop := passDualb c = true
def passPhi (r : PhiClass) : Prop := passPhib r = true

def dualSelmerCode : Finset DualClass :=
  Finset.univ.filter fun c => passDualb c = true

def phiSelmerCode : Finset PhiClass :=
  Finset.univ.filter fun r => passPhib r = true

theorem candidate_count :
    Fintype.card DualClass + Fintype.card PhiClass = 84 := by
  set_option maxHeartbeats 0 in
    decide

theorem local_image_cardinalities :
    (Finset.univ.filter fun c => inDualImage2b c = true).card = 3 ∧
    (Finset.univ.filter fun c => inDualImage3b c = true).card = 3 ∧
    (Finset.univ.filter fun r => inPhiImage2b r = true).card = 1 ∧
    (Finset.univ.filter fun v => inPhiImage3b v = true).card = 27 := by
  set_option maxHeartbeats 0 in
    decide

theorem phiSelmerCode_eq :
    phiSelmerCode = ({0} : Finset PhiClass) := by
  set_option maxHeartbeats 0 in
    decide

theorem dualSelmerCode_eq :
    dualSelmerCode =
      ({mkDual 0 0 0 0, mkDual 0 0 1 0, mkDual 0 0 2 0} :
        Finset DualClass) := by
  set_option maxHeartbeats 0 in
    decide

theorem passPhi_iff_all :
    ∀ r : PhiClass, passPhi r ↔ r = 0 := by
  intro r
  simp [passPhi, passPhib, inPhiImage2b, inPhiImage3b,
    locPhi2, locPhi3]

theorem passDual_iff_all :
    ∀ c : DualClass,
      passDual c ↔ ∃ k : F3, c = mkDual 0 0 k 0 := by
  intro c
  constructor
  · intro hc
    have hcoords : c 0 = 0 ∧ c 1 = 0 ∧ c 3 = 0 := by
      simpa [passDual, passDualb, inDualImage2b, inDualImage3b,
        locDual2, locDual3, LocalThree.passDual3Finite_iff] using hc
    refine ⟨c 2, ?_⟩
    funext i
    fin_cases i <;> simp [mkDual, hcoords.1, hcoords.2.1, hcoords.2.2]
  · rintro ⟨k, rfl⟩
    simp [passDual, passDualb, inDualImage2b, inDualImage3b,
      locDual2, locDual3, mkDual, LocalThree.passDual3Finite_iff]

theorem dualLine_represented :
    ∀ k : F3, ∃ n : Fin 3,
      n.val • dualTClass = mkDual 0 0 k 0 := by
  set_option maxHeartbeats 0 in
    decide

section Chase

variable {E Ehat : Type*} [AddCommGroup E] [AddCommGroup Ehat]
variable (T : E)

structure IsogenyData where
  phi : E →+ Ehat
  phihat : Ehat →+ E
  phihat_phi : ∀ P : E, phihat (phi P) = 3 • P
  phi_phihat : ∀ Q : Ehat, phi (phihat Q) = 3 • Q
  T_order : 3 • T = 0

structure KummerData (I : IsogenyData (E := E) (Ehat := Ehat) T) where
  deltaHat : E →+ DualClass
  deltaPhi : Ehat →+ PhiClass
  deltaHat_T : deltaHat T = dualTClass
  kernelHat : ∀ P : E,
    deltaHat P = 0 ↔ ∃ Q : Ehat, I.phihat Q = P
  kernelPhi : ∀ Q : Ehat,
    deltaPhi Q = 0 ↔ ∃ P : E, I.phi P = Q
  deltaHat_local : ∀ P : E, passDual (deltaHat P)
  deltaPhi_local : ∀ Q : Ehat, passPhi (deltaPhi Q)

theorem weakThreeDescent
    (I : IsogenyData (E := E) (Ehat := Ehat) T)
    (D : KummerData (E := E) (Ehat := Ehat) T I)
    (P : E) :
    ∃ n : Fin 3, ∃ Q : E,
      P = n.val • T + 3 • Q := by
  have hdual : passDual (D.deltaHat P) := D.deltaHat_local P
  obtain ⟨k, hk⟩ := (passDual_iff_all (D.deltaHat P)).mp hdual
  obtain ⟨n, hn⟩ := dualLine_represented k
  have hTclass : D.deltaHat (n.val • T) = mkDual 0 0 k 0 := by
    simpa only [map_nsmul, D.deltaHat_T] using hn
  have hkerHat : D.deltaHat (P - n.val • T) = 0 := by
    rw [map_sub, hk, hTclass, sub_self]
  obtain ⟨R, hR⟩ := (D.kernelHat (P - n.val • T)).mp hkerHat
  have hphi : passPhi (D.deltaPhi R) := D.deltaPhi_local R
  have hkerPhi : D.deltaPhi R = 0 :=
    (passPhi_iff_all (D.deltaPhi R)).mp hphi
  obtain ⟨Q, hQ⟩ := (D.kernelPhi R).mp hkerPhi
  refine ⟨n, Q, ?_⟩
  calc
    P = n.val • T + I.phihat R := by rw [hR]; abel
    _ = n.val • T + I.phihat (I.phi Q) := by rw [hQ]
    _ = n.val • T + 3 • Q := by rw [I.phihat_phi]

theorem weakThreeDescent_with_killed_representative
    (I : IsogenyData (E := E) (Ehat := Ehat) T)
    (D : KummerData (E := E) (Ehat := Ehat) T I)
    (P : E) :
    ∃ h : E, 3 • h = 0 ∧
      ∃ Q : E, P = h + 3 • Q := by
  obtain ⟨n, Q, hPQ⟩ := weakThreeDescent T I D P
  refine ⟨n.val • T, ?_, Q, hPQ⟩
  calc
    3 • (n.val • T) = n.val • (3 • T) :=
      Separated.nsmul_nsmul_comm 3 n.val T
    _ = 0 := by rw [I.T_order, nsmul_zero]

end Chase

end

end MazurProof.N18RouteC.ThreeDescent
