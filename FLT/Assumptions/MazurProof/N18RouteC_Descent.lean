import FLT.Assumptions.MazurProof.N18RouteC_Split

/-!
# Pure descent and annihilator layer for N18 Route C

This file contains the finite 84-row wrapper and the group-theoretic part of
the `3`-descent/formal-kernel argument.  Arithmetic soundness of the local
predicates is supplied by the later fixed-field modules; no Selmer-rank
inference is made here.
-/

namespace MazurProof.N18RouteC

/-! ## The finite candidate wrapper -/

abbrev F3 := Fin 3

structure DualCandidate where
  i : F3
  j : F3
  k : F3
  l : F3
  deriving DecidableEq, Fintype

def passDual2 (_ : DualCandidate) : Bool := true

def passDual3 (c : DualCandidate) : Bool :=
  decide (c.i = 0 ∧ c.j = 0 ∧ c.l = 0)

def dualSurvivors : Finset DualCandidate :=
  Finset.univ.filter fun c => passDual2 c && passDual3 c

theorem dual_candidate_count : Fintype.card DualCandidate = 81 := by
  decide

theorem dual_survivor_count : dualSurvivors.card = 3 := by
  set_option maxHeartbeats 0 in
    decide

theorem mem_dualSurvivors_iff (c : DualCandidate) :
    c ∈ dualSurvivors ↔ c.i = 0 ∧ c.j = 0 ∧ c.l = 0 := by
  simp [dualSurvivors, passDual2, passDual3]

abbrev PhiCandidate := F3

def passPhi2 (r : PhiCandidate) : Bool := decide (r = 0)
def passPhi3 (r : PhiCandidate) : Bool := decide (r = 0)

def phiSurvivors : Finset PhiCandidate :=
  Finset.univ.filter fun r => passPhi2 r && passPhi3 r

theorem phi_candidate_count : Fintype.card PhiCandidate = 3 := by
  decide

theorem phi_survivor_count : phiSurvivors.card = 1 := by
  decide

theorem mem_phiSurvivors_iff (r : PhiCandidate) :
    r ∈ phiSurvivors ↔ r = 0 := by
  simp [phiSurvivors, passPhi2, passPhi3]

theorem descent_candidate_count :
    Fintype.card PhiCandidate + Fintype.card DualCandidate = 84 := by
  norm_num [phi_candidate_count, dual_candidate_count]

/-! ## Weak descent and separated filtrations -/

section WeakDescent

variable {G : Type*} [AddCommGroup G]

def WeakDescent (m : ℕ) (H : AddSubgroup G) : Prop :=
  ∀ x : G, ∃ h : H, ∃ y : G, x = (h : G) + m • y

def InfinitelyDivisibleIn (m : ℕ) (H : AddSubgroup G) (x : H) : Prop :=
  ∀ n : ℕ, ∃ q : H, (m ^ n) • q = x

theorem weakDescent_iterate
    (m : ℕ) (H : AddSubgroup G)
    (hweak : WeakDescent m H) :
    ∀ n : ℕ, ∀ x : G,
      ∃ h : H, ∃ y : G, x = (h : G) + (m ^ n) • y := by
  intro n
  induction n with
  | zero =>
      intro x
      exact ⟨0, x, by simp⟩
  | succ n ih =>
      intro x
      obtain ⟨h, y, hxy⟩ := ih x
      obtain ⟨h', y', hy⟩ := hweak y
      refine ⟨h + (m ^ n) • h', y', ?_⟩
      rw [hxy, hy]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_nsmul, nsmul_add,
        pow_succ, mul_nsmul]
      simp [smul_smul, Nat.mul_comm, add_assoc]

/-- A multiplier-raising separated filtration, stated without valuations. -/
structure RaisingFiltration (m : ℕ) where
  level : ℕ → G → Prop
  level_zero : ∀ x, level 0 x
  raise : ∀ n x, level n x → level (n + 1) (m • x)
  separated : ∀ x, (∀ n, level n x) → x = 0

theorem RaisingFiltration.pow_smul_mem
    {m : ℕ} (F : RaisingFiltration (G := G) m) :
    ∀ n x, F.level n ((m ^ n) • x) := by
  intro n
  induction n with
  | zero =>
      intro x
      simpa using F.level_zero x
  | succ n ih =>
      intro x
      have h := F.raise n ((m ^ n) • x) (ih x)
      simpa [pow_succ, smul_smul, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using h

theorem RaisingFiltration.eq_zero_of_infinitelyDivisible
    {m : ℕ} (F : RaisingFiltration (G := G) m)
    {x : G}
    (hx : ∀ n : ℕ, ∃ q : G, (m ^ n) • q = x) :
    x = 0 := by
  apply F.separated
  intro n
  obtain ⟨q, rfl⟩ := hx n
  exact F.pow_smul_mem n q

end WeakDescent

/-! ## Reduction plus formal separatedness -/

section Annihilator

variable {G R : Type*} [AddCommGroup G] [AddCommGroup R]

theorem annihilator_of_weakDescent_reduction
    (m hExp rExp : ℕ)
    (H : AddSubgroup G)
    (red : G →+ R)
    (hweak : WeakDescent m H)
    (hHExp : ∀ h : H, hExp • (h : G) = 0)
    (hRExp : ∀ r : R, rExp • r = 0)
    (hsep : ∀ z : red.ker,
      InfinitelyDivisibleIn m red.ker z → z = 0) :
    ∀ x : G, (hExp * rExp) • x = 0 := by
  intro x
  let N := hExp * rExp
  have hNker (y : G) : red (N • y) = 0 := by
    rw [map_nsmul]
    change (hExp * rExp) • red y = 0
    rw [mul_nsmul, hRExp]
  let z : red.ker := ⟨N • x, hNker x⟩
  have hzdiv : InfinitelyDivisibleIn m red.ker z := by
    intro n
    obtain ⟨h, y, hxy⟩ := weakDescent_iterate m H hweak n x
    let q : red.ker := ⟨N • y, hNker y⟩
    refine ⟨q, Subtype.ext ?_⟩
    change (m ^ n) • (N • y) = N • x
    have hNh : N • (h : G) = 0 := by
      calc
        N • (h : G) = rExp • (hExp • (h : G)) := by
          simp [N, smul_smul, Nat.mul_comm]
        _ = 0 := by rw [hHExp]; simp
    rw [hxy, nsmul_add, hNh, zero_add]
    simp [smul_smul, Nat.mul_comm]
  have hz : z = 0 := hsep z hzdiv
  have hzval := congrArg Subtype.val hz
  simpa [z, N] using hzval

theorem twentyOne_nsmul_eq_zero
    (H : AddSubgroup G)
    (red : G →+ R)
    (hweak : WeakDescent 3 H)
    (hH3 : ∀ h : H, 3 • (h : G) = 0)
    (hR7 : ∀ r : R, 7 • r = 0)
    (hsep : ∀ z : red.ker,
      InfinitelyDivisibleIn 3 red.ker z → z = 0) :
    ∀ x : G, 21 • x = 0 := by
  simpa using annihilator_of_weakDescent_reduction
    3 3 7 H red hweak hH3 hR7 hsep

end Annihilator

/-! ## Isogeny and push-pull exponent transport -/

section Transport

theorem sixtyThree_nsmul_eq_zero_of_dual_three_isogeny
    {E Ehat : Type*} [AddCommGroup E] [AddCommGroup Ehat]
    (phi : E →+ Ehat) (phiHat : Ehat →+ E)
    (hdual : ∀ Q : Ehat, phi (phiHat Q) = 3 • Q)
    (hE21 : ∀ P : E, 21 • P = 0) :
    ∀ Q : Ehat, 63 • Q = 0 := by
  intro Q
  calc
    63 • Q = 21 • (3 • Q) := by norm_num [smul_smul]
    _ = 21 • phi (phiHat Q) := by rw [hdual]
    _ = phi (21 • phiHat Q) := by simp
    _ = 0 := by rw [hE21]; simp

theorem annihilator_of_pushPull
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (Phi : A →+ B) (Psi : B →+ A)
    (d N : ℕ)
    (hcomp : ∀ x : A, Psi (Phi x) = d • x)
    (hB : ∀ y : B, N • y = 0) :
    ∀ x : A, (N * d) • x = 0 := by
  intro x
  calc
    (N * d) • x = N • (d • x) := by simp [smul_smul]
    _ = N • Psi (Phi x) := by rw [hcomp]
    _ = Psi (N • Phi x) := by simp
    _ = 0 := by rw [hB]; simp

end Transport

end MazurProof.N18RouteC
