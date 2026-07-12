import Mathlib

set_option autoImplicit false

namespace FLT.CyclicExclusion.N18.PushPullReference

section GenericAlgebra

variable {J EPlus EMinus : Type*}
variable [AddCommGroup J] [AddCommGroup EPlus] [AddCommGroup EMinus]

/-- The subgroup `A[2] = ker ([2] : A → A)`. -/
def twoTorsion (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (((2 : ℕ) • AddMonoidHom.id A)).ker

@[simp] theorem mem_twoTorsion_iff (x : J) :
    x ∈ twoTorsion J ↔ (2 : ℕ) • x = 0 := by
  simp [twoTorsion]

/-- Abstract interface exported by the concrete Mumford/divisor implementation.
The four trace/deck facts are the only geometric input needed below. -/
structure Data (J EPlus EMinus : Type*)
    [AddCommGroup J] [AddCommGroup EPlus] [AddCommGroup EMinus] where
  hStar : J →+ J
  sigmaStar : J →+ J
  tauStar : J →+ J
  pushPlus : J →+ EPlus
  pushMinus : J →+ EMinus
  pullPlus : EPlus →+ J
  pullMinus : EMinus →+ J
  /-- Concrete Mumford group-law theorem: `D + h_* D = 0`. -/
  h_add : ∀ D : J, D + hStar D = 0
  /-- Functoriality for `tau = h ∘ sigma`. -/
  tau_comp : tauStar = hStar.comp sigmaStar
  /-- Degree-two push-pull for the `sigma` quotient. -/
  plus_push_pull :
    pullPlus.comp pushPlus = AddMonoidHom.id J + sigmaStar
  /-- Degree-two push-pull for the `tau` quotient. -/
  minus_push_pull :
    pullMinus.comp pushMinus = AddMonoidHom.id J + tauStar

namespace Data

variable (d : Data J EPlus EMinus)

/-- The hyperelliptic involution acts pointwise as negation. -/
theorem hStar_apply_eq_neg (D : J) : d.hStar D = -D := by
  calc
    d.hStar D = -D + (D + d.hStar D) := by abel
    _ = -D := by rw [d.h_add D]; simp

/-- Operator form of `h_* = -1`. -/
theorem hStar_eq_neg_id :
    d.hStar = -(AddMonoidHom.id J) := by
  ext D
  change d.hStar D = -D
  exact d.hStar_apply_eq_neg D

/-- Pointwise form of `tau_* = -sigma_*`. -/
theorem tauStar_apply_eq_neg_sigmaStar (D : J) :
    d.tauStar D = -d.sigmaStar D := by
  calc
    d.tauStar D = d.hStar (d.sigmaStar D) := by
      have h := congrArg (fun f : J →+ J => f D) d.tau_comp
      simpa using h
    _ = -d.sigmaStar D := d.hStar_apply_eq_neg (d.sigmaStar D)

/-- Operator form of `tau_* = -sigma_*`. -/
theorem tauStar_eq_neg_sigmaStar :
    d.tauStar = -d.sigmaStar := by
  ext D
  exact d.tauStar_apply_eq_neg_sigmaStar D

/-- Pointwise plus-cover trace formula. -/
theorem pullPlus_pushPlus_apply (D : J) :
    d.pullPlus (d.pushPlus D) = D + d.sigmaStar D := by
  have h := congrArg (fun f : J →+ J => f D) d.plus_push_pull
  simpa using h

/-- Pointwise minus-cover trace formula. -/
theorem pullMinus_pushMinus_apply (D : J) :
    d.pullMinus (d.pushMinus D) = D + d.tauStar D := by
  have h := congrArg (fun f : J →+ J => f D) d.minus_push_pull
  simpa using h

/-- `Phi = (q+_*, q-_*)`. -/
def Phi : J →+ EPlus × EMinus where
  toFun D := (d.pushPlus D, d.pushMinus D)
  map_zero' := by simp
  map_add' x y := by simp

/-- `Psi(P,Q) = q+^* P + q-^* Q`. -/
def Psi : EPlus × EMinus →+ J where
  toFun P := d.pullPlus P.1 + d.pullMinus P.2
  map_zero' := by simp
  map_add' x y := by
    change d.pullPlus (x.1 + y.1) + d.pullMinus (x.2 + y.2) =
      (d.pullPlus x.1 + d.pullMinus x.2) +
        (d.pullPlus y.1 + d.pullMinus y.2)
    rw [map_add, map_add]
    abel

/-- The load-bearing pointwise trace identity. -/
theorem PsiPhi_apply (D : J) :
    d.Psi (d.Phi D) = (2 : ℕ) • D := by
  change d.pullPlus (d.pushPlus D) + d.pullMinus (d.pushMinus D) =
    (2 : ℕ) • D
  rw [d.pullPlus_pushPlus_apply D, d.pullMinus_pushMinus_apply D,
    d.tauStar_apply_eq_neg_sigmaStar D]
  simp only [two_nsmul]
  abel

/-- Exact operator identity `Psi ∘ Phi = [2]`. -/
theorem Psi_comp_Phi :
    d.Psi.comp d.Phi = (2 : ℕ) • AddMonoidHom.id J := by
  ext D
  change d.Psi (d.Phi D) = (((2 : ℕ) • AddMonoidHom.id J) D)
  calc
    d.Psi (d.Phi D) = (2 : ℕ) • D := d.PsiPhi_apply D
    _ = (((2 : ℕ) • AddMonoidHom.id J) D) := by simp

/-- `ker Phi` is killed by two. -/
theorem ker_Phi_le_twoTorsion :
    d.Phi.ker ≤ twoTorsion J := by
  intro D hD
  rw [mem_twoTorsion_iff]
  change d.Phi D = 0 at hD
  calc
    (2 : ℕ) • D = d.Psi (d.Phi D) := (d.PsiPhi_apply D).symm
    _ = d.Psi 0 := by rw [hD]
    _ = 0 := by simp

/-- If `J` has no nonzero two-torsion, then `Phi` is injective. -/
theorem Phi_injective_of_no_twoTorsion
    (h2 : ∀ D : J, (2 : ℕ) • D = 0 → D = 0) :
    Function.Injective d.Phi := by
  intro x y hxy
  have hsub : d.Phi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmem : x - y ∈ d.Phi.ker := hsub
  have htwo : (2 : ℕ) • (x - y) = 0 :=
    (mem_twoTorsion_iff (x - y)).mp (d.ker_Phi_le_twoTorsion hmem)
  exact sub_eq_zero.mp (h2 (x - y) htwo)

/-- More useful formulation: `Phi` is injective on any subgroup with no
nonzero two-torsion (for example an odd-primary subgroup). -/
theorem Phi_injOn_of_no_twoTorsion
    (H : AddSubgroup J)
    (hH : ∀ D : J, D ∈ H → (2 : ℕ) • D = 0 → D = 0) :
    Set.InjOn d.Phi (H : Set J) := by
  intro x hx y hy hxy
  have hsub : d.Phi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hmem : x - y ∈ d.Phi.ker := hsub
  have htwo : (2 : ℕ) • (x - y) = 0 :=
    (mem_twoTorsion_iff (x - y)).mp (d.ker_Phi_le_twoTorsion hmem)
  exact sub_eq_zero.mp (hH (x - y) (H.sub_mem hx hy) htwo)

end Data

end GenericAlgebra

end FLT.CyclicExclusion.N18.PushPullReference
