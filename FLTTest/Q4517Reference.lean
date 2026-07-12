import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace Q4517Reference

open scoped BigOperators

def C {R : Type*} [Ring R] (u : R) : R := u ^ 3 - 6 * u + 4

def A {R : Type*} [Ring R] (u : R) : R := u ^ 3 + 6 * u - 8

def B {R : Type*} [Ring R] (u : R) : R := -18 * u ^ 2 + 24 * u - 8

theorem velu_certificate {R : Type*} [CommRing R] (u w : R) :
    (A u * w + B u) ^ 2
      - 3 * u * C u * (A u * w + B u)
      + 2 * u ^ 3 * (A u * w + B u)
      - C u ^ 3 - 30 * u ^ 4 * C u - 26 * u ^ 6
      = A u ^ 2 * (w ^ 2 - 3 * u * w + 2 * w - u ^ 3) := by
  simp only [A, B, C]
  ring

def U {R : Type*} [Ring R] (X : R) : R := X ^ 3 - 9 * X ^ 2 + 81 * X - 243

def V {R : Type*} [Ring R] (X : R) : R := X ^ 3 - 81 * X + 486

def RE {R : Type*} [Ring R] (u Y : R) : R :=
  4 * Y ^ 2 - 4 * u ^ 3 - 9 * u ^ 2 + 12 * u - 4

def REprime {R : Type*} [Ring R] (X Z : R) : R :=
  4 * Z ^ 2 - 4 * X ^ 3 + 27 * X ^ 2 - 162 * X + 243

theorem dual_certificate {K : Type*} [Field K] [CharZero K]
    (X Z : K) (hX : X ≠ 0) :
    729 * X ^ 6 * RE (U X / (9 * X ^ 2)) (V X * Z / (27 * X ^ 3))
      = V X ^ 2 * REprime X Z := by
  field_simp [RE, REprime, U, V, hX]
  ring

theorem phi_kummer_norm {K : Type*} [CommRing K]
    (xi eta zeta : K)
    (hsum : zeta + zeta ^ 2 = -1)
    (hprod : zeta * zeta ^ 2 = 1)
    (hE : eta ^ 2 - 3 * xi * eta + 2 * eta = xi ^ 3 + 30 * xi + 26) :
    (eta + 1 + 3 * zeta * xi) * (eta + 1 + 3 * zeta ^ 2 * xi)
      = (xi + 3) ^ 3 := by
  calc
    (eta + 1 + 3 * zeta * xi) * (eta + 1 + 3 * zeta ^ 2 * xi)
        = (eta + 1) ^ 2 + 3 * (zeta + zeta ^ 2) * xi * (eta + 1)
            + 9 * (zeta * zeta ^ 2) * xi ^ 2 := by ring
    _ = (eta + 1) ^ 2 - 3 * xi * (eta + 1) + 9 * xi ^ 2 := by
      rw [hsum, hprod]
      ring
    _ = (xi + 3) ^ 3 := by
      rw [show eta ^ 2 - 3 * xi * eta + 2 * eta = xi ^ 3 + 30 * xi + 26 from hE]
      ring

theorem a_mul_inverse {K : Type*} [CommRing K] (a : K)
    (ha : a ^ 3 = 3 * a + 1) : a * (a ^ 2 - 3) = 1 := by
  calc
    a * (a ^ 2 - 3) = a ^ 3 - 3 * a := by ring
    _ = 1 := by rw [ha]; ring

theorem aplus_mul_inverse {K : Type*} [CommRing K] (a : K)
    (ha : a ^ 3 = 3 * a + 1) :
    (a + 1) * (-a ^ 2 + a + 2) = 1 := by
  calc
    (a + 1) * (-a ^ 2 + a + 2) = -a ^ 3 + 3 * a + 2 := by ring
    _ = 1 := by rw [ha]; ring

abbrev F3 := ZMod 3
abbrev DualClass := Fin 4 → F3
abbrev PhiClass := F3
abbrev PhiLocal3 := Fin 4 → F3

def mkDual (i j k l : F3) : DualClass := ![i, j, k, l]

def dualTClass : DualClass := mkDual 0 0 2 0

def locDual2 (c : DualClass) : F3 := c 2

def inDualImage2 (_ : F3) : Prop := True

def locDual3 (c : DualClass) : DualClass := c

def inDualImage3 (c : DualClass) : Prop :=
  c 0 = 0 ∧ c 1 = 0 ∧ c 3 = 0

def locPhi2 (r : PhiClass) : F3 := r

def inPhiImage2 (r : F3) : Prop := r = 0

def locPhi3 (r : PhiClass) : PhiLocal3 := ![r, 0, 0, 0]

def inPhiImage3 (v : PhiLocal3) : Prop := v 0 = 0

def passDual (c : DualClass) : Prop :=
  inDualImage2 (locDual2 c) ∧ inDualImage3 (locDual3 c)

def passPhi (r : PhiClass) : Prop :=
  inPhiImage2 (locPhi2 r) ∧ inPhiImage3 (locPhi3 r)

def dualSelmerCode : Finset DualClass := Finset.univ.filter passDual

def phiSelmerCode : Finset PhiClass := Finset.univ.filter passPhi

theorem candidate_count : Fintype.card DualClass + Fintype.card PhiClass = 84 := by
  native_decide

theorem local_image_cardinalities :
    (Finset.univ.filter inDualImage2).card = 3 ∧
    (Finset.univ.filter inDualImage3).card = 3 ∧
    (Finset.univ.filter inPhiImage2).card = 1 ∧
    (Finset.univ.filter inPhiImage3).card = 27 := by
  native_decide

theorem phiSelmerCode_eq :
    phiSelmerCode = ({0} : Finset PhiClass) := by
  native_decide

theorem dualSelmerCode_eq :
    dualSelmerCode =
      ({mkDual 0 0 0 0, mkDual 0 0 1 0, mkDual 0 0 2 0} : Finset DualClass) := by
  native_decide

theorem passDual_iff :
    ∀ c : DualClass, passDual c ↔ ∃ k : F3, c = mkDual 0 0 k 0 := by
  native_decide

theorem passPhi_iff : ∀ r : PhiClass, passPhi r ↔ r = 0 := by
  native_decide

theorem dualLine_represented :
    ∀ k : F3, ∃ n : Fin 3, n.val • dualTClass = mkDual 0 0 k 0 := by
  native_decide

end Q4517Reference