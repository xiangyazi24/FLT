import FLT.Assumptions.MazurProof.N18RouteC_FiberTable
import FLT.Assumptions.MazurProof.N18RouteC_Reduction

/-!
# Assembly of the finite N18 quotient bound

This file closes the finite group theory between the weak three-descent,
injectivity of reduction on seven-torsion, the verified order-21 table, and
the rational fiber computation.
-/

namespace MazurProof.N18RouteC.Block7

open Finiteness Isogeny TorsionTable

noncomputable section

section ModThree

variable {G : Type*} [AddCommGroup G]

def torsionRepresentativesToModThree (H : AddSubgroup G) :
    H → G ⧸ ThreeRange G :=
  fun h ↦ QuotientAddGroup.mk' (ThreeRange G) (h : G)

theorem torsionRepresentativesToModThree_surjective
    (H : AddSubgroup G)
    (hweak : ∀ P : G, ∃ h : H, ∃ Q : G, P = (h : G) + 3 • Q) :
    Function.Surjective (torsionRepresentativesToModThree H) := by
  intro z
  obtain ⟨P, rfl⟩ := QuotientAddGroup.mk'_surjective (ThreeRange G) z
  obtain ⟨h, Q, hP⟩ := hweak P
  refine ⟨h, ?_⟩
  apply (QuotientAddGroup.mk'_eq_mk' (ThreeRange G)).2
  refine ⟨3 • Q, ⟨Q, rfl⟩, ?_⟩
  exact hP.symm

theorem finite_modThree_of_weak
    (H : AddSubgroup G) [Finite H]
    (hweak : ∀ P : G, ∃ h : H, ∃ Q : G, P = (h : G) + 3 • Q) :
    Finite (G ⧸ ThreeRange G) :=
  Finite.of_surjective (torsionRepresentativesToModThree H)
    (torsionRepresentativesToModThree_surjective H hweak)

theorem card_modThree_le
    (H : AddSubgroup G) [Finite H]
    (hweak : ∀ P : G, ∃ h : H, ∃ Q : G, P = (h : G) + 3 • Q) :
    Nat.card (G ⧸ ThreeRange G) ≤ Nat.card H := by
  letI : Finite (G ⧸ ThreeRange G) := finite_modThree_of_weak H hweak
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (G ⧸ ThreeRange G) := Fintype.ofFinite (G ⧸ ThreeRange G)
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_surjective (torsionRepresentativesToModThree H)
      (torsionRepresentativesToModThree_surjective H hweak)

end ModThree

theorem e0_card_le_twenty_one
    (h21 : ∀ P : E0Point, (21 : ℕ) • P = 0)
    (hweak : ∀ P : E0Point,
      ∃ h : H3, ∃ Q : E0Point, P = (h : E0Point) + 3 • Q)
    (red : E0Point →+ Reduction.RedPoint)
    (hker7 : ∀ P : E0Point,
      (7 : ℕ) • P = 0 → red P = 0 → P = 0) :
    Nat.card E0Point ≤ 21 := by
  letI : Finite H3 := Nat.finite_of_card_ne_zero (by
    rw [card_H3]
    norm_num)
  letI : Finite (E0Point ⧸ ThreeRange E0Point) :=
    finite_modThree_of_weak H3 hweak
  have hmod3 : Nat.card (E0Point ⧸ ThreeRange E0Point) ≤ 3 := by
    calc
      Nat.card (E0Point ⧸ ThreeRange E0Point) ≤ Nat.card H3 :=
        card_modThree_le H3 hweak
      _ = 3 := card_H3
  have hredcard : Nat.card Reduction.RedPoint = 7 := by
    simpa only [Nat.card_eq_fintype_card] using Reduction.redPoint_card
  exact card_le_twentyOne h21 hmod3 red hker7 hredcard

theorem all_rational_points_are_cusps
    (h21 : ∀ P : E0Point, (21 : ℕ) • P = 0)
    (hweak : ∀ P : E0Point,
      ∃ h : H3, ∃ Q : E0Point, P = (h : E0Point) + 3 • Q)
    (red : E0Point →+ Reduction.RedPoint)
    (hker7 : ∀ P : E0Point,
      (7 : ℕ) • P = 0 → red P = 0 → P = 0) :
    ∀ P : CurvePointQ, CurvePoint.IsCusp P := by
  have hcard := e0_card_le_twenty_one h21 hweak red hker7
  letI : Finite E0Point := by
    letI : Finite H3 := Nat.finite_of_card_ne_zero (by
      rw [card_H3]
      norm_num)
    letI : Finite (E0Point ⧸ ThreeRange E0Point) :=
      finite_modThree_of_weak H3 hweak
    exact finite_of_modThree_and_reduction h21 red hker7
  exact FiberTable.all_rational_points_are_cusps_of_card_le hcard

end

end MazurProof.N18RouteC.Block7
