import FLT.Assumptions.MazurProof.TorsionDefs

/-!
# Cyclic order 20 and 24 exclusion via 2-isogeny quotient

A rational point P of order 20 (resp. 24) gives, on the quotient
E' = E/⟨10P⟩ (resp. E/⟨12P⟩), a copy of Z/2 × Z/10 (resp. Z/2 × Z/12).
This contradicts the already-proved noncyclic exclusions.

The argument: φ(P) has order 10 (resp. 12) on E', and the dual-kernel
generator η ∈ E'[2] is independent from the unique order-2 element
5·φ(P) (resp. 6·φ(P)) in ⟨φ(P)⟩. Independence follows from the fact
that any lift T of η to E[2] would have order 2, but 5P and 15P
(resp. 6P and 18P) have order 4.

The sole geometric input is the existence of rational 2-isogeny quotients,
formalized as `RationalTwoIsogenyData`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

/-! ## Minimal 2-isogeny API -/

structure RationalTwoIsogenyData
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (Q : G) where
  phi : G →+ H
  eta : H
  eta_order : addOrderOf eta = 2
  ker_eq : ∀ R : G, phi R = 0 ↔ R = 0 ∨ R = Q
  eta_lift : ∃ T : G, addOrderOf T = 2 ∧ T ≠ 0 ∧ T ≠ Q ∧ phi T = eta

/-! ## Group-theory lemmas -/

private theorem image_order_10_of_order_20
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 20)
    (D : RationalTwoIsogenyData (G := G) (H := H) (10 • P)) :
    addOrderOf (D.phi P) = 10 := by
  sorry

private theorem image_order_12_of_order_24
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 24)
    (D : RationalTwoIsogenyData (G := G) (H := H) (12 • P)) :
    addOrderOf (D.phi P) = 12 := by
  sorry

private theorem eta_ne_half_image_20
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 20)
    (D : RationalTwoIsogenyData (G := G) (H := H) (10 • P)) :
    D.eta ≠ 5 • D.phi P := by
  obtain ⟨T, hT_ord, hT_ne0, hT_neQ, hT_phi⟩ := D.eta_lift
  intro h
  have hker : D.phi (T - 5 • P) = 0 := by
    rw [map_sub, map_nsmul, hT_phi, h, sub_self]
  sorry

private theorem eta_ne_half_image_24
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 24)
    (D : RationalTwoIsogenyData (G := G) (H := H) (12 • P)) :
    D.eta ≠ 6 • D.phi P := by
  obtain ⟨T, hT_ord, hT_ne0, hT_neQ, hT_phi⟩ := D.eta_lift
  intro h
  have hker : D.phi (T - 6 • P) = 0 := by
    rw [map_sub, map_nsmul, hT_phi, h, sub_self]
  sorry

/-! ## Geometric input: existence of 2-isogeny quotient -/

axiom exists_rational_two_isogeny_quotient
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {Q : (E⁄ℚ).Point} (hQ : addOrderOf Q = 2) :
    ∃ (E' : WeierstrassCurve ℚ) (hE' : E'.IsElliptic)
      (phi : (E⁄ℚ).Point →+ (E'⁄ℚ).Point)
      (eta : (E'⁄ℚ).Point),
      addOrderOf eta = 2 ∧
      (∀ R, phi R = 0 ↔ R = 0 ∨ R = Q) ∧
      (∃ T : (E⁄ℚ).Point, addOrderOf T = 2 ∧ T ≠ 0 ∧ T ≠ Q ∧ phi T = eta)

/-! ## Final exclusion theorems -/

-- These need the noncyclic exclusion API. For now, state as sorry.

theorem no_rational_point_of_order_20
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 20 := by
  sorry

theorem no_rational_point_of_order_24
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 24 := by
  sorry

end MazurProof
