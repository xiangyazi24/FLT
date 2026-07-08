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

private lemma image_five_nsmul_ne_zero_of_order_20
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 20)
    (D : RationalTwoIsogenyData (G := G) (H := H) (10 • P)) :
    5 • D.phi P ≠ 0 := by
  intro h5
  have hker : D.phi (5 • P) = 0 := by simpa using h5
  rcases (D.ker_eq (5 • P)).mp hker with h0 | hQ
  · have : 20 ∣ 5 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h0
    norm_num at this
  · have : 5 • P = 0 := by
      calc 5 • P = 10 • P - 5 • P := by abel
        _ = 0 := by rw [← hQ, sub_self]
    have : 20 ∣ 5 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero this
    norm_num at this

private lemma image_two_nsmul_ne_zero_of_order_20
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 20)
    (D : RationalTwoIsogenyData (G := G) (H := H) (10 • P)) :
    2 • D.phi P ≠ 0 := by
  intro h2
  have hker : D.phi (2 • P) = 0 := by simpa using h2
  rcases (D.ker_eq (2 • P)).mp hker with h0 | hQ
  · have : 20 ∣ 2 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h0
    norm_num at this
  · have : 8 • P = 0 := by
      calc 8 • P = 10 • P - 2 • P := by abel
        _ = 0 := by rw [← hQ, sub_self]
    have : 20 ∣ 8 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero this
    norm_num at this

private theorem image_order_10_of_order_20
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 20)
    (D : RationalTwoIsogenyData (G := G) (H := H) (10 • P)) :
    addOrderOf (D.phi P) = 10 := by
  have h10 : 10 • D.phi P = 0 := by
    have : D.phi (10 • P) = 0 := (D.ker_eq (10 • P)).mpr (Or.inr rfl)
    simpa using this
  have h5 := image_five_nsmul_ne_zero_of_order_20 hP D
  have h2 := image_two_nsmul_ne_zero_of_order_20 hP D
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul (by norm_num : 0 < 10) h10 ?_
  intro p hp hpdiv
  have hple : p ≤ 10 := Nat.le_of_dvd (by norm_num) hpdiv
  have hpge : 2 ≤ p := hp.two_le
  interval_cases p
  · exact h5
  · norm_num at hpdiv
  · norm_num at hp
  · exact h2
  · norm_num at hp
  · norm_num at hpdiv
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp

private theorem image_order_12_of_order_24
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 24)
    (D : RationalTwoIsogenyData (G := G) (H := H) (12 • P)) :
    addOrderOf (D.phi P) = 12 := by
  have h12 : 12 • D.phi P = 0 := by
    have : D.phi (12 • P) = 0 := (D.ker_eq (12 • P)).mpr (Or.inr rfl)
    simpa using this
  have h6 : 6 • D.phi P ≠ 0 := by
    intro h6
    have hker : D.phi (6 • P) = 0 := by simpa using h6
    rcases (D.ker_eq (6 • P)).mp hker with h0 | hQ
    · have : 24 ∣ 6 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h0
      norm_num at this
    · have : 6 • P = 0 := by
        calc 6 • P = 12 • P - 6 • P := by abel
          _ = 0 := by rw [← hQ, sub_self]
      have : 24 ∣ 6 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero this
      norm_num at this
  have h4 : 4 • D.phi P ≠ 0 := by
    intro h4
    have hker : D.phi (4 • P) = 0 := by simpa using h4
    rcases (D.ker_eq (4 • P)).mp hker with h0 | hQ
    · have : 24 ∣ 4 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h0
      norm_num at this
    · have : 8 • P = 0 := by
        calc 8 • P = 12 • P - 4 • P := by abel
          _ = 0 := by rw [← hQ, sub_self]
      have : 24 ∣ 8 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero this
      norm_num at this
  refine addOrderOf_eq_of_nsmul_and_div_prime_nsmul (by norm_num : 0 < 12) h12 ?_
  intro p hp hpdiv
  have hple : p ≤ 12 := Nat.le_of_dvd (by norm_num) hpdiv
  have hpge : 2 ≤ p := hp.two_le
  interval_cases p
  · exact h6
  · exact h4
  · norm_num at hp
  · norm_num at hpdiv
  · norm_num at hp
  · norm_num at hpdiv
  · norm_num at hp
  · norm_num at hp
  · norm_num at hp
  · norm_num at hpdiv
  · norm_num at hp

private theorem eta_ne_half_image_20
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 20)
    (D : RationalTwoIsogenyData (G := G) (H := H) (10 • P)) :
    D.eta ≠ 5 • D.phi P := by
  obtain ⟨T, hT_ord, _, _, hT_phi⟩ := D.eta_lift
  intro h
  have h2T : 2 • T = 0 := by
    have := addOrderOf_nsmul_eq_zero T; simpa [hT_ord] using this
  have hker : D.phi (T - 5 • P) = 0 := by
    rw [map_sub, map_nsmul, hT_phi, h, sub_self]
  rcases (D.ker_eq (T - 5 • P)).mp hker with h0 | hQ
  · have hT : T = 5 • P := sub_eq_zero.mp h0
    have h10P : 10 • P = 0 := by
      have : 2 • (5 • P) = 0 := hT ▸ h2T
      rwa [← mul_nsmul, show 2 * 5 = 10 from by norm_num] at this
    have : 20 ∣ 10 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h10P
    norm_num at this
  · have hT : T = 15 • P := by
      have := sub_eq_iff_eq_add.mp hQ; rw [this]; abel
    have h30P : 30 • P = 0 := by
      have : 2 • (15 • P) = 0 := hT ▸ h2T
      rwa [← mul_nsmul, show 2 * 15 = 30 from by norm_num] at this
    have : 20 ∣ 30 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h30P
    norm_num at this

private theorem eta_ne_half_image_24
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 24)
    (D : RationalTwoIsogenyData (G := G) (H := H) (12 • P)) :
    D.eta ≠ 6 • D.phi P := by
  obtain ⟨T, hT_ord, _, _, hT_phi⟩ := D.eta_lift
  intro h
  have h2T : 2 • T = 0 := by
    have := addOrderOf_nsmul_eq_zero T; simpa [hT_ord] using this
  have hker : D.phi (T - 6 • P) = 0 := by
    rw [map_sub, map_nsmul, hT_phi, h, sub_self]
  rcases (D.ker_eq (T - 6 • P)).mp hker with h0 | hQ
  · have hT : T = 6 • P := sub_eq_zero.mp h0
    have h12P : 12 • P = 0 := by
      have : 2 • (6 • P) = 0 := hT ▸ h2T
      rwa [← mul_nsmul, show 2 * 6 = 12 from by norm_num] at this
    have : 24 ∣ 12 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h12P
    norm_num at this
  · have hT : T = 18 • P := by
      have := sub_eq_iff_eq_add.mp hQ; rw [this]; abel
    have h36P : 36 • P = 0 := by
      have : 2 • (18 • P) = 0 := hT ▸ h2T
      rwa [← mul_nsmul, show 2 * 18 = 36 from by norm_num] at this
    have : 24 ∣ 36 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h36P
    norm_num at this

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

theorem no_rational_point_of_order_20
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 20 := by
  sorry

theorem no_rational_point_of_order_24
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 24 := by
  sorry

end MazurProof
