import FLT.Assumptions.MazurProof.TorsionDefs
import FLT.Assumptions.MazurProof.DescentBridge
import FLT.Assumptions.MazurProof.DescentBridgeN12
import FLT.Assumptions.MazurProof.Velu2Isogeny

/-!
# Cyclic order 20 and 24 exclusion via 2-isogeny quotient

A rational point P of order 20 (resp. 24) gives, on the quotient
E' = E/⟨10P⟩ (resp. E/⟨12P⟩), a copy of Z/2 × Z/10 (resp. Z/2 × Z/12).
This contradicts the already-proved noncyclic exclusions.

The argument: φ(P) has order 10 (resp. 12) on E', and the dual-kernel
generator η ∈ E'[2] is independent from the unique order-2 element
5·φ(P) (resp. 6·φ(P)) in ⟨φ(P)⟩.  If they were equal, applying the dual
isogeny would give 10P = 0 (resp. 12P = 0), contradicting the exact order
of P.

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
  dual : H →+ G
  eta : H
  eta_order : addOrderOf eta = 2
  ker_eq : ∀ R : G, phi R = 0 ↔ R = 0 ∨ R = Q
  dual_phi : ∀ R : G, dual (phi R) = 2 • R
  dual_eta : dual eta = 0

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
  intro h
  have h10P : (10 : ℕ) • P = 0 := by
    calc
      (10 : ℕ) • P = 5 • (2 • P) := by rw [← mul_nsmul]
      _ = D.dual (5 • D.phi P) := by rw [map_nsmul, D.dual_phi]
      _ = D.dual D.eta := by rw [h]
      _ = 0 := D.dual_eta
  have : 20 ∣ 10 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h10P
  norm_num at this

private theorem eta_ne_half_image_24
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    {P : G} (hP : addOrderOf P = 24)
    (D : RationalTwoIsogenyData (G := G) (H := H) (12 • P)) :
    D.eta ≠ 6 • D.phi P := by
  intro h
  have h12P : (12 : ℕ) • P = 0 := by
    calc
      (12 : ℕ) • P = 6 • (2 • P) := by rw [← mul_nsmul]
      _ = D.dual (6 • D.phi P) := by rw [map_nsmul, D.dual_phi]
      _ = D.dual D.eta := by rw [h]
      _ = 0 := D.dual_eta
  have : 24 ∣ 12 := by simpa [hP] using addOrderOf_dvd_of_nsmul_eq_zero h12P
  norm_num at this

/-! ## Z/2 × Z/n injective embedding machinery -/

private def intSmulHom' {H : Type*} [AddCommGroup H] (x : H) : ℤ →+ H where
  toFun z := z • x
  map_zero' := by simp
  map_add' a b := by simp [add_zsmul]

private theorem eq_five_nsmul_of_order_two_in_zmultiples'
    {H : Type*} [AddCommGroup H] {η Q : H}
    (hη : addOrderOf η = 2) (hQ : addOrderOf Q = 10)
    (hmem : η ∈ AddSubgroup.zmultiples Q) : η = 5 • Q := by
  rw [AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨z, hz⟩ := hmem
  have h2η : (2 : ℤ) • η = 0 := by
    exact_mod_cast (by simpa [hη] using addOrderOf_nsmul_eq_zero η : (2 : ℕ) • η = 0)
  have h2zQ : (2 * z) • Q = 0 := by
    calc (2 * z) • Q = (2 : ℤ) • (z • Q) := by rw [mul_zsmul]
      _ = (2 : ℤ) • η := by rw [hz]
      _ = 0 := h2η
  have hdvd : (10 : ℤ) ∣ (2 * z) := by
    have h := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h2zQ
    rwa [hQ] at h
  have h5dvz : (5 : ℤ) ∣ z := by omega
  obtain ⟨k, rfl⟩ := h5dvz
  have hη_ne : η ≠ 0 := by intro h; rw [h] at hη; simp at hη
  have h10Q : (10 : ℤ) • Q = 0 := by
    exact_mod_cast (by simpa [hQ] using addOrderOf_nsmul_eq_zero Q : (10 : ℕ) • Q = 0)
  have hk_odd : ¬ (2 : ℤ) ∣ k := by
    intro ⟨m, hm⟩; apply hη_ne
    calc η = (5 * k) • Q := hz.symm
      _ = (5 * (2 * m)) • Q := by rw [hm]
      _ = (10 * m) • Q := by ring_nf
      _ = (10 : ℤ) • (m • Q) := by rw [mul_zsmul]
      _ = m • ((10 : ℤ) • Q) := by rw [zsmul_comm]
      _ = m • (0 : H) := by rw [h10Q]
      _ = 0 := smul_zero m
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, k = 2 * m + 1 := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exfalso; exact hk_odd ⟨m, by linarith⟩
    · exact ⟨m, by linarith⟩
  have key : (5 * (2 * m + 1) : ℤ) • Q = (5 : ℕ) • Q := by
    rw [show (5 : ℤ) * (2 * m + 1) = 10 * m + 5 from by ring, add_zsmul, mul_zsmul]
    rw [show (10 : ℤ) • (m • Q) = m • ((10 : ℤ) • Q) from by rw [zsmul_comm]]
    rw [h10Q, smul_zero, zero_add]; exact_mod_cast (rfl : (5 : ℕ) • Q = (5 : ℕ) • Q)
  exact hz.symm.trans key

private theorem exists_injective_Z2xZn
    {H : Type*} [AddCommGroup H] {η Q : H}
    (hη : addOrderOf η = 2) (hQ : addOrderOf Q = 10)
    (hindep : η ≠ 5 • Q) :
    ∃ f : ZMod 2 × ZMod 10 →+ H, Function.Injective f := by
  have hη₂ : (2 : ℕ) • η = 0 := by simpa [hη] using addOrderOf_nsmul_eq_zero η
  have hQ₁₀ : (10 : ℕ) • Q = 0 := by simpa [hQ] using addOrderOf_nsmul_eq_zero Q
  let gη : ZMod 2 →+ H := ZMod.lift 2 ⟨intSmulHom' η, by
    change ((2 : ℤ) • η) = 0; exact_mod_cast hη₂⟩
  let gQ : ZMod 10 →+ H := ZMod.lift 10 ⟨intSmulHom' Q, by
    change ((10 : ℤ) • Q) = 0; exact_mod_cast hQ₁₀⟩
  have hgη : ∀ z : ℤ, gη (z : ZMod 2) = z • η := by intro z; simp [gη, intSmulHom']
  have hgQ : ∀ z : ℤ, gQ (z : ZMod 10) = z • Q := by intro z; simp [gQ, intSmulHom']
  refine ⟨gη.coprod gQ, ?_⟩
  rw [injective_iff_map_eq_zero]
  rintro ⟨a0, b0⟩ hker
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a0
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b0
  have hker' : (a • η + b • Q : H) = 0 := by
    simpa [AddMonoidHom.coprod_apply, hgη a, hgQ b] using hker
  by_cases ha0 : (a : ZMod 2) = 0
  · have haη : a • η = 0 := by
      have h := congrArg gη ha0; simpa [hgη a] using h
    have hbQ : b • Q = 0 := by simpa [haη] using hker'
    have hbdiv : (10 : ℤ) ∣ b := by
      simpa [hQ] using (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hbQ : ↑(addOrderOf Q) ∣ b)
    exact Prod.ext ha0 ((ZMod.intCast_zmod_eq_zero_iff_dvd b 10).mpr hbdiv)
  · exfalso
    have ha1 : (a : ZMod 2) = 1 := by
      have : (a : ZMod 2) = 0 ∨ (a : ZMod 2) = 1 := by
        have h2 : (2 : ℤ) ∣ a ∨ ¬ (2 : ℤ) ∣ a := em _
        rcases h2 with h | h
        · left; exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr h
        · right
          rw [show (a : ZMod 2) = ((a % 2 : ℤ) : ZMod 2) from by
            simp [ZMod.intCast_eq_intCast_iff']]
          simp [show a % 2 = 1 from by omega]
      exact this.resolve_left ha0
    have haη : a • η = η := by
      have h1 : gη (1 : ZMod 2) = η := by simpa using hgη (1 : ℤ)
      have h := congrArg gη ha1; simpa [hgη a, h1] using h
    have hrel : η + b • Q = 0 := by simpa [haη] using hker'
    have hmem : η ∈ AddSubgroup.zmultiples Q := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨-b, by simpa [neg_zsmul] using (eq_neg_of_add_eq_zero_left hrel).symm⟩
    exact hindep (eq_five_nsmul_of_order_two_in_zmultiples' hη hQ hmem)

/-! ## Final exclusion theorems -/

private theorem no_rational_point_of_order_20_aux
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hno : ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic],
      ¬ ∃ f : (ZMod 2 × ZMod 10) →+ (E'⁄ℚ).Point, Function.Injective f) :
    ¬ HasRationalPointOfOrder E 20 := by
  rintro ⟨P, hP⟩
  have h10P : addOrderOf ((10 : ℕ) • P) = 2 := by
    rw [addOrderOf_nsmul' P (by norm_num), hP]; norm_num
  obtain ⟨E', hE', phi, dual, eta, hη, hker, hdualPhi, hdualEta⟩ :=
    exists_rational_two_isogeny_quotient E h10P
  letI : E'.IsElliptic := hE'
  let D : RationalTwoIsogenyData ((10 : ℕ) • P) :=
    ⟨phi, dual, eta, hη, hker, hdualPhi, hdualEta⟩
  have himg := image_order_10_of_order_20 hP D
  have hindep := eta_ne_half_image_20 hP D
  have ⟨f, hf⟩ := exists_injective_Z2xZn hη himg hindep
  exact hno E' ⟨f, hf⟩

theorem no_rational_point_of_order_20
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 20 :=
  no_rational_point_of_order_20_aux E (fun E' => no_Z2_cross_Z10_from_descent E')

/-! ## Order 24 → Z/2 × Z/12 -/

private theorem eq_six_nsmul_of_order_two_in_zmultiples'
    {H : Type*} [AddCommGroup H] {η Q : H}
    (hη : addOrderOf η = 2) (hQ : addOrderOf Q = 12)
    (hmem : η ∈ AddSubgroup.zmultiples Q) : η = 6 • Q := by
  rw [AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨z, hz⟩ := hmem
  have h2η : (2 : ℤ) • η = 0 := by
    exact_mod_cast (by simpa [hη] using addOrderOf_nsmul_eq_zero η : (2 : ℕ) • η = 0)
  have h2zQ : (2 * z) • Q = 0 := by
    calc (2 * z) • Q = (2 : ℤ) • (z • Q) := by rw [mul_zsmul]
      _ = (2 : ℤ) • η := by rw [hz]
      _ = 0 := h2η
  have hdvd : (12 : ℤ) ∣ (2 * z) := by
    have h := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h2zQ
    rwa [hQ] at h
  have h6dvz : (6 : ℤ) ∣ z := by omega
  obtain ⟨k, rfl⟩ := h6dvz
  have hη_ne : η ≠ 0 := by intro h; rw [h] at hη; simp at hη
  have h12Q : (12 : ℤ) • Q = 0 := by
    exact_mod_cast (by simpa [hQ] using addOrderOf_nsmul_eq_zero Q : (12 : ℕ) • Q = 0)
  have hk_odd : ¬ (2 : ℤ) ∣ k := by
    intro ⟨m, hm⟩; apply hη_ne
    calc η = (6 * k) • Q := hz.symm
      _ = (6 * (2 * m)) • Q := by rw [hm]
      _ = (12 * m) • Q := by ring_nf
      _ = (12 : ℤ) • (m • Q) := by rw [mul_zsmul]
      _ = m • ((12 : ℤ) • Q) := by rw [zsmul_comm]
      _ = m • (0 : H) := by rw [h12Q]
      _ = 0 := smul_zero m
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, k = 2 * m + 1 := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exfalso; exact hk_odd ⟨m, by linarith⟩
    · exact ⟨m, by linarith⟩
  have key : (6 * (2 * m + 1) : ℤ) • Q = (6 : ℕ) • Q := by
    rw [show (6 : ℤ) * (2 * m + 1) = 12 * m + 6 from by ring, add_zsmul, mul_zsmul]
    rw [show (12 : ℤ) • (m • Q) = m • ((12 : ℤ) • Q) from by rw [zsmul_comm]]
    rw [h12Q, smul_zero, zero_add]; exact_mod_cast (rfl : (6 : ℕ) • Q = (6 : ℕ) • Q)
  exact hz.symm.trans key

private theorem exists_injective_Z2xZ12
    {H : Type*} [AddCommGroup H] {η Q : H}
    (hη : addOrderOf η = 2) (hQ : addOrderOf Q = 12)
    (hindep : η ≠ 6 • Q) :
    ∃ f : ZMod 2 × ZMod 12 →+ H, Function.Injective f := by
  have hη₂ : (2 : ℕ) • η = 0 := by simpa [hη] using addOrderOf_nsmul_eq_zero η
  have hQ₁₂ : (12 : ℕ) • Q = 0 := by simpa [hQ] using addOrderOf_nsmul_eq_zero Q
  let gη : ZMod 2 →+ H := ZMod.lift 2 ⟨intSmulHom' η, by
    change ((2 : ℤ) • η) = 0; exact_mod_cast hη₂⟩
  let gQ : ZMod 12 →+ H := ZMod.lift 12 ⟨intSmulHom' Q, by
    change ((12 : ℤ) • Q) = 0; exact_mod_cast hQ₁₂⟩
  have hgη : ∀ z : ℤ, gη (z : ZMod 2) = z • η := by intro z; simp [gη, intSmulHom']
  have hgQ : ∀ z : ℤ, gQ (z : ZMod 12) = z • Q := by intro z; simp [gQ, intSmulHom']
  refine ⟨gη.coprod gQ, ?_⟩
  rw [injective_iff_map_eq_zero]
  rintro ⟨a0, b0⟩ hker
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a0
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b0
  have hker' : (a • η + b • Q : H) = 0 := by
    simpa [AddMonoidHom.coprod_apply, hgη a, hgQ b] using hker
  by_cases ha0 : (a : ZMod 2) = 0
  · have haη : a • η = 0 := by
      have h := congrArg gη ha0; simpa [hgη a] using h
    have hbQ : b • Q = 0 := by simpa [haη] using hker'
    have hbdiv : (12 : ℤ) ∣ b := by
      simpa [hQ] using (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hbQ : ↑(addOrderOf Q) ∣ b)
    exact Prod.ext ha0 ((ZMod.intCast_zmod_eq_zero_iff_dvd b 12).mpr hbdiv)
  · exfalso
    have ha1 : (a : ZMod 2) = 1 := by
      have : (a : ZMod 2) = 0 ∨ (a : ZMod 2) = 1 := by
        have h2 : (2 : ℤ) ∣ a ∨ ¬ (2 : ℤ) ∣ a := em _
        rcases h2 with h | h
        · left; exact (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr h
        · right
          rw [show (a : ZMod 2) = ((a % 2 : ℤ) : ZMod 2) from by
            simp [ZMod.intCast_eq_intCast_iff']]
          simp [show a % 2 = 1 from by omega]
      exact this.resolve_left ha0
    have haη : a • η = η := by
      have h1 : gη (1 : ZMod 2) = η := by simpa using hgη (1 : ℤ)
      have h := congrArg gη ha1; simpa [hgη a, h1] using h
    have hrel : η + b • Q = 0 := by simpa [haη] using hker'
    have hmem : η ∈ AddSubgroup.zmultiples Q := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨-b, by simpa [neg_zsmul] using (eq_neg_of_add_eq_zero_left hrel).symm⟩
    exact hindep (eq_six_nsmul_of_order_two_in_zmultiples' hη hQ hmem)

private theorem no_rational_point_of_order_24_aux
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hno : ∀ (E' : WeierstrassCurve ℚ) [E'.IsElliptic],
      ¬ ∃ f : (ZMod 2 × ZMod 12) →+ (E'⁄ℚ).Point, Function.Injective f) :
    ¬ HasRationalPointOfOrder E 24 := by
  rintro ⟨P, hP⟩
  have h12P : addOrderOf ((12 : ℕ) • P) = 2 := by
    rw [addOrderOf_nsmul' P (by norm_num), hP]; norm_num
  obtain ⟨E', hE', phi, dual, eta, hη, hker, hdualPhi, hdualEta⟩ :=
    exists_rational_two_isogeny_quotient E h12P
  letI : E'.IsElliptic := hE'
  let D : RationalTwoIsogenyData ((12 : ℕ) • P) :=
    ⟨phi, dual, eta, hη, hker, hdualPhi, hdualEta⟩
  have himg := image_order_12_of_order_24 hP D
  have hindep := eta_ne_half_image_24 hP D
  have ⟨f, hf⟩ := exists_injective_Z2xZ12 hη himg hindep
  exact hno E' ⟨f, hf⟩

theorem no_rational_point_of_order_24
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ HasRationalPointOfOrder E 24 :=
  no_rational_point_of_order_24_aux E (fun E' => no_Z2_cross_Z12_from_descent E')

end MazurProof
