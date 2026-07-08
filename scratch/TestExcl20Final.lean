import Mathlib

set_option maxHeartbeats 800000

noncomputable section
open Function

variable {H : Type*} [AddCommGroup H]

-- Already proved in TestZ2Z10.lean
axiom eq_five_nsmul_of_order_two_in_zmultiples
    {η Q : H}
    (hη : addOrderOf η = 2)
    (hQ : addOrderOf Q = 10)
    (hmem : η ∈ AddSubgroup.zmultiples Q) :
    η = 5 • Q

private def intSmulHom (x : H) : ℤ →+ H where
  toFun z := z • x
  map_zero' := by simp
  map_add' a b := by simp [add_zsmul]

theorem zmod_two_ten_coprod_injective
    {η Q : H}
    (hη : addOrderOf η = 2)
    (hQ : addOrderOf Q = 10)
    (hindep : η ≠ 5 • Q)
    (gη : ZMod 2 →+ H)
    (gQ : ZMod 10 →+ H)
    (hgη : ∀ z : ℤ, gη (z : ZMod 2) = z • η)
    (hgQ : ∀ z : ℤ, gQ (z : ZMod 10) = z • Q) :
    Function.Injective (gη.coprod gQ) := by
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
          have : a % 2 = 1 := by omega
          rw [show (a : ZMod 2) = ((a % 2 : ℤ) : ZMod 2) from by simp [ZMod.intCast_eq_intCast_iff'], this]
          simp
      exact this.resolve_left ha0
    have haη : a • η = η := by
      have h1 : gη (1 : ZMod 2) = η := by simpa using hgη (1 : ℤ)
      have h := congrArg gη ha1; simpa [hgη a, h1] using h
    have hrel : η + b • Q = 0 := by simpa [haη] using hker'
    have hmem : η ∈ AddSubgroup.zmultiples Q := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨-b, by simpa [neg_zsmul] using (eq_neg_of_add_eq_zero_left hrel).symm⟩
    exact hindep (eq_five_nsmul_of_order_two_in_zmultiples hη hQ hmem)

theorem exists_injective_Z2xZ10_full
    {η Q : H}
    (hη : addOrderOf η = 2)
    (hQ : addOrderOf Q = 10)
    (hindep : η ≠ 5 • Q) :
    ∃ f : ZMod 2 × ZMod 10 →+ H, Function.Injective f := by
  have hη₂ : (2 : ℕ) • η = 0 := by simpa [hη] using addOrderOf_nsmul_eq_zero η
  have hQ₁₀ : (10 : ℕ) • Q = 0 := by simpa [hQ] using addOrderOf_nsmul_eq_zero Q
  let gη : ZMod 2 →+ H := ZMod.lift 2 ⟨intSmulHom η, by
    change ((2 : ℤ) • η) = 0; exact_mod_cast hη₂⟩
  let gQ : ZMod 10 →+ H := ZMod.lift 10 ⟨intSmulHom Q, by
    change ((10 : ℤ) • Q) = 0; exact_mod_cast hQ₁₀⟩
  have hgη : ∀ z : ℤ, gη (z : ZMod 2) = z • η := by intro z; simp [gη, intSmulHom]
  have hgQ : ∀ z : ℤ, gQ (z : ZMod 10) = z • Q := by intro z; simp [gQ, intSmulHom]
  exact ⟨gη.coprod gQ, zmod_two_ten_coprod_injective hη hQ hindep gη gQ hgη hgQ⟩
