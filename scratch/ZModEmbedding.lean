import Mathlib

theorem zmod_prod_contains_square (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    ∃ f : ZMod m × ZMod m →+ ZMod m × ZMod n, Function.Injective f := by
  let k : ℕ := n / m
  have hmk : m * k = n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hmn
  have hk_pos : 0 < k := by
    have hprod : 0 < m * k := by
      rw [hmk]
      exact hn
    exact pos_of_mul_pos_right hprod hm.le
  let phi : ℤ →+ ZMod n :=
    { toFun := fun a => (a : ZMod n) * (k : ZMod n)
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [Int.cast_add, add_mul] }
  have phi_m_zero : phi (m : ℤ) = 0 := by
    dsimp [phi]
    rw [Int.cast_natCast]
    rw [← Nat.cast_mul, hmk, ZMod.natCast_self]
  let g : ZMod m →+ ZMod n := ZMod.lift m ⟨phi, phi_m_zero⟩
  have hg : Function.Injective g := by
    rw [ZMod.lift_injective]
    intro a ha
    change phi a = 0 at ha
    dsimp [phi] at ha
    have ha' : (((a * (k : ℤ)) : ℤ) : ZMod n) = 0 := by
      rw [Int.cast_mul]
      simpa [Int.cast_natCast] using ha
    have hdiv_n : (n : ℤ) ∣ a * (k : ℤ) := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a * (k : ℤ)) n).mp ha'
    have hdiv_mk : ((m : ℤ) * (k : ℤ)) ∣ a * (k : ℤ) := by
      have hcast : (m : ℤ) * (k : ℤ) = (n : ℤ) := by
        exact_mod_cast hmk
      simpa [hcast] using hdiv_n
    have hk_ne : (k : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk_pos)
    have hdiv_m : (m : ℤ) ∣ a := by
      exact Int.dvd_of_mul_dvd_mul_right hk_ne hdiv_mk
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd a m).mpr hdiv_m
  let f : ZMod m × ZMod m →+ ZMod m × ZMod n :=
    { toFun := fun p => (p.1, g p.2)
      map_zero' := by
        ext <;> simp
      map_add' := by
        intro x y
        ext <;> simp }
  refine ⟨f, ?_⟩
  intro x y hxy
  have h1 : x.1 = y.1 := by
    have h1' : (f x).1 = (f y).1 :=
      congrArg (fun p : ZMod m × ZMod n => p.1) hxy
    exact h1'
  have h2 : g x.2 = g y.2 := by
    have h2' : (f x).2 = (f y).2 :=
      congrArg (fun p : ZMod m × ZMod n => p.2) hxy
    exact h2'
  have h2' : x.2 = y.2 := hg h2
  ext <;> assumption
