import Mathlib

/-!
# Finite cyclic-group embeddings for the Mazur proof scaffold

This file contains pure finite abelian group lemmas used by the Mazur torsion
framework.  The key construction is the standard injection
`ZMod m →+ ZMod n` when `m ∣ n`, sending `x` to `(n / m) * x`.
-/

namespace MazurProof

/--
If `m ∣ n`, then `ZMod m` embeds additively in `ZMod n`.

The map sends the class of `a` modulo `m` to `(n / m) * a` modulo `n`.
-/
theorem zmod_contains_of_dvd (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    ∃ g : ZMod m →+ ZMod n, Function.Injective g := by
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
  refine ⟨g, ?_⟩
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

/-- If `m ∣ n`, then `ZMod m × ZMod m` embeds in `ZMod m × ZMod n`. -/
theorem zmod_prod_contains_square (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    ∃ f : ZMod m × ZMod m →+ ZMod m × ZMod n, Function.Injective f := by
  rcases zmod_contains_of_dvd m n hm hn hmn with ⟨g, hg⟩
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

/--
If `r ∣ m ∣ n`, then `ZMod r × ZMod r` embeds in `ZMod m × ZMod n`.
-/
theorem zmod_prod_contains_square_of_dvd
    (r m n : ℕ) (hr : 0 < r) (hm : 0 < m) (hn : 0 < n)
    (hrm : r ∣ m) (hmn : m ∣ n) :
    ∃ f : ZMod r × ZMod r →+ ZMod m × ZMod n, Function.Injective f := by
  rcases zmod_contains_of_dvd r m hr hm hrm with ⟨g₁, hg₁⟩
  rcases zmod_contains_of_dvd r n hr hn (dvd_trans hrm hmn) with ⟨g₂, hg₂⟩
  let f : ZMod r × ZMod r →+ ZMod m × ZMod n :=
    { toFun := fun p => (g₁ p.1, g₂ p.2)
      map_zero' := by
        ext <;> simp
      map_add' := by
        intro x y
        ext <;> simp }
  refine ⟨f, ?_⟩
  intro x y hxy
  have h1 : g₁ x.1 = g₁ y.1 := by
    have h1' : (f x).1 = (f y).1 :=
      congrArg (fun p : ZMod m × ZMod n => p.1) hxy
    exact h1'
  have h2 : g₂ x.2 = g₂ y.2 := by
    have h2' : (f x).2 = (f y).2 :=
      congrArg (fun p : ZMod m × ZMod n => p.2) hxy
    exact h2'
  have h1' : x.1 = y.1 := hg₁ h1
  have h2' : x.2 = y.2 := hg₂ h2
  ext <;> assumption

/--
Correct finite-group version of the `(ZMod 3)^2` containment statement:
the first invariant factor must be divisible by `3`, not merely at least `3`.
-/
theorem zmod_prod_contains_three_square_of_three_dvd
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h3m : 3 ∣ m) (hmn : m ∣ n) :
    ∃ f : ZMod 3 × ZMod 3 →+ ZMod m × ZMod n, Function.Injective f := by
  exact zmod_prod_contains_square_of_dvd 3 m n (by norm_num) hm hn h3m hmn

/-- `ZMod 2 × ZMod n` embeds in itself. -/
theorem zmod_two_prod_contains_self (n : ℕ) :
    ∃ f : ZMod 2 × ZMod n →+ ZMod 2 × ZMod n, Function.Injective f := by
  exact ⟨AddMonoidHom.id (ZMod 2 × ZMod n), fun _ _ h => h⟩

/--
If `r ∣ n`, then `ZMod 2 × ZMod r` embeds in `ZMod 2 × ZMod n`.
This is the useful specialization for excluding noncyclic torsion with a
specified second invariant factor.
-/
theorem zmod_two_prod_contains_second_factor_of_dvd
    (r n : ℕ) (hr : 0 < r) (hn : 0 < n) (hrn : r ∣ n) :
    ∃ f : ZMod 2 × ZMod r →+ ZMod 2 × ZMod n, Function.Injective f := by
  rcases zmod_contains_of_dvd r n hr hn hrn with ⟨g, hg⟩
  let f : ZMod 2 × ZMod r →+ ZMod 2 × ZMod n :=
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
      congrArg (fun p : ZMod 2 × ZMod n => p.1) hxy
    exact h1'
  have h2 : g x.2 = g y.2 := by
    have h2' : (f x).2 = (f y).2 :=
      congrArg (fun p : ZMod 2 × ZMod n => p.2) hxy
    exact h2'
  have h2' : x.2 = y.2 := hg h2
  ext <;> assumption

/--
If `10 ∣ n`, then `ZMod 2 × ZMod 10` embeds in `ZMod 2 × ZMod n`.
-/
theorem zmod_two_prod_contains_ten_of_ten_dvd
    (n : ℕ) (hn : 0 < n) (h10n : 10 ∣ n) :
    ∃ f : ZMod 2 × ZMod 10 →+ ZMod 2 × ZMod n, Function.Injective f := by
  exact zmod_two_prod_contains_second_factor_of_dvd 10 n (by norm_num) hn h10n

/-- The first factor `ZMod 1` is additively trivial. -/
def zmod_one_prod_addEquiv (n : ℕ) : ZMod 1 × ZMod n ≃+ ZMod n where
  toFun p := p.2
  invFun y := (0, y)
  left_inv p := by
    ext
    · exact Subsingleton.elim _ _
    · rfl
  right_inv y := rfl
  map_add' x y := rfl

/-- Existence form of `ZMod 1 × ZMod n ≃+ ZMod n`. -/
theorem zmod_one_prod_addEquiv_exists (n : ℕ) :
    Nonempty (ZMod 1 × ZMod n ≃+ ZMod n) :=
  ⟨zmod_one_prod_addEquiv n⟩

/-- Cardinality of ZMod m × ZMod n is m * n. -/
theorem card_zmod_prod (m n : ℕ) [NeZero m] [NeZero n] :
    Fintype.card (ZMod m × ZMod n) = m * n := by
  simp [Fintype.card_prod]

/-- If m | n, there is an injective hom ZMod m × ZMod m →+ ZMod m × ZMod n. -/
theorem zmod_prod_embed (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) :
    ∃ f : ZMod m × ZMod m →+ ZMod m × ZMod n, Function.Injective f :=
  zmod_prod_contains_square m n hm hn hmn

end MazurProof
