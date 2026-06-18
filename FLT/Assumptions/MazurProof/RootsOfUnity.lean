import Mathlib

/-!
# Roots of unity in `ℚ`

The cyclotomic route is available in Mathlib via
`Polynomial.cyclotomic_eq_minpoly_rat` and `Nat.totient_eq_one_iff`, but for
`ℚ` there is a shorter argument: a finite-order element in a linear ordered
ring has order at most two.
-/

namespace MazurProof

/-- If a rational number is a primitive `m`-th root of unity, then `m ≤ 2`. -/
theorem isPrimitiveRoot_rat_order_le_two {ζ : ℚ} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) :
    m ≤ 2 := by
  rw [hζ.eq_orderOf]
  exact LinearOrderedRing.orderOf_le_two

/-- The only roots of unity in `ℚ` are `±1`. -/
theorem rat_root_of_unity_eq_one_or_neg_one (ζ : ℚ) {n : ℕ} (hn : 1 ≤ n)
    (hζ : ζ ^ n = 1) : ζ = 1 ∨ ζ = -1 := by
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hζ⟩
  by_cases hnonneg : 0 ≤ ζ
  · exact Or.inl (IsOfFinOrder.eq_one hnonneg hfin)
  · exact Or.inr (IsOfFinOrder.eq_neg_one (le_of_not_ge hnonneg) hfin)

/-- Equivalent existential formulation. -/
theorem rat_root_of_unity_exists_eq_one_or_neg_one (ζ : ℚ)
    (hζ : ∃ n : ℕ, 1 ≤ n ∧ ζ ^ n = 1) : ζ = 1 ∨ ζ = -1 := by
  rcases hζ with ⟨n, hn, hpow⟩
  exact rat_root_of_unity_eq_one_or_neg_one ζ hn hpow

end MazurProof
