# Q: FLT Lean N12 no nonaxis residual from shifted x-cases

I would **not** try to eliminate the `q = 3` and `q = 1/3` alternatives by proving irrationality of `√3` in this file. There is a cleaner branch-local route: in each branch, those extra shifted-x cases force `m = n` or `m = -n` directly from the branch identity and `A*C = m*n`. This avoids importing or proving rational nonsquare lemmas.

Below is paste-oriented Lean for the reusable helpers and a complete B1 branch proof. The B2/B3/B4 branch helpers should be proved by the same pattern; I list their exact target statements after the code. This is the safest next increment because the full final theorem becomes a short `rcases` once those three analogous branch helpers are present.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- From `A*C = m*n` and `m*n ≠ 0`, the normalizing denominator `A` is nonzero. -/
theorem A_ne_zero_of_hAC_hmn0
    {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n) :
    A ≠ 0 := by
  intro hA
  apply hmn0
  rw [← hAC, hA, zero_mul]

/-- From `A*C = m*n` and `m*n ≠ 0`, the normalized factor `C` is nonzero. -/
theorem C_ne_zero_of_hAC_hmn0
    {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n) :
    C ≠ 0 := by
  intro hC
  apply hmn0
  rw [← hAC, hC, mul_zero]

/-- Left factor of a nonzero product is nonzero. -/
theorem left_ne_zero_of_mul_ne_zero {m n : ℤ} (hmn0 : m * n ≠ 0) : m ≠ 0 := by
  intro hm
  apply hmn0
  simp [hm]

/-- Right factor of a nonzero product is nonzero. -/
theorem right_ne_zero_of_mul_ne_zero {m n : ℤ} (hmn0 : m * n ≠ 0) : n ≠ 0 := by
  intro hn
  apply hmn0
  simp [hn]

/-- The rational square `((m : ℚ)/(A : ℚ))^2` is nonzero under the bridge hypotheses. -/
theorem ratio_sq_ne_zero_of_hmn0_hA
    {m n A : ℤ}
    (hmn0 : m * n ≠ 0)
    (hA : A ≠ 0) :
    ((m : ℚ) / (A : ℚ)) ^ 2 ≠ 0 := by
  have hm0 : m ≠ 0 := left_ne_zero_of_mul_ne_zero hmn0
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hAQ : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hdiv : (m : ℚ) / (A : ℚ) ≠ 0 := div_ne_zero hmQ hAQ
  intro hzero
  have hpos : 0 < ((m : ℚ) / (A : ℚ)) ^ 2 := sq_pos_of_ne_zero hdiv
  nlinarith

/-- Opposite parity contradicts `m = n`. -/
theorem opposite_parity_not_eq
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
    (h : m = n) :
    False := by
  omega

/-- Opposite parity contradicts `m = -n`. -/
theorem opposite_parity_not_neg
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
    (h : m = -n) :
    False := by
  omega

/-- If `(m/A)^2 = 1` over `ℚ`, then `m = A` or `m = -A` over `ℤ`. -/
theorem int_ratio_sq_eq_one_cases
    {m A : ℤ}
    (hA : A ≠ 0)
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = A ∨ m = -A := by
  have hAQ : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hsq : (m : ℚ) ^ 2 = (A : ℚ) ^ 2 := by
    field_simp [hAQ] at hq
    simpa using hq
  have hprod : ((m : ℚ) - (A : ℚ)) * ((m : ℚ) + (A : ℚ)) = 0 := by
    ring_nf
    nlinarith
  rcases mul_eq_zero.mp hprod with hsub | hsum
  · left
    apply Int.cast_injective
    linarith
  · right
    apply Int.cast_injective
    have hmneg : (m : ℚ) = - (A : ℚ) := by linarith
    simpa using hmneg

/-- B1 algebraic relation in normalized rational variables.

This is the same relation used internally by `branch_B1_to_F`, but exported because it
is useful when the shifted-x boundary returns the visible point `X = 3`. -/
theorem branch_B1_relation
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C)) :
    let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
    let r : ℚ := (C : ℚ) / (A : ℚ)
    (q + 1) * r ^ 2 - 4 * q * r + 3 * q - q ^ 2 = 0 := by
  intro q r
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
    exact_mod_cast hAC
  have hB1q :
      ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
        ((A : ℚ) - (C : ℚ)) * (3 * (A : ℚ) - (C : ℚ)) := by
    exact_mod_cast hB1
  have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
    rw [hACq]
  have hB1mul :
      ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
        ((m : ℚ) ^ 2) * (((A : ℚ) - (C : ℚ)) * (3 * (A : ℚ) - (C : ℚ))) := by
    rw [hB1q]
  field_simp [q, r, hAq]
  ring_nf at hACsq hB1mul ⊢
  nlinarith

/-- In B1, the shifted-x case `q = 1` forces `m = n`. -/
theorem branch_B1_q1_forces_m_eq_n
    {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C))
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = n := by
  have hm0 : m ≠ 0 := left_ne_zero_of_mul_ne_zero hmn0
  have hA : A ≠ 0 := A_ne_zero_of_hAC_hmn0 hmn0 hAC
  rcases int_ratio_sq_eq_one_cases hA hq with hmA | hmnegA
  · have hAeq : A = m := by omega
    have hCeq : C = n := by
      have hmul : m * C = m * n := by simpa [hAeq] using hAC
      exact mul_left_cancel₀ hm0 hmul
    have hEq := hB1
    rw [hAeq, hCeq] at hEq
    ring_nf at hEq
    nlinarith
  · have hAeq : A = -m := by omega
    have hCeq : C = -n := by
      have hmul : m * (-C) = m * n := by
        calc
          m * (-C) = (-m) * C := by ring
          _ = A * C := by rw [hAeq]
          _ = m * n := hAC
      have hnegC : -C = n := mul_left_cancel₀ hm0 hmul
      omega
    have hEq := hB1
    rw [hAeq, hCeq] at hEq
    ring_nf at hEq
    nlinarith

/-- In B1, the shifted-x case `q = 3` also forces `m = n`.

This avoids a separate rational-irrationality proof for `√3`. -/
theorem branch_B1_q3_forces_m_eq_n
    {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C))
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 3) :
    m = n := by
  have hm0 : m ≠ 0 := left_ne_zero_of_mul_ne_zero hmn0
  have hC0 : C ≠ 0 := C_ne_zero_of_hAC_hmn0 hmn0 hAC
  have hA : A ≠ 0 := A_ne_zero_of_hAC_hmn0 hmn0 hAC
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (q + 1) * r ^ 2 - 4 * q * r + 3 * q - q ^ 2 = 0 := by
    simpa [q, r] using branch_B1_relation (m := m) (n := n) (A := A) (C := C) hAC hA hB1
  have hq' : q = 3 := by simpa [q] using hq
  have hrprod : r * (r - 3) = 0 := by
    ring_nf at hrel ⊢
    nlinarith
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  have hCq_ne : (C : ℚ) ≠ 0 := by exact_mod_cast hC0
  have hr_ne_zero : r ≠ 0 := by
    dsimp [r]
    exact div_ne_zero hCq_ne hAq
  have hr : r = 3 := by
    rcases mul_eq_zero.mp hrprod with hr0 | hr3
    · exact False.elim (hr_ne_zero hr0)
    · linarith
  have hCq : (C : ℚ) = 3 * (A : ℚ) := by
    have hmul := congrArg (fun z : ℚ => z * (A : ℚ)) hr
    dsimp [r] at hmul
    field_simp [hAq] at hmul
    linarith
  have hq_sq : (m : ℚ) ^ 2 = 3 * (A : ℚ) ^ 2 := by
    dsimp [q] at hq'
    field_simp [hAq] at hq'
    nlinarith
  have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
    exact_mod_cast hAC
  have hm2mn : (m : ℚ) ^ 2 = (m : ℚ) * (n : ℚ) := by
    nlinarith
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hmq : (m : ℚ) = (n : ℚ) := by
    have hmul : (m : ℚ) * (m : ℚ) = (m : ℚ) * (n : ℚ) := by
      simpa [pow_two] using hm2mn
    exact mul_left_cancel₀ hmQ hmul
  exact_mod_cast hmq

/-- Complete B1 branch contradiction from the shifted x-coordinate boundary. -/
theorem branch_B1_contra_of_F_boundary
    (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
      X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
    {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
    (hAC : A * C = m * n)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C)) :
    False := by
  have hA : A ≠ 0 := A_ne_zero_of_hAC_hmn0 hmn0 hAC
  obtain ⟨Y, hY⟩ := branch_B1_to_F (m := m) (n := n) (A := A) (C := C) hAC hA hB1
  rcases hFbd hY with hX | hX | hX | hX | hX
  · have hnonneg : 0 ≤ (((m : ℚ) / (A : ℚ)) ^ 2) := sq_nonneg _
    nlinarith
  · exact ratio_sq_ne_zero_of_hmn0_hA (m := m) (n := n) (A := A) hmn0 hA hX
  · exact opposite_parity_not_eq hpar (branch_B1_q1_forces_m_eq_n hmn0 hAC hB1 hX)
  · have hnonneg : 0 ≤ (((m : ℚ) / (A : ℚ)) ^ 2) := sq_nonneg _
    nlinarith
  · exact opposite_parity_not_eq hpar (branch_B1_q3_forces_m_eq_n hmn0 hAC hB1 hX)

end RationalPointsN12
end MazurProof
```

## Exact remaining branch-helper targets

Add these three helpers next. Their proofs are the same as B1, with the visible shifted-x exceptional cases handled branch-locally instead of via rational nonsquare lemmas:

```lean
namespace MazurProof
namespace RationalPointsN12

-- B2: `X = -q`; surviving shifted-x cases are `X = -1` (`q=1`) and
-- the visible exceptional `X = -3` (`q=3`). Both force `m = -n`.
-- theorem branch_B2_contra_of_F_boundary
--     (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
--       X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
--     {m n A C : ℤ}
--     (hmn0 : m * n ≠ 0)
--     (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
--     (hAC : A * C = m * n)
--     (hB2 : (m - n) * (m + n) = -((A + C) * (3 * A + C))) :
--     False

-- B3: `X = 3*q`; surviving shifted-x cases are `X = 3` (`q=1`) and
-- the visible exceptional `X = 1` (`q=1/3`). Both force `m = n`.
-- theorem branch_B3_contra_of_F_boundary
--     (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
--       X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
--     {m n A C : ℤ}
--     (hmn0 : m * n ≠ 0)
--     (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
--     (hAC : A * C = m * n)
--     (hB3 : (m - n) * (m + n) = (A - C) * (A - 3 * C)) :
--     False

-- B4: `X = -3*q`; surviving shifted-x cases are `X = -3` (`q=1`) and
-- the visible exceptional `X = -1` (`q=1/3`). Both force `m = -n`.
-- theorem branch_B4_contra_of_F_boundary
--     (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
--       X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
--     {m n A C : ℤ}
--     (hmn0 : m * n ≠ 0)
--     (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
--     (hAC : A * C = m * n)
--     (hB4 : (m - n) * (m + n) = -((A + C) * (A + 3 * C))) :
--     False

end RationalPointsN12
end MazurProof
```

Once those three helpers are available, the final theorem is just this split:

```lean
namespace MazurProof
namespace RationalPointsN12

-- theorem no_NonAxisFactorIdentityResidual_of_F_boundary
--     (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
--       X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
--     {m n a c : ℤ}
--     (hmn0 : m * n ≠ 0)
--     (hcop : Int.gcd m n = 1)
--     (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
--     (hres : NonAxisFactorIdentityResidual m n a c) :
--     False := by
--   obtain ⟨A, C, hnorm⟩ := nonAxisFactorIdentityResidual_normalize hres
--   rcases hnorm with ⟨hAC, hB1 | hB2 | hB3 | hB4⟩
--   · exact branch_B1_contra_of_F_boundary hFbd hmn0 hpar hAC hB1
--   · exact branch_B2_contra_of_F_boundary hFbd hmn0 hpar hAC hB2
--   · exact branch_B3_contra_of_F_boundary hFbd hmn0 hpar hAC hB3
--   · exact branch_B4_contra_of_F_boundary hFbd hmn0 hpar hAC hB4

end RationalPointsN12
end MazurProof
```

The `hcop` argument is unused in this final contradiction; keep it only because it matches the bridge theorem shape.
