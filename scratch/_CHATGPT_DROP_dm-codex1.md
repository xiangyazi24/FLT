# Q: FLT Lean N12 no nonaxis residual from shifted x-cases (redispatch after no-commit)

The safest route is to **case-split on the normalized branch**, not to use only the aggregate `normalizedNonAxisFactorIdentity_to_F` output. The aggregate output forces `X ∈ {q,-q,3q,-3q}`, and then a purely squareclass proof needs rational nonsquare lemmas for `3` and `1/3`. Branch-splitting avoids those: the apparent exceptional cases `q=3` or `q=1/3` are killed by the branch identity itself.

Below is paste-oriented Lean with no `sorry` in the executable code. It gives the general elementary helpers, the `q=1` branch helper, and a complete B1 branch contradiction. The final theorem is then a short split once the analogous B2/B3/B4 branch contradictions are added.

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
  exact hdiv (sq_eq_zero_iff.mp hzero)

/-- A rational square is not `-1`. -/
theorem ratio_sq_ne_neg_one {t : ℚ} : t ^ 2 ≠ (-1 : ℚ) := by
  intro h
  have hnonneg : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith

/-- A rational square is not `-3`. -/
theorem ratio_sq_ne_neg_three {t : ℚ} : t ^ 2 ≠ (-3 : ℚ) := by
  intro h
  have hnonneg : 0 ≤ t ^ 2 := sq_nonneg t
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

/-- If `A*C=m*n` and `(m/A)^2=1`, then `(A,C)` equals `(m,n)` or `(-m,-n)`. -/
theorem AC_eq_mn_or_neg_of_ratio_sq_eq_one
    {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hAC : A * C = m * n)
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    (A = m ∧ C = n) ∨ (A = -m ∧ C = -n) := by
  have hm0 : m ≠ 0 := left_ne_zero_of_mul_ne_zero hmn0
  have hA0 : A ≠ 0 := A_ne_zero_of_hAC_hmn0 hmn0 hAC
  rcases int_ratio_sq_eq_one_cases (m := m) (A := A) hA0 hq with hmA | hmnegA
  · left
    have hAeq : A = m := by omega
    constructor
    · exact hAeq
    · have hmul : m * C = m * n := by simpa [hAeq] using hAC
      exact mul_left_cancel₀ hm0 hmul
  · right
    have hAeq : A = -m := by omega
    constructor
    · exact hAeq
    · have hmul : m * (-C) = m * n := by
        calc
          m * (-C) = (-m) * C := by ring
          _ = A * C := by rw [hAeq]
          _ = m * n := hAC
      have hnegC : -C = n := mul_left_cancel₀ hm0 hmul
      omega

/-- Under any normalized branch, the case `q=1` forces `m=n` or `m=-n`. -/
theorem normalized_branch_q1_forces_m_eq_or_neg
    {m n A C : ℤ}
    (hmn0 : m * n ≠ 0)
    (hnorm : NormalizedNonAxisFactorIdentity m n A C)
    (hq : ((m : ℚ) / (A : ℚ)) ^ 2 = 1) :
    m = n ∨ m = -n := by
  rcases hnorm with ⟨hAC, hB1 | hB2 | hB3 | hB4⟩
  · rcases AC_eq_mn_or_neg_of_ratio_sq_eq_one hmn0 hAC hq with hpair | hpair
    · rcases hpair with ⟨hA, hC⟩
      left
      have hEq := hB1
      rw [hA, hC] at hEq
      ring_nf at hEq
      nlinarith
    · rcases hpair with ⟨hA, hC⟩
      left
      have hEq := hB1
      rw [hA, hC] at hEq
      ring_nf at hEq
      nlinarith
  · rcases AC_eq_mn_or_neg_of_ratio_sq_eq_one hmn0 hAC hq with hpair | hpair
    · rcases hpair with ⟨hA, hC⟩
      right
      have hm0 : m ≠ 0 := left_ne_zero_of_mul_ne_zero hmn0
      have hEq := hB2
      rw [hA, hC] at hEq
      have hprod : m * (m + n) = 0 := by
        ring_nf at hEq
        nlinarith
      rcases mul_eq_zero.mp hprod with hm | hsum
      · exact False.elim (hm0 hm)
      · omega
    · rcases hpair with ⟨hA, hC⟩
      right
      have hm0 : m ≠ 0 := left_ne_zero_of_mul_ne_zero hmn0
      have hEq := hB2
      rw [hA, hC] at hEq
      have hprod : m * (m + n) = 0 := by
        ring_nf at hEq
        nlinarith
      rcases mul_eq_zero.mp hprod with hm | hsum
      · exact False.elim (hm0 hm)
      · omega
  · rcases AC_eq_mn_or_neg_of_ratio_sq_eq_one hmn0 hAC hq with hpair | hpair
    · rcases hpair with ⟨hA, hC⟩
      left
      have hn0 : n ≠ 0 := right_ne_zero_of_mul_ne_zero hmn0
      have hEq := hB3
      rw [hA, hC] at hEq
      have hprod : n * (m - n) = 0 := by
        ring_nf at hEq
        nlinarith
      rcases mul_eq_zero.mp hprod with hn | hdiff
      · exact False.elim (hn0 hn)
      · omega
    · rcases hpair with ⟨hA, hC⟩
      left
      have hn0 : n ≠ 0 := right_ne_zero_of_mul_ne_zero hmn0
      have hEq := hB3
      rw [hA, hC] at hEq
      have hprod : n * (m - n) = 0 := by
        ring_nf at hEq
        nlinarith
      rcases mul_eq_zero.mp hprod with hn | hdiff
      · exact False.elim (hn0 hn)
      · omega
  · rcases AC_eq_mn_or_neg_of_ratio_sq_eq_one hmn0 hAC hq with hpair | hpair
    · rcases hpair with ⟨hA, hC⟩
      right
      have hEq := hB4
      rw [hA, hC] at hEq
      ring_nf at hEq
      nlinarith
    · rcases hpair with ⟨hA, hC⟩
      right
      have hEq := hB4
      rw [hA, hC] at hEq
      ring_nf at hEq
      nlinarith

/-- B1 algebraic relation in normalized rational variables. -/
theorem branch_B1_relation
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C)) :
    ((((m : ℚ) / (A : ℚ)) ^ 2 + 1) * ((C : ℚ) / (A : ℚ)) ^ 2
      - 4 * (((m : ℚ) / (A : ℚ)) ^ 2) * ((C : ℚ) / (A : ℚ))
      + 3 * (((m : ℚ) / (A : ℚ)) ^ 2)
      - (((m : ℚ) / (A : ℚ)) ^ 2) ^ 2) = 0 := by
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
  field_simp [hAq]
  ring_nf at hACsq hB1mul ⊢
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
    rw [hq'] at hrel
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
  · have hnorm : NormalizedNonAxisFactorIdentity m n A C := ⟨hAC, Or.inl hB1⟩
    rcases normalized_branch_q1_forces_m_eq_or_neg hmn0 hnorm hX with hmn | hmneg
    · exact opposite_parity_not_eq hpar hmn
    · exact opposite_parity_not_neg hpar hmneg
  · have hnonneg : 0 ≤ (((m : ℚ) / (A : ℚ)) ^ 2) := sq_nonneg _
    nlinarith
  · exact opposite_parity_not_eq hpar (branch_B1_q3_forces_m_eq_n hmn0 hAC hB1 hX)

end RationalPointsN12
end MazurProof
```

## Exact remaining branch interfaces

The full theorem should use the following three analogous branch contradictions. Their proofs follow the B1 pattern: use `branch_B*_to_F`; the `q=1` case is already handled by `normalized_branch_q1_forces_m_eq_or_neg`; the visible exceptional case is killed by the corresponding branch algebra.

```lean
namespace MazurProof
namespace RationalPointsN12

-- B2: `X=-q`; boundary leaves `q=1` or `q=3`; both force `m=-n`.
-- theorem branch_B2_contra_of_F_boundary
--     (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
--       X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
--     {m n A C : ℤ}
--     (hmn0 : m * n ≠ 0)
--     (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
--     (hAC : A * C = m * n)
--     (hB2 : (m - n) * (m + n) = -((A + C) * (3 * A + C))) :
--     False

-- B3: `X=3*q`; boundary leaves `q=1` or `q=1/3`; both force `m=n`.
-- theorem branch_B3_contra_of_F_boundary
--     (hFbd : ∀ {X Y : ℚ}, F_N12_AffineEquation X Y →
--       X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3)
--     {m n A C : ℤ}
--     (hmn0 : m * n ≠ 0)
--     (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨ (m % 2 = 1 ∧ n % 2 = 0))
--     (hAC : A * C = m * n)
--     (hB3 : (m - n) * (m + n) = (A - C) * (A - 3 * C)) :
--     False

-- B4: `X=-3*q`; boundary leaves `q=1` or `q=1/3`; both force `m=-n`.
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

After those are present, the final theorem is just:

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

`hcop` is intentionally unused; it is kept only to match the bridge theorem’s existing output shape.
