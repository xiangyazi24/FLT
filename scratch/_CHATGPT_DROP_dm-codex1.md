# Q: FLT Lean N12 branch-to-F proof code

The branch formulas from the prior answer are algebraically correct. The implementation below proves each branch by first deriving the relevant quadratic relation in

```text
q = ((m : ℚ) / A)^2,   r = (C : ℚ) / A,
```

then using `ring_nf`/`nlinarith` to verify the shifted curve equation. The B3/B4 witnesses need the displayed factor `3` in `Y`; without it they would land on the wrong scaling of `F`.

If `F_N12_AffineEquation` is already present in the file, omit that `def` and keep the rest.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- Shifted N=12 curve: `Y^2 = X^3 + 2X^2 - 3X`. -/
def F_N12_AffineEquation (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- Normalized four-branch factor identity after absorbing the sign of `a*c = ±m*n`. -/
def NormalizedNonAxisFactorIdentity (m n A C : ℤ) : Prop :=
  A * C = m * n ∧
    ((m - n) * (m + n) = (A - C) * (3 * A - C) ∨
     (m - n) * (m + n) = -((A + C) * (3 * A + C)) ∨
     (m - n) * (m + n) = (A - C) * (A - 3 * C) ∨
     (m - n) * (m + n) = -((A + C) * (A + 3 * C)))

/-- The compact residual sign-normalizes to `A*C = m*n` and one of four branches. -/
theorem nonAxisFactorIdentityResidual_normalize
    {m n a c : ℤ}
    (h : NonAxisFactorIdentityResidual m n a c) :
    ∃ A C : ℤ, NormalizedNonAxisFactorIdentity m n A C := by
  unfold NonAxisFactorIdentityResidual at h
  rcases h with ⟨hac, hbr⟩ | ⟨hac, hbr⟩
  · refine ⟨a, c, ?_⟩
    unfold NormalizedNonAxisFactorIdentity
    exact ⟨hac, hbr⟩
  · refine ⟨a, -c, ?_⟩
    unfold NormalizedNonAxisFactorIdentity
    constructor
    · rw [mul_neg, hac]
      ring
    · rcases hbr with h1 | h2 | h3 | h4
      · left
        calc
          (m - n) * (m + n) = (a + c) * (3 * a + c) := h1
          _ = (a - -c) * (3 * a - -c) := by ring
      · right; left
        calc
          (m - n) * (m + n) = -((a - c) * (3 * a - c)) := h2
          _ = -((a + -c) * (3 * a + -c)) := by ring
      · right; right; left
        calc
          (m - n) * (m + n) = (a + c) * (a + 3 * c) := h3
          _ = (a - -c) * (a - 3 * -c) := by ring
      · right; right; right
        calc
          (m - n) * (m + n) = -((a - c) * (a - 3 * c)) := h4
          _ = -((a + -c) * (a + 3 * -c)) := by ring

/-- Branch B1 gives a point on `F` with `X = ((m/A)^2)`. -/
theorem branch_B1_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB1 : (m - n) * (m + n) = (A - C) * (3 * A - C)) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (((m : ℚ) / (A : ℚ)) ^ 2) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (q + 1) * r ^ 2 - 4 * q * r + 3 * q - q ^ 2 = 0 := by
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
  refine ⟨(q + 1) * r - 2 * q, ?_⟩
  change F_N12_AffineEquation q ((q + 1) * r - 2 * q)
  dsimp [F_N12_AffineEquation]
  ring_nf at hrel ⊢
  nlinarith

/-- Branch B2 gives a point on `F` with `X = -((m/A)^2)`. -/
theorem branch_B2_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB2 : (m - n) * (m + n) = -((A + C) * (3 * A + C))) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (-(((m : ℚ) / (A : ℚ)) ^ 2)) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (q - 1) * r ^ 2 + 4 * q * r + q ^ 2 + 3 * q = 0 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
    have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
      exact_mod_cast hAC
    have hB2q :
        ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
          -(((A : ℚ) + (C : ℚ)) * (3 * (A : ℚ) + (C : ℚ))) := by
      exact_mod_cast hB2
    have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
      rw [hACq]
    have hB2mul :
        ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
          ((m : ℚ) ^ 2) * (-(((A : ℚ) + (C : ℚ)) * (3 * (A : ℚ) + (C : ℚ)))) := by
      rw [hB2q]
    field_simp [q, r, hAq]
    ring_nf at hACsq hB2mul ⊢
    nlinarith
  refine ⟨(q - 1) * r + 2 * q, ?_⟩
  change F_N12_AffineEquation (-q) ((q - 1) * r + 2 * q)
  dsimp [F_N12_AffineEquation]
  ring_nf at hrel ⊢
  nlinarith

/-- Branch B3 gives a point on `F` with `X = 3 * (m/A)^2`. -/
theorem branch_B3_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB3 : (m - n) * (m + n) = (A - C) * (A - 3 * C)) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (3 * (((m : ℚ) / (A : ℚ)) ^ 2)) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (3 * q + 1) * r ^ 2 - 4 * q * r + q - q ^ 2 = 0 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
    have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
      exact_mod_cast hAC
    have hB3q :
        ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
          ((A : ℚ) - (C : ℚ)) * ((A : ℚ) - 3 * (C : ℚ)) := by
      exact_mod_cast hB3
    have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
      rw [hACq]
    have hB3mul :
        ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
          ((m : ℚ) ^ 2) * (((A : ℚ) - (C : ℚ)) * ((A : ℚ) - 3 * (C : ℚ))) := by
      rw [hB3q]
    field_simp [q, r, hAq]
    ring_nf at hACsq hB3mul ⊢
    nlinarith
  refine ⟨3 * ((3 * q + 1) * r - 2 * q), ?_⟩
  change F_N12_AffineEquation (3 * q) (3 * ((3 * q + 1) * r - 2 * q))
  dsimp [F_N12_AffineEquation]
  ring_nf at hrel ⊢
  nlinarith

/-- Branch B4 gives a point on `F` with `X = -3 * (m/A)^2`. -/
theorem branch_B4_to_F
    {m n A C : ℤ}
    (hAC : A * C = m * n)
    (hA : A ≠ 0)
    (hB4 : (m - n) * (m + n) = -((A + C) * (A + 3 * C))) :
    ∃ Y : ℚ,
      F_N12_AffineEquation (-3 * (((m : ℚ) / (A : ℚ)) ^ 2)) Y := by
  let q : ℚ := ((m : ℚ) / (A : ℚ)) ^ 2
  let r : ℚ := (C : ℚ) / (A : ℚ)
  have hrel : (3 * q - 1) * r ^ 2 + 4 * q * r + q + q ^ 2 = 0 := by
    have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
    have hACq : (A : ℚ) * (C : ℚ) = (m : ℚ) * (n : ℚ) := by
      exact_mod_cast hAC
    have hB4q :
        ((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ)) =
          -(((A : ℚ) + (C : ℚ)) * ((A : ℚ) + 3 * (C : ℚ))) := by
      exact_mod_cast hB4
    have hACsq : ((A : ℚ) * (C : ℚ)) ^ 2 = ((m : ℚ) * (n : ℚ)) ^ 2 := by
      rw [hACq]
    have hB4mul :
        ((m : ℚ) ^ 2) * (((m : ℚ) - (n : ℚ)) * ((m : ℚ) + (n : ℚ))) =
          ((m : ℚ) ^ 2) * (-(((A : ℚ) + (C : ℚ)) * ((A : ℚ) + 3 * (C : ℚ)))) := by
      rw [hB4q]
    field_simp [q, r, hAq]
    ring_nf at hACsq hB4mul ⊢
    nlinarith
  refine ⟨3 * ((3 * q - 1) * r + 2 * q), ?_⟩
  change F_N12_AffineEquation (-3 * q) (3 * ((3 * q - 1) * r + 2 * q))
  dsimp [F_N12_AffineEquation]
  ring_nf at hrel ⊢
  nlinarith

end RationalPointsN12
end MazurProof
```
