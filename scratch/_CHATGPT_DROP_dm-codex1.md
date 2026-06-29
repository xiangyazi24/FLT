# Q: FLT Lean N12 EC boundary API compact

Use one hard shifted-curve theorem, one x-coordinate corollary, then feed the existing affine-boundary wrapper.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- Hard theorem, to be proved in a future EC file by 2-isogeny descent + torsion. -/
theorem F_N12_shifted_affine_points
    {X Y : ℚ}
    (hF : Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X) :
    (X = -3 ∧ Y = 0) ∨
    (X = 0 ∧ Y = 0) ∨
    (X = 1 ∧ Y = 0) ∨
    (X = -1 ∧ (Y = 2 ∨ Y = -2)) ∨
    (X = 3 ∧ (Y = 6 ∨ Y = -6)) := by
  -- future proof, not an axiom
  sorry

/-- Lightweight corollary: only the shifted x-coordinate cases. -/
theorem F_N12_shifted_x_cases
    {X Y : ℚ}
    (hF : Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X) :
    X = -3 ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3 := by
  rcases F_N12_shifted_affine_points hF with h | h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h.1)))

/-- Convert shifted x-cases to the existing original-curve affine boundary. -/
theorem E_N12_affine_boundary_of_shifted_x_cases :
    ∀ u w : ℚ,
      MazurProof.E_N12_AffineEquation u w →
      MazurProof.E_N12_DegenerateParameter u := by
  intro u w hE
  have hF : w ^ 2 = (u - 1) ^ 3 + 2 * (u - 1) ^ 2 - 3 * (u - 1) := by
    dsimp [MazurProof.E_N12_AffineEquation] at hE
    rw [hE]
    ring
  rcases F_N12_shifted_x_cases hF with h | h | h | h | h
  · dsimp [MazurProof.E_N12_DegenerateParameter]; left; linarith
  · dsimp [MazurProof.E_N12_DegenerateParameter]; right; right; left; linarith
  · dsimp [MazurProof.E_N12_DegenerateParameter]; right; right; right; left; linarith
  · dsimp [MazurProof.E_N12_DegenerateParameter]; right; left; linarith
  · dsimp [MazurProof.E_N12_DegenerateParameter]; right; right; right; right; linarith

/-- Final N12 residual: just specialize the already-existing wrapper. -/
theorem N12NoNontrivialSquareDenominatorResidual
    {A B C : ℤ}
    (hB : B > 1)
    (hcop : Int.gcd A B = 1)
    (hEq : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    False := by
  exact N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    E_N12_affine_boundary_of_shifted_x_cases hB hcop hEq

end RationalPointsN12
end MazurProof
```

Suggested split:

```text
RationalPointsN12/TwoIsogeny.lean
  proves F_N12_shifted_affine_points

RationalPointsN12.lean
  imports the boundary theorem
  defines F_N12_shifted_x_cases
  defines E_N12_affine_boundary_of_shifted_x_cases
  specializes N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
```

The current obstruction file should depend only on:

```lean
theorem E_N12_affine_boundary_of_shifted_x_cases :
    ∀ u w : ℚ,
      MazurProof.E_N12_AffineEquation u w →
      MazurProof.E_N12_DegenerateParameter u
```
