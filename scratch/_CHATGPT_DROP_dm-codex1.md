# Q: FLT Lean N12 EC boundary API

This API keeps the current N12 obstruction code dependent only on a point-list boundary theorem, not on the future 2-isogeny proof internals.

I could not fetch `FLT/Assumptions/MazurProof/RationalPointsN12.lean` through the connector at the path in the prompt, so the code below is intentionally a namespace/name sketch. It uses the theorem names you gave as fixed existing wrappers.

## Recommended boundary theorem names

Put the hard arithmetic statement in `MazurProof.RationalPointsN12`. The most useful boundary is the shifted curve point list.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- Hard arithmetic boundary for the shifted N=12 curve.

This is the theorem to prove later by 2-isogeny descent plus torsion enumeration.
It should not depend on the denominator-residual file. -/
theorem shifted_F_affine_rational_points
    {X Y : ℚ}
    (hF : Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X) :
    (X = -3 ∧ Y = 0) ∨
    (X = 0 ∧ Y = 0) ∨
    (X = 1 ∧ Y = 0) ∨
    (X = -1 ∧ (Y = 2 ∨ Y = -2)) ∨
    (X = 3 ∧ (Y = 6 ∨ Y = -6)) := by
  -- Future proof file: 2-isogeny descent on F/F' + torsion via mod 5 and 7.
  sorry

end RationalPointsN12
end MazurProof
```

This theorem is the cleanest hard boundary. Everything below is elementary wrapper code.

## Shifted-to-original affine classification

The original curve is

```text
E_N12 : w^2 = u^3 - u^2 - 4u + 4.
```

The shift is `X = u - 1`, `Y = w`, since

```text
(u - 1)^3 + 2 (u - 1)^2 - 3 (u - 1)
  = u^3 - u^2 - 4u + 4.
```

Suggested wrapper theorem:

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- Elementary conversion from the shifted point list to the original affine point list. -/
theorem E_N12_affine_rational_points_of_shifted
    (hShifted : ∀ {X Y : ℚ},
      Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X →
        (X = -3 ∧ Y = 0) ∨
        (X = 0 ∧ Y = 0) ∨
        (X = 1 ∧ Y = 0) ∨
        (X = -1 ∧ (Y = 2 ∨ Y = -2)) ∨
        (X = 3 ∧ (Y = 6 ∨ Y = -6)))
    {u w : ℚ}
    (hE : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    (u = -2 ∧ w = 0) ∨
    (u = 1 ∧ w = 0) ∨
    (u = 2 ∧ w = 0) ∨
    (u = 0 ∧ (w = 2 ∨ w = -2)) ∨
    (u = 4 ∧ (w = 6 ∨ w = -6)) := by
  have hF : w ^ 2 = (u - 1) ^ 3 + 2 * (u - 1) ^ 2 - 3 * (u - 1) := by
    rw [hE]
    ring
  rcases hShifted (X := u - 1) (Y := w) hF with h | h | h | h | h
  · rcases h with ⟨hX, hY⟩
    left
    constructor
    · nlinarith
    · exact hY
  · rcases h with ⟨hX, hY⟩
    right; left
    constructor
    · nlinarith
    · exact hY
  · rcases h with ⟨hX, hY⟩
    right; right; left
    constructor
    · nlinarith
    · exact hY
  · rcases h with ⟨hX, hY⟩
    right; right; right; left
    constructor
    · nlinarith
    · exact hY
  · rcases h with ⟨hX, hY⟩
    right; right; right; right
    constructor
    · nlinarith
    · exact hY

/-- Original affine point-list boundary, derived from the shifted hard theorem. -/
theorem E_N12_affine_rational_points
    {u w : ℚ}
    (hE : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    (u = -2 ∧ w = 0) ∨
    (u = 1 ∧ w = 0) ∨
    (u = 2 ∧ w = 0) ∨
    (u = 0 ∧ (w = 2 ∨ w = -2)) ∨
    (u = 4 ∧ (w = 6 ∨ w = -6)) := by
  exact E_N12_affine_rational_points_of_shifted
    (hShifted := shifted_F_affine_rational_points) hE

end RationalPointsN12
end MazurProof
```

## U-only boundary for `E_N12_DegenerateParameter`

The current denominator residual likely wants only the possible `u` values. Keep this as a small theorem around the existing predicate `MazurProof.E_N12_DegenerateParameter u`.

Use whichever accessor/unfolding lemma already exists for `E_N12_DegenerateParameter`. If the definition is literally `∃ w, w^2 = u^3 - u^2 - 4u + 4`, the proof is just `rcases hu with ⟨w, hw⟩`.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- U-coordinate boundary for the original N=12 degenerate-parameter predicate. -/
theorem E_N12_DegenerateParameter_u_cases
    {u : ℚ}
    (hu : MazurProof.E_N12_DegenerateParameter u) :
    u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4 := by
  -- Replace this line by the actual accessor/unfolding already present in the file.
  -- Expected shape if the predicate is existential:
  --   rcases hu with ⟨w, hw⟩
  obtain ⟨w, hw⟩ : ∃ w : ℚ, w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 := by
    -- e.g. exact MazurProof.E_N12_DegenerateParameter.exists_curve_point hu
    -- or `simpa [MazurProof.E_N12_DegenerateParameter] using hu`
    sorry

  rcases E_N12_affine_rational_points (u := u) (w := w) hw with h | h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.1)))
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h.1)))

end RationalPointsN12
end MazurProof
```

If the existing wrapper `N12NoNontrivialSquareDenominatorResidual_of_affine_boundary` expects an affine equation boundary rather than the predicate boundary, use `E_N12_affine_rational_points` directly instead of `E_N12_DegenerateParameter_u_cases`.

## Denominator residual wrapper

Given the existing wrapper name from the prompt, the final theorem in `RationalPointsN12.lean` should be only a one-line specialization.

```lean
import Mathlib

namespace MazurProof
namespace RationalPointsN12

/-- Final N=12 denominator residual, obtained from the hard affine boundary. -/
theorem N12NoNontrivialSquareDenominatorResidual
    {A B C : ℤ}
    (hB : B > 1)
    (hcop : Int.gcd A B = 1)
    (hEq : C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2)) :
    False := by
  exact N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    (boundary := E_N12_affine_rational_points)
    hB hcop hEq

end RationalPointsN12
end MazurProof
```

If the actual wrapper argument is the u-only predicate boundary, the specialization should instead be:

```lean
  exact N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    (boundary := E_N12_DegenerateParameter_u_cases)
    hB hcop hEq
```

Either way, the denominator theorem should not mention 2-isogenies, Selmer groups, reduction maps, or torsion.

## Suggested future file split

Recommended module split:

```text
FLT/Assumptions/MazurProof/RationalPointsN12.lean
  - imports only the boundary API theorem and elementary wrappers
  - contains square_denominator_rational_curve_equation
  - contains primitive_square_denominator_not_E_N12_DegenerateParameter
  - contains N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
  - contains final specialization N12NoNontrivialSquareDenominatorResidual

FLT/Assumptions/MazurProof/RationalPointsN12/Boundary.lean
  - states/proves shifted_F_affine_rational_points
  - proves E_N12_affine_rational_points_of_shifted
  - proves E_N12_affine_rational_points
  - proves E_N12_DegenerateParameter_u_cases

FLT/Assumptions/MazurProof/RationalPointsN12/TwoIsogenyCertificate.lean
  - proves the hard theorem shifted_F_affine_rational_points
  - contains alpha/alpha' image certificates
  - contains mod-16 dual obstruction
  - contains rank-zero theorem and torsion enumeration
```

If the hard proof is not ready, keep the current obstruction theorem parameterized via the already-added wrapper:

```lean
theorem N12NoNontrivialSquareDenominatorResidual_of_boundary
    (boundary : ∀ {u w : ℚ},
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 →
        (u = -2 ∧ w = 0) ∨
        (u = 1 ∧ w = 0) ∨
        (u = 2 ∧ w = 0) ∨
        (u = 0 ∧ (w = 2 ∨ w = -2)) ∨
        (u = 4 ∧ (w = 6 ∨ w = -6))) :
    ∀ {A B C : ℤ},
      B > 1 →
      Int.gcd A B = 1 →
      C ^ 2 = (A - B ^ 2) * (A - 2 * B ^ 2) * (A + 2 * B ^ 2) →
      False := by
  intro A B C hB hcop hEq
  exact N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    (boundary := boundary) hB hcop hEq
```

That keeps the current file compiling around an explicit parameter without introducing a new axiom.

## Minimal dependency boundary

The preferred boundary for the current N12 file is this u-only theorem:

```lean
theorem E_N12_DegenerateParameter_u_cases
    {u : ℚ}
    (hu : MazurProof.E_N12_DegenerateParameter u) :
    u = -2 ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4
```

The stronger affine theorem is better for the future EC proof:

```lean
theorem E_N12_affine_rational_points
    {u w : ℚ}
    (hE : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    (u = -2 ∧ w = 0) ∨
    (u = 1 ∧ w = 0) ∨
    (u = 2 ∧ w = 0) ∨
    (u = 0 ∧ (w = 2 ∨ w = -2)) ∨
    (u = 4 ∧ (w = 6 ∨ w = -6))
```

The actual hard theorem to prove by 2-isogeny descent is only:

```lean
theorem shifted_F_affine_rational_points
    {X Y : ℚ}
    (hF : Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X) :
    (X = -3 ∧ Y = 0) ∨
    (X = 0 ∧ Y = 0) ∨
    (X = 1 ∧ Y = 0) ∨
    (X = -1 ∧ (Y = 2 ∨ Y = -2)) ∨
    (X = 3 ∧ (Y = 6 ∨ Y = -6))
```
