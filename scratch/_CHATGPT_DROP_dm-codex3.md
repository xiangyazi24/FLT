# Q2211 Lean drop: shifted-curve boundary for the N=12 rational-points theorem

This proposes the public theorem boundary and elementary wrappers for
`FLT/Assumptions/MazurProof/RationalPointsN12.lean`, using the existing namespaces

```lean
namespace MazurProof
namespace MazurProof.RationalPointsN12
```

The hard arithmetic result should eventually be proved elsewhere, probably from a 2-descent / 2-isogeny computation on the shifted curve

```text
F : Y^2 = X^3 + 2X^2 - 3X = X(X + 3)(X - 1),
```

where

```text
X = u - 1,   Y = w.
```

The N=12 obstruction file should consume only a theorem such as

```lean
F_N12_rational_points_degenerate_x
```

or the stronger exact point classification, not the internals of the descent proof.

## 1. Shifted curve definitions and point-list predicates

Put these elementary definitions either near the existing N=12 curve wrappers or in a small public file such as
`FLT/Assumptions/MazurProof/RationalPointsN12/Boundary.lean`.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Shifted N=12 curve: `Y^2 = X^3 + 2X^2 - 3X`. -/
def F_N12_AffineCurve (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- The shifted `X`-coordinates corresponding to the degenerate N=12 parameters. -/
def F_N12_DegenerateX (X : ℚ) : Prop :=
  X = (-3 : ℚ) ∨ X = 0 ∨ X = 1 ∨ X = -1 ∨ X = 3

/-- Exact affine rational point list for the shifted curve. -/
def F_N12_ExactAffinePoint (X Y : ℚ) : Prop :=
  (X = (-3 : ℚ) ∧ Y = 0) ∨
  (X = 0 ∧ Y = 0) ∨
  (X = 1 ∧ Y = 0) ∨
  (X = -1 ∧ Y = 2) ∨
  (X = -1 ∧ Y = -2) ∨
  (X = 3 ∧ Y = 6) ∨
  (X = 3 ∧ Y = -6)

/-- Exact shifted point classification implies the weaker shifted `X`-classification. -/
theorem F_N12_DegenerateX_of_exactAffinePoint
    {X Y : ℚ}
    (h : F_N12_ExactAffinePoint X Y) :
    F_N12_DegenerateX X := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr (Or.inl h.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h.1)))

end MazurProof.RationalPointsN12
```

The exact point list is stronger than the obstruction file needs, but it is the right certifiable arithmetic theorem to prove later.  The weak `X` theorem is the right theorem for wrappers.

## 2. Shift equivalence between `E_N12` and `F_N12`

The polynomial identity is

```text
u^3 - u^2 - 4u + 4 = (u - 1)^3 + 2(u - 1)^2 - 3(u - 1).
```

The elementary Lean wrapper is very small.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- Moving from `E_N12` to the shifted curve by `X = u - 1`. -/
theorem F_N12_curve_of_E_N12_curve
    (u w : ℚ)
    (hE : w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4) :
    F_N12_AffineCurve (u - 1) w := by
  dsimp [F_N12_AffineCurve]
  rw [hE]
  ring

/-- Moving from the shifted curve back to `E_N12` by `u = X + 1`. -/
theorem E_N12_curve_of_F_N12_curve
    (X Y : ℚ)
    (hF : F_N12_AffineCurve X Y) :
    Y ^ 2 = (X + 1) ^ 3 - (X + 1) ^ 2 - 4 * (X + 1) + 4 := by
  dsimp [F_N12_AffineCurve] at hF
  rw [hF]
  ring

end MazurProof.RationalPointsN12
```

## 3. Converting shifted `X` classification to `MazurProof.E_N12_DegenerateParameter u`

Assuming the existing predicate is definitionally a five-value disjunction, this should be close to compiling.  If the existing predicate is not reducible by `simp`, add the displayed iff lemma next to its definition.

```lean
import Mathlib

namespace MazurProof

/--
Use this only if `simp [MazurProof.E_N12_DegenerateParameter]` does not expose
the five concrete values.  The proof should be `rfl` or `by simp [...]`,
depending on how the predicate is currently defined.
-/
theorem E_N12_DegenerateParameter_iff_rat (u : ℚ) :
    E_N12_DegenerateParameter u ↔
      u = (-2 : ℚ) ∨ u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 4 := by
  -- Preferred if the predicate is a direct def:
  --   rfl
  -- Otherwise:
  --   simp [E_N12_DegenerateParameter]
  simp [E_N12_DegenerateParameter]

end MazurProof

namespace MazurProof.RationalPointsN12

/-- Shifted degenerate `X = u - 1` implies original degenerate parameter `u`. -/
theorem E_N12_DegenerateParameter_of_F_N12_DegenerateX_shift
    {u : ℚ}
    (hX : F_N12_DegenerateX (u - 1)) :
    MazurProof.E_N12_DegenerateParameter u := by
  rw [MazurProof.E_N12_DegenerateParameter_iff_rat]
  rcases hX with hX | hX | hX | hX | hX
  · left
    linarith
  · right; right; left
    linarith
  · right; right; right; left
    linarith
  · right; left
    linarith
  · right; right; right; right
    linarith

/-- A shifted-curve `X`-classification gives the original affine boundary. -/
theorem E_N12_affine_boundary_of_F_N12_degenerate_x_boundary
    (hFboundary : ∀ X Y : ℚ,
      F_N12_AffineCurve X Y → F_N12_DegenerateX X) :
    ∀ u w : ℚ,
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 →
      MazurProof.E_N12_DegenerateParameter u := by
  intro u w hE
  exact E_N12_DegenerateParameter_of_F_N12_DegenerateX_shift
    (hFboundary (u - 1) w (F_N12_curve_of_E_N12_curve u w hE))

/-- Exact shifted point classification gives the original affine boundary. -/
theorem E_N12_affine_boundary_of_F_N12_exact_boundary
    (hFexact : ∀ X Y : ℚ,
      F_N12_AffineCurve X Y → F_N12_ExactAffinePoint X Y) :
    ∀ u w : ℚ,
      w ^ 2 = u ^ 3 - u ^ 2 - 4 * u + 4 →
      MazurProof.E_N12_DegenerateParameter u := by
  exact E_N12_affine_boundary_of_F_N12_degenerate_x_boundary
    (fun X Y hF => F_N12_DegenerateX_of_exactAffinePoint (hFexact X Y hF))

end MazurProof.RationalPointsN12
```

If `E_N12_DegenerateParameter_iff_rat` already exists under another name, use that existing theorem instead of adding a duplicate.

## 4. Wrappers from boundary theorem to the denominator residual

These wrappers should be in `MazurProof.RationalPointsN12`, next to the already-added
`N12NoNontrivialSquareDenominatorResidual_of_affine_boundary`.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/--
Denominator residual from shifted `X`-coordinate classification.
This is probably the best public wrapper for the current N=12 file.
-/
theorem N12NoNontrivialSquareDenominatorResidual_of_F_N12_degenerate_x_boundary
    (hFboundary : ∀ X Y : ℚ,
      F_N12_AffineCurve X Y → F_N12_DegenerateX X) :
    N12NoNontrivialSquareDenominatorResidual := by
  exact N12NoNontrivialSquareDenominatorResidual_of_affine_boundary
    (E_N12_affine_boundary_of_F_N12_degenerate_x_boundary hFboundary)

/-- Denominator residual from exact shifted affine point classification. -/
theorem N12NoNontrivialSquareDenominatorResidual_of_F_N12_exact_boundary
    (hFexact : ∀ X Y : ℚ,
      F_N12_AffineCurve X Y → F_N12_ExactAffinePoint X Y) :
    N12NoNontrivialSquareDenominatorResidual := by
  exact N12NoNontrivialSquareDenominatorResidual_of_F_N12_degenerate_x_boundary
    (fun X Y hF => F_N12_DegenerateX_of_exactAffinePoint (hFexact X Y hF))

end MazurProof.RationalPointsN12
```

If the current wrapper `N12NoNontrivialSquareDenominatorResidual_of_affine_boundary` has its boundary hypothesis written as a local rational predicate rather than `MazurProof.E_N12_DegenerateParameter`, add this bridge once:

```lean
namespace MazurProof.RationalPointsN12

/-- Adapter if the already-added wrapper expects a local `N12DegenerateXQ` predicate. -/
theorem N12DegenerateXQ_of_E_N12_DegenerateParameter
    {u : ℚ}
    (h : MazurProof.E_N12_DegenerateParameter u) :
    N12DegenerateXQ u := by
  -- Usually:
  --   simpa [N12DegenerateXQ] using
  --     (MazurProof.E_N12_DegenerateParameter_iff_rat u).mp h
  simpa [N12DegenerateXQ] using
    (MazurProof.E_N12_DegenerateParameter_iff_rat u).mp h

end MazurProof.RationalPointsN12
```

Then compose through that adapter.

## 5. Public theorem names to prove elsewhere

Do **not** introduce these as axioms in `RationalPointsN12.lean`.  They are theorem names for the future arithmetic file to prove.

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/--
Hard arithmetic theorem, weak public form:
all rational affine points on `F_N12` have degenerate `X`-coordinate.
-/
theorem F_N12_rational_points_degenerate_x
    (X Y : ℚ)
    (hF : F_N12_AffineCurve X Y) :
    F_N12_DegenerateX X := by
  -- Future proof file: rank-zero/torsion/integral-points or 2-isogeny descent.
  -- No axiom here.
  sorry

/--
Hard arithmetic theorem, strong public form:
exact affine rational point list for `F_N12`.
-/
theorem F_N12_rational_points_exact
    (X Y : ℚ)
    (hF : F_N12_AffineCurve X Y) :
    F_N12_ExactAffinePoint X Y := by
  -- Future proof file.
  -- This theorem implies `F_N12_rational_points_degenerate_x`.
  sorry

/-- Public zero-argument theorem once the hard boundary is proved. -/
theorem N12NoNontrivialSquareDenominatorResidual_from_F_N12 :
    N12NoNontrivialSquareDenominatorResidual := by
  exact N12NoNontrivialSquareDenominatorResidual_of_F_N12_exact_boundary
    F_N12_rational_points_exact

end MazurProof.RationalPointsN12
```

In the current file, keep the wrappers parameterized.  Once `F_N12_rational_points_exact` is proved in a later file, add the final zero-argument theorem above in the public boundary file.

## 6. Suggested future file split

Recommended split:

```text
FLT/Assumptions/MazurProof/RationalPointsN12.lean
```

Contains the current denominator work and imports only the public boundary API if a closed theorem is needed.

```text
FLT/Assumptions/MazurProof/RationalPointsN12/Boundary.lean
```

Contains:

```lean
F_N12_AffineCurve
F_N12_DegenerateX
F_N12_ExactAffinePoint
F_N12_curve_of_E_N12_curve
E_N12_curve_of_F_N12_curve
F_N12_DegenerateX_of_exactAffinePoint
E_N12_DegenerateParameter_of_F_N12_DegenerateX_shift
E_N12_affine_boundary_of_F_N12_degenerate_x_boundary
E_N12_affine_boundary_of_F_N12_exact_boundary
N12NoNontrivialSquareDenominatorResidual_of_F_N12_degenerate_x_boundary
N12NoNontrivialSquareDenominatorResidual_of_F_N12_exact_boundary
```

All of these are elementary and should be sorry-free.

```text
FLT/Assumptions/MazurProof/RationalPointsN12/Public.lean
```

Exports the hard theorem names after they are proved:

```lean
F_N12_rational_points_degenerate_x
F_N12_rational_points_exact
N12NoNontrivialSquareDenominatorResidual_from_F_N12
```

This file may import the proof internals, but clients only use the names above.

```text
FLT/Assumptions/MazurProof/RationalPointsN12/Descent/*.lean
```

Private implementation files for the arithmetic proof, for example:

```text
Descent/BasicCurve.lean
Descent/Torsion.lean
Descent/TwoIsogenySelmer.lean
Descent/LocalSolubility.lean
Descent/PointClassification.lean
```

The N12 obstruction file should never mention Selmer groups, local covers, Magma/PARI certificates, or 2-isogeny internals directly.  It should depend only on the public theorem

```lean
F_N12_rational_points_degenerate_x
```

or, preferably, the stronger

```lean
F_N12_rational_points_exact
```

plus the elementary wrappers above.

## 7. Audit notes

The shifted point list is:

```text
X = -3, 0, 1, -1, 3
```

with exact affine points

```text
(-3, 0), (0, 0), (1, 0), (-1, ±2), (3, ±6).
```

These correspond to original `u = X + 1` values

```text
u = -2, 1, 2, 0, 4,
```

which are exactly the degenerate N=12 parameters

```text
u ∈ {-2, 0, 1, 2, 4}.
```

The ordering of disjunctions in `F_N12_DegenerateX` need not match the ordering in `E_N12_DegenerateParameter`; the conversion lemma handles the reordering with `linarith`.