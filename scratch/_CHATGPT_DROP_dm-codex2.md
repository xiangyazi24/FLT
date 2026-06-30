# Q2377 (dm-codex2): local E24/E1 shift and point-list plumbing

```lean
import FLT.Assumptions.MazurProof.RationalPointsN12

namespace MazurProof.RationalPointsN12

/-!
If `E24` or `E24XCoordinateClassification` already exist from Q2368, do not
re-add those duplicate `def`s.  The theorem proofs below are otherwise local
and should be pasteable unchanged.
-/

/-- The shifted hard residual curve. -/
def E24 (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4

/-- The convenient translated curve, with `X = U - 1`. -/
def E1 (X Y : ℚ) : Prop :=
  Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X

/-- Full affine rational point list for `E1`.  This is the hard input. -/
def E1AffinePointList : Prop :=
  ∀ {X Y : ℚ}, E1 X Y →
    (X = -3 ∧ Y = 0) ∨
    (X = 0 ∧ Y = 0) ∨
    (X = 1 ∧ Y = 0) ∨
    (X = -1 ∧ Y = 2) ∨
    (X = -1 ∧ Y = -2) ∨
    (X = 3 ∧ Y = 6) ∨
    (X = 3 ∧ Y = -6)

/-- Full affine rational point list for `E24`. -/
def E24AffineRationalPoints : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    (U = -2 ∧ V = 0) ∨
    (U = 1 ∧ V = 0) ∨
    (U = 2 ∧ V = 0) ∨
    (U = 0 ∧ V = 2) ∨
    (U = 0 ∧ V = -2) ∨
    (U = 4 ∧ V = 6) ∨
    (U = 4 ∧ V = -6)

/-- X-coordinate-only classification for `E24`. -/
def E24XCoordinateClassification : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    U = -2 ∨ U = 0 ∨ U = 1 ∨ U = 2 ∨ U = 4

/-- Forward translation: `E24(U,V)` gives `E1(U-1,V)`. -/
theorem e1_of_e24_shift {U V : ℚ}
    (h : E24 U V) :
    E1 (U - 1) V := by
  unfold E24 E1 at *
  calc
    V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4 := h
    _ = (U - 1) ^ 3 + 2 * (U - 1) ^ 2 - 3 * (U - 1) := by
      ring

/-- Reverse translation, useful for sanity checks and alternative wrappers. -/
theorem e24_of_e1_shift {X Y : ℚ}
    (h : E1 X Y) :
    E24 (X + 1) Y := by
  unfold E1 E24 at *
  calc
    Y ^ 2 = X ^ 3 + 2 * X ^ 2 - 3 * X := h
    _ = (X + 1) ^ 3 - (X + 1) ^ 2 - 4 * (X + 1) + 4 := by
      ring

/-- Tiny linear helper for converting an `E1` `X`-coordinate to an `E24` `U`. -/
theorem rat_eq_of_sub_one_eq_add_one {U A B : ℚ}
    (hUA : U - 1 = A) (hAB : A + 1 = B) :
    U = B := by
  calc
    U = (U - 1) + 1 := by ring
    _ = A + 1 := by rw [hUA]
    _ = B := hAB

/-- Translate the hard `E1` full point list into the full `E24` point list. -/
theorem E24AffineRationalPoints_of_E1AffineRationalPoints
    (hpts : E1AffinePointList) :
    E24AffineRationalPoints := by
  intro U V hE24
  have hE1 : E1 (U - 1) V := e1_of_e24_shift hE24
  rcases hpts (X := U - 1) (Y := V) hE1 with
      h_m3 | h_0 | h_1 | h_neg1_pos | h_neg1_neg | h_3_pos | h_3_neg
  · rcases h_m3 with ⟨hX, hY⟩
    exact Or.inl ⟨rat_eq_of_sub_one_eq_add_one hX (by norm_num), hY⟩
  · rcases h_0 with ⟨hX, hY⟩
    exact Or.inr (Or.inl ⟨rat_eq_of_sub_one_eq_add_one hX (by norm_num), hY⟩)
  · rcases h_1 with ⟨hX, hY⟩
    exact Or.inr (Or.inr (Or.inl ⟨rat_eq_of_sub_one_eq_add_one hX (by norm_num), hY⟩))
  · rcases h_neg1_pos with ⟨hX, hY⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rat_eq_of_sub_one_eq_add_one hX (by norm_num), hY⟩)))
  · rcases h_neg1_neg with ⟨hX, hY⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rat_eq_of_sub_one_eq_add_one hX (by norm_num), hY⟩))))
  · rcases h_3_pos with ⟨hX, hY⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rat_eq_of_sub_one_eq_add_one hX (by norm_num), hY⟩)))))
  · rcases h_3_neg with ⟨hX, hY⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rat_eq_of_sub_one_eq_add_one hX (by norm_num), hY⟩)))))

/-- Full `E24` affine list implies the X-coordinate-only classification. -/
theorem e24_xCoordinateClassification_of_e24_points
    (hpts : E24AffineRationalPoints) :
    E24XCoordinateClassification := by
  intro U V hE24
  rcases hpts (U := U) (V := V) hE24 with
      h_m2 | h_1 | h_2 | h_0_pos | h_0_neg | h_4_pos | h_4_neg
  · exact Or.inl h_m2.1
  · exact Or.inr (Or.inr (Or.inl h_1.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h_2.1)))
  · exact Or.inr (Or.inl h_0_pos.1)
  · exact Or.inr (Or.inl h_0_neg.1)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h_4_pos.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h_4_neg.1)))

/-- Direct wrapper from the hard `E1` point-list theorem to `E24` X-coordinates. -/
theorem e24_xCoordinateClassification_of_e1_points
    (hpts : E1AffinePointList) :
    E24XCoordinateClassification := by
  exact e24_xCoordinateClassification_of_e24_points
    (E24AffineRationalPoints_of_E1AffineRationalPoints hpts)

end MazurProof.RationalPointsN12
```

## Notes

The polynomial shift is exactly

```lean
(U - 1)^3 + 2*(U - 1)^2 - 3*(U - 1)
  = U^3 - U^2 - 4*U + 4.
```

So `e1_of_e24_shift` is just `unfold` plus a single tiny `ring` goal.  The point-list conversion uses no point type, no torsion API, and no hard arithmetic.  The only coordinate arithmetic after the hard `E1AffinePointList` theorem is the local helper

```lean
U - 1 = A → A + 1 = B → U = B
```

with `norm_num` closing the seven rational constants.

If Q2368 already defined `E24XCoordinateClassification` with a different disjunction order, keep `E24AffineRationalPoints_of_E1AffineRationalPoints` unchanged and adjust only the final seven `Or.inr` nestings in `e24_xCoordinateClassification_of_e24_points`.
