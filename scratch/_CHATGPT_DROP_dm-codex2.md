# Q2380 (dm-codex2): C12 to E24 local bridge

```lean
import Mathlib

namespace MazurProof.RationalPointsN12

/-- The rational quartic `C12`: `y^2 = x^4 - x^2 + 1`. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- The elliptic curve model used for the `N = 12` obstruction. -/
def E24 (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4

/-- The `U` coordinate of the standard rational map `C12 -> E24`. -/
def C12ToE24U (x y : ℚ) : ℚ :=
  2 * (y + 1) / x ^ 2

/-- The `V` coordinate of the standard rational map `C12 -> E24`. -/
def C12ToE24V (x y : ℚ) : ℚ :=
  x * (C12ToE24U x y ^ 2 - 4) / 2

/-- Residual hard input: the possible `U`-coordinates on `E24`.

The disjunction order is intentionally
`U = -2`, `U = 1`, `U = 2`, `U = 0`, `U = 4`.
-/
def E24XCoordinateClassification : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    U = -2 ∨ U = 1 ∨ U = 2 ∨ U = 0 ∨ U = 4

private lemma c12_to_e24_U_relation_clear_den {x y : ℚ}
    (hC : RatQuarticEisenstein x y) :
    (2 * (y + 1)) ^ 2 - 4 * (x ^ 2) ^ 2 =
      4 * (2 * (y + 1)) - 4 * x ^ 2 := by
  unfold RatQuarticEisenstein at hC
  ring_nf at hC ⊢
  nlinarith

/-- The denominator-cleared relation for the `U` coordinate of the map. -/
theorem c12_to_e24_U_relation {x y : ℚ}
    (hC : RatQuarticEisenstein x y) (hx : x ≠ 0) :
    x ^ 2 * (C12ToE24U x y ^ 2 - 4) =
      4 * (C12ToE24U x y - 1) := by
  set u : ℚ := C12ToE24U x y with hu
  set z : ℚ := x ^ 2 with hz
  set a : ℚ := 2 * (y + 1) with ha
  have hz_ne : z ≠ 0 := by
    rw [hz]
    exact pow_ne_zero 2 hx
  have hu_mul : u * z = a := by
    rw [hu, hz, ha]
    unfold C12ToE24U
    exact div_mul_cancel₀ (2 * (y + 1)) (pow_ne_zero 2 hx)
  have hclear : a ^ 2 - 4 * z ^ 2 = 4 * a - 4 * z := by
    rw [ha, hz]
    exact c12_to_e24_U_relation_clear_den hC
  apply mul_right_cancel₀ hz_ne
  calc
    (z * (u ^ 2 - 4)) * z = (u * z) ^ 2 - 4 * z ^ 2 := by
      ring
    _ = a ^ 2 - 4 * z ^ 2 := by
      rw [hu_mul]
    _ = 4 * a - 4 * z := hclear
    _ = (4 * (u - 1)) * z := by
      rw [← hu_mul]
      ring

private lemma e24_of_U_relation {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1)) :
    E24 U (x * (U ^ 2 - 4) / 2) := by
  unfold E24
  calc
    (x * (U ^ 2 - 4) / 2) ^ 2
        = (x ^ 2 * (U ^ 2 - 4)) * (U ^ 2 - 4) / 4 := by
      ring
    _ = (4 * (U - 1)) * (U ^ 2 - 4) / 4 := by
      rw [hrel]
    _ = U ^ 3 - U ^ 2 - 4 * U + 4 := by
      ring

/-- The rational map from the nonzero-`x` part of `C12` lands on `E24`. -/
theorem c12_to_e24_map_correct {x y : ℚ}
    (hC : RatQuarticEisenstein x y) (hx : x ≠ 0) :
    E24 (C12ToE24U x y) (C12ToE24V x y) := by
  unfold C12ToE24V
  exact e24_of_U_relation (x := x) (U := C12ToE24U x y)
    (c12_to_e24_U_relation hC hx)

private lemma c12_relation_false_of_U_eq_neg_two {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = -2) : False := by
  rw [hU] at hrel
  norm_num at hrel

private lemma c12_relation_false_of_U_eq_one {x U : ℚ}
    (hx : x ≠ 0)
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 1) : False := by
  rw [hU] at hrel
  norm_num at hrel
  have hx2_zero : x ^ 2 = 0 := by
    nlinarith
  exact (pow_ne_zero 2 hx) hx2_zero

private lemma c12_relation_false_of_U_eq_two {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 2) : False := by
  rw [hU] at hrel
  norm_num at hrel

private lemma c12_relation_x_sq_eq_one_of_U_eq_zero {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 0) :
    x ^ 2 = 1 := by
  rw [hU] at hrel
  norm_num at hrel
  nlinarith

private lemma c12_relation_x_sq_eq_one_of_U_eq_four {x U : ℚ}
    (hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1))
    (hU : U = 4) :
    x ^ 2 = 1 := by
  rw [hU] at hrel
  norm_num at hrel
  nlinarith

/-- The `E24` `U`-coordinate classification forces the original quartic `x` to be
zero or satisfy `x^2 = 1`. -/
theorem ratQuarticEisensteinXClassification_of_e24_x
    (hE24x : E24XCoordinateClassification)
    {x y : ℚ}
    (hC : RatQuarticEisenstein x y) :
    x = 0 ∨ x ^ 2 = 1 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · have hrel :
        x ^ 2 * (C12ToE24U x y ^ 2 - 4) =
          4 * (C12ToE24U x y - 1) :=
      c12_to_e24_U_relation hC hx
    have hE24 : E24 (C12ToE24U x y) (C12ToE24V x y) :=
      c12_to_e24_map_correct hC hx
    rcases hE24x hE24 with hU_neg_two | hU_one | hU_two | hU_zero | hU_four
    · exact False.elim (c12_relation_false_of_U_eq_neg_two hrel hU_neg_two)
    · exact False.elim (c12_relation_false_of_U_eq_one hx hrel hU_one)
    · exact False.elim (c12_relation_false_of_U_eq_two hrel hU_two)
    · exact Or.inr (c12_relation_x_sq_eq_one_of_U_eq_zero hrel hU_zero)
    · exact Or.inr (c12_relation_x_sq_eq_one_of_U_eq_four hrel hU_four)

end MazurProof.RationalPointsN12
```

## Brief fragile-line notes

- If this is pasted directly into `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, omit the `import Mathlib` line if the file already has stronger local imports.
- The only polynomial normalization in the quartic part is isolated in `c12_to_e24_U_relation_clear_den`; after `ring_nf at hC ⊢`, the goal is the cleared identity equivalent to `hC`.
- In `c12_to_e24_U_relation`, after `apply mul_right_cancel₀ hz_ne`, the expected goal shape is
  ```lean
  (z * (u ^ 2 - 4)) * z = (4 * (u - 1)) * z
  ```
  and the `calc` block uses only `hu_mul : u * z = a` plus `ring`.
- The final classification branches intentionally follow the residual order `-2, 1, 2, 0, 4`; the `U = 0` and `U = 4` branches reduce by `norm_num at hrel` to linear equations in `x ^ 2`, then `nlinarith` proves `x ^ 2 = 1`.
