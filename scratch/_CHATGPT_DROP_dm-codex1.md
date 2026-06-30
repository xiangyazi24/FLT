# Q2371 (dm-codex1): small-step Lean algebra for the C12 → E24 local reduction

This drop replaces the previous `field_simp`-heavy local algebra with a small-step proof. The key point is to use the denominator identity

```text
U * x^2 = 2 * (y + 1)
```

for `U = 2*(y+1)/x^2`, then cancel a final factor of `x^2`. The proof of the relation does not call `field_simp` or `ring_nf`; it uses only `div_mul_cancel₀`, `mul_right_cancel₀`, `rw`, and small `ring` goals.

The code below is standalone. In `FLT/Assumptions/MazurProof/RationalPointsN12.lean`, omit any definitions that already exist and paste the theorem bodies after the corresponding definitions.

```lean
import Mathlib.Tactic

/-- Rational affine Eisenstein quartic. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- Rational x-coordinate classification for the Eisenstein quartic. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1

/-- The affine elliptic curve birational to `RatQuarticEisenstein`. -/
def E24 (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4

/-- The `U`-coordinate of the rational map `C12 → E24`, away from `x = 0`. -/
def C12ToE24U (x y : ℚ) : ℚ :=
  2 * (y + 1) / x ^ 2

/-- The `V`-coordinate of the rational map `C12 → E24`, away from `x = 0`. -/
def C12ToE24V (x y : ℚ) : ℚ :=
  x * ((C12ToE24U x y) ^ 2 - 4) / 2

/-- Optional full affine point-list residual.  The local proof below only needs
`E24XCoordinateClassification`. -/
def E24AffineRationalPoints : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    (U = -2 ∧ V = 0) ∨
    (U = 1 ∧ V = 0) ∨
    (U = 2 ∧ V = 0) ∨
    (U = 0 ∧ V = 2) ∨
    (U = 0 ∧ V = -2) ∨
    (U = 4 ∧ V = 6) ∨
    (U = 4 ∧ V = -6)

/-- The exact residual needed locally: only the possible affine `U`-coordinates on `E24`. -/
def E24XCoordinateClassification : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    U = -2 ∨ U = 1 ∨ U = 2 ∨ U = 0 ∨ U = 4

/-- Full affine list implies the weaker `U`-coordinate list. -/
theorem e24_xCoordinateClassification_of_affine
    (h : E24AffineRationalPoints) :
    E24XCoordinateClassification := by
  intro U V hE
  rcases h hE with hP | hP | hP | hP | hP | hP | hP
  · exact Or.inl hP.1
  · exact Or.inr (Or.inl hP.1)
  · exact Or.inr (Or.inr (Or.inl hP.1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hP.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hP.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hP.1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hP.1)))

/-- Small-step proof of the key relation for the map from `C12` to `E24`.

No `field_simp` is used.  The proof first records
`U * x^2 = 2*(y+1)`, proves equality after multiplying by `x^2`, and then
cancels the nonzero factor `x^2`. -/
theorem c12_to_e24_U_relation {x y : ℚ}
    (hC : RatQuarticEisenstein x y)
    (hx : x ≠ 0) :
    x ^ 2 * ((C12ToE24U x y) ^ 2 - 4) =
      4 * (C12ToE24U x y - 1) := by
  unfold RatQuarticEisenstein at hC
  set U : ℚ := C12ToE24U x y with hU
  change x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1)
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hUx : U * x ^ 2 = 2 * (y + 1) := by
    rw [hU]
    unfold C12ToE24U
    simpa using (div_mul_cancel₀ (2 * (y + 1)) hx2)
  suffices hmul :
      (x ^ 2 * (U ^ 2 - 4)) * x ^ 2 = (4 * (U - 1)) * x ^ 2 by
    exact mul_right_cancel₀ hx2 hmul
  calc
    (x ^ 2 * (U ^ 2 - 4)) * x ^ 2
        = (U * x ^ 2) ^ 2 - 4 * x ^ 4 := by
            ring
    _ = (2 * (y + 1)) ^ 2 - 4 * x ^ 4 := by
            rw [hUx]
    _ = 4 * (y ^ 2 + 2 * y + 1 - x ^ 4) := by
            ring
    _ = 4 * ((x ^ 4 - x ^ 2 + 1) + 2 * y + 1 - x ^ 4) := by
            rw [hC]
    _ = 4 * (2 * (y + 1) - x ^ 2) := by
            ring
    _ = (4 * (U - 1)) * x ^ 2 := by
            rw [← hUx]
            ring

/-- The rational map sends affine `C12` points with `x ≠ 0` to affine `E24` points.

This proof uses only `c12_to_e24_U_relation` and tiny `ring` goals. -/
theorem c12_to_e24_map_correct {x y : ℚ}
    (hC : RatQuarticEisenstein x y)
    (hx : x ≠ 0) :
    E24 (C12ToE24U x y) (C12ToE24V x y) := by
  unfold E24 C12ToE24V
  set U : ℚ := C12ToE24U x y with hU
  change (x * (U ^ 2 - 4) / 2) ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4
  have hrel : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1) := by
    simpa [hU] using c12_to_e24_U_relation (x := x) (y := y) hC hx
  calc
    (x * (U ^ 2 - 4) / 2) ^ 2
        = (x ^ 2 * (U ^ 2 - 4)) * (U ^ 2 - 4) / 4 := by
            ring
    _ = (4 * (U - 1)) * (U ^ 2 - 4) / 4 := by
            rw [hrel]
    _ = U ^ 3 - U ^ 2 - 4 * U + 4 := by
            ring

/-- From the finite `U`-coordinate classification on `E24`, deduce the rational
x-coordinate classification on `C12`. -/
theorem ratQuarticEisensteinXClassification_of_e24_x
    (hE : E24XCoordinateClassification) :
    RatQuarticEisensteinXClassification := by
  intro x y hC
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hrel :
        x ^ 2 * ((C12ToE24U x y) ^ 2 - 4) =
          4 * (C12ToE24U x y - 1) :=
      c12_to_e24_U_relation (x := x) (y := y) hC hx
    have hmap : E24 (C12ToE24U x y) (C12ToE24V x y) :=
      c12_to_e24_map_correct (x := x) (y := y) hC hx
    rcases hE (U := C12ToE24U x y) (V := C12ToE24V x y) hmap with
      hU | hU | hU | hU | hU
    · -- `U = -2`: the relation gives `0 = -12`.
      exfalso
      have hrel' :
          x ^ 2 * (((-2 : ℚ) ^ 2) - 4) = 4 * ((-2 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
    · -- `U = 1`: the relation gives `-3*x^2 = 0`, hence `x = 0`, contradiction.
      exfalso
      have hrel' :
          x ^ 2 * (((1 : ℚ) ^ 2) - 4) = 4 * ((1 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
      have hx2zero : x ^ 2 = 0 := by
        linarith [hrel']
      exact hx (sq_eq_zero_iff.mp hx2zero)
    · -- `U = 2`: the relation gives `0 = 4`.
      exfalso
      have hrel' :
          x ^ 2 * (((2 : ℚ) ^ 2) - 4) = 4 * ((2 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
    · -- `U = 0`: the relation gives `-4*x^2 = -4`, hence `x^2 = 1`.
      have hrel' :
          x ^ 2 * (((0 : ℚ) ^ 2) - 4) = 4 * ((0 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
      linarith [hrel']
    · -- `U = 4`: the relation gives `12*x^2 = 12`, hence `x^2 = 1`.
      have hrel' :
          x ^ 2 * (((4 : ℚ) ^ 2) - 4) = 4 * ((4 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
      linarith [hrel']
```

## Notes on tactic robustness

- The relation proof contains no `field_simp` and no `ring_nf`.
- The only divisions handled by automation are divisions by numerals in `ring`, and the one variable denominator is eliminated explicitly by `div_mul_cancel₀`.
- The finite split uses `norm_num` only after substituting a concrete rational value for `U`; those goals are tiny.
- The `U = 1`, `U = 0`, and `U = 4` branches use `linarith`, not `nlinarith`, after `norm_num`; at that point `x^2` is just a linear atom.

## If a local theorem name differs

Lean 4.31 Mathlib should have both `div_mul_cancel₀` and `mul_right_cancel₀`. If the local environment prefers the iff-style cancellation lemma, replace only this line:

```lean
exact mul_right_cancel₀ hx2 hmul
```

with:

```lean
exact (mul_right_inj' hx2).mp hmul
```

No mathematical change is involved.
