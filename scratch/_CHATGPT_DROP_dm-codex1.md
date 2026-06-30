# Q2368 (dm-codex1): local Lean pieces for the C12 → E24 reduction

This drop gives the local algebraic pieces for the current N=12 frontier in `FLT/Assumptions/MazurProof/RationalPointsN12.lean`.

The hard arithmetic input is isolated as the x-coordinate theorem for the affine elliptic curve

```text
E24 : V^2 = U^3 - U^2 - 4U + 4.
```

The local proof then uses only the map

```text
U(x,y) = 2*(y+1)/x^2,
V(x,y) = x*(U(x,y)^2 - 4)/2,
```

the relation

```text
x^2 * (U^2 - 4) = 4 * (U - 1),
```

and a finite split over `U ∈ {-2,1,2,0,4}`.

I could not run Lean in the local worktree through the GitHub connector, but the code is written to keep the denominator-clearing goals small. The only tactic-sensitive line is the `field_simp [hx, hx2]` in `c12_to_e24_U_relation`; if your local imports already expose `field_simp`, `ring_nf`, `norm_num`, and `nlinarith`, no extra import should be needed.

## Lean code

If the target file already contains some of these definitions, omit the duplicates and keep the theorem bodies. Standalone, `Mathlib.Tactic` should be enough for the tactics used here; the project file may already import enough.

```lean
import Mathlib.Tactic

/-- Rational affine Eisenstein quartic. -/
def RatQuarticEisenstein (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 4 - x ^ 2 + 1

/-- The rational x-coordinate classification needed downstream. -/
def RatQuarticEisensteinXClassification : Prop :=
  ∀ {x y : ℚ}, RatQuarticEisenstein x y → x = 0 ∨ x ^ 2 = 1

/-- The affine elliptic curve birational to `RatQuarticEisenstein`. -/
def E24 (U V : ℚ) : Prop :=
  V ^ 2 = U ^ 3 - U ^ 2 - 4 * U + 4

/-- The `U`-coordinate of the rational map `C12 → E24`, defined away from `x = 0`. -/
def C12ToE24U (x y : ℚ) : ℚ :=
  2 * (y + 1) / x ^ 2

/-- The `V`-coordinate of the rational map `C12 → E24`, defined away from `x = 0`. -/
def C12ToE24V (x y : ℚ) : ℚ :=
  x * ((C12ToE24U x y) ^ 2 - 4) / 2

/-- Full affine point-list version of the hard residual, if you want the audited stronger
interface.  The proof below only needs the weaker `E24XCoordinateClassification`. -/
def E24AffineRationalPoints : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    (U = -2 ∧ V = 0) ∨
    (U = 1 ∧ V = 0) ∨
    (U = 2 ∧ V = 0) ∨
    (U = 0 ∧ V = 2) ∨
    (U = 0 ∧ V = -2) ∨
    (U = 4 ∧ V = 6) ∨
    (U = 4 ∧ V = -6)

/-- The exact hard residual needed for the quartic x-classification. -/
def E24XCoordinateClassification : Prop :=
  ∀ {U V : ℚ}, E24 U V →
    U = -2 ∨ U = 1 ∨ U = 2 ∨ U = 0 ∨ U = 4

/-- The full affine list implies the weaker x-coordinate list. -/
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

/-- Key relation for the map from `C12` to `E24`.

With `U = 2*(y+1)/x^2`, the quartic equation implies
`x^2*(U^2 - 4) = 4*(U - 1)`. -/
theorem c12_to_e24_U_relation {x y : ℚ}
    (hC : RatQuarticEisenstein x y)
    (hx : x ≠ 0) :
    x ^ 2 * ((C12ToE24U x y) ^ 2 - 4) =
      4 * (C12ToE24U x y - 1) := by
  unfold RatQuarticEisenstein at hC
  unfold C12ToE24U
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  field_simp [hx, hx2]
  ring_nf
  nlinarith [hC]

/-- The rational map sends affine `C12` points with `x ≠ 0` to affine `E24` points. -/
theorem c12_to_e24_map_correct {x y : ℚ}
    (hC : RatQuarticEisenstein x y)
    (hx : x ≠ 0) :
    E24 (C12ToE24U x y) (C12ToE24V x y) := by
  unfold E24 C12ToE24V
  set U : ℚ := C12ToE24U x y with hU
  have hrelU : x ^ 2 * (U ^ 2 - 4) = 4 * (U - 1) := by
    simpa [hU] using c12_to_e24_U_relation (x := x) (y := y) hC hx
  calc
    (x * (U ^ 2 - 4) / 2) ^ 2
        = (x ^ 2 * (U ^ 2 - 4)) * (U ^ 2 - 4) / 4 := by
            ring
    _ = (4 * (U - 1)) * (U ^ 2 - 4) / 4 := by
            rw [hrelU]
    _ = U ^ 3 - U ^ 2 - 4 * U + 4 := by
            ring

/-- From the finite `U`-coordinate list on `E24`, deduce the rational
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
    · -- `U = -2`: relation gives `0 = -12`, contradiction.
      exfalso
      have hrel' :
          x ^ 2 * (((-2 : ℚ) ^ 2) - 4) = 4 * ((-2 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
    · -- `U = 1`: relation gives `-3*x^2 = 0`, contradicting `x ≠ 0`.
      exfalso
      have hrel' :
          x ^ 2 * (((1 : ℚ) ^ 2) - 4) = 4 * ((1 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
      have hx0 : x = 0 := by
        apply sq_eq_zero_iff.mp
        nlinarith [hrel']
      exact hx hx0
    · -- `U = 2`: relation gives `0 = 4`, contradiction.
      exfalso
      have hrel' :
          x ^ 2 * (((2 : ℚ) ^ 2) - 4) = 4 * ((2 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
    · -- `U = 0`: relation gives `-4*x^2 = -4`, hence `x^2 = 1`.
      have hrel' :
          x ^ 2 * (((0 : ℚ) ^ 2) - 4) = 4 * ((0 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
      nlinarith [hrel']
    · -- `U = 4`: relation gives `12*x^2 = 12`, hence `x^2 = 1`.
      have hrel' :
          x ^ 2 * (((4 : ℚ) ^ 2) - 4) = 4 * ((4 : ℚ) - 1) := by
        simpa [hU] using hrel
      norm_num at hrel'
      nlinarith [hrel']
```

## Dependency order for insertion

1. Add the rational definitions: `RatQuarticEisenstein`, `E24`, `C12ToE24U`, `C12ToE24V`.
2. Add either the hard residual `E24XCoordinateClassification`, or the stronger `E24AffineRationalPoints` plus `e24_xCoordinateClassification_of_affine`.
3. Add `c12_to_e24_U_relation`.
4. Add `c12_to_e24_map_correct`.
5. Add `ratQuarticEisensteinXClassification_of_e24_x`.
6. Compose with the existing Q2360-style theorem

   ```lean
   theorem eisensteinQuarticSquareClassification_of_rat_x
       (hRat : RatQuarticEisensteinXClassification) :
       EisensteinQuarticSquareClassification := ...
   ```

   to obtain the integer theorem from the one residual `E24XCoordinateClassification`.

## Sanity checks preserved by this code

- It does not claim the quartic has no solutions. The diagonal cases `m^2 = n^2` and the axis cases `m = 0` or `n = 0` remain allowed.
- The map is used only under `x ≠ 0`; the `x = 0` branch of `RatQuarticEisensteinXClassification` is handled before division by `x^2`.
- The finite split rules out `U = -2`, `U = 1`, and `U = 2` only for points in the image of affine `C12` with `x ≠ 0`; those `U` values may still occur on `E24` itself.
- The surviving image cases are exactly `U = 0` and `U = 4`, and both give `x^2 = 1`, not `x = 1`.
